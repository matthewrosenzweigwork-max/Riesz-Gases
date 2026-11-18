import HRS.Prob.Metrics

/-!
# Gaussian comparison with an additive error (package MF-01, packet P13b)

See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P13b.

* `traceNormMatrix_le_sum`: `‖Q‖_{S₁} ≤ ∑_{ij} |Q_{ij}|`;
* `smoothDist_le_of_gaussian_part`: if `G ~ N(0,M)` then
  `d_{C²}(law X, N(0,Σ)) ≤ E‖X - G‖ + ½‖M - Σ‖_{S₁}`.

The route is `smoothDist_triangle`, the `1`-Lipschitz property of the `C¹` unit ball for the
first term and `gaussian_covariance_comparison` for the second.  No first-moment lemma for
`multivariateGaussian` is needed: the integrability of `‖G‖` is a hypothesis.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.PDE.MFLinear

/-- P13b: trace norm bounded by the entries. -/
theorem traceNormMatrix_le_sum {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) :
    traceNormMatrix Q ≤ ∑ i, ∑ j, |Q i j| := by
  refine ciSup_le fun U => ?_
  have hU : ∀ i j, |(U : Matrix (Fin p) (Fin p) ℝ) i j| ≤ 1 := by
    intro i j
    have := entry_norm_bound_of_unitary U.2 i j
    simpa using this
  rw [Finset.sum_comm (f := fun i j => |Q i j|)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  calc Q j i * (U : Matrix (Fin p) (Fin p) ℝ) j i
      ≤ |Q j i * (U : Matrix (Fin p) (Fin p) ℝ) j i| := le_abs_self _
    _ = |Q j i| * |(U : Matrix (Fin p) (Fin p) ℝ) j i| := abs_mul _ _
    _ ≤ |Q j i| * 1 := by gcongr; exact hU j i
    _ = |Q j i| := mul_one _

/-- The `C²`-smooth distance between two centered Gaussians is at most `½ ‖Q - Q'‖_{S₁}`. -/
theorem smoothDist_two_gaussian_covariance {p : ℕ} (Q Q' : Matrix (Fin p) (Fin p) ℝ)
    (hQ : Q.PosSemidef) (hQ' : Q'.PosSemidef) :
    smoothDist 2 (ProbabilityTheory.multivariateGaussian 0 Q)
        (ProbabilityTheory.multivariateGaussian 0 Q') ≤
      (1 / 2) * traceNormMatrix (Q - Q') := by
  have hT := traceNormMatrix_nonneg (Q - Q')
  have : Nonempty (CbUnitBall (EuclideanSpace ℝ (Fin p)) 2) := ⟨⟨0, zero_mem_cbUnitBall 2⟩⟩
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  obtain ⟨hΦ, hb, hc⟩ := Φ.2
  have hb2 := hb 2 le_rfl
  have hsum : (⨆ x, ‖iteratedFDeriv ℝ 2 Φ.1 x‖) ≤ 1 := by
    refine le_trans ?_ hc
    unfold cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z : EuclideanSpace ℝ (Fin p),
      ‖iteratedFDeriv ℝ j Φ.1 z‖) (fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _)
      (by simp : 2 ∈ Finset.range (2 + 1))
  have := gaussian_covariance_comparison Q Q' hQ hQ' Φ.1 hΦ hb2
  refine this.trans ?_
  have h0 : 0 ≤ ⨆ x, ‖iteratedFDeriv ℝ 2 Φ.1 x‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  nlinarith

/-- P13b: smooth distance of `X = G + Y` to `N(0,Σ)` when `G ~ N(0,M)`:
`d_{C²} ≤ E‖Y‖ + ½‖M - Σ‖_{S₁}`. -/
theorem smoothDist_le_of_gaussian_part {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : ℕ} (X G : Ω → EuclideanSpace ℝ (Fin p)) (hX : Measurable X)
    (hG : Measurable G) (hXi : Integrable (fun ω => ‖X ω‖) P)
    (hGi : Integrable (fun ω => ‖G ω‖) P) (M Sg : Matrix (Fin p) (Fin p) ℝ) (hM : M.PosSemidef)
    (hSg : Sg.PosSemidef) (hlaw : law P G = ProbabilityTheory.multivariateGaussian 0 M) :
    smoothDist 2 (law P X) (ProbabilityTheory.multivariateGaussian 0 Sg) ≤
      (∫ ω, ‖X ω - G ω‖ ∂P) + (1 / 2) * traceNormMatrix (M - Sg) := by
  have : IsProbabilityMeasure (law P X) := inferInstance
  have : IsProbabilityMeasure (law P G) := inferInstance
  have : IsProbabilityMeasure (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) Sg) :=
    inferInstance
  refine (smoothDist_triangle 2 (law P X) (law P G) _).trans ?_
  refine add_le_add ?_ ?_
  · -- first term: `E‖X - G‖`
    have hsub : Integrable (fun ω => ‖X ω - G ω‖) P :=
      Integrable.mono' (hXi.add hGi) ((hX.sub hG).norm.aestronglyMeasurable)
        (ae_of_all _ fun ω => by
          simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using norm_sub_le (X ω) (G ω))
    have : Nonempty (CbUnitBall (EuclideanSpace ℝ (Fin p)) 2) :=
      ⟨⟨0, zero_mem_cbUnitBall 2⟩⟩
    refine Real.iSup_le (fun Φ => ?_) (integral_nonneg fun ω => norm_nonneg _)
    have hΦc : Continuous Φ.1 := Φ.2.1.continuous
    have hΦ1 : Φ.1 ∈ CbUnitBall (EuclideanSpace ℝ (Fin p)) 1 := cbUnitBall_mono Φ.2
    have hint : ∀ Y : Ω → EuclideanSpace ℝ (Fin p), Measurable Y → Integrable (fun ω => Φ.1 (Y ω)) P :=
      fun Y hY => Integrable.of_bound (hΦc.measurable.comp hY).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by simpa using abs_apply_le_of_mem Φ.2 (Y ω))
    have e1 : ∫ z, Φ.1 z ∂(law P X) = ∫ ω, Φ.1 (X ω) ∂P :=
      integral_map hX.aemeasurable hΦc.aestronglyMeasurable
    have e2 : ∫ z, Φ.1 z ∂(law P G) = ∫ ω, Φ.1 (G ω) ∂P :=
      integral_map hG.aemeasurable hΦc.aestronglyMeasurable
    rw [e1, e2, ← integral_sub (hint X hX) (hint G hG)]
    calc |∫ ω, (Φ.1 (X ω) - Φ.1 (G ω)) ∂P|
        = ‖∫ ω, (Φ.1 (X ω) - Φ.1 (G ω)) ∂P‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ ω, ‖Φ.1 (X ω) - Φ.1 (G ω)‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ‖X ω - G ω‖ ∂P :=
          integral_mono ((hint X hX).sub (hint G hG)).norm hsub
            (fun ω => norm_sub_le_of_mem_one hΦ1 _ _)
  · -- second term: the Gaussian comparison
    rw [hlaw]
    exact smoothDist_two_gaussian_covariance M Sg hM hSg

end HRS.PDE.MFLinear
