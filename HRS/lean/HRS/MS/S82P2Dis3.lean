import HRS.MS.S82P2Dis2

/-!
# S8.2 (S82P2): normalised one-coordinate disintegration of the weak reference law
Under the probability facts of `WeakReferenceSetup`, the expectation of `F` under
`referenceLaw N (m+1) pins` is the average, over the law of coordinate `i`, of the expectation of
`F` with that coordinate frozen under the `m`-coordinate law with the extra pin `z = X i`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_tilt_of_prob {α : Type*} [MeasurableSpace α] (P : Measure α) (V : α → ℝ)
    (hV : Measurable V) (hp : IsProbabilityMeasure (exponentialTilt P V)) :
    (P.withDensity (fun x => ENNReal.ofReal (Real.exp (V x)))) Set.univ ≠ 0 ∧
    (P.withDensity (fun x => ENNReal.ofReal (Real.exp (V x)))) Set.univ ≠ ⊤ ∧
    exponentialTilt P V =
      ((P.withDensity (fun x => ENNReal.ofReal (Real.exp (V x)))) Set.univ)⁻¹ •
        P.withDensity (fun x => ENNReal.ofReal (Real.exp (V x))) := by
  set W := P.withDensity (fun x => ENNReal.ofReal (Real.exp (V x))) with hWdef
  have hW : W Set.univ = ∫⁻ x, ENNReal.ofReal (Real.exp (V x)) ∂P := by
    rw [hWdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h1 := hp.measure_univ
  unfold exponentialTilt at h1
  rw [← hWdef, Measure.smul_apply, smul_eq_mul] at h1
  set c := ENNReal.ofReal (∫ x, Real.exp (V x) ∂P) with hc
  have hne0 : W Set.univ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have hcinv : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hnet : W Set.univ ≠ ⊤ := by
    intro ht
    rw [ht, ENNReal.mul_top hcinv] at h1
    exact ENNReal.top_ne_one h1
  have hint : Integrable (fun x => Real.exp (V x)) P :=
    ⟨hV.exp.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)).2
        (lt_top_iff_ne_top.2 (hW ▸ hnet))⟩
  have hceq : c = W Set.univ := by
    rw [hc, hW]
    exact ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)
  refine ⟨hne0, hnet, ?_⟩
  unfold exponentialTilt
  rw [← hWdef, ← hc, hceq]

lemma s82p2_ref_of_prob {d p n : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SigmaFinite mu] (hq : Measurable q) (beta : ℝ) (N : ℕ)
    (hh : Measurable (h N)) (pins : Fin p → Euc d)
    (hp : IsProbabilityMeasure (referenceLaw q h mu beta N n pins)) :
    (s82p2_W q h mu beta N pins : Measure (EucConfig d n)) Set.univ ≠ 0 ∧
    (s82p2_W q h mu beta N pins : Measure (EucConfig d n)) Set.univ ≠ ⊤ ∧
    referenceLaw q h mu beta N n pins =
      ((s82p2_W q h mu beta N pins : Measure (EucConfig d n)) Set.univ)⁻¹ •
        (s82p2_W q h mu beta N pins : Measure (EucConfig d n)) :=
  s82p2_tilt_of_prob (Measure.pi fun _ : Fin n => mu) _
    (s82p2_exponent_measurable hq beta N hh pins) hp

end HRS.MS.S82P2
