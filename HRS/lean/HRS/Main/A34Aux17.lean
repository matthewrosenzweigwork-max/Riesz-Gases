import HRS.Main.A34Aux16

/-!
# Packet A34, helper 17: uniqueness of a centred Gaussian law on `E_γ` from its covariance on
smooth test functions
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_isSmooth_comb (e : ℕ ≃ NonzeroLattice d) (c : ℕ → ℝ) (n : ℕ) :
    Torus.IsSmooth (fun x => ∑ i ∈ Finset.range n, c i * Torus.realMode (e i) x) := by
  unfold Torus.IsSmooth Torus.IsCk
  have h : ∀ i : NonzeroLattice d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Torus.lift (Torus.realMode i)) := fun i => HRS.FieldSingAux.isSmooth_realMode i
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x => ∑ i ∈ Finset.range n, c i * Torus.realMode (e i) (Torus.mk x))
  exact ContDiff.sum fun i _ => contDiff_const.mul (h (e i))

theorem a34_eval_comb {m : ℝ} (e : ℕ ≃ NonzeroLattice d) (F : NegSobolev d m) (c : ℕ → ℝ) (n : ℕ) :
    NegSobolev.eval F (fun x => ∑ i ∈ Finset.range n, c i * Torus.realMode (e i) x) =
      ∑ i ∈ Finset.range n, c i * NegSobolev.fourierCoeff F (e i) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact a33_eval_const F 0
  | succ n ih =>
    have hs1 := a34_isSmooth_comb e c n
    have hs2 : Torus.IsSmooth (Torus.realMode (e n)) := HRS.FieldSingAux.isSmooth_realMode _
    have h := a33_eval_lin F (a33_cont hs1) (a33_cont hs2) (a33_ws_smooth m hs1)
      (a33_ws_smooth m hs2) 1 (c n)
    have e1 : (fun x => ∑ i ∈ Finset.range (n + 1), c i * Torus.realMode (e i) x) =
        fun x => 1 * (∑ i ∈ Finset.range n, c i * Torus.realMode (e i) x) +
          c n * Torus.realMode (e n) x := by
      funext x; rw [Finset.sum_range_succ]; ring
    rw [e1, h, ih, a33_eval_realMode, Finset.sum_range_succ]
    unfold NegSobolev.fourierCoeff
    ring

theorem a34_Ln_bound {m : ℝ} (e : ℕ ≃ NonzeroLattice d) (F a : NegSobolev d m) (n : ℕ) :
    |∑ i ∈ Finset.range n, NegSobolev.coord F (e i) * NegSobolev.coord a (e i)| ≤ ‖a‖ * ‖F‖ := by
  obtain ⟨hF2, hFn⟩ := NegSobolev.coord_sq F
  obtain ⟨ha2, han⟩ := NegSobolev.coord_sq a
  have hcs := Torus.cs_tsum (fun k => |NegSobolev.coord F k|) (fun k => |NegSobolev.coord a k|)
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) (by simpa [sq_abs] using hF2)
    (by simpa [sq_abs] using ha2)
  have hsq : Summable fun k => |NegSobolev.coord F k| * |NegSobolev.coord a k| := hcs.1
  have h1 : |∑ i ∈ Finset.range n, NegSobolev.coord F (e i) * NegSobolev.coord a (e i)| ≤
      ∑ i ∈ Finset.range n, |NegSobolev.coord F (e i)| * |NegSobolev.coord a (e i)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => abs_mul _ _
  have hg : Summable fun i : ℕ => |NegSobolev.coord F (e i)| * |NegSobolev.coord a (e i)| :=
    (e.summable_iff (f := fun k => |NegSobolev.coord F k| * |NegSobolev.coord a k|)).2 hsq
  have h2 : ∑ i ∈ Finset.range n, |NegSobolev.coord F (e i)| * |NegSobolev.coord a (e i)| ≤
      ∑' i : ℕ, |NegSobolev.coord F (e i)| * |NegSobolev.coord a (e i)| :=
    hg.sum_le_tsum _ (fun i _ => by positivity)
  have h3 : ∑' i : ℕ, |NegSobolev.coord F (e i)| * |NegSobolev.coord a (e i)| =
      ∑' k, |NegSobolev.coord F k| * |NegSobolev.coord a k| :=
    e.tsum_eq (fun k => |NegSobolev.coord F k| * |NegSobolev.coord a k|)
  have h4 := hcs.2
  simp only [sq_abs] at h4
  have e1 : Real.sqrt (∑' k, NegSobolev.coord F k ^ 2) = ‖F‖ := by
    rw [← hFn]; exact Real.sqrt_sq (norm_nonneg _)
  have e2 : Real.sqrt (∑' k, NegSobolev.coord a k ^ 2) = ‖a‖ := by
    rw [← han]; exact Real.sqrt_sq (norm_nonneg _)
  rw [e1, e2] at h4
  rw [mul_comm]
  linarith

theorem a34_gauss_unique {γ : ℝ} (e : ℕ ≃ NonzeroLattice d) {ν₁ ν₂ : Measure (NegSobolev d γ)}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (h₁ : IsCenteredGaussian ν₁)
    (h₂ : IsCenteredGaussian ν₂)
    (hcov : ∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
      ∫ F, NegSobolev.eval F φ * NegSobolev.eval F ψ ∂ν₁ =
        ∫ F, NegSobolev.eval F φ * NegSobolev.eval F ψ ∂ν₂) : ν₁ = ν₂ := by
  haveI := h₁.1
  haveI := h₂.1
  -- second moments of continuous linear functionals agree
  have key : ∀ L : StrongDual ℝ (NegSobolev d γ), ∫ F, (L F) ^ 2 ∂ν₁ = ∫ F, (L F) ^ 2 ∂ν₂ := by
    intro L
    set a : NegSobolev d γ := (InnerProductSpace.toDual ℝ (NegSobolev d γ)).symm L with ha
    have hL : ∀ F : NegSobolev d γ, L F = inner ℝ a F := fun F =>
      (InnerProductSpace.toDual_symm_apply (x := F) (y := L)).symm
    set Ln : ℕ → NegSobolev d γ → ℝ := fun n F => ∑ i ∈ Finset.range n,
      NegSobolev.coord F (e i) * NegSobolev.coord a (e i) with hLn
    set c : ℕ → ℝ := fun i => NegSobolev.coord a (e i) * Lattice.jp (e i).1 ^ (-γ) with hc
    have hLnev : ∀ n F, Ln n F = NegSobolev.eval F (fun x => ∑ i ∈ Finset.range n,
        c i * Torus.realMode (e i) x) := by
      intro n F
      rw [a34_eval_comb e F c n]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hj : Lattice.jp (e i).1 ^ (-γ) * Lattice.jp (e i).1 ^ γ = 1 := by
        rw [← Real.rpow_add (Torus.jp_pos _)]; simp
      simp only [hLn, hc, NegSobolev.fourierCoeff]
      calc NegSobolev.coord F (e i) * NegSobolev.coord a (e i) =
          NegSobolev.coord F (e i) * NegSobolev.coord a (e i) * 1 := by ring
        _ = _ := by rw [← hj]; ring
    have hcontLn : ∀ n, Continuous (Ln n) := fun n =>
      continuous_finsetSum _ fun i _ => ((a33_continuous_coord (e i)).mul continuous_const)
    have hLnm : ∀ n, Measurable (Ln n) := fun n => (hcontLn n).measurable
    have hlim : ∀ F, Tendsto (fun n => Ln n F) atTop (𝓝 (L F)) := by
      intro F; rw [hL]; exact a33_inner_tendsto e a F
    have hmem : ∀ (ν : Measure (NegSobolev d γ)) [IsProbabilityMeasure ν], IsCenteredGaussian ν →
        Tendsto (fun n => ∫ F, (Ln n F) ^ 2 ∂ν) atTop (𝓝 (∫ F, (L F) ^ 2 ∂ν)) := by
      intro ν _ hν
      haveI := hν.1
      have hI : Integrable (fun F : NegSobolev d γ => ‖F‖ ^ 2) ν := by
        have := IsGaussian.memLp_id ν 2 (by simp)
        exact (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).1 this
      refine tendsto_integral_of_dominated_convergence (fun F => ‖a‖ ^ 2 * ‖F‖ ^ 2)
        (fun n => ((hLnm n).pow_const 2).aestronglyMeasurable) (hI.const_mul _) (fun n => ?_) ?_
      · refine Eventually.of_forall fun F => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← mul_pow]
        calc Ln n F ^ 2 = |Ln n F| ^ 2 := (sq_abs _).symm
          _ ≤ (‖a‖ * ‖F‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (a34_Ln_bound e F a n) 2
      · exact Eventually.of_forall fun F => ((hlim F).pow 2)
    have e1 := hmem ν₁ h₁
    have e2 := hmem ν₂ h₂
    have heq : ∀ n, ∫ F, (Ln n F) ^ 2 ∂ν₁ = ∫ F, (Ln n F) ^ 2 ∂ν₂ := by
      intro n
      have := hcov _ _ (a34_isSmooth_comb e c n) (a34_isSmooth_comb e c n)
      simp only [hLnev n, sq]
      simpa [hLnev n] using this
    simp_rw [heq] at e1
    exact tendsto_nhds_unique e1 e2
  refine Measure.ext_of_charFunDual ?_
  funext L
  rw [IsGaussian.charFunDual_eq, IsGaussian.charFunDual_eq]
  have m1 : ν₁[L] = 0 := h₁.2 L
  have m2 : ν₂[L] = 0 := h₂.2 L
  have hLm : AEMeasurable (fun F => L F) ν₁ := L.continuous.measurable.aemeasurable
  have hLm2 : AEMeasurable (fun F => L F) ν₂ := L.continuous.measurable.aemeasurable
  have v1 : Var[L; ν₁] = ∫ F, (L F) ^ 2 ∂ν₁ := variance_of_integral_eq_zero hLm m1
  have v2 : Var[L; ν₂] = ∫ F, (L F) ^ 2 ∂ν₂ := variance_of_integral_eq_zero hLm2 m2
  have m1c : ∫ x, ((L x : ℝ) : ℂ) ∂ν₁ = 0 := by rw [integral_complex_ofReal]; simp [m1]
  have m2c : ∫ x, ((L x : ℝ) : ℂ) ∂ν₂ = 0 := by rw [integral_complex_ofReal]; simp [m2]
  rw [m1c, m2c, v1, v2, key L]

end HRS.A34
