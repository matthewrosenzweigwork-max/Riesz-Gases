import HRS.MS.S111X1E7

/-!
# S11.1 X1 (energy), part 8: the energy estimate for classical adjoint solutions of the stationary model
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

theorem phi_continuousOn {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) {ρ : Euc d → ℝ} (hρi : Integrable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) :
    ContinuousOn (fun r => ∫ x, f r x ^ 2 * ρ x) (Set.Icc (0 : ℝ) t) := by
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hB⟩ := classical_bounds hf
  rw [continuousOn_iff_continuous_domRestrict]
  have hc0 : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1 p.2 := by
    have := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp (hf.cont_c2 0 (by norm_num))
    convert this using 1
    funext p
    simp
  refine continuous_of_dominated (bound := fun x => B0 ^ 2 * ρ x) (fun r => ?_)
    (fun r => Filter.Eventually.of_forall fun x => ?_) (hρi.const_mul _)
    (Filter.Eventually.of_forall fun x => ?_)
  · have : Continuous fun x : Euc d => f (r : ℝ) x := hc0.comp (Continuous.prodMk continuous_const continuous_id)
    exact ((this.pow 2).aestronglyMeasurable).mul hρi.aestronglyMeasurable
  · show ‖f (r : ℝ) x ^ 2 * ρ x‖ ≤ B0 ^ 2 * ρ x
    have h1 := (hB r r.2 x).1
    have h3 := hρ0 x
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg h3]
    have : |f r x| ≤ B0 := by rwa [← Real.norm_eq_abs]
    gcongr
  · have : Continuous fun r : Set.Icc (0 : ℝ) t => f (r : ℝ) x :=
      hc0.comp (Continuous.prodMk continuous_id continuous_const)
    exact (this.pow 2).mul continuous_const

theorem energy_main {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d} (E : EnData d s β ρ M C)
    {t : ℝ} (ht : 0 ≤ t) {ψ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t ψ f) :
    (∀ r ∈ Set.Icc (0 : ℝ) t, ∫ x, f r x ^ 2 * ρ x ≤
        Real.exp (β * kA d s M ρ ^ 2 * (t - r)) * ∫ x, ψ x ^ 2 * ρ x) ∧
      ∫ r in Set.Icc (0 : ℝ) t, ∫ x, inner ℝ (gradient (f r) x) (gradient (f r) x) * ρ x ≤
        β * ((∫ x, ψ x ^ 2 * ρ x) + β * kA d s M ρ ^ 2 * t * Real.exp (β * kA d s M ρ ^ 2 * t) *
          ∫ x, ψ x ^ 2 * ρ x) := by
  have hβ := E.hβ
  have hA0 := kA_nonneg E.K
  set A := kA d s M ρ with hA
  set C₂ : ℝ := β * A ^ 2 with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hB⟩ := classical_bounds hf
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hft : f t = ψ := hf.terminal
  have hΦc := phi_continuousOn hf E.K.int E.K.nonneg
  have hDc := x1_pair_continuousOn hf hf E.K.int E.K.nonneg (le_refl t) (le_refl t)
  have hnnΦ : ∀ r, 0 ≤ ∫ x, f r x ^ 2 * ρ x := fun r =>
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (E.K.nonneg x)
  have hnnD : ∀ r, 0 ≤ ∫ x, inner ℝ (gradient (f r) x) (gradient (f r) x) * ρ x := fun r =>
    integral_nonneg fun x => mul_nonneg real_inner_self_nonneg (E.K.nonneg x)
  have key := gronwall_gen (Φ := fun r => ∫ x, f r x ^ 2 * ρ x)
    (Dd := fun r => ∫ x, inner ℝ (gradient (f r) x) (gradient (f r) x) * ρ x) (C₂ := C₂) (β := β) ht hβ hC₂0
    hΦc hDc ?_ (fun r _ => hnnD r) (fun r _ => hnnΦ r)
  · simp only [hft] at key
    exact key
  · intro r hr
    refine ⟨_, phi_deriv E hf hr, ?_⟩
    have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have hgb : ∀ x, ‖gradient (f r) x‖ ≤ B1 := fun x => by simpa [gradient] using (hB r hr' x).2.1
    have hgc : Continuous (gradient (f r)) := by
      have : Continuous fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (f r) x) :=
        (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
          ((hf.c2 r hr').continuous_fderiv (by norm_num))
      exact this
    have hfc : Continuous (f r) := (hf.c2 r hr').continuous
    have hbd := nl_bound E.K (a := fun y => gradient (f r) y) hgc.measurable hgb hfc.measurable
      (Bf := B0) (fun x => by rw [← Real.norm_eq_abs]; exact (hB r hr' x).1)
    set Dr := ∫ x, inner ℝ (gradient (f r) x) (gradient (f r) x) * ρ x with hDr
    set Pr := ∫ x, f r x ^ 2 * ρ x with hPr
    have e1 : ∫ y, ρ y * ‖gradient (f r) y‖ ^ 2 = Dr := by
      rw [hDr]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [real_inner_self_eq_norm_sq]; ring
    have e2 : ∫ x, ρ x * f r x ^ 2 = Pr := by
      rw [hPr]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [e1, e2] at hbd
    have hD0 := hnnD r
    have hP0 := hnnΦ r
    set u := Real.sqrt Dr with hu
    set v := Real.sqrt Pr with hv
    have hu2 : u ^ 2 = Dr := Real.sq_sqrt hD0
    have hv2 : v ^ 2 = Pr := Real.sq_sqrt hP0
    have hamgm : 2 * (A * u * v) ≤ β⁻¹ * u ^ 2 + β * A ^ 2 * v ^ 2 := by
      have := mul_nonneg (inv_pos.2 hβ).le (sq_nonneg (u - β * A * v))
      have hbb : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ.ne'
      nlinarith [this, hbb]
    have hbd' : |∫ x, f r x * ρ x * Nnl d s ρ (fun y => gradient (f r) y) x| ≤ A * u * v := hbd
    have hPn := abs_le.1 hbd'
    show β⁻¹ * Dr - C₂ * Pr ≤ 2 * β⁻¹ * Dr - 2 * ∫ x, f r x * ρ x * Nnl d s ρ (fun y => gradient (f r) y) x
    rw [hC₂, ← hu2, ← hv2]
    nlinarith [hPn.1, hPn.2, hamgm]

end HRS.MS.S111X1
