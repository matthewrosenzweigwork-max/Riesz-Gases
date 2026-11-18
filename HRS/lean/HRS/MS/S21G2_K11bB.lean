import HRS.MS.S21G2_K11bA

/-!
# S21G2 K11b (part B) -- centering the kernel does not change the coefficients (R26-T3.K11b)

For `k ∈ L¹(μ⊗μ)` and bounded continuous mean-zero `e₁, e₂`:
`∬ (r2CenterKernel μ k) e₁ ⊗ e₂ = ∬ k e₁ ⊗ e₂` (all centering terms integrate to zero).  Helpers `s21g2_k11b_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21g2_k11b_center {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {k : HRS.Euc d → HRS.Euc d → ℝ} (hk : Integrable (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) (μ.prod μ))
    {e1 e2 : HRS.Euc d → ℝ} (hc1 : Continuous e1) (hc2 : Continuous e2)
    {C1 C2 : ℝ} (hb1 : ∀ x, |e1 x| ≤ C1) (hb2 : ∀ x, |e2 x| ≤ C2)
    (h1z : ∫ x, e1 x ∂μ = 0) (h2z : ∫ x, e2 x ∂μ = 0) :
    ∫ x, ∫ y, HRS.Whole.r2CenterKernel μ k x y * e1 x * e2 y ∂μ ∂μ =
      ∫ x, ∫ y, k x y * e1 x * e2 y ∂μ ∂μ := by
  set m : HRS.Euc d → ℝ := fun x => ∫ y, k x y ∂μ with hm
  set m' : HRS.Euc d → ℝ := fun y => ∫ x, k x y ∂μ with hm'
  set C : ℝ := ∫ x, m x ∂μ with hC
  have hmi : Integrable m μ := hk.integral_prod_left
  have hmi' : Integrable m' μ := hk.integral_prod_right
  have hbd : ∀ (e : HRS.Euc d → ℝ) (c : ℝ), Continuous e → (∀ x, |e x| ≤ c) → ∀ g : HRS.Euc d → ℝ,
      Integrable g μ → Integrable (fun y => g y * e y) μ := fun e c hce hbe g hg =>
    hg.mul_bdd hce.aestronglyMeasurable (ae_of_all _ fun y => by simpa using hbe y)
  have hei : ∀ (e : HRS.Euc d → ℝ) (c : ℝ), Continuous e → (∀ x, |e x| ≤ c) → Integrable e μ :=
    fun e c hce hbe => Integrable.of_bound hce.aestronglyMeasurable c (ae_of_all _ fun y => by simpa using hbe y)
  have hg : Continuous fun z : HRS.Euc d × HRS.Euc d => e1 z.1 * e2 z.2 :=
    (hc1.comp continuous_fst).mul (hc2.comp continuous_snd)
  have hP : Integrable (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2 * (e1 z.1 * e2 z.2)) (μ.prod μ) :=
    hk.mul_bdd hg.aestronglyMeasurable (c := C1 * C2) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hb1 z.1) (hb2 z.2) (abs_nonneg _) ((abs_nonneg _).trans (hb1 z.1)))
  have hT1 : Integrable (fun x => ∫ y, k x y * e1 x * e2 y ∂μ) μ := by
    have := hP.integral_prod_left
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [mul_assoc]
  set M : ℝ := ∫ y, m' y * e2 y ∂μ with hM
  have hae : ∀ᵐ x ∂μ, ∫ y, HRS.Whole.r2CenterKernel μ k x y * e1 x * e2 y ∂μ =
      (∫ y, k x y * e1 x * e2 y ∂μ) - e1 x * M := by
    filter_upwards [hk.prod_right_ae] with x hx
    have iT1 : Integrable (fun y => k x y * e1 x * e2 y) μ :=
      ((hbd e2 C2 hc2 hb2 _ hx).const_mul (e1 x)).congr (ae_of_all _ fun y => by ring)
    have iT2 : Integrable (fun y => m x * e1 x * e2 y) μ := (hei e2 C2 hc2 hb2).const_mul _
    have iT3 : Integrable (fun y => m' y * e1 x * e2 y) μ :=
      ((hbd e2 C2 hc2 hb2 _ hmi').const_mul (e1 x)).congr (ae_of_all _ fun y => by ring)
    have iT4 : Integrable (fun y => C * e1 x * e2 y) μ := (hei e2 C2 hc2 hb2).const_mul _
    have e : ∀ y, HRS.Whole.r2CenterKernel μ k x y * e1 x * e2 y =
        k x y * e1 x * e2 y - m x * e1 x * e2 y - m' y * e1 x * e2 y + C * e1 x * e2 y := fun y => by
      simp only [HRS.Whole.r2CenterKernel, hm, hm', hC]; ring
    simp_rw [e]
    have iA : Integrable (fun y => k x y * e1 x * e2 y - m x * e1 x * e2 y) μ := iT1.sub iT2
    have iB : Integrable (fun y => k x y * e1 x * e2 y - m x * e1 x * e2 y - m' y * e1 x * e2 y) μ :=
      iA.sub iT3
    rw [integral_add iB iT4, integral_sub iA iT3, integral_sub iT1 iT2]
    have i2 : ∫ y, m x * e1 x * e2 y ∂μ = 0 := by rw [integral_const_mul, h2z, mul_zero]
    have i4 : ∫ y, C * e1 x * e2 y ∂μ = 0 := by rw [integral_const_mul, h2z, mul_zero]
    have i3 : ∫ y, m' y * e1 x * e2 y ∂μ = e1 x * M := by
      rw [hM, ← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun y => by ring)
    rw [i2, i3, i4]; ring
  rw [integral_congr_ae hae, integral_sub hT1 ((hei e1 C1 hc1 hb1).mul_const M), integral_mul_const, h1z]
  simp

end HRS.MS.R26T3
