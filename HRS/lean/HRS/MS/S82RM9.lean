import HRS.MS.S82RM8

/-!
# S8.2 R02 (S82R), M9: duality of the weight recursion and supersolutions
If `rho >= 0` is integrable with `(1-1/n) rho + ((n-1)/n) Gam rho <= rho - b/n` then
`(1/n) sum_i int W_i b + sum_i int (S W)_i rho <= sum_i int W_i rho`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

lemma s82r_Gam_bdd {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    (hΓ : Measurable (uncurry Γ)) (hΓ0 : ∀ z u, 0 ≤ Γ z u) {G0 : ℝ} (hG0 : ∀ z u, Γ z u ≤ G0)
    {w : E → ℝ} (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) {B : ℝ} (hwB : ∀ z, w z ≤ B) (u : E) :
    |s82r_Gam μ Γ w u| ≤ B * G0 := by
  rw [abs_of_nonneg (s82r_Gam_nonneg hΓ0 hw0 u)]
  have hwΓ : Integrable (fun z => w z * Γ z u) μ :=
    Integrable.of_bound (hw.mul (hΓ.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
      (B * G0) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 z) (hΓ0 z u))]
        exact mul_le_mul (hwB z) (hG0 z u) (hΓ0 z u) ((hw0 z).trans (hwB z)))
  unfold s82r_Gam
  calc ∫ z, w z * Γ z u ∂μ ≤ ∫ z, B * G0 ∂μ :=
        integral_mono hwΓ (integrable_const _) fun z =>
          mul_le_mul (hwB z) (hG0 z u) (hΓ0 z u) ((hw0 z).trans (hwB z))
    _ = B * G0 := by simp

/-- Symmetry of the pairing. -/
lemma s82r_Gam_pair {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    (hΓ : Measurable (uncurry Γ)) (hΓ0 : ∀ z u, 0 ≤ Γ z u) {G0 : ℝ} (hG0 : ∀ z u, Γ z u ≤ G0)
    (hsym : ∀ z u, Γ z u = Γ u z) {w ρ : E → ℝ} (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    {B : ℝ} (hwB : ∀ z, w z ≤ B) (hρ : Measurable ρ) (hρ0 : ∀ z, 0 ≤ ρ z) (hρi : Integrable ρ μ) :
    ∫ u, s82r_Gam μ Γ w u * ρ u ∂μ = ∫ z, w z * s82r_Gam μ Γ ρ z ∂μ := by
  have hf : Integrable (fun p : E × E => w p.2 * Γ p.2 p.1 * ρ p.1) (μ.prod μ) := by
    have h1 : Integrable (fun p : E × E => ρ p.1) (μ.prod μ) := hρi.comp_fst μ
    refine Integrable.mono' (h1.const_mul (B * G0)) ?_ (ae_of_all _ fun p => ?_)
    · exact (((hw.comp measurable_snd).mul (hΓ.comp (measurable_snd.prodMk measurable_fst))).mul
        (hρ.comp measurable_fst)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hw0 p.2) (hΓ0 p.2 p.1)) (hρ0 p.1))]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hwB p.2) (hG0 p.2 p.1) (hΓ0 p.2 p.1)
        ((hw0 p.2).trans (hwB p.2))) (hρ0 p.1)
  have hswap := integral_integral_swap (f := fun u z => w z * Γ z u * ρ u) hf
  have e1 : ∫ u, s82r_Gam μ Γ w u * ρ u ∂μ = ∫ u, ∫ z, w z * Γ z u * ρ u ∂μ ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    show (s82r_Gam μ Γ w u) * ρ u = ∫ z, w z * Γ z u * ρ u ∂μ
    unfold s82r_Gam
    exact (integral_mul_const _ _).symm
  have e2 : ∫ z, w z * s82r_Gam μ Γ ρ z ∂μ = ∫ z, ∫ u, w z * Γ z u * ρ u ∂μ ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show w z * s82r_Gam μ Γ ρ z = ∫ u, w z * Γ z u * ρ u ∂μ
    unfold s82r_Gam
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    show w z * (ρ u * Γ u z) = w z * Γ z u * ρ u
    rw [hsym u z]; ring
  rw [e1, e2]
  exact hswap

end HRS.MS.S82R

end
