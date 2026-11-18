import HRS.MS.SA16Y5Cv2

/-!
# S.A.16 (SA16Y5) Lb1: algebraic decomposition of the heat-composed Riesz term (K2, part 1)

For `0 < s < d`, a smooth coefficient `μ'` and `v ∈ C_c^∞` put `P = μ' v`, `Q = (∂_jμ') v` and
`Tm a μ' i j v = g_a ⋆ ∂_i (ρ ⋆ (μ' ∂_j v))`.  `sa16y5_Tm_eq`:
`Tm = rn ⋆ ((∂_i∂_j g_a) ⋆ P) - rn ⋆ ((∂_i g_a) ⋆ Q) + V_i ⋆ ((∂_j g_a) ⋆ P) - V_i ⋆ (g_a ⋆ Q)`
for every cutoff scale `ε > 0`; this is what turns the heat gain into the bound `a^{-(s+2-d)/2}` (`Lb2`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lb1
variable {d : ℕ} {s : ℝ}

def sa16y5_Tm (d : ℕ) (s a : ℝ) (μ' : Euc d → ℝ) (i j : Fin d) (v : Euc d → ℝ) : Euc d → ℝ :=
  sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ (sa16r_cv (rieszKernel d s)
    (fun y' => μ' y' * fderiv ℝ v y' (sa16z_e j))) y (sa16z_e i))

lemma sa16y5_int_bdd {κ F : Euc d → ℝ} (hκ : Integrable κ) (hF : Continuous F) {B : ℝ}
    (hB : ∀ y, |F y| ≤ B) (x : Euc d) : Integrable (fun z => κ z * F (x - z)) := by
  refine Integrable.mono' (hκ.norm.mul_const B) ?_ (Eventually.of_forall fun z => ?_)
  · exact hκ.1.mul ((hF.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB (x - z)) (norm_nonneg _)

lemma sa16y5_cv_bdd {κ f : Euc d → ℝ} (hκ : Integrable κ) (hf : IsCcInfty f) :
    ∃ B : ℝ, ∀ x, |sa16r_cv κ f x| ≤ B := by
  obtain ⟨Bf, hBf⟩ := sa16r_cc_bdd hf
  refine ⟨(∫ z, |κ z|) * Bf, fun x => ?_⟩
  unfold sa16r_cv
  rw [← Real.norm_eq_abs]
  calc ‖∫ z, κ z * f (x - z)‖ ≤ ∫ z, |κ z| * Bf := by
        refine norm_integral_le_of_norm_le (hκ.abs.mul_const Bf) (Eventually.of_forall fun z => ?_)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hBf _) (abs_nonneg _)
    _ = (∫ z, |κ z|) * Bf := by rw [integral_mul_const]

lemma sa16y5_cv_sub_bdd {κ F G : Euc d → ℝ} (hκ : Integrable κ) (hF : Continuous F) (hG : Continuous G)
    {B : ℝ} (hB : ∀ y, |F y| ≤ B) {B' : ℝ} (hB' : ∀ y, |G y| ≤ B') (x : Euc d) :
    sa16r_cv κ (fun y => F y - G y) x = sa16r_cv κ F x - sa16r_cv κ G x := by
  unfold sa16r_cv
  rw [← integral_sub (sa16y5_int_bdd hκ hF hB x) (sa16y5_int_bdd hκ hG hB' x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mul_sub]

lemma sa16y5_cv_add_bdd {κ F G : Euc d → ℝ} (hκ : Integrable κ) (hF : Continuous F) (hG : Continuous G)
    {B : ℝ} (hB : ∀ y, |F y| ≤ B) {B' : ℝ} (hB' : ∀ y, |G y| ≤ B') (x : Euc d) :
    sa16r_cv κ (fun y => F y + G y) x = sa16r_cv κ F x + sa16r_cv κ G x := by
  unfold sa16r_cv
  rw [← integral_add (sa16y5_int_bdd hκ hF hB x) (sa16y5_int_bdd hκ hG hB' x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mul_add]

/-- `cv κ f` is continuous and bounded for `κ` integrable and `f ∈ C_c^∞` -/
lemma sa16y5_cv_cont {κ f : Euc d → ℝ} (hκ : Integrable κ) (hf : IsCcInfty f) :
    Continuous (sa16r_cv κ f) :=
  (sa16y5_cv_cc_contDiff hκ.locallyIntegrable hf).continuous

end Lb1

end HRS.Whole.AppendixA.Phase2SA16R
