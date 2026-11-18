import HRS.MS.SA16RHeat4

/-!
# S.A.16 (SA16R) Heat5: the heat operator with gain of one derivative on `WmpSpace`

`sa16r_Gam d k p a : WmpSpace d k p →L WmpSpace d (k+1) p` extends `φ ↦ g_a ⋆ φ` from `C_c^∞`; norm
`≤ 1 + d (4/3)^{d/2} a^{-1/2}` (`sa16r_Gam_norm`), zeroth component `g_a ⋆ (zeroth component)` on jets of `C_c^∞`
(`sa16r_Gam_cc`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution

section Heat5
variable {d : ℕ}

lemma sa16r_cc_bdd {u : Euc d → ℝ} (hu : IsCcInfty u) : ∃ B : ℝ, ∀ y, |u y| ≤ B := by
  obtain ⟨B, hB⟩ := hu.1.continuous.bounded_above_of_compact_support hu.2
  exact ⟨B, fun y => by simpa [Real.norm_eq_abs] using hB y⟩

lemma sa16r_cv_integrand {κ : Euc d → ℝ} (hκ : Integrable κ) {u : Euc d → ℝ} (hu : IsCcInfty u) (x : Euc d) :
    Integrable (fun z => κ z * u (x - z)) := by
  obtain ⟨B, hB⟩ := sa16r_cc_bdd hu
  refine Integrable.mono' (hκ.norm.mul_const B) ?_ (Eventually.of_forall fun z => ?_)
  · exact hκ.1.mul ((hu.1.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB (x - z)) (norm_nonneg _)

lemma sa16r_cv_add {κ : Euc d → ℝ} (hκ : Integrable κ) {u v : Euc d → ℝ} (hu : IsCcInfty u)
    (hv : IsCcInfty v) : sa16r_cv κ (fun y => u y + v y) = fun x => sa16r_cv κ u x + sa16r_cv κ v x := by
  funext x
  unfold sa16r_cv
  rw [← integral_add (sa16r_cv_integrand hκ hu x) (sa16r_cv_integrand hκ hv x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mul_add]

lemma sa16r_cv_smul (κ : Euc d → ℝ) (c : ℝ) (u : Euc d → ℝ) :
    sa16r_cv κ (fun y => c * u y) = fun x => c * sa16r_cv κ u x := by
  funext x
  unfold sa16r_cv
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  ring

lemma sa16r_cv_abs_le {K κ u m : Euc d → ℝ} (hK : Integrable K) (hum : IsCcInfty u)
    (hm0 : ∀ y, 0 ≤ m y) (hmb : ∃ B, ∀ y, m y ≤ B) (hmc : Continuous m)
    (hκK : ∀ z, |κ z| ≤ K z) (hu : ∀ y, |u y| ≤ m y) (x : Euc d) :
    |sa16r_cv κ u x| ≤ sa16r_cv K m x := by
  obtain ⟨B, hB⟩ := hmb
  have hint : Integrable (fun z => K z * m (x - z)) := by
    refine Integrable.mono' (hK.norm.mul_const B) ?_ (Eventually.of_forall fun z => ?_)
    · exact hK.1.mul ((hmc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    · rw [norm_mul]
      have hK0 : 0 ≤ K z := (abs_nonneg _).trans (hκK z)
      rw [Real.norm_eq_abs (m (x - z)), abs_of_nonneg (hm0 _)]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  unfold sa16r_cv
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun z => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul (hκK z) (hu _) (abs_nonneg _) ((abs_nonneg _).trans (hκK z))

end Heat5

end HRS.Whole.AppendixA.Phase2SA16R
