import HRS.MS.SA16Y5Lb2

/-!
# S.A.16 (SA16Y5) Lb3: the heat-gain bound `‖g_a ⋆ ∂_i(ρ ⋆ (μ' ∂_j v))‖_p ≤ C a^{-(s+2-d)/2} ‖v‖_p` (K2, part 3)

`sa16y5_Tm_bound` (`d - 1 < s < d`, `0 < a ≤ 1`, `p ≥ 1`): for a smooth coefficient `μ'` with `|μ'| ≤ B0`, `|∂_jμ'| ≤ B1`, and `v ∈ C_c^∞`,
`‖Tm a μ' i j v‖_p ≤ C (B0 + B1) a^{-(s+2-d)/2} ‖v‖_p`, `C = C(d,s)` (cutoff scale `ε = √a` in `sa16y5_Tm_eq`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lb3
variable {d : ℕ} {s : ℝ}

lemma sa16y5_mul_bound {c v : Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B) (hc : ∀ y, |c y| ≤ B)
    (hm : AEStronglyMeasurable (fun y => c y * v y) volume) {p : ℝ} :
    eLpNorm (fun y => c y * v y) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal B * eLpNorm v (ENNReal.ofReal p) volume := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm (Eventually.of_forall fun y => ?_) _
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hc y) (abs_nonneg _)

lemma sa16y5_young2 {k₁ k₂ : Euc d → ℝ} (h1m : Measurable k₁) (h2m : Measurable k₂)
    (h1 : Integrable k₁) (h2 : Integrable k₂) {μ' v : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ') {B : ℝ} (hB : 0 ≤ B)
    (hμB : ∀ y, |μ' y| ≤ B) (hv : IsCcInfty v) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (sa16r_cv k₁ (sa16r_cv k₂ (fun y => μ' y * v y))) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((∫ z, |k₁ z|) * (∫ z, |k₂ z|) * B) * eLpNorm v (ENNReal.ofReal p) volume := by
  have hP : IsCcInfty (fun y => μ' y * v y) := sa16y5_cc_mul hμ hv
  have n1 : 0 ≤ ∫ z, |k₁ z| := integral_nonneg fun z => abs_nonneg _
  have n2 : 0 ≤ ∫ z, |k₂ z| := integral_nonneg fun z => abs_nonneg _
  have s1 := sa16y5_young h1m h1 (sa16y5_cv_cont h2 hP) hp
  have s2 := sa16y5_young h2m h2 hP.1.continuous hp
  have s3 := sa16y5_mul_bound (v := v) (p := p) hB hμB hP.1.continuous.aestronglyMeasurable
  calc _ ≤ ENNReal.ofReal (∫ z, |k₁ z|) * eLpNorm (sa16r_cv k₂ (fun y => μ' y * v y)) (ENNReal.ofReal p) volume := s1
    _ ≤ ENNReal.ofReal (∫ z, |k₁ z|) * (ENNReal.ofReal (∫ z, |k₂ z|) *
          eLpNorm (fun y => μ' y * v y) (ENNReal.ofReal p) volume) := by gcongr
    _ ≤ ENNReal.ofReal (∫ z, |k₁ z|) * (ENNReal.ofReal (∫ z, |k₂ z|) *
          (ENNReal.ofReal B * eLpNorm v (ENNReal.ofReal p) volume)) := by gcongr
    _ = _ := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (mul_nonneg n1 n2)]

end Lb3

end HRS.Whole.AppendixA.Phase2SA16R
