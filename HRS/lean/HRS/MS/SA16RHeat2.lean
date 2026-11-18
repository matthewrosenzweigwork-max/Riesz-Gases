import HRS.MS.SA16RHeat1
import HRS.MS.SA16JetConv

/-!
# S.A.16 (SA16R) Heat2: Young's inequality for convolution with an `L¹` kernel

`sa16r_cv k u x = ∫ k z * u (x - z) dz`.  `sa16r_young`: `‖k ⋆ u‖_p ≤ ‖k‖_1 ‖u‖_p` (Minkowski), for `k` measurable
with `∫ |k| < ∞` and `u` continuous.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat2
variable {d : ℕ}

/-- convolution `k ⋆ u` -/
def sa16r_cv (k u : Euc d → ℝ) (x : Euc d) : ℝ := ∫ z, k z * u (x - z)

lemma sa16r_cv_aesm {k u : Euc d → ℝ} (hk : Measurable k) (hu : Continuous u) :
    AEStronglyMeasurable (sa16r_cv k u) volume := by
  have := sa16j_conv_aesm (F := ℝ) hk hu
  have h2 : AEStronglyMeasurable (fun x => ∫ z, k z * u (x - z)) volume := by
    simpa [smul_eq_mul] using this
  exact h2

lemma sa16r_young_enorm {k u : Euc d → ℝ} (hk : Measurable k) (hu : Measurable u) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖sa16r_cv k u x‖ₑ ^ p ≤ (∫⁻ z, ‖k z‖ₑ) ^ p * ∫⁻ x, ‖u x‖ₑ ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hpt : ∀ x, ‖sa16r_cv k u x‖ₑ ^ p ≤ (∫⁻ y, ‖k y‖ₑ * ‖u (x - y)‖ₑ) ^ p := by
    intro x
    refine ENNReal.rpow_le_rpow ?_ hp0
    unfold sa16r_cv
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul]
  have hF : Measurable (Function.uncurry fun (x y : Euc d) => ‖u (x - y)‖ₑ) :=
    (hu.comp (measurable_fst.sub measurable_snd)).enorm
  have hm := sa16j_mink (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d))) hp
    (a := fun y => ‖k y‖ₑ) hk.enorm hF
  have hshift : ∀ y : Euc d, ∫⁻ x, ‖u (x - y)‖ₑ ^ p = ∫⁻ x, ‖u x‖ₑ ^ p := fun y =>
    lintegral_sub_right_eq_self (fun x => ‖u x‖ₑ ^ p) y
  have hA : (∫⁻ y, ‖k y‖ₑ) ^ (p - 1) * (∫⁻ y, ‖k y‖ₑ) = (∫⁻ y, ‖k y‖ₑ) ^ p := by
    have := ENNReal.rpow_add_of_nonneg (x := ∫⁻ y, ‖k y‖ₑ) (p - 1) 1 (by linarith) zero_le_one
    rw [sub_add_cancel, ENNReal.rpow_one] at this
    exact this.symm
  calc ∫⁻ x, ‖sa16r_cv k u x‖ₑ ^ p
      ≤ ∫⁻ x, (∫⁻ y, ‖k y‖ₑ * ‖u (x - y)‖ₑ) ^ p := lintegral_mono hpt
    _ ≤ (∫⁻ y, ‖k y‖ₑ) ^ (p - 1) * ∫⁻ y, ‖k y‖ₑ * ∫⁻ x, ‖u (x - y)‖ₑ ^ p := hm
    _ = (∫⁻ y, ‖k y‖ₑ) ^ (p - 1) * ((∫⁻ y, ‖k y‖ₑ) * ∫⁻ x, ‖u x‖ₑ ^ p) := by
        congr 1
        simp_rw [hshift]
        exact lintegral_mul_const _ hk.enorm
    _ = (∫⁻ z, ‖k z‖ₑ) ^ p * ∫⁻ x, ‖u x‖ₑ ^ p := by rw [← mul_assoc, hA]

/-- `‖k ⋆ u‖_p ≤ ‖k‖_1 ‖u‖_p` -/
lemma sa16r_young {k u : Euc d → ℝ} (hk : Measurable k) (hu : Continuous u) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (sa16r_cv k u) (ENNReal.ofReal p) volume ≤
      (∫⁻ z, ‖k z‖ₑ) * eLpNorm u (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hpe0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hpet : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpet (sa16r_cv_aesm hk hu),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpet hu.aestronglyMeasurable, hpr]
  have h := sa16r_young_enorm hk hu.measurable hp
  calc (∫⁻ x, ‖sa16r_cv k u x‖ₑ ^ p) ^ (1 / p)
      ≤ ((∫⁻ z, ‖k z‖ₑ) ^ p * ∫⁻ x, ‖u x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = (∫⁻ z, ‖k z‖ₑ) * (∫⁻ x, ‖u x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        have : p * (1 / p) = 1 := by field_simp
        rw [this, ENNReal.rpow_one]

end Heat2

end HRS.Whole.AppendixA.Phase2SA16R
