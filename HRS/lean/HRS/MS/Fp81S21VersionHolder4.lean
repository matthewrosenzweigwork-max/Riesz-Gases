import HRS.MS.Fp81S21VersionHolder3

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MP.KC

variable {E : Type*} [NormedAddCommGroup E]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Convert a simultaneous dyadic modulus into an eighth-Hölder estimate. -/
theorem fp81s21_dyadic_modulus_holder
    (P : Measure Ω) {H : ℝ} (hH : 0 < H)
    (Y : Ω → C(Set.Icc (0 : ℝ) H, E)) (L : Ω → ℝ)
    (hL : ∀ ω, 0 ≤ L ω)
    (hdyad : ∀ᵐ ω ∂P, ∀ s t : Set.Icc (0 : ℝ) H, ∀ m : ℕ,
      |(t : ℝ) - s| ≤ H / 2 ^ m →
        ‖Y ω t - Y ω s‖ ≤ mkc_c (9 / 10 : ℝ) * (L ω * (9 / 10 : ℝ) ^ m)) :
    ∀ᵐ ω ∂P, ∀ s t : Set.Icc (0 : ℝ) H,
      ‖Y ω t - Y ω s‖ ≤
        (mkc_c (9 / 10 : ℝ) * L ω * (2 / H) ^ (1 / 8 : ℝ)) *
          |(t : ℝ) - s| ^ (1 / 8 : ℝ) := by
  have hc : 0 ≤ mkc_c (9 / 10 : ℝ) := by unfold mkc_c; positivity
  filter_upwards [hdyad] with ω hω s t
  by_cases heq : (t : ℝ) = s
  · have : t = s := Subtype.ext heq
    subst t
    simp
  · have hd : 0 < |(t : ℝ) - s| := abs_pos.mpr (sub_ne_zero.mpr heq)
    have hdH : |(t : ℝ) - s| ≤ H := by
      apply abs_le.mpr
      constructor <;> linarith [s.property.1, s.property.2, t.property.1, t.property.2]
    obtain ⟨m, hm, hscale⟩ := fp81s21_dyadic_holder_scale hH hd hdH
    calc
      ‖Y ω t - Y ω s‖ ≤ mkc_c (9 / 10 : ℝ) * (L ω * (9 / 10 : ℝ) ^ m) := hω s t m hm
      _ ≤ mkc_c (9 / 10 : ℝ) * (L ω * (2 * |(t : ℝ) - s| / H) ^ (1 / 8 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscale (hL ω)) hc
      _ = _ := by
        rw [show 2 * |(t : ℝ) - s| / H = (2 / H) * |(t : ℝ) - s| by ring,
          Real.mul_rpow (by positivity : 0 ≤ 2 / H) (abs_nonneg _)]
        ring

#print axioms fp81s21_dyadic_modulus_holder

end HRS.Fp81.S21
