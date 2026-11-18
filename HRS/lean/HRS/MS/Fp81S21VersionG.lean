import HRS.MS.Fp81S21EmpFour2
import HRS.MS.Fp81S21VersionHolder6

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MS.R26T6

/-- A selected sixth-moment representative and a uniform fourth-increment
bound give the continuous version with the same horizon-dependent envelope
bound for every probability space and representative. -/
theorem fp81s21_holder_version_from_six
    (H M6 C : ℝ) (hH : 0 < H) (hM6 : 0 ≤ M6) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (q : ℝ → Ω → r26t6_Coeff),
      (∀ t, Measurable (q t)) →
      fp81s21_Six P q M6 →
      (∀ a : ℝ, 0 ≤ a → ∀ s t : Set.Icc (0 : ℝ) H,
        MemLp (fun ω => q (a + t) ω - q (a + s) ω) 4 P ∧
        (∫ ω, ‖q (a + t) ω - q (a + s) ω‖ ^ 4 ∂P) ≤
          C * |(t : ℝ) - s| ^ 2) →
      ∀ a : ℝ, 0 ≤ a →
      ∃ X : Ω → C(Set.Icc (0 : ℝ) H, r26t6_Coeff),
        Measurable X ∧ MemLp X 2 P ∧
          (∀ t : Set.Icc (0 : ℝ) H,
            (fun ω => X ω t) =ᵐ[P] q (a + t)) ∧
          ∃ B : Ω → ℝ, Measurable B ∧ (∀ ω, 0 ≤ B ω) ∧
            Integrable (fun ω => B ω ^ 2) P ∧
            (∫ ω, B ω ^ 2 ∂P) ≤ D ∧
            ∀ᵐ ω ∂P, ∀ s t : Set.Icc (0 : ℝ) H,
              ‖X ω t - X ω s‖ ≤ B ω * |(t : ℝ) - s| ^ (1 / 8 : ℝ) := by
  obtain ⟨D, hD, hHolder⟩ :=
    fp81s21_exists_holder_version (E := r26t6_Coeff) H (1 + M6) C hH hC
  refine ⟨D, hD, ?_⟩
  intro Ω _ P _ q hqm hSix hInc a ha
  have hq6 := hSix a ha
  have hq4 := fp81s21_empFour_Moment6_to_fourth (q a) M6 hq6
  have hq4mem : MemLp (q a) 4 P := by
    rw [← integrable_norm_rpow_iff hq6.1.aestronglyMeasurable
      (by norm_num) (by norm_num)]
    simpa using hq4.1
  exact hHolder P q a hqm hq4mem hq4.2 (fun s t => hInc a ha s t)

#print axioms HRS.Fp81.S21.fp81s21_holder_version_from_six

end HRS.Fp81.S21

end
