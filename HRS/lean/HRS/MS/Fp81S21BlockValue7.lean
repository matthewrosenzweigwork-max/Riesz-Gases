import HRS.MS.Fp81S21BlockValue6

/-!
# S2.1(iii), packet 15d-4: cutoff conversion

Away from the unit-clock origin, the clipped block clock is equivalent to the
physical-time cutoff. The excluded origin is the singleton removed in the
integral argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Set

namespace HRS.Fp81.S21

/-- The clipped unit-clock cutoff agrees with the physical cutoff for
strictly positive unit-clock times. The strict lower endpoint is essential. -/
theorem fp81s21_unitClock_cutoff_iff
    (k : ℕ) (b : ℝ) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    (k : ℝ) + s ≤ b ↔ s ≤ max 0 (min (b - (k : ℝ)) 1) := by
  change ((k : ℝ) + s ≤ b) ↔ s ≤ max 0 (min (b - (k : ℝ)) 1)
  have hphys : ((k : ℝ) + s ≤ b) ↔ s ≤ b - (k : ℝ) := by
    constructor <;> intro h <;> linarith
  have hspos : 0 < s := hs.1
  have hsle : s ≤ 1 := hs.2
  by_cases h0 : b - (k : ℝ) ≤ 0
  · have hclip : max 0 (min (b - (k : ℝ)) 1) = 0 := by
      rw [max_eq_left ((min_le_left _ _).trans h0)]
    rw [hphys, hclip]
    constructor <;> intro h <;> linarith
  · by_cases h1 : b - (k : ℝ) ≤ 1
    · have hclip : max 0 (min (b - (k : ℝ)) 1) = b - (k : ℝ) := by
        rw [min_eq_left h1, max_eq_right (le_of_not_ge h0)]
      rw [hphys, hclip]
    · have hclip : max 0 (min (b - (k : ℝ)) 1) = 1 := by
        rw [min_eq_right (le_of_not_ge h1), max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      rw [hphys, hclip]
      constructor <;> intro h <;> linarith

/-- The observation cutoff `v ≤ a+t` agrees with the clipped block-clock
cutoff at every `s∈(0,1]`. -/
theorem fp81s21_blockClock_cutoff_iff
    {H a : ℝ} (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    (k : ℝ) + s ≤ a + t ↔
      s ≤ (fp81s21_blockClock a k ⟨t, ht⟩ : ℝ) := by
  exact fp81s21_unitClock_cutoff_iff k (a + t) hs

#print axioms fp81s21_unitClock_cutoff_iff
#print axioms fp81s21_blockClock_cutoff_iff

end HRS.Fp81.S21

end
