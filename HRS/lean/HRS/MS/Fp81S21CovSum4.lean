import HRS.MS.Fp81S21CovSum3

/-!
# S2.1(iii), packet 16b: half-open unit-block source partition

The half-open convention `(k,k+1]` assigns every shared integer endpoint to
exactly one block. The resulting disjoint partition justifies exchanging the
block tsum with one source lintegral.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

/-- The natural half-open unit intervals tile the positive half-line. -/
theorem fp81s21_natUnitBlocks_iUnion :
    (⋃ k : ℕ, Ioc (k : ℝ) ((k : ℝ) + 1)) = Ioi 0 := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    exact lt_of_le_of_lt (Nat.cast_nonneg k) hk.1
  · intro hx
    let k : ℕ := ⌊x⌋₊
    have hx0 : 0 ≤ x := le_of_lt hx
    have hfloor : (k : ℝ) ≤ x := by
      dsimp [k]
      exact Nat.floor_le hx0
    have hsucc : x < (k : ℝ) + 1 := by
      dsimp [k]
      exact Nat.lt_floor_add_one x
    by_cases hstrict : (k : ℝ) < x
    · exact Set.mem_iUnion.mpr ⟨k, ⟨hstrict, hsucc.le⟩⟩
    · have hxk : x = (k : ℝ) := le_antisymm (le_of_not_gt hstrict) hfloor
      have hkpos : 0 < k := by
        by_contra hk
        have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
        have hxkpos : (0 : ℝ) < (k : ℝ) := by
          rw [← hxk]
          exact hx
        rw [hk0] at hxkpos
        norm_num at hxkpos
      have hpred : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
      have hpredlt : k - 1 < k := by omega
      refine Set.mem_iUnion.mpr ⟨k - 1, ?_⟩
      constructor
      · rw [hxk]
        exact_mod_cast hpredlt
      · rw [hxk]
        have hpredreal : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
          exact_mod_cast hpred
        rw [← hpredreal]

private lemma fp81s21_tsum_indicator_eq_iUnion
    (B : ℕ → Set ℝ) (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (f : ℝ → ℝ≥0∞) (x : ℝ) :
    (∑' k, (B k).indicator f x) = (⋃ k, B k).indicator f x := by
  by_cases hx : x ∈ ⋃ k, B k
  · rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    have hzero : ∀ j ≠ k, (B j).indicator f x = 0 := by
      intro j hj
      have hnot : x ∉ B j := by
        intro hjx
        exact (Set.disjoint_left.mp (hdisj j k hj)) hjx hk
      simp [Set.indicator, hnot]
    rw [tsum_eq_single k hzero]
    simp [Set.indicator, hx, hk]
  · have hzero : ∀ k, (B k).indicator f x = 0 := by
      intro k
      have hnot : x ∉ B k := by
        intro hk
        exact hx (Set.mem_iUnion.mpr ⟨k, hk⟩)
      simp [Set.indicator, hnot]
    rw [ENNReal.tsum_eq_zero.mpr hzero]
    simp [Set.indicator, hx]

private lemma fp81s21_natUnitBlocks_disjoint_inter
    (S : Set ℝ) :
    ∀ i j : ℕ, i ≠ j →
      Disjoint (Ioc (i : ℝ) ((i : ℝ) + 1) ∩ S)
        (Ioc (j : ℝ) ((j : ℝ) + 1) ∩ S) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hij' | hji
  · have hstep : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hij'
    linarith [hx.1.2, hy.1.1]
  · have hstep : (j : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hji
    linarith [hy.1.2, hx.1.1]

/-- Integrating the sum of half-open unit-block restrictions is exactly one
source integral whenever the source is contained in the positive half-line.
All shared endpoints are handled by the half-open partition itself. -/
theorem fp81s21_lintegral_natUnitBlocks_eq
    (f : ℝ → ℝ≥0∞)
    (S : Set ℝ) (hS : MeasurableSet S) (hSpos : S ⊆ Ioi 0) :
    ∫⁻ x, ∑' k : ℕ,
      (Ioc (k : ℝ) ((k : ℝ) + 1) ∩ S).indicator f x ∂volume =
        ∫⁻ x in S, f x := by
  let B : ℕ → Set ℝ := fun k => Ioc (k : ℝ) ((k : ℝ) + 1) ∩ S
  have hB : ∀ k, MeasurableSet (B k) := by
    intro k
    exact measurableSet_Ioc.inter hS
  have hdisj : ∀ i j : ℕ, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    exact fp81s21_natUnitBlocks_disjoint_inter S i j hij
  have hUnion : (⋃ k, B k) = S := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
      exact hk.2
    · intro hx
      have hxpos := hSpos hx
      have hxunit : x ∈ ⋃ k : ℕ, Ioc (k : ℝ) ((k : ℝ) + 1) := by
        rw [fp81s21_natUnitBlocks_iUnion]
        exact hxpos
      rcases Set.mem_iUnion.mp hxunit with ⟨k, hk⟩
      exact Set.mem_iUnion.mpr ⟨k, ⟨hk, hx⟩⟩
  calc
    ∫⁻ x, ∑' k : ℕ,
        (Ioc (k : ℝ) ((k : ℝ) + 1) ∩ S).indicator f x ∂volume =
        ∫⁻ x, (⋃ k, B k).indicator f x ∂volume := by
          apply lintegral_congr
          intro x
          simpa only [B] using fp81s21_tsum_indicator_eq_iUnion B hdisj f x
    _ = ∫⁻ x, S.indicator f x ∂volume := by rw [hUnion]
    _ = ∫⁻ x in S, f x := lintegral_indicator hS f

#print axioms fp81s21_natUnitBlocks_iUnion
#print axioms fp81s21_lintegral_natUnitBlocks_eq

end HRS.Fp81.S21

end
