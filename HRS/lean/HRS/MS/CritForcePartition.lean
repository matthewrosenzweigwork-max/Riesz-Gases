import HRS.MS.CritForceDefs

/-!
# S8.2.01: deterministic partition of the time history into unit blocks
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

/-- The `j`-th truncated left endpoint `max 0 (a₀ - j)`. -/
def s82_g (a₀ : ℝ) (j : ℕ) : ℝ := max 0 (a₀ - (j : ℝ))

lemma s82_Icc_integral_eq (f : ℝ → ℝ) {x y : ℝ} (h : x ≤ y) :
    ∫ r in Set.Icc x y, f r = ∫ r in x..y, f r := by
  rw [intervalIntegral.integral_of_le h, integral_Icc_eq_integral_Ioc]

lemma s82_g_nonneg (a₀ : ℝ) (j : ℕ) : 0 ≤ s82_g a₀ j := le_max_left _ _

lemma s82_g_le (a₀ : ℝ) (ha₀ : 0 ≤ a₀) (j : ℕ) : s82_g a₀ j ≤ a₀ := by
  unfold s82_g
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  exact max_le ha₀ (by linarith)

lemma s82_g_succ_le (a₀ : ℝ) (j : ℕ) : s82_g a₀ (j + 1) ≤ s82_g a₀ j := by
  unfold s82_g
  push_cast
  exact max_le_max le_rfl (by linarith)

lemma s82_g_zero (a₀ : ℝ) (ha₀ : 0 ≤ a₀) : s82_g a₀ 0 = a₀ := by
  simp [s82_g, ha₀]

lemma s82_g_eventually (a₀ : ℝ) (J : ℕ) (hJ : a₀ ≤ J) : s82_g a₀ J = 0 := by
  unfold s82_g
  exact max_eq_left (by linarith)

/-- Telescoping of the old blocks. -/
lemma s82_block_sum (f : ℝ → ℝ) (a₀ : ℝ) (ha₀ : 0 ≤ a₀)
    (hint : ∀ x ∈ Set.Icc (0 : ℝ) a₀, ∀ y ∈ Set.Icc (0 : ℝ) a₀,
      IntervalIntegrable f volume x y) (n : ℕ) :
    ∑ j ∈ Finset.range n, ∫ r in Set.Icc (s82_g a₀ (j + 1)) (s82_g a₀ j), f r =
      ∫ r in s82_g a₀ n..a₀, f r := by
  have hg : ∀ j, s82_g a₀ j ∈ Set.Icc (0 : ℝ) a₀ :=
    fun j => ⟨s82_g_nonneg _ _, s82_g_le _ ha₀ _⟩
  induction n with
  | zero => simp [s82_g_zero a₀ ha₀]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, s82_Icc_integral_eq f (s82_g_succ_le a₀ n)]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (a := s82_g a₀ (n + 1)) (b := s82_g a₀ n) (c := a₀)]
    · ring
    · exact hint _ (hg _) _ (hg _)
    · exact hint _ (hg _) _ (by exact ⟨ha₀, le_rfl⟩)

theorem s82_history_partition (f : ℝ → ℝ) (a₀ t : ℝ)
    (ha₀ : 0 ≤ a₀) (ht : 0 ≤ t)
    (hf : IntegrableOn f (Set.Icc 0 (a₀ + t))) :
    Summable (fun j : ℕ =>
      ∫ r in Set.Icc (max 0 (a₀ - ((j : ℝ) + 1))) (max 0 (a₀ - (j : ℝ))), f r) ∧
    (∫ r in Set.Icc (0 : ℝ) (a₀ + t), f r) =
      (∫ r in Set.Icc a₀ (a₀ + t), f r) +
        ∑' j : ℕ, ∫ r in Set.Icc
          (max 0 (a₀ - ((j : ℝ) + 1))) (max 0 (a₀ - (j : ℝ))), f r := by
  have hat : a₀ ≤ a₀ + t := by linarith
  have hint : ∀ x ∈ Set.Icc (0 : ℝ) (a₀ + t), ∀ y ∈ Set.Icc (0 : ℝ) (a₀ + t),
      IntervalIntegrable f volume x y := fun x hx y hy =>
    (hf.mono_set (Set.uIcc_subset_Icc hx hy)).intervalIntegrable
  have hint' : ∀ x ∈ Set.Icc (0 : ℝ) a₀, ∀ y ∈ Set.Icc (0 : ℝ) a₀,
      IntervalIntegrable f volume x y := fun x hx y hy =>
    hint x ⟨hx.1, hx.2.trans hat⟩ y ⟨hy.1, hy.2.trans hat⟩
  obtain ⟨J, hJ⟩ := exists_nat_ge a₀
  -- the series is a finite sum
  have hzero : ∀ j ∉ Finset.range J,
      ∫ r in Set.Icc (s82_g a₀ (j + 1)) (s82_g a₀ j), f r = 0 := by
    intro j hj
    have hj' : J ≤ j := by simpa using hj
    have hjR : a₀ ≤ (j : ℝ) := hJ.trans (by exact_mod_cast hj')
    have h1 : s82_g a₀ j = 0 := s82_g_eventually a₀ j hjR
    have h2 : s82_g a₀ (j + 1) = 0 := s82_g_eventually a₀ (j + 1) (by push_cast; linarith)
    rw [h1, h2]
    simp
  have hfun : (fun j : ℕ =>
      ∫ r in Set.Icc (max 0 (a₀ - ((j : ℝ) + 1))) (max 0 (a₀ - (j : ℝ))), f r) =
      fun j : ℕ => ∫ r in Set.Icc (s82_g a₀ (j + 1)) (s82_g a₀ j), f r := by
    funext j
    simp only [s82_g]
    push_cast
    rfl
  rw [hfun]
  refine ⟨summable_of_ne_finset_zero hzero, ?_⟩
  rw [tsum_eq_sum hzero, s82_block_sum f a₀ ha₀ hint' J, s82_g_eventually a₀ J hJ,
    s82_Icc_integral_eq f hat, s82_Icc_integral_eq f (by linarith : (0:ℝ) ≤ a₀ + t)]
  have := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 ⟨le_rfl, by linarith⟩ a₀ ⟨ha₀, hat⟩)
    (hint a₀ ⟨ha₀, hat⟩ (a₀ + t) ⟨by linarith, le_rfl⟩)
  linarith

end HRS.MS.S82BD
