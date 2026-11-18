import HRS.Sections.ScrnAux37

/-!
# Packet SCRN, part 38: the Lindeberg term `∫ |f - m|³ ≤ 2 p A · p B`

For continuous tests `f_a^0` with `|f_a^0| ≤ A` and `∫ (f_a^0)² ≤ B` (Haar measure):
`∫ ‖scrnFvec f y - ∫ scrnFvec f‖³ dy ≤ 2 p A · (p B)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem scrn_lind {p : ℕ} (f : Fin p → ℝ → Torus d → ℝ) (hfc : ∀ a, Continuous (f a 0)) {A B : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ a y, |f a 0 y| ≤ A)
    (hB : ∀ a, ∫ y, f a 0 y ^ 2 ∂(volume : Measure (Torus d)) ≤ B) :
    ∫ y, ‖scrnFvec f y - ∫ y', scrnFvec f y' ∂(volume : Measure (Torus d))‖ ^ 3
        ∂(volume : Measure (Torus d)) ≤ 2 * p * A * (p * B) := by
  set m : ℝ^p := ∫ y', scrnFvec f y' ∂(volume : Measure (Torus d)) with hm
  set G : Torus d → ℝ^p := fun y => scrnFvec f y - m with hG
  have hma : ∀ a, m a = ∫ y, f a 0 y := fun a => scrn_integral_fvec_apply hfc a
  have hGa : ∀ a y, G y a = f a 0 y - ∫ y', f a 0 y' := by
    intro a y
    simp only [hG, PiLp.sub_apply, hma a]
    rfl
  have hint : ∀ a, Integrable (f a 0) (volume : Measure (Torus d)) := fun a =>
    (hfc a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmabs : ∀ a, |∫ y, f a 0 y| ≤ A := by
    intro a
    have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d))) (f := f a 0)
      (C := A) (Filter.Eventually.of_forall fun y => by simpa using hA a y)
    simpa using this
  have hGabs : ∀ a y, |G y a| ≤ 2 * A := by
    intro a y
    rw [hGa]
    have := hA a y
    have := hmabs a
    calc |f a 0 y - ∫ y', f a 0 y'| ≤ |f a 0 y| + |∫ y', f a 0 y'| := abs_sub _ _
      _ ≤ 2 * A := by linarith
  have hGn : ∀ y, ‖G y‖ ≤ 2 * p * A := by
    intro y
    have h2 : ‖G y‖ ^ 2 ≤ (2 * p * A) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ a, G y a ^ 2 ≤ ∑ _a : Fin p, (2 * A) ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            exact sq_le_sq' (by linarith [abs_le.1 (hGabs a y)]) (abs_le.1 (hGabs a y)).2
        _ = p * (2 * A) ^ 2 := by simp
        _ ≤ (p : ℝ) ^ 2 * (2 * A) ^ 2 := by
            have : (p : ℝ) ≤ (p : ℝ) ^ 2 := by
              rcases Nat.eq_zero_or_pos p with h | h
              · simp [h]
              · have : (1 : ℝ) ≤ p := by exact_mod_cast h
                nlinarith
            exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        _ = (2 * p * A) ^ 2 := by ring
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  have hGcont : Continuous G := (scrn_continuous_fvec hfc).sub continuous_const
  have hnc : Continuous fun y => ‖G y‖ := hGcont.norm
  have h3 : ∫ y, ‖G y‖ ^ 3 ∂(volume : Measure (Torus d)) ≤
      ∫ y, (2 * p * A) * ‖G y‖ ^ 2 ∂(volume : Measure (Torus d)) := by
    refine integral_mono ?_ ?_ fun y => ?_
    · exact (hnc.pow 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact ((hnc.pow 2).const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · have := hGn y
      have h0 := norm_nonneg (G y)
      calc ‖G y‖ ^ 3 = ‖G y‖ * ‖G y‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h4 : ∫ y, ‖G y‖ ^ 2 ∂(volume : Measure (Torus d)) ≤ p * B := by
    have e : ∀ y, ‖G y‖ ^ 2 = ∑ a, (f a 0 y - ∫ y', f a 0 y') ^ 2 := by
      intro y
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun a _ => by rw [hGa]
    simp_rw [e]
    have hi : ∀ a ∈ (Finset.univ : Finset (Fin p)), Integrable
        (fun y => (f a 0 y - ∫ y', f a 0 y' ∂(volume : Measure (Torus d))) ^ 2)
        (volume : Measure (Torus d)) := fun a _ =>
      (((hfc a).sub continuous_const).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_finsetSum _ hi]
    calc ∑ a, ∫ y, (f a 0 y - ∫ y', f a 0 y') ^ 2 ≤ ∑ _a : Fin p, B := by
          refine Finset.sum_le_sum fun a _ => ?_
          have hv := variance_le_expectation_sq (μ := (volume : Measure (Torus d))) (X := f a 0)
            (hfc a).aestronglyMeasurable
          rw [variance_eq_integral (hfc a).aemeasurable] at hv
          refine le_trans ?_ (hB a)
          simpa using hv
      _ = p * B := by simp
  calc ∫ y, ‖G y‖ ^ 3 ∂(volume : Measure (Torus d))
      ≤ ∫ y, (2 * p * A) * ‖G y‖ ^ 2 ∂(volume : Measure (Torus d)) := h3
    _ = (2 * p * A) * ∫ y, ‖G y‖ ^ 2 ∂(volume : Measure (Torus d)) := integral_const_mul _ _
    _ ≤ (2 * p * A) * (p * B) := mul_le_mul_of_nonneg_left h4 (by positivity)

end HRS
