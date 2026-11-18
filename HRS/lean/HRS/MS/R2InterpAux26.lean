import HRS.MS.R2InterpAux25

/-!
# S10.2 (worker S102), part 26 (packet B1, algebra): the norm of the synthesis map

For coefficients `c(i,α)` on the index set of `P_L`: `‖∑_{(i,α)} c(i,α) b_{(i,α)}‖_𝒳 ≤ B` as soon as `∑_{α ∈ S_L} c(i,α)² ≤ B²` for every
grid index `i` (the polygonal interpolation is a convex combination of the grid values).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Sec7

variable {d : ℕ} {m T : ℝ}

/-- The finite set of Hermite indices of degree `≤ L`. -/
def s102_SL (d L : ℕ) : Finset (MultiIndex d) := (multiIndex_sublevel_finite d L).toFinset

theorem s102_norm_wi (L : ℕ) (cc : MultiIndex d → ℝ) :
    ‖∑ α ∈ s102_SL d L, cc α • s102_e (m := m) α‖ = Real.sqrt (∑ α ∈ s102_SL d L, cc α ^ 2) := by
  classical
  rw [OscDual.norm_eq_coord]
  congr 1
  have hco : ∀ β, OscDual.coord (∑ α ∈ s102_SL d L, cc α • s102_e (m := m) α) β =
      if β ∈ s102_SL d L then cc β else 0 := by
    intro β
    have : ∀ (S : Finset (MultiIndex d)), OscDual.coord (∑ α ∈ S, cc α • s102_e (m := m) α) β =
        ∑ α ∈ S, cc α * OscDual.coord (s102_e (m := m) α) β := by
      intro S
      induction S using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, OscDual.coord_add, OscDual.coord_smul, ih]
    rw [this]
    simp_rw [s102_coord_e]
    by_cases h : β ∈ s102_SL d L
    · rw [if_pos h, Finset.sum_eq_single β]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro hb; exact absurd h hb
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun a ha => ?_
      have : a ≠ β := by rintro rfl; exact h ha
      simp [Ne.symm this]
  simp_rw [hco]
  rw [tsum_eq_sum (s := s102_SL d L)]
  · refine Finset.sum_congr rfl fun β hβ => ?_
    simp [hβ]
  · intro β hβ
    simp [hβ]

theorem s102_Lam'_norm_le (hT : 0 < T) (L : ℕ) (cc : ℕ × MultiIndex d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ i ∈ Finset.range (2 ^ L + 1), ∑ α ∈ s102_SL d L, cc (i, α) ^ 2 ≤ B ^ 2) :
    ‖∑ p ∈ s102_idx d L, cc p • s102_bpath (m := m) T L p‖ ≤ B := by
  classical
  refine (ContinuousMap.norm_le _ hB).2 (fun t => ?_)
  have hs0 : 0 ≤ (t : ℝ) * 2 ^ L / T := by
    have := t.2.1
    positivity
  have hsN : (t : ℝ) * 2 ^ L / T ≤ ((2 ^ L : ℕ) : ℝ) := by
    have := t.2.2
    rw [div_le_iff₀ hT]
    push_cast
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) L]
  have hsum := q17_hat_sum (2 ^ L) _ hs0 hsN
  erw [ContinuousMap.sum_apply]
  have hval : ∀ p : ℕ × MultiIndex d, OscPath.at' (cc p • s102_bpath (m := m) T L p) t =
      q17_hat ((t : ℝ) * 2 ^ L / T) p.1 • (cc p • s102_e (m := m) p.2) := by
    intro p
    show cc p • (q17_hat ((t : ℝ) * 2 ^ L / T) p.1 • s102_e (m := m) p.2) = _
    rw [smul_comm]
  change ‖∑ p ∈ s102_idx d L, OscPath.at' (cc p • s102_bpath (m := m) T L p) t‖ ≤ B
  simp_rw [hval]
  unfold s102_idx
  rw [Finset.sum_product]
  have : ∀ i ∈ Finset.range (2 ^ L + 1), ∑ α ∈ (multiIndex_sublevel_finite d L).toFinset,
      q17_hat ((t : ℝ) * 2 ^ L / T) (i, α).1 • (cc (i, α) • s102_e (m := m) (i, α).2) =
      q17_hat ((t : ℝ) * 2 ^ L / T) i • ∑ α ∈ s102_SL d L, cc (i, α) • s102_e (m := m) α := by
    intro i _
    rw [Finset.smul_sum]
    rfl
  rw [Finset.sum_congr rfl this]
  calc ‖∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
        ∑ α ∈ s102_SL d L, cc (i, α) • s102_e (m := m) α‖
      ≤ ∑ i ∈ Finset.range (2 ^ L + 1), ‖q17_hat ((t : ℝ) * 2 ^ L / T) i •
        ∑ α ∈ s102_SL d L, cc (i, α) • s102_e (m := m) α‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i * B := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (q17_hat_nonneg _ _)]
        refine mul_le_mul_of_nonneg_left ?_ (q17_hat_nonneg _ _)
        rw [s102_norm_wi]
        calc Real.sqrt (∑ α ∈ s102_SL d L, cc (i, α) ^ 2) ≤ Real.sqrt (B ^ 2) :=
              Real.sqrt_le_sqrt (hc i hi)
          _ = B := Real.sqrt_sq hB
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

end HRS.MS.R2Interp

end
