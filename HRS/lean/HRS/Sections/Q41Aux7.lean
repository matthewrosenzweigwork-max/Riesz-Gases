import Mathlib

/-!
# Packet Q41, helper 7: deterministic part of the Kolmogorov continuity criterion

If a function `Z : ℝ → E` into a complete normed space has dyadic increments
`‖Z((j+1)/2^n) - Z(j/2^n)‖ ≤ c^n` (`c < 1`) for all `n ≥ n₀` and `j < N 2^n`, then the values on the
dyadic rationals in `[0,N)` extend to a continuous function on `[0,N)` (`q41_kc_det`).  The
extension is `f(t) = lim_n Z(⌊2^n t⌋/2^n)`.
-/

noncomputable section

open Filter Topology

namespace HRS.Q41

lemma q41_floor_double {x : ℝ} (hx : 0 ≤ x) :
    ⌊2 * x⌋₊ = 2 * ⌊x⌋₊ ∨ ⌊2 * x⌋₊ = 2 * ⌊x⌋₊ + 1 := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  have h3 : ((2 * ⌊x⌋₊ : ℕ) : ℝ) ≤ 2 * x := by push_cast; linarith
  have h4 : 2 * x < ((2 * ⌊x⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hge : 2 * ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := Nat.le_floor h3
  have hlt : ⌊2 * x⌋₊ < 2 * ⌊x⌋₊ + 2 := (Nat.floor_lt (by positivity)).2 h4
  omega

lemma q41_floor_close {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (m : ℕ) (h : t - s < 1 / 2 ^ m) :
    ⌊2 ^ m * t⌋₊ = ⌊2 ^ m * s⌋₊ ∨ ⌊2 ^ m * t⌋₊ = ⌊2 ^ m * s⌋₊ + 1 := by
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have h1 : 2 ^ m * s ≤ 2 ^ m * t := mul_le_mul_of_nonneg_left hst hpos.le
  have h2 : 2 ^ m * t < 2 ^ m * s + 1 := by
    have : 2 ^ m * (t - s) < 1 := by
      have := mul_lt_mul_of_pos_left h hpos
      rwa [mul_one_div_cancel hpos.ne'] at this
    linarith
  have hge : ⌊2 ^ m * s⌋₊ ≤ ⌊2 ^ m * t⌋₊ := Nat.floor_le_floor h1
  have hle : ⌊2 ^ m * t⌋₊ ≤ ⌊2 ^ m * s + 1⌋₊ := Nat.floor_le_floor h2.le
  rw [Nat.floor_add_one (by positivity)] at hle
  omega

theorem q41_kc_det {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (Z : ℝ → E) (N : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (n₀ : ℕ)
    (hΔ : ∀ n : ℕ, n₀ ≤ n → ∀ j : ℕ, j < N * 2 ^ n →
      ‖Z (((j : ℝ) + 1) / 2 ^ n) - Z ((j : ℝ) / 2 ^ n)‖ ≤ c ^ n) :
    ∃ f : ℝ → E, ContinuousOn f (Set.Ico 0 (N : ℝ)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) N, Tendsto (fun n : ℕ => Z ((⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n)) atTop
        (𝓝 (f t))) ∧
      ∀ n j : ℕ, (j : ℝ) / 2 ^ n < N → f ((j : ℝ) / 2 ^ n) = Z ((j : ℝ) / 2 ^ n) := by
  set W : ℕ → ℝ → E := fun n t => Z ((⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n) with hW
  -- floor index is below `N 2^n`
  have hfl : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → t < N → ⌊2 ^ n * t⌋₊ < N * 2 ^ n := by
    intro n t ht0 htN
    have h1 : ((⌊2 ^ n * t⌋₊ : ℕ) : ℝ) ≤ 2 ^ n * t := Nat.floor_le (by positivity)
    have h2 : (2 : ℝ) ^ n * t < N * 2 ^ n := by
      have : (0 : ℝ) < 2 ^ n := by positivity
      nlinarith
    have : ((⌊2 ^ n * t⌋₊ : ℕ) : ℝ) < ((N * 2 ^ n : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  -- successive differences
  have hstep : ∀ n : ℕ, n₀ ≤ n → ∀ t : ℝ, 0 ≤ t → t < N → ‖W (n + 1) t - W n t‖ ≤ c ^ (n + 1) := by
    intro n hn t ht0 htN
    have hx : 0 ≤ 2 ^ n * t := by positivity
    have hq : (2 : ℝ) ^ (n + 1) * t = 2 * (2 ^ n * t) := by ring
    have hp := hfl n t ht0 htN
    simp only [hW]
    rw [hq]
    have heq : Z (((2 * ⌊2 ^ n * t⌋₊ : ℕ) : ℝ) / 2 ^ (n + 1)) = Z ((⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n) := by
      congr 1
      push_cast
      field_simp
      ring
    rcases q41_floor_double hx with h | h
    · rw [h, heq, sub_self, norm_zero]
      positivity
    · rw [h]
      have := hΔ (n + 1) (by omega) (2 * ⌊2 ^ n * t⌋₊) (by
        have : 2 * ⌊2 ^ n * t⌋₊ < N * 2 ^ (n + 1) := by rw [pow_succ]; nlinarith
        exact this)
      have e1 : (((2 * ⌊2 ^ n * t⌋₊ : ℕ) : ℝ) + 1) / 2 ^ (n + 1) =
          ((2 * ⌊2 ^ n * t⌋₊ + 1 : ℕ) : ℝ) / 2 ^ (n + 1) := by push_cast; ring
      rw [e1] at this
      rw [← heq]
      exact this
  have hcau : ∀ t : ℝ, 0 ≤ t → t < N → CauchySeq (fun k => W (n₀ + k) t) := by
    intro t ht0 htN
    refine cauchySeq_of_le_geometric c (c ^ (n₀ + 1)) hc1 fun k => ?_
    rw [dist_comm, dist_eq_norm]
    have := hstep (n₀ + k) (by omega) t ht0 htN
    calc ‖W (n₀ + k + 1) t - W (n₀ + k) t‖ ≤ c ^ (n₀ + k + 1) := by
          simpa [add_assoc] using this
      _ = c ^ (n₀ + 1) * c ^ k := by ring
  classical
  let f : ℝ → E := fun t =>
    if h : 0 ≤ t ∧ t < N then (cauchySeq_tendsto_of_complete (hcau t h.1 h.2)).choose else 0
  have hf : ∀ t : ℝ, 0 ≤ t → t < N → Tendsto (fun k => W (n₀ + k) t) atTop (𝓝 (f t)) := by
    intro t ht0 htN
    simp only [f, dif_pos (And.intro ht0 htN)]
    exact (cauchySeq_tendsto_of_complete (hcau t ht0 htN)).choose_spec
  have htail : ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → t < N →
      ‖W (n₀ + k) t - f t‖ ≤ c ^ (n₀ + 1) * c ^ k / (1 - c) := by
    intro k t ht0 htN
    have hu : ∀ k, dist (W (n₀ + k) t) (W (n₀ + (k + 1)) t) ≤ c ^ (n₀ + 1) * c ^ k := by
      intro k
      rw [dist_comm, dist_eq_norm]
      have := hstep (n₀ + k) (by omega) t ht0 htN
      calc ‖W (n₀ + (k + 1)) t - W (n₀ + k) t‖ ≤ c ^ (n₀ + k + 1) := by
            simpa [add_assoc] using this
        _ = c ^ (n₀ + 1) * c ^ k := by ring
    have := dist_le_of_le_geometric_of_tendsto c (c ^ (n₀ + 1)) hc1 hu (hf t ht0 htN) k
    rwa [dist_eq_norm] at this
  refine ⟨f, ?_, ?_, ?_⟩
  · -- uniform continuity on `[0, N)`
    refine (Metric.uniformContinuousOn_iff.2 fun ε hε => ?_).continuousOn
    have h1 : Tendsto (fun k : ℕ => c ^ (n₀ + 1) * c ^ k / (1 - c)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul (c ^ (n₀ + 1))
      simpa using this.div_const (1 - c)
    have h2 : Tendsto (fun k : ℕ => c ^ (n₀ + k)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul (c ^ n₀)
      simpa [pow_add] using this
    obtain ⟨k, hk1, hk2⟩ := ((h1.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))).and
      (h2.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity)))).exists
    refine ⟨1 / 2 ^ (n₀ + k), by positivity, ?_⟩
    have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < N → t - s < 1 / 2 ^ (n₀ + k) →
        dist (f s) (f t) < ε := by
      intro s t hs hst htN hd
      have hsN : s < N := lt_of_le_of_lt hst htN
      have ht0 : 0 ≤ t := hs.trans hst
      have hcl : ‖W (n₀ + k) t - W (n₀ + k) s‖ ≤ c ^ (n₀ + k) := by
        simp only [hW]
        rcases q41_floor_close hs hst (n₀ + k) hd with h | h
        · rw [h, sub_self, norm_zero]; positivity
        · rw [h]
          have hp := hfl (n₀ + k) s hs hsN
          have := hΔ (n₀ + k) (by omega) ⌊2 ^ (n₀ + k) * s⌋₊ hp
          have e : ((⌊2 ^ (n₀ + k) * s⌋₊ + 1 : ℕ) : ℝ) = (⌊2 ^ (n₀ + k) * s⌋₊ : ℝ) + 1 := by push_cast; ring
          rw [e]; exact this
      have h3 := htail k t ht0 htN
      have h4 := htail k s hs hsN
      calc dist (f s) (f t) = ‖f s - f t‖ := dist_eq_norm _ _
        _ ≤ ‖f s - W (n₀ + k) s‖ + ‖W (n₀ + k) s - W (n₀ + k) t‖ + ‖W (n₀ + k) t - f t‖ := by
            calc ‖f s - f t‖ = ‖(f s - W (n₀ + k) s) + (W (n₀ + k) s - W (n₀ + k) t) +
                (W (n₀ + k) t - f t)‖ := by congr 1; abel
              _ ≤ _ := norm_add₃_le
        _ < ε := by
            have e1 : ‖f s - W (n₀ + k) s‖ = ‖W (n₀ + k) s - f s‖ := norm_sub_rev _ _
            have e2 : ‖W (n₀ + k) s - W (n₀ + k) t‖ = ‖W (n₀ + k) t - W (n₀ + k) s‖ := norm_sub_rev _ _
            linarith
    intro s hs t ht hst
    rcases le_total s t with h | h
    · refine key s t hs.1 h ht.2 ?_
      rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)] at hst
      linarith
    · have := key t s ht.1 h hs.2 (by
        rw [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hst
        linarith)
      rwa [dist_comm] at this
  · intro t ht
    have := hf t ht.1 ht.2
    exact (tendsto_add_atTop_iff_nat (f := fun n => W n t) n₀).1 (by simpa [add_comm] using this)
  · intro n j hjN
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / 2 ^ n := by positivity
    refine tendsto_nhds_unique (hf _ hj0 hjN) ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop n] with k hk
    simp only [hW]
    have hfloor : ⌊(2 : ℝ) ^ (n₀ + k) * ((j : ℝ) / 2 ^ n)⌋₊ = j * 2 ^ (n₀ + k - n) := by
      have : (2 : ℝ) ^ (n₀ + k) * ((j : ℝ) / 2 ^ n) = ((j * 2 ^ (n₀ + k - n) : ℕ) : ℝ) := by
        obtain ⟨r, hr⟩ : ∃ r, n₀ + k = n + r := ⟨n₀ + k - n, by omega⟩
        rw [hr, pow_add]
        push_cast
        rw [show n + r - n = r by omega]
        field_simp
      rw [this, Nat.floor_natCast]
    rw [hfloor]
    congr 1
    obtain ⟨r, hr⟩ : ∃ r, n₀ + k = n + r := ⟨n₀ + k - n, by omega⟩
    rw [hr, pow_add, show n + r - n = r by omega]
    push_cast
    field_simp

end HRS.Q41
