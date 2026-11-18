import HRS.MC.S7PIDPCont

/-!
# Packet PI-D, sub-packet P (part 3): proof of `s7_PID_poly` (the deterministic facts on `polyPath`)

The statement is copied verbatim from `HRS/MC/S7PIDPlan.lean` (`s7_PID_poly`, the first conjunct conditional on `c < c'`).
Helpers from `S7PIDPHat.lean` (hat weights) and `S7PIDPCont.lean` (continuity, diagonal `V^{t,t} = id`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDP

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE

variable {d : ℕ}

/-- the position of the hat weights of `polyAt c c' n` at time `t` lies in `[0, 2^n]` (for `c ≤ c'`) -/
theorem S7PIDP_X_bounds (c c' t : ℝ) (hc : 0 ≤ c) (hcc : c ≤ c') (n : ℕ) :
    0 ≤ (max c (min t c') - c) / (c' - c) * (2 : ℝ) ^ n ∧
      (max c (min t c') - c) / (c' - c) * (2 : ℝ) ^ n ≤ ((2 ^ n : ℕ) : ℝ) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hr : 0 ≤ (max c (min t c') - c) / (c' - c) ∧ (max c (min t c') - c) / (c' - c) ≤ 1 := by
    rcases eq_or_lt_of_le hcc with h | h
    · rw [← h]; simp
    · have hpos : 0 < c' - c := by linarith
      constructor
      · exact div_nonneg (sub_nonneg.2 (le_max_left _ _)) hpos.le
      · rw [div_le_one hpos]
        have : max c (min t c') ≤ c' := max_le hcc (min_le_right _ _)
        linarith
  push_cast
  exact ⟨mul_nonneg hr.1 h2.le, mul_le_of_le_one_left h2.le hr.2⟩

/-- the norm of `polyAt c c' n v t` is bounded by the largest node norm -/
theorem S7PIDP_polyAt_norm {m : ℝ} (c c' t : ℝ) (hc : 0 ≤ c) (hcc : c ≤ c') (n : ℕ) (v : ℕ → NegSobolev d m)
    (b : ℝ) (hb0 : 0 ≤ b) (hv : ∀ i ≤ 2 ^ n, ‖v i‖ ≤ b) :
    ‖PID.polyAt c c' n v t‖ ≤ b := by
  obtain ⟨h0, h1⟩ := S7PIDP_X_bounds c c' t hc hcc n
  unfold PID.polyAt
  exact S7PIDP_hat_norm_le (2 ^ n) _ h0 h1 v b hb0 hv

/-- degenerate case `c = c'`: `polyAt` is the constant `v 0` -/
theorem S7PIDP_polyAt_degen {m : ℝ} (c t : ℝ) (n : ℕ) (v : ℕ → NegSobolev d m) :
    PID.polyAt c c n v t = v 0 := by
  have hX : (max c (min t c) - c) / (c - c) * (2 : ℝ) ^ n = 0 := by simp
  unfold PID.polyAt
  rw [hX, S7PIDP_hat_aux (2 ^ n) 0 0 (by norm_num) (by norm_num) (Nat.zero_le _) (by positivity) v]
  simp

/-- the value at the right end point -/
theorem S7PIDP_polyAt_right' {m : ℝ} (c c' : ℝ) (hcc : c < c') (n : ℕ) (v : ℕ → NegSobolev d m) :
    PID.polyAt c c' n v c' = v (2 ^ n) := S7PIDP_polyAt_right c c' hcc n v

/-- the refinement estimate pointwise in `t` (case `c < c'`) -/
theorem S7PIDP_polyAt_refine {m : ℝ} (c c' : ℝ) (hc : 0 ≤ c) (hcc : c < c') (n : ℕ) (v : ℕ → NegSobolev d m)
    (t B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ B) :
    ‖PID.polyAt c c' (n + 1) v t - PID.polyAt c c' n (fun i => v (2 * i)) t‖ ≤ B := by
  obtain ⟨h0, h1⟩ := S7PIDP_X_bounds c c' t hc hcc.le n
  have hX : (max c (min t c') - c) / (c' - c) * (2 : ℝ) ^ (n + 1) =
      2 * ((max c (min t c') - c) / (c' - c) * (2 : ℝ) ^ n) := by ring
  have hcore := S7PIDP_diff_core (2 ^ n) _ h0 h1 v B hB0
    (by rw [show 2 * 2 ^ n = 2 ^ (n + 1) by ring]; exact hB)
  unfold PID.polyAt
  rw [hX, show 2 ^ (n + 1) = 2 * 2 ^ n by ring]
  exact hcore

/-- a path given by a continuous function is the `pathOf` of it -/
theorem S7PIDP_pathOf_cont {m T : ℝ} {g : ℝ → NegSobolev d m} (hg : Continuous fun t : Set.Icc (0 : ℝ) T => g t.1) :
    pathOf m T g = (⟨fun t : Set.Icc (0 : ℝ) T => g t.1, hg⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
  unfold pathOf
  exact dif_pos hg

/-- the sup-norm of the `pathOf` of a function bounded on `[0,T]` -/
theorem S7PIDP_norm_pathOf_le {m T : ℝ} (g : ℝ → NegSobolev d m) (K : ℝ) (hK : 0 ≤ K)
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖g t‖ ≤ K) : ‖pathOf m T g‖ ≤ K := by
  by_cases h : Continuous fun t : Set.Icc (0 : ℝ) T => g t.1
  · rw [S7PIDP_pathOf_cont h]
    refine (ContinuousMap.norm_le _ hK).2 ?_
    intro x
    exact hg x.1 x.2
  · have e : pathOf m T g = 0 := by
      unfold pathOf
      exact dif_neg h
    rw [e, norm_zero]
    exact hK

theorem S7PIDP_pathAt_cont {m T : ℝ} {g : ℝ → NegSobolev d m} (hg : Continuous fun t : Set.Icc (0 : ℝ) T => g t.1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : pathAt (pathOf m T g) t = g t := by
  rw [S7PIDP_pathOf_cont hg]
  unfold pathAt
  rw [dif_pos ht]
  rfl

/-- **s7_PID_poly_proof**: proof of `HRS.MC.Sec7.PIDPlan.s7_PID_poly` (statement verbatim). -/
theorem s7_PID_poly_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → ∀ (n : ℕ) (v : ℕ → NegSobolev d m),
      (c < c' → ∀ t ∈ Set.Icc (0 : ℝ) T, pathAt (polyPath R.D R.ρ m T c c' n v) t =
        if t ≤ c' then polyAt c c' n v t else Vprop R.D R.ρ m t c' (v (2 ^ n))) ∧
      (∀ b : ℝ, (∀ i ≤ 2 ^ n, ‖v i‖ ≤ b) → ‖polyPath R.D R.ρ m T c c' n v‖ ≤ C₁ * b) ∧
      (∀ B : ℝ, (∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ B) →
        ‖polyPath R.D R.ρ m T c c' (n + 1) v - polyPath R.D R.ρ m T c c' n (fun i => v (2 * i))‖ ≤ B) := by
  obtain ⟨J, n₀, H, hn₀, hJ, hm0, hm1⟩ := S7PIDP_pie R m hm T hT
  obtain ⟨C, hC0, hCb⟩ := pie_Vbound H m n₀ hn₀ hJ hm0 hm1
  refine ⟨max 1 C, le_max_left _ _, fun c c' hc hcc hc'T n v => ⟨?_, ?_, ?_⟩⟩
  · -- (a) the genuine continuous path on `[0,T]`
    intro hlt t ht
    exact S7PIDP_pathAt_cont (S7PIDP_cont H hn₀ hJ hm0 hm1 c c' hc hlt hc'T n v) t ht
  · -- (b) the norm bound (valid also for `c = c'`: then the path is `pathOf` of a bounded function)
    intro b hb
    have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
    have hC1 : (1 : ℝ) ≤ max 1 C := le_max_left _ _
    have hnn : 0 ≤ max 1 C * b := mul_nonneg (zero_le_one.trans hC1) hb0
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖if t ≤ c' then PID.polyAt c c' n v t
        else Vprop R.D R.ρ m t c' (v (2 ^ n))‖ ≤ max 1 C * b := by
      intro t ht
      split_ifs with h
      · exact (S7PIDP_polyAt_norm c c' t hc hcc n v b hb0 hb).trans (le_mul_of_one_le_left hb0 hC1)
      · have htpos : 0 < t := lt_of_le_of_lt (hc.trans hcc) (not_le.1 h)
        have hV := hCb t ⟨htpos, ht.2⟩ c' ⟨hc.trans hcc, (not_le.1 h).le⟩ (v (2 ^ n))
        calc _ ≤ C * ‖v (2 ^ n)‖ := hV
          _ ≤ C * b := mul_le_mul_of_nonneg_left (hb _ le_rfl) hC0
          _ ≤ max 1 C * b := mul_le_mul_of_nonneg_right (le_max_right _ _) hb0
    unfold polyPath
    exact S7PIDP_norm_pathOf_le _ _ hnn hpt
  · -- (c) refinement
    intro B hB
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (pow_pos (by norm_num) _))
    rcases eq_or_lt_of_le hcc with heq | hlt
    · subst heq
      have hEq : polyPath R.D R.ρ m T c c (n + 1) v = polyPath R.D R.ρ m T c c n (fun i => v (2 * i)) := by
        unfold polyPath
        congr 1
        funext t
        dsimp only
        split_ifs with h
        · rw [S7PIDP_polyAt_degen, S7PIDP_polyAt_degen]
        · show Vprop R.D R.ρ m t c (v (2 ^ (n + 1))) = Vprop R.D R.ρ m t c (v (2 * 2 ^ n))
          rw [pow_succ']
      rw [hEq, sub_self, norm_zero]
      exact hB0
    · have hcont1 := S7PIDP_cont H hn₀ hJ hm0 hm1 c c' hc hlt hc'T (n + 1) v
      have hcont0 := S7PIDP_cont H hn₀ hJ hm0 hm1 c c' hc hlt hc'T n (fun i => v (2 * i))
      unfold polyPath
      rw [S7PIDP_pathOf_cont hcont1, S7PIDP_pathOf_cont hcont0]
      refine (ContinuousMap.norm_le _ hB0).2 ?_
      intro x
      show ‖(if x.1 ≤ c' then PID.polyAt c c' (n + 1) v x.1
          else Vprop R.D R.ρ m x.1 c' (v (2 ^ (n + 1)))) -
        (if x.1 ≤ c' then PID.polyAt c c' n (fun i => v (2 * i)) x.1
          else Vprop R.D R.ρ m x.1 c' (v (2 * 2 ^ n)))‖ ≤ B
      split_ifs with h
      · exact S7PIDP_polyAt_refine c c' hc hlt n v x.1 B hB0 hB
      · rw [show 2 * 2 ^ n = 2 ^ (n + 1) by ring, sub_self, norm_zero]
        exact hB0

end HRS.MC.Sec7.S7PIDP

end
