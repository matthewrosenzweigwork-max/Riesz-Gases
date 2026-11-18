import HRS.MS.R26T8AP06a1

/-!
# S8.2 nonlocal layer: dyadic sums of the annular bounds (P11e, part 2)
Terms `T_n(r) = (2^-n)^gamma L(2^-n)` (near, `r <= 4 * 2^-n`) and `(2^-n)^delta r^(gamma-delta) L(2^-n)` (far), `L(t) = (1+|log t|)^b`,
`delta > 0`: all partial sums are `<= C (1 + r^gamma (1+|log r|)^(b+1))` for `0 < r <= 2`.
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology

namespace HRS.MS.R26T8A

/-- The far part: `n = n0 + m`, `2^-n0 < r/4 <= 2^-(n0-1)`. -/
theorem r26t8a_sum_far (b : ℕ) {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (r : ℝ) (n0 : ℕ), 0 < r → 4 * ((1:ℝ) / 2) ^ n0 < r → r ≤ 8 * ((1:ℝ) / 2) ^ n0 →
      ∀ M : ℕ, ∑ m ∈ Finset.range M, (((1:ℝ) / 2) ^ (n0 + m)) ^ δ * r ^ (γ - δ) *
        (1 + |Real.log (((1:ℝ) / 2) ^ (n0 + m))|) ^ b ≤ Cf * (r ^ γ * (1 + |Real.log r|) ^ b) := by
  have hρ0 : 0 ≤ ((1:ℝ) / 2) ^ δ := by positivity
  have hρ1 : ((1:ℝ) / 2) ^ δ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hδ
  set ρ := ((1:ℝ) / 2) ^ δ with hρ
  have hsum := r26t8a_p06_summable b hρ0 hρ1
  set S := ∑' m : ℕ, ((m : ℝ) + 2) ^ b * ρ ^ m with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun m => by positivity
  refine ⟨((1:ℝ) / 4) ^ δ * 4 ^ b * S, by positivity, ?_⟩
  intro r n0 hr h1 h3 M
  set τ : ℝ := ((1:ℝ) / 2) ^ n0 with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hL1 : 1 ≤ 1 + |Real.log r| := by linarith [abs_nonneg (Real.log r)]
  have hLτ : (1 + |Real.log τ|) ^ b ≤ (4 * (1 + |Real.log r|)) ^ b := by
    refine (r26t8a_p06_pw2 b (l := r / 8) (s := τ) (by positivity) (by linarith) hτ1).trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ b
    have hl8 : Real.log 8 ≤ 3 := by
      have : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      rw [this]; have := Real.log_two_lt_d9; linarith
    have : |Real.log (r / 8)| ≤ |Real.log r| + Real.log 8 := by
      rw [Real.log_div hr.ne' (by norm_num)]
      calc |Real.log r - Real.log 8| ≤ |Real.log r| + |Real.log 8| := abs_sub _ _
        _ = |Real.log r| + Real.log 8 := by rw [abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 8))]
    linarith
  have hterm : ∀ m ∈ Finset.range M, (((1:ℝ) / 2) ^ (n0 + m)) ^ δ * r ^ (γ - δ) *
      (1 + |Real.log (((1:ℝ) / 2) ^ (n0 + m))|) ^ b ≤
      (((1:ℝ) / 4) ^ δ * 4 ^ b) * (r ^ γ * (1 + |Real.log r|) ^ b) * (((m : ℝ) + 2) ^ b * ρ ^ m) := by
    intro m _
    have e1a : (((1:ℝ) / 2) ^ m) ^ δ = ρ ^ m := by
      rw [hρ, ← Real.rpow_natCast ((1:ℝ) / 2) m, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have e1 : (((1:ℝ) / 2) ^ (n0 + m)) ^ δ = τ ^ δ * ρ ^ m := by
      rw [pow_add, Real.mul_rpow (by positivity) (by positivity), e1a]
    have e2 : τ ^ δ ≤ (r / 4) ^ δ := Real.rpow_le_rpow hτ0.le (by linarith) hδ.le
    have e3 : (r / 4) ^ δ * r ^ (γ - δ) = ((1:ℝ) / 4) ^ δ * r ^ γ := by
      rw [show r / 4 = (1:ℝ) / 4 * r by ring, Real.mul_rpow (by norm_num) hr.le, mul_assoc,
        ← Real.rpow_add hr]
      congr 2; ring
    have e4 : (1 + |Real.log (((1:ℝ) / 2) ^ (n0 + m))|) ^ b ≤
        ((m : ℝ) + 2) ^ b * (4 ^ b * (1 + |Real.log r|) ^ b) := by
      have h := r26t8a_p06_pw3 b m (r := τ) hτ0 hτ1
      rw [show ((1:ℝ) / 2) ^ (n0 + m) = ((1:ℝ) / 2) ^ m * τ by rw [pow_add, mul_comm]]
      refine h.trans ?_
      rw [← mul_pow 4 (1 + |Real.log r|)]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) b) hLτ (by positivity) (by positivity)
    calc (((1:ℝ) / 2) ^ (n0 + m)) ^ δ * r ^ (γ - δ) * (1 + |Real.log (((1:ℝ) / 2) ^ (n0 + m))|) ^ b
        = (τ ^ δ * r ^ (γ - δ)) * ρ ^ m * (1 + |Real.log (((1:ℝ) / 2) ^ (n0 + m))|) ^ b := by
          rw [e1]; ring
      _ ≤ (((1:ℝ) / 4) ^ δ * r ^ γ) * ρ ^ m * (((m : ℝ) + 2) ^ b * (4 ^ b * (1 + |Real.log r|) ^ b)) := by
          have hτr : τ ^ δ * r ^ (γ - δ) ≤ ((1:ℝ) / 4) ^ δ * r ^ γ := by
            rw [← e3]; exact mul_le_mul_of_nonneg_right e2 (Real.rpow_nonneg hr.le _)
          have hpos : 0 ≤ ρ ^ m := pow_nonneg hρ0 m
          exact mul_le_mul (mul_le_mul_of_nonneg_right hτr hpos) e4 (by positivity) (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h2 : ∑ m ∈ Finset.range M, ((m : ℝ) + 2) ^ b * ρ ^ m ≤ S :=
    hsum.sum_le_tsum _ (fun m _ => by positivity)
  have h4 : 0 ≤ (((1:ℝ) / 4) ^ δ * 4 ^ b) * (r ^ γ * (1 + |Real.log r|) ^ b) := by positivity
  calc _ ≤ (((1:ℝ) / 4) ^ δ * 4 ^ b) * (r ^ γ * (1 + |Real.log r|) ^ b) * S := mul_le_mul_of_nonneg_left h2 h4
    _ = _ := by ring

/-- The near part: `n < n0`, `r <= 8 * 2^-n0`. -/
theorem r26t8a_sum_near (b : ℕ) (γ : ℝ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ (r : ℝ) (n0 : ℕ), 0 < r → r ≤ 2 → r ≤ 8 * ((1:ℝ) / 2) ^ n0 →
      ∑ n ∈ Finset.range n0, (((1:ℝ) / 2) ^ n) ^ γ * (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b ≤
        Cn * (1 + r ^ γ * (1 + |Real.log r|) ^ (b + 1)) := by
  have hL : ∀ n : ℕ, (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b ≤ ((n : ℝ) + 1) ^ b := fun n => by
    have h := r26t8a_p06_pw3 b n (r := 1) one_pos le_rfl
    simpa using h
  have hn0 : ∀ (r : ℝ) (n0 : ℕ), 0 < r → r ≤ 8 * ((1:ℝ) / 2) ^ n0 → (n0 : ℝ) ≤ 3 * (1 + |Real.log r|) := by
    intro r n0 hr h
    have h1 : Real.log (r / 8) ≤ Real.log (((1:ℝ) / 2) ^ n0) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div hr.ne' (by norm_num), Real.log_pow] at h1
    have hl2 : Real.log ((1:ℝ) / 2) = -Real.log 2 := by simp [Real.log_inv]
    rw [hl2] at h1
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlog2p : 0 < Real.log 2 := by linarith
    have : (n0 : ℝ) * Real.log 2 ≤ 3 * Real.log 2 + |Real.log r| := by
      have := neg_abs_le (Real.log r)
      nlinarith [le_abs_self (Real.log r)]
    nlinarith [abs_nonneg (Real.log r)]
  rcases lt_trichotomy γ 0 with hγ | hγ | hγ
  · -- negative exponent: geometric sum dominated by the last term
    set lam : ℝ := ((1:ℝ) / 2) ^ γ with hlam
    have hlam1 : 1 < lam := Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) hγ
    refine ⟨3 ^ b * ((1:ℝ) / 8) ^ γ / (lam - 1), by
      have : 0 < lam - 1 := by linarith
      positivity, ?_⟩
    intro r n0 hr hr2 h8
    have hpowl : ∀ n : ℕ, (((1:ℝ) / 2) ^ n) ^ γ = lam ^ n := fun n => by
      rw [hlam, ← Real.rpow_natCast ((1:ℝ) / 2) n, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have hL1 : 1 ≤ 1 + |Real.log r| := by linarith [abs_nonneg (Real.log r)]
    have hnb : ∀ n ∈ Finset.range n0, (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b ≤ (3 * (1 + |Real.log r|)) ^ b := by
      intro n hn
      refine (hL n).trans (pow_le_pow_left₀ (by positivity) ?_ b)
      have := hn0 r n0 hr h8
      have : (n : ℝ) + 1 ≤ n0 := by exact_mod_cast Finset.mem_range.1 hn
      linarith
    have hgeo : ∑ n ∈ Finset.range n0, lam ^ n ≤ lam ^ n0 / (lam - 1) := by
      rw [geom_sum_eq hlam1.ne']
      have : 0 < lam - 1 := by linarith
      rw [div_le_div_iff_of_pos_right this]; linarith
    have hlast : lam ^ n0 ≤ ((1:ℝ) / 8) ^ γ * r ^ γ := by
      rw [← hpowl n0, ← Real.mul_rpow (by norm_num) hr.le]
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hγ.le
      linarith
    calc ∑ n ∈ Finset.range n0, (((1:ℝ) / 2) ^ n) ^ γ * (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b
        ≤ ∑ n ∈ Finset.range n0, lam ^ n * (3 * (1 + |Real.log r|)) ^ b :=
          Finset.sum_le_sum fun n hn => by
            rw [hpowl]; exact mul_le_mul_of_nonneg_left (hnb n hn) (by positivity)
      _ = (∑ n ∈ Finset.range n0, lam ^ n) * (3 * (1 + |Real.log r|)) ^ b := by rw [Finset.sum_mul]
      _ ≤ (lam ^ n0 / (lam - 1)) * (3 * (1 + |Real.log r|)) ^ b :=
          mul_le_mul_of_nonneg_right hgeo (by positivity)
      _ ≤ ((((1:ℝ) / 8) ^ γ * r ^ γ) / (lam - 1)) * (3 * (1 + |Real.log r|)) ^ b := by
          have : 0 < lam - 1 := by linarith
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlast this.le) (by positivity)
      _ ≤ 3 ^ b * ((1:ℝ) / 8) ^ γ / (lam - 1) * (1 + r ^ γ * (1 + |Real.log r|) ^ (b + 1)) := by
          have hlp : 0 < lam - 1 := by linarith
          have hrg : 0 ≤ r ^ γ := Real.rpow_nonneg hr.le _
          have h18 : 0 ≤ ((1:ℝ) / 8) ^ γ := Real.rpow_nonneg (by norm_num) _
          have e : ((((1:ℝ) / 8) ^ γ * r ^ γ) / (lam - 1)) * (3 * (1 + |Real.log r|)) ^ b =
              3 ^ b * ((1:ℝ) / 8) ^ γ / (lam - 1) * (r ^ γ * (1 + |Real.log r|) ^ b) := by
            rw [mul_pow]; field_simp
          rw [e]
          have hLb : (1 + |Real.log r|) ^ b ≤ (1 + |Real.log r|) ^ (b + 1) :=
            pow_le_pow_right₀ hL1 (Nat.le_succ b)
          have hc : 0 ≤ 3 ^ b * ((1:ℝ) / 8) ^ γ / (lam - 1) := by positivity
          refine mul_le_mul_of_nonneg_left ?_ hc
          nlinarith [mul_le_mul_of_nonneg_left hLb hrg]
  · -- critical exponent: n0 terms
    subst hγ
    refine ⟨3 ^ (b + 1), by positivity, ?_⟩
    intro r n0 hr hr2 h8
    have hL1 : 1 ≤ 1 + |Real.log r| := by linarith [abs_nonneg (Real.log r)]
    have hn := hn0 r n0 hr h8
    have hsum : ∑ n ∈ Finset.range n0, (((1:ℝ) / 2) ^ n) ^ (0 : ℝ) *
        (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b ≤ ∑ n ∈ Finset.range n0, (3 * (1 + |Real.log r|)) ^ b := by
      refine Finset.sum_le_sum fun n hn' => ?_
      rw [Real.rpow_zero, one_mul]
      refine (hL n).trans (pow_le_pow_left₀ (by positivity) ?_ b)
      have : (n : ℝ) + 1 ≤ n0 := by exact_mod_cast Finset.mem_range.1 hn'
      linarith
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 : (n0 : ℝ) * (3 * (1 + |Real.log r|)) ^ b ≤ (3 * (1 + |Real.log r|)) ^ (b + 1) := by
      rw [pow_succ, mul_comm ((3 * (1 + |Real.log r|)) ^ b)]
      exact mul_le_mul_of_nonneg_right hn (by positivity)
    refine h1.trans ?_
    rw [Real.rpow_zero, one_mul, mul_pow]
    nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + |Real.log r|) (b + 1), pow_pos (by norm_num : (0:ℝ) < 3) (b + 1)]
  · -- positive exponent: bounded by a convergent series
    have hρ0 : 0 ≤ ((1:ℝ) / 2) ^ γ := by positivity
    have hρ1 : ((1:ℝ) / 2) ^ γ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hγ
    set ρ := ((1:ℝ) / 2) ^ γ with hρ
    have hsum := r26t8a_p06_summable b hρ0 hρ1
    refine ⟨∑' n : ℕ, ((n : ℝ) + 2) ^ b * ρ ^ n, tsum_nonneg fun n => by positivity, ?_⟩
    intro r n0 hr hr2 h8
    have hpowl : ∀ n : ℕ, (((1:ℝ) / 2) ^ n) ^ γ = ρ ^ n := fun n => by
      rw [hρ, ← Real.rpow_natCast ((1:ℝ) / 2) n, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have hS0 : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 2) ^ b * ρ ^ n := tsum_nonneg fun n => by positivity
    have h1 : ∑ n ∈ Finset.range n0, (((1:ℝ) / 2) ^ n) ^ γ * (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b ≤
        ∑' n : ℕ, ((n : ℝ) + 2) ^ b * ρ ^ n := by
      refine (Finset.sum_le_sum fun n _ => ?_).trans (hsum.sum_le_tsum (Finset.range n0) (fun n _ => by positivity))
      rw [hpowl]
      have : (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b ≤ ((n : ℝ) + 2) ^ b :=
        (hL n).trans (pow_le_pow_left₀ (by positivity) (by linarith) b)
      nlinarith [pow_nonneg hρ0 n]
    refine h1.trans ?_
    have : 0 ≤ r ^ γ * (1 + |Real.log r|) ^ (b + 1) := by positivity
    nlinarith

theorem r26t8a_sum_split {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (n0 N : ℕ) :
    ∑ n ∈ Finset.range N, f n ≤ ∑ n ∈ Finset.range n0, f n + ∑ m ∈ Finset.range N, f (n0 + m) := by
  by_cases h : N ≤ n0
  · have : ∑ n ∈ Finset.range N, f n ≤ ∑ n ∈ Finset.range n0, f n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h) (fun i _ _ => hf i)
    have h2 : 0 ≤ ∑ m ∈ Finset.range N, f (n0 + m) := Finset.sum_nonneg fun m _ => hf _
    linarith
  · obtain ⟨K, hK⟩ : ∃ K, N = n0 + K := ⟨N - n0, by omega⟩
    subst hK
    rw [Finset.sum_range_add]
    have : ∑ m ∈ Finset.range K, f (n0 + m) ≤ ∑ m ∈ Finset.range (n0 + K), f (n0 + m) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) (fun i _ _ => hf _)
    linarith

/-- Dyadic sum of the annular bounds: near for `r <= 4 * 2^-n`, far otherwise. -/
theorem r26t8a_sum_bound (b : ℕ) {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → r ≤ 2 → ∀ N : ℕ,
      ∑ n ∈ Finset.range N, (if r ≤ 4 * ((1:ℝ) / 2) ^ n then
          (((1:ℝ) / 2) ^ n) ^ γ * (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b
        else (((1:ℝ) / 2) ^ n) ^ δ * r ^ (γ - δ) * (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b) ≤
      C * (1 + r ^ γ * (1 + |Real.log r|) ^ (b + 1)) := by
  obtain ⟨Cf, hCf0, hCf⟩ := r26t8a_sum_far b hδ γ
  obtain ⟨Cn, hCn0, hCn⟩ := r26t8a_sum_near b γ
  refine ⟨Cf + Cn, add_nonneg hCf0 hCn0, ?_⟩
  intro r hr hr2 N
  have hex : ∃ n : ℕ, 4 * ((1:ℝ) / 2) ^ n < r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < r / 4 by positivity) (by norm_num : ((1:ℝ) / 2) < 1)
    exact ⟨n, by linarith⟩
  classical
  set n0 := Nat.find hex with hn0
  have hn0spec : 4 * ((1:ℝ) / 2) ^ n0 < r := Nat.find_spec hex
  have hmin : ∀ n < n0, r ≤ 4 * ((1:ℝ) / 2) ^ n := fun n hn => by
    have := Nat.find_min hex hn
    push Not at this; exact this
  have hn0pos : 1 ≤ n0 := by
    by_contra h
    have : n0 = 0 := by omega
    rw [this] at hn0spec; norm_num at hn0spec; linarith
  have h8 : r ≤ 8 * ((1:ℝ) / 2) ^ n0 := by
    have := hmin (n0 - 1) (by omega)
    have e : ((1:ℝ) / 2) ^ (n0 - 1) = 2 * ((1:ℝ) / 2) ^ n0 := by
      obtain ⟨k, hk⟩ : ∃ k, n0 = k + 1 := ⟨n0 - 1, by omega⟩
      rw [hk, pow_succ]; simp; ring
    rw [e] at this; linarith
  set f : ℕ → ℝ := fun n => if r ≤ 4 * ((1:ℝ) / 2) ^ n then
          (((1:ℝ) / 2) ^ n) ^ γ * (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b
        else (((1:ℝ) / 2) ^ n) ^ δ * r ^ (γ - δ) * (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    rw [hf]; dsimp only
    split_ifs
    · positivity
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hr.le _)) (by positivity)
  refine (r26t8a_sum_split hf0 n0 N).trans ?_
  have hnear : ∑ n ∈ Finset.range n0, f n =
      ∑ n ∈ Finset.range n0, (((1:ℝ) / 2) ^ n) ^ γ * (1 + |Real.log (((1:ℝ) / 2) ^ n)|) ^ b :=
    Finset.sum_congr rfl fun n hn => by rw [hf]; dsimp only; rw [if_pos (hmin n (Finset.mem_range.1 hn))]
  have hfar : ∀ m : ℕ, f (n0 + m) = (((1:ℝ) / 2) ^ (n0 + m)) ^ δ * r ^ (γ - δ) *
      (1 + |Real.log (((1:ℝ) / 2) ^ (n0 + m))|) ^ b := fun m => by
    rw [hf]; dsimp only
    rw [if_neg]
    push Not
    have : ((1:ℝ) / 2) ^ (n0 + m) ≤ ((1:ℝ) / 2) ^ n0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  rw [hnear, Finset.sum_congr rfl fun m _ => hfar m]
  have h1 := hCn r n0 hr hr2 h8
  have h2 := hCf r n0 hr hn0spec h8 N
  have hL1 : 1 ≤ 1 + |Real.log r| := by linarith [abs_nonneg (Real.log r)]
  have hLb : (1 + |Real.log r|) ^ b ≤ (1 + |Real.log r|) ^ (b + 1) :=
    pow_le_pow_right₀ hL1 (Nat.le_succ b)
  have hrg : 0 ≤ r ^ γ := Real.rpow_nonneg hr.le _
  have h3 : Cf * (r ^ γ * (1 + |Real.log r|) ^ b) ≤ Cf * (1 + r ^ γ * (1 + |Real.log r|) ^ (b + 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCf0
    nlinarith [mul_le_mul_of_nonneg_left hLb hrg]
  nlinarith

end HRS.MS.R26T8A
