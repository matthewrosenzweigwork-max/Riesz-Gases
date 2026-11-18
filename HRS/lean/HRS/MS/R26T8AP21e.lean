import HRS.MS.R26T8AP21d

/-!
# S8.2 local Newton layer, packet T8A.P21 (part e): bounds for the contraction chain and for the nested jets of `u_m(tau)`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_arith_small {K z : ℝ} (hK : 0 ≤ K) (hz0 : 0 ≤ z) (hz : z ≤ 1) (a m q : ℕ) {u v : ℝ}
    (hu : u ≤ K * ((q : ℝ) + 2) ^ a * z ^ (m - (q + 1))) (hv : v ≤ K * ((q : ℝ) + 1) ^ a * z ^ (m - q)) :
    z * u + ((q : ℝ) + 1) * v ≤ K * ((q : ℝ) + 2) ^ (a + 1) * z ^ (m + 1 - (q + 1)) := by
  have e : m + 1 - (q + 1) = m - q := by omega
  rw [e]
  have h1 : z ^ (1 + (m - (q + 1))) ≤ z ^ (m - q) := pow_le_pow_of_le_one hz0 hz (by omega)
  have hz1 : z * z ^ (m - (q + 1)) ≤ z ^ (m - q) := by rw [← pow_succ']; rw [add_comm] at h1; exact h1
  have hq : ((q : ℝ) + 1) ^ a ≤ ((q : ℝ) + 2) ^ a := pow_le_pow_left₀ (by positivity) (by linarith) a
  have hA : 0 ≤ ((q : ℝ) + 2) ^ a := by positivity
  have hzq : 0 ≤ z ^ (m - q) := by positivity
  calc z * u + ((q : ℝ) + 1) * v ≤ z * (K * ((q : ℝ) + 2) ^ a * z ^ (m - (q + 1))) +
        ((q : ℝ) + 1) * (K * ((q : ℝ) + 1) ^ a * z ^ (m - q)) := by
        gcongr
    _ = K * ((q : ℝ) + 2) ^ a * (z * z ^ (m - (q + 1))) + ((q : ℝ) + 1) * (K * ((q : ℝ) + 1) ^ a * z ^ (m - q)) := by ring
    _ ≤ K * ((q : ℝ) + 2) ^ a * z ^ (m - q) + ((q : ℝ) + 1) * (K * ((q : ℝ) + 2) ^ a * z ^ (m - q)) := by
        gcongr
    _ = _ := by rw [pow_succ]; ring

theorem r26t8a_arith_large {K z : ℝ} (hK : 0 ≤ K) (hz0 : 0 ≤ z) (a b q : ℕ) {u v : ℝ}
    (hu : u ≤ K * ((q : ℝ) + 2) ^ a * (1 + z) ^ b) (hv : v ≤ K * ((q : ℝ) + 1) ^ a * (1 + z) ^ b) :
    z * u + ((q : ℝ) + 1) * v ≤ K * ((q : ℝ) + 2) ^ (a + 1) * (1 + z) ^ (b + 1) := by
  have hq : ((q : ℝ) + 1) ^ a ≤ ((q : ℝ) + 2) ^ a := pow_le_pow_left₀ (by positivity) (by linarith) a
  have hA : 0 ≤ ((q : ℝ) + 2) ^ a := by positivity
  have hB : 0 ≤ (1 + z) ^ b := by positivity
  calc z * u + ((q : ℝ) + 1) * v ≤ z * (K * ((q : ℝ) + 2) ^ a * (1 + z) ^ b) +
        ((q : ℝ) + 1) * (K * ((q : ℝ) + 1) ^ a * (1 + z) ^ b) := by gcongr
    _ ≤ z * (K * ((q : ℝ) + 2) ^ a * (1 + z) ^ b) + ((q : ℝ) + 1) * (K * ((q : ℝ) + 2) ^ a * (1 + z) ^ b) := by
        gcongr
    _ = K * ((q : ℝ) + 2) ^ a * (1 + z) ^ b * (z + (q + 1)) := by ring
    _ ≤ K * ((q : ℝ) + 2) ^ a * (1 + z) ^ b * (((q : ℝ) + 2) * (1 + z)) := by
        gcongr
        nlinarith [mul_nonneg hz0 (by positivity : (0 : ℝ) ≤ q)]
    _ = _ := by rw [pow_succ, pow_succ]; ring

section Chain2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_chain_small (N p : ℕ) {K : ℝ} (hK : 0 ≤ K) (X z : E) (hz : ‖z‖ ≤ 1) :
    ∀ (j : ℕ) {n : ℕ} (a m : ℕ) (G : E × E → r26t8a_Mult E (n + j)), ContDiff ℝ (N : WithTop ℕ∞) G →
      (∀ q, p + q ≤ N → ‖r26t8a_nest p q G X z‖ ≤ K * ((q : ℝ) + 1) ^ a * ‖z‖ ^ (m - q)) →
      ∀ q, p + q ≤ N → ‖r26t8a_nest p q (r26t8a_contrIter j G) X z‖ ≤
        K * ((q : ℝ) + 1) ^ (a + j) * ‖z‖ ^ (m + j - q)
  | 0, _, a, m, G, _, hb, q, hq => by simpa [r26t8a_contrIter] using hb q hq
  | j + 1, n, a, m, G, hG, hb, q, hq => by
    have hcd := r26t8a_contr_contDiff hG
    have key := r26t8a_chain_small N p hK X z hz j (a + 1) (m + 1) (r26t8a_contr G) hcd (n := n) (fun q hq => by
      have hGq : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) G := hG.of_le (by exact_mod_cast hq)
      refine (r26t8a_contr_step p q G X z hGq).trans ?_
      rcases q with _ | q
      · have := hb 0 (by simpa using hq)
        simp only [Nat.cast_zero, zero_add, one_pow, mul_one, Nat.sub_zero] at this ⊢
        calc ‖z‖ * ‖r26t8a_nest p 0 G X z‖ + 0 * _ ≤ ‖z‖ * (K * ‖z‖ ^ m) := by
              rw [zero_mul, add_zero]; exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = K * ‖z‖ ^ (m + 1) := by ring
      · have h1 := hb (q + 1) hq
        have h2 := hb q (by omega)
        have e1 : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by push_cast; ring
        have e2 : ((q + 1 : ℕ) : ℝ) + 1 = (q : ℝ) + 2 := by push_cast; ring
        rw [e2] at h1
        rw [e2, e1, Nat.add_sub_cancel]
        exact r26t8a_arith_small hK (norm_nonneg z) hz a m q h1 h2) q hq
    simpa [r26t8a_contrIter, add_assoc, add_comm, add_left_comm] using key

theorem r26t8a_chain_large (N p : ℕ) {K : ℝ} (hK : 0 ≤ K) (X z : E) :
    ∀ (j : ℕ) {n : ℕ} (a b : ℕ) (G : E × E → r26t8a_Mult E (n + j)), ContDiff ℝ (N : WithTop ℕ∞) G →
      (∀ q, p + q ≤ N → ‖r26t8a_nest p q G X z‖ ≤ K * ((q : ℝ) + 1) ^ a * (1 + ‖z‖) ^ b) →
      ∀ q, p + q ≤ N → ‖r26t8a_nest p q (r26t8a_contrIter j G) X z‖ ≤
        K * ((q : ℝ) + 1) ^ (a + j) * (1 + ‖z‖) ^ (b + j)
  | 0, _, a, b, G, _, hb, q, hq => by simpa [r26t8a_contrIter] using hb q hq
  | j + 1, n, a, b, G, hG, hb, q, hq => by
    have hcd := r26t8a_contr_contDiff hG
    have key := r26t8a_chain_large N p hK X z j (a + 1) (b + 1) (r26t8a_contr G) hcd (n := n) (fun q hq => by
      have hGq : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) G := hG.of_le (by exact_mod_cast hq)
      refine (r26t8a_contr_step p q G X z hGq).trans ?_
      rcases q with _ | q
      · have := hb 0 (by simpa using hq)
        simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at this ⊢
        calc ‖z‖ * ‖r26t8a_nest p 0 G X z‖ + 0 * _ ≤ ‖z‖ * (K * (1 + ‖z‖) ^ b) := by
              rw [zero_mul, add_zero]; exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ ≤ K * (1 + ‖z‖) ^ (b + 1) := by
              rw [pow_succ]
              have : 0 ≤ K * (1 + ‖z‖) ^ b := by positivity
              nlinarith [mul_nonneg this (norm_nonneg z)]
      · have h1 := hb (q + 1) hq
        have h2 := hb q (by omega)
        have e1 : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by push_cast; ring
        have e2 : ((q + 1 : ℕ) : ℝ) + 1 = (q : ℝ) + 2 := by push_cast; ring
        rw [e2] at h1
        rw [e2, e1, Nat.add_sub_cancel]
        exact r26t8a_arith_large hK (norm_nonneg z) a b q h1 h2) q hq
    simpa [r26t8a_contrIter, add_assoc, add_comm, add_left_comm] using key

end Chain2

end HRS.MS.R26T8A
