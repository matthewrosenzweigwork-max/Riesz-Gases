import HRS.MS.R26T8AR1b
import HRS.MS.R26T8AP22g

/-!
# S8.2 T8A R1c: the three pointwise bounds of the sharp corrector from sharp mixed jets of order `≤ 2`
`r26t8a_R1_pair_bounds`: if `‖mixedJet p q Q X z‖ ≤ A w (1 + r^(-(s-2+q)) + [q=0] lg |log r|)` for `p+q ≤ 2` (`r = min 1 |z|`, `lg ∈ {0,1}`, `lg = 1 → 2 ≤ s`) then for `x ≠ y`:
`‖∇_x Q‖ + ‖∇_y Q‖ ≤ 20 A w (1 + r^(1-s))` and `‖D^2 Q (x,y)‖ ≤ 20 A w (1 + r^(-s))`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_R1_abs_log_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : |Real.log r| ≤ r ^ (-(1 : ℝ)) := by
  rw [Real.rpow_neg_one, abs_of_nonpos (Real.log_nonpos hr0.le hr1)]
  have := Real.log_le_sub_one_of_pos (inv_pos.2 hr0)
  rw [Real.log_inv] at this
  linarith

theorem r26t8a_R1_pair_bounds {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (M s lg A : ℝ) (hA : 0 ≤ A)
    (hlg : lg = 0 ∨ (lg = 1 ∧ 2 ≤ s)) (hs1 : 1 ≤ s) {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2})
    (hj : ∀ p q : ℕ, p + q ≤ 2 → ∀ X z : Euc d, z ≠ 0 →
      ‖mixedJet p q Q X z‖ ≤ A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        (1 + (min 1 ‖z‖) ^ (-((s - 2) + (q : ℝ))) + (if q = 0 then lg * |Real.log (min 1 ‖z‖)| else 0)))
    {x y : Euc d} (hxy : x ≠ y) :
    ‖pairGradX Q x y‖ + ‖pairGradY Q x y‖ ≤
      20 * A * HRS.MS.Phase2S82.pairWeight M x y * (1 + (min 1 ‖x - y‖) ^ (1 - s)) ∧
    ‖iteratedFDeriv ℝ 2 (Function.uncurry Q) (x, y)‖ ≤
      20 * A * HRS.MS.Phase2S82.pairWeight M x y * (1 + (min 1 ‖x - y‖) ^ (-s)) := by
  set X : Euc d := (1 / 2 : ℝ) • (x + y) with hX
  set z : Euc d := x - y with hz
  have hz0 : z ≠ 0 := sub_ne_zero.2 hxy
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have e1 : X + (1 / 2 : ℝ) • z = x := by rw [hX, hz]; module
  have e2 : X - (1 / 2 : ℝ) • z = y := by rw [hX, hz]; module
  set r : ℝ := min 1 ‖z‖ with hr
  have hr0 : 0 < r := lt_min one_pos hzn
  have hr1 : r ≤ 1 := min_le_left _ _
  set w : ℝ := HRS.MS.Phase2S82.pairWeight M x y with hw
  have hw0 : 0 ≤ w := by
    rw [hw]; unfold HRS.MS.Phase2S82.pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hjj : ∀ p q : ℕ, p + q ≤ 2 → ‖mixedJet p q Q X z‖ ≤
      A * w * (1 + r ^ (-((s - 2) + (q : ℝ))) + (if q = 0 then lg * |Real.log r| else 0)) := by
    intro p q hpq
    have := hj p q hpq X z hz0
    rwa [e1, e2] at this
  -- elementary comparisons
  have hmono : ∀ a b : ℝ, b ≤ a → r ^ a ≤ r ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hab
  have hlogG : lg * |Real.log r| ≤ r ^ (1 - s) := by
    rcases hlg with h | ⟨h, h2⟩
    · rw [h, zero_mul]; exact Real.rpow_nonneg hr0.le _
    · rw [h, one_mul]; exact (r26t8a_R1_abs_log_le hr0 hr1).trans (hmono _ _ (by linarith))
  have h0 : r ^ (-((s - 2) + (0 : ℕ))) ≤ r ^ (1 - s) := hmono _ _ (by push_cast; linarith)
  have h1 : r ^ (-((s - 2) + (1 : ℕ))) = r ^ (1 - s) := by push_cast; congr 1; ring
  have h2 : r ^ (-((s - 2) + (2 : ℕ))) = r ^ (-s) := by push_cast; congr 1; ring
  have hpos1 : 0 ≤ r ^ (1 - s) := Real.rpow_nonneg hr0.le _
  have hpos2 : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr0.le _
  have hAw : 0 ≤ A * w := mul_nonneg hA hw0
  have hQ1 : ContDiffOn ℝ (1 : ℕ) (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} := hQ.of_le (by norm_num)
  -- jets
  set G : ℝ := 1 + r ^ (1 - s) with hG
  set G2 : ℝ := 1 + r ^ (-s) with hG2
  have hG1 : G ≤ G2 := by rw [hG, hG2]; linarith [hmono (1 - s) (-s) (by linarith)]
  have hG0 : 0 ≤ G := by rw [hG]; linarith
  have J10 : ‖mixedJet 1 0 Q X z‖ ≤ A * w * (2 * G) := by
    have := hjj 1 0 (by norm_num); rw [if_pos rfl] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hAw)
    linarith [hlogG, h0]
  have J01 : ‖mixedJet 0 1 Q X z‖ ≤ A * w * G := by
    have := hjj 0 1 (by norm_num); rw [if_neg one_ne_zero, add_zero, h1] at this
    exact this
  have J20 : ‖mixedJet 2 0 Q X z‖ ≤ A * w * (2 * G2) := by
    have := hjj 2 0 (by norm_num); rw [if_pos rfl] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hAw)
    linarith [hmono (1 - s) (-s) (by linarith), hlogG, h0]
  have J11 : ‖mixedJet 1 1 Q X z‖ ≤ A * w * G2 := by
    have := hjj 1 1 (by norm_num); rw [if_neg one_ne_zero, add_zero, h1] at this
    exact this.trans (mul_le_mul_of_nonneg_left hG1 hAw)
  have J02 : ‖mixedJet 0 2 Q X z‖ ≤ A * w * G2 := by
    have := hjj 0 2 (by norm_num); rw [if_neg (by norm_num), add_zero, h2] at this
    exact this
  refine ⟨?_, ?_⟩
  · have hx := r26t8a_R1_xslice hchi (j := 1) hQ1 hxy
    have hy := r26t8a_R1_yslice hchi (j := 1) hQ1 hxy
    have gx : ‖pairGradX Q x y‖ = ‖iteratedFDeriv ℝ 1 (fun u => Q u y) x‖ := by
      unfold pairGradX
      rw [r26t8a_p22_grad_norm, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0), norm_iteratedFDeriv_zero]
    have gy : ‖pairGradY Q x y‖ = ‖iteratedFDeriv ℝ 1 (Q x) y‖ := by
      unfold pairGradY
      rw [r26t8a_p22_grad_norm, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0), norm_iteratedFDeriv_zero]
    have hx' : ‖iteratedFDeriv ℝ 1 (fun u => Q u y) x‖ ≤ ‖mixedJet 1 0 Q X z‖ + ‖mixedJet 0 1 Q X z‖ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right, Nat.choose_self,
        Nat.sub_zero, Nat.sub_self, Nat.cast_one, one_mul] at hx
      exact hx
    have hy' : ‖iteratedFDeriv ℝ 1 (Q x) y‖ ≤ ‖mixedJet 1 0 Q X z‖ + ‖mixedJet 0 1 Q X z‖ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right, Nat.choose_self,
        Nat.sub_zero, Nat.sub_self, Nat.cast_one, one_mul] at hy
      exact hy
    rw [gx, gy]
    have : A * w * (2 * G) + A * w * G ≤ 10 * A * w * G := by nlinarith [mul_nonneg hAw hG0]
    nlinarith [mul_nonneg hAw hG0]
  · have hf := r26t8a_R1_full hchi (j := 2) hQ hxy
    have hf' : ‖iteratedFDeriv ℝ 2 (Function.uncurry Q) (x, y)‖ ≤
        4 * (‖mixedJet 2 0 Q X z‖ + 2 * ‖mixedJet 1 1 Q X z‖ + ‖mixedJet 0 2 Q X z‖) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right, Nat.choose_self,
        Nat.choose_one_right, Nat.sub_zero, Nat.sub_self, Nat.reduceSub, Nat.cast_one, Nat.cast_ofNat, one_mul] at hf
      nlinarith [hf]
    have hG20 : 0 ≤ G2 := by linarith
    nlinarith [mul_nonneg hAw hG20]

end HRS.MS.R26T8A
