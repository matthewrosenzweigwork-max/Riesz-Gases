import HRS.MS.R26T8AP11f9
import HRS.MS.R26T8AP11f3

/-!
# S8.2 T8A P11f (part 10): helper bounds for jets of products on an open set, and the envelope on `|u-y| ≥ 1/4`
`r26t8a_f10_jet_mul_on`: `f, g` of class `C^n` on an open `s`, jets of order `≤ n` at `x ∈ s` bounded by `a`, `b` give `‖D^n (f g) x‖ ≤ 2^n a b`.
`r26t8a_f10_env_bdd`: `1 + s^(-e) (1+|log s|)^b ≤ C` for `s = min 1 r`, `r ≥ 1/4`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_f10_jet_mul_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (hs : IsOpen s)
    {f g : E → ℝ} {n : ℕ} (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f s) (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g s)
    {x : E} (hx : x ∈ s) {a b : ℝ} (ha : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ a)
    (hb : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ b) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2 ^ n * (a * b) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 (Nat.zero_le _))
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  have hU : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have e : ∀ (m : ℕ) (h : E → ℝ), iteratedFDerivWithin ℝ m h s x = iteratedFDeriv ℝ m h x :=
    fun m h => iteratedFDerivWithin_of_isOpen m hs hx
  rw [← e]
  refine (norm_iteratedFDerivWithin_mul_le hf hg hU hx (n := n) le_rfl).trans ?_
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g s x‖ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (a * b) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [e, e]
        have := mul_le_mul (ha i hi') (hb (n - i) (Nat.sub_le n i)) (norm_nonneg _) ha0
        calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖
            = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) := by ring
          _ ≤ (n.choose i : ℝ) * (a * b) := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    _ = 2 ^ n * (a * b) := by
        rw [← Finset.sum_mul]
        have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by exact_mod_cast Nat.sum_range_choose n
        rw [this]

theorem r26t8a_f10_env_bdd (b : ℕ) (e : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 / 4 ≤ r →
      1 + (min 1 r) ^ (-e) * (1 + |Real.log (min 1 r)|) ^ b ≤ C := by
  refine ⟨1 + (4 : ℝ) ^ |e| * (1 + Real.log 4) ^ b, by positivity, fun r hr => ?_⟩
  have hs0 : 0 < min 1 r := lt_min one_pos (by linarith)
  have hs1 : min 1 r ≤ 1 := min_le_left _ _
  have hs4 : 1 / 4 ≤ min 1 r := le_min (by norm_num) hr
  have h1 : (min 1 r) ^ (-e) ≤ 4 ^ |e| := by
    have h2 : (min 1 r) ^ (-e) ≤ (min 1 r) ^ (-|e|) :=
      Real.rpow_le_rpow_of_exponent_ge hs0 hs1 (by linarith [le_abs_self e])
    have h3 : (min 1 r) ^ (-|e|) ≤ (1 / 4 : ℝ) ^ (-|e|) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hs4 (by linarith [abs_nonneg e])
    refine h2.trans (h3.trans (le_of_eq ?_))
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
  have h4 : |Real.log (min 1 r)| ≤ Real.log 4 := by
    rw [abs_of_nonpos (Real.log_nonpos hs0.le hs1)]
    have : Real.log (1 / 4) ≤ Real.log (min 1 r) := Real.log_le_log (by norm_num) hs4
    rw [one_div, Real.log_inv] at this
    linarith
  have h5 : (1 + |Real.log (min 1 r)|) ^ b ≤ (1 + Real.log 4) ^ b :=
    pow_le_pow_left₀ (by positivity) (by linarith) b
  have h6 : 0 ≤ (min 1 r) ^ (-e) := Real.rpow_nonneg hs0.le _
  have := mul_le_mul h1 h5 (by positivity) (by positivity)
  linarith

end HRS.MS.R26T8A
