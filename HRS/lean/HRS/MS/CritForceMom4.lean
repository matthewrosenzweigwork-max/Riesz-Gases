import HRS.MS.CritForceMom3

/-!
# S8.2 NormalForm packet R03, part 4: definitions, rpow bookkeeping, the two cutoff-free rows

`s82n_smallRadius`, `s82n_pole`, `s82n_logN`, `S82nShortRangePole` are the Pro definitions
(`smallRadius`, `pole`, `logN`, `ShortRangePole` of `S8.2-Defs/Moments.lean`) with `criticalS d = d/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

def s82n_smallRadius {d : ℕ} (x y : Euc d) : ℝ := min 1 ‖x - y‖

def s82n_pole {d : ℕ} (x y : Euc d) : ℝ := 1 + s82n_smallRadius x y ^ (-s82n_critS d)

def s82n_logN (N : ℕ) : ℝ := Real.log (Real.exp 1 * N)

/-- The small heat-cutoff singular kernel. -/
structure S82nShortRangePole (d : ℕ) (q : Euc d → ℝ) : Prop where
  measurable : Measurable q
  smooth : ContDiffOn ℝ ∞ q {z | z ≠ 0}
  even : ∀ z, q (-z) = q z
  nonneg : ∀ z, 0 ≤ q z
  near : ∃ r c C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧
    ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r →
      c * ‖z‖ ^ (-s82n_critS d) ≤ q z ∧ q z ≤ C * ‖z‖ ^ (-s82n_critS d)
  far : ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧
    ∀ z, r ≤ ‖z‖ → q z ≤ C * Real.exp (-c * ‖z‖ ^ 2)

/-- Gaussian moment constant, exact value. -/
lemma s82n_mom_bound (hd : 1 ≤ d) (M G c : ℝ) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c) :
    ∫⁻ y : Euc d, ENNReal.ofReal (G * Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M) ≤
      ENNReal.ofReal (G * ∫ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M) := by
  have hi := (s82n_gauss_moment hd M c hM hc).const_mul G
  have h0 : ∀ y : Euc d, 0 ≤ G * (Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M) := fun y =>
    mul_nonneg hG (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (s82n_jb_pos y).le _))
  calc ∫⁻ y : Euc d, ENNReal.ofReal (G * Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M)
      = ∫⁻ y : Euc d, ENNReal.ofReal (G * (Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M)) := by
        refine lintegral_congr fun y => ?_
        rw [mul_assoc]
    _ = ENNReal.ofReal (∫ y : Euc d, G * (Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M)) :=
        (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall h0)).symm
    _ ≤ _ := le_of_eq (by rw [integral_const_mul])

/-- `w = r^s` bookkeeping, `s = d/2`: all powers of `r` are rational in `r` and `w`. -/
lemma s82n_rpow_forms (hd : 1 ≤ d) (r : ℝ) (hr : 0 < r) :
    r ^ (d - 1) = (r ^ s82n_critS d) ^ 2 / r ∧
    r ^ (s82n_critS d - 1) = r ^ s82n_critS d / r ∧
    r ^ (-s82n_critS d) = (r ^ s82n_critS d)⁻¹ ∧
    r ^ (1 - s82n_critS d) = r / r ^ s82n_critS d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (r ^ s82n_critS d) ^ 2 = r ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_natCast]
      congr 1; unfold s82n_critS; push_cast; ring
    rw [h1]
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp [pow_succ]
    field_simp
  · exact Real.rpow_sub_one hr.ne' _
  · exact Real.rpow_neg hr.le _
  · rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one, Real.rpow_neg hr.le]
    ring

lemma s82n_critS_pos (hd : 1 ≤ d) : 0 < s82n_critS d := by
  unfold s82n_critS; have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma s82n_critS_ge_one (hd : 2 ≤ d) : 1 ≤ s82n_critS d := by
  unfold s82n_critS; have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma s82n_rpow_neg_anti (a r0 t : ℝ) (ha : 0 ≤ a) (hr0 : 0 < r0) (h : r0 ≤ t) :
    t ^ (-a) ≤ r0 ^ (-a) := by
  have ht : 0 < t := lt_of_lt_of_le hr0 h
  rw [Real.rpow_neg ht.le, Real.rpow_neg hr0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hr0 _) (Real.rpow_le_rpow hr0.le h ha)

end HRS.MS.S82N
