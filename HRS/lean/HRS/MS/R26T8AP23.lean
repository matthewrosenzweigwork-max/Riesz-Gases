import HRS.MS.R26T8AR4e
import HRS.MS.R26T8AR1c

/-!
# S8.2 local Newton layer, packet T8A.P23: sharp value, gradient and Hessian of the finite local corrector (Pro contract verbatim)
`parametrix = R_L + W` with `R_L = rawNewton β⁻¹ χ (src f)` (R4e: sharp mixed jets, the logarithm only for `d = 4` and only for `q = 0`) and
`W` of class `Conormal 8 0 M (s-2)` (R4d, log-free); the mixed jets are additive (Y3a) and R1c turns the sharp mixed jets of order `≤ 2` into the
pointwise bounds on `Q`, `∇Q` and `D²Q`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 6400000 in
theorem r26t8a_parametrix_sharp (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
      let Q := r26t8a_parametrix (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f
      ∀ x y, x ≠ y →
        |Q x y| ≤ C * A * HRS.MS.Phase2S82.pairWeight M x y * (1 + HRS.MS.Phase2S82.smallRadius x y ^ (2 - criticalS d) +
          if d = 4 then |Real.log (HRS.MS.Phase2S82.smallRadius x y)| else 0) ∧
        ‖pairGradX Q x y‖ + ‖pairGradY Q x y‖ ≤ C * A * HRS.MS.Phase2S82.pairWeight M x y *
          (1 + HRS.MS.Phase2S82.smallRadius x y ^ (1 - criticalS d)) ∧
        ‖iteratedFDeriv ℝ 2 (Function.uncurry Q) (x, y)‖ ≤ C * A * HRS.MS.Phase2S82.pairWeight M x y *
          HRS.MS.Phase2S82.pole x y := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C4, hC40, hC4⟩ := r26t8a_R4_W_class hd a beta ha hbeta chi hchi
  obtain ⟨CR, hCR0, hCR⟩ := r26t8a_R4_RL_jets hd a beta ha hbeta chi hchi
  set M : ℝ := 2 * (iterationCount d : ℝ) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨20 * (CR + C4), M, by positivity, hM0, fun rho hrho f A hA hf => ?_⟩
  intro Q x y hxy
  obtain ⟨hRLc, hWc⟩ := hC4 rho hrho f A hA hf
  set RL : Euc d → Euc d → ℝ := rawNewton beta⁻¹ chi (r26t8a_R3_src f) with hRL
  set W : Euc d → Euc d → ℝ := fun x y => Q x y - RL x y with hW
  have hQeq : Q = fun x y => RL x y + W x y := by funext x y; simp only [hW]; ring
  have hRL2 : ContDiffOn ℝ 2 (Function.uncurry RL) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hRLc.1.of_le (by norm_num)
  have hW2 : ContDiffOn ℝ 2 (Function.uncurry W) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hWc.1.of_le (by norm_num)
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} := by
    rw [hQeq]; exact hRL2.add hW2
  set lg : ℝ := if d = 4 then 1 else 0 with hlg
  have hlg' : lg = 0 ∨ (lg = 1 ∧ 2 ≤ criticalS d) := by
    by_cases h4 : d = 4
    · right; refine ⟨by simp [hlg, h4], ?_⟩
      unfold criticalS; rw [h4]; norm_num
    · left; simp [hlg, h4]
  have hs1 : 1 ≤ criticalS d := by unfold criticalS; linarith
  have hCRW : 0 ≤ (CR + C4) * A := mul_nonneg (by positivity) hA
  have hj : ∀ p q : ℕ, p + q ≤ 2 → ∀ X z : Euc d, z ≠ 0 →
      ‖mixedJet p q Q X z‖ ≤ ((CR + C4) * A) * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        (1 + (min 1 ‖z‖) ^ (-((criticalS d - 2) + (q : ℝ))) +
          (if q = 0 then lg * |Real.log (min 1 ‖z‖)| else 0)) := by
    intro p q hpq X z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hr0 : 0 < min 1 ‖z‖ := lt_min one_pos hzn
    have hadd := r26t8a_Y3a_jet_add hchi (n := 2) hRL2 hW2 p q hpq X z hz
    have hQ' : mixedJet p q Q X z = mixedJet p q RL X z + mixedJet p q W X z := by
      rw [hQeq]; exact hadd
    have h1 := hCR rho hrho f A hA hf p q hpq X z hz
    have h2 := hWc.2 p q (by omega) X z hz
    simp only [pow_zero, mul_one] at h2
    have hpw := r26t8a_pairWeight_nonneg (d := d) M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)
    set pw := HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) with hpwd
    have hlgeq : (if q = 0 then (if d = 4 then |Real.log (min 1 ‖z‖)| else 0) else 0) =
        (if q = 0 then lg * |Real.log (min 1 ‖z‖)| else 0) := by
      by_cases hq : q = 0 <;> by_cases h4 : d = 4 <;> simp [hlg, hq, h4]
    rw [hlgeq] at h1
    rw [hQ']
    refine (norm_add_le _ _).trans ?_
    have hrp : 0 ≤ (min 1 ‖z‖) ^ (-((criticalS d - 2) + (q : ℝ))) := Real.rpow_nonneg hr0.le _
    have hlgn : 0 ≤ (if q = 0 then lg * |Real.log (min 1 ‖z‖)| else 0) := by
      split_ifs
      · rcases hlg' with h | ⟨h, -⟩ <;> rw [h] <;> positivity
      · exact le_rfl
    have hAw : 0 ≤ A * pw := mul_nonneg hA hpw
    nlinarith [mul_nonneg (mul_nonneg hC40 hAw) hlgn, mul_nonneg hAw hrp, mul_nonneg (mul_nonneg hCR0 hAw) hrp,
      mul_nonneg (mul_nonneg hCR0 hAw) hlgn, mul_nonneg hAw hlgn, mul_nonneg hCR0 hAw, mul_nonneg hC40 hAw,
      mul_nonneg (mul_nonneg hC40 hAw) hrp]
  obtain ⟨hgrad, hhess⟩ := r26t8a_R1_pair_bounds hchi M (criticalS d) lg ((CR + C4) * A) hCRW hlg' hs1 hQ2 hj hxy
  have hw0 : 0 ≤ HRS.MS.Phase2S82.pairWeight M x y := r26t8a_pairWeight_nonneg (d := d) M x y
  have hr0 : 0 < HRS.MS.Phase2S82.smallRadius x y := lt_min one_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy))
  refine ⟨?_, ?_, ?_⟩
  · -- the value
    have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    have h0 := hj 0 0 (by norm_num) ((1 / 2 : ℝ) • (x + y)) (x - y) hz
    have e1 : (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y) = x := by module
    have e2 : (1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • (x - y) = y := by module
    rw [e1, e2] at h0
    have e0 : ‖mixedJet 0 0 Q ((1 / 2 : ℝ) • (x + y)) (x - y)‖ = |Q x y| := by
      unfold mixedJet
      simp only [norm_iteratedFDeriv_zero, midPair, e1, e2, Real.norm_eq_abs]
    rw [e0] at h0
    have hlgeq : lg * |Real.log (min 1 ‖x - y‖)| = if d = 4 then |Real.log (min 1 ‖x - y‖)| else 0 := by
      by_cases h4 : d = 4 <;> simp [hlg, h4]
    simp only [if_true, Nat.cast_zero, add_zero] at h0
    rw [hlgeq] at h0
    have e3 : (min 1 ‖x - y‖) ^ (-(criticalS d - 2)) = (min 1 ‖x - y‖) ^ (2 - criticalS d) := by
      congr 1; ring
    rw [e3] at h0
    unfold HRS.MS.Phase2S82.smallRadius
    have hnn : 0 ≤ ((CR + C4) * A) * HRS.MS.Phase2S82.pairWeight M x y *
        (1 + (min 1 ‖x - y‖) ^ (2 - criticalS d) + if d = 4 then |Real.log (min 1 ‖x - y‖)| else 0) := by
      refine mul_nonneg (mul_nonneg hCRW hw0) ?_
      have h1 : 0 ≤ (min 1 ‖x - y‖) ^ (2 - criticalS d) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
      have h2 : 0 ≤ (if d = 4 then |Real.log (min 1 ‖x - y‖)| else (0 : ℝ)) := by split_ifs <;> positivity
      linarith
    refine h0.trans ?_
    nlinarith
  · refine hgrad.trans ?_
    unfold HRS.MS.Phase2S82.smallRadius
    have h1 : 0 ≤ (min 1 ‖x - y‖) ^ (1 - criticalS d) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
    have hP : 0 ≤ HRS.MS.Phase2S82.pairWeight M x y * (1 + (min 1 ‖x - y‖) ^ (1 - criticalS d)) :=
      mul_nonneg hw0 (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hCR0 hA) hP, mul_nonneg (mul_nonneg hC40 hA) hP, mul_nonneg hA hP]
  · refine hhess.trans ?_
    unfold HRS.MS.Phase2S82.pole HRS.MS.Phase2S82.smallRadius
    have h1 : 0 ≤ (min 1 ‖x - y‖) ^ (-criticalS d) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
    have hP : 0 ≤ HRS.MS.Phase2S82.pairWeight M x y * (1 + (min 1 ‖x - y‖) ^ (-criticalS d)) :=
      mul_nonneg hw0 (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hCR0 hA) hP, mul_nonneg (mul_nonneg hC40 hA) hP, mul_nonneg hA hP]

end HRS.MS.R26T8A
