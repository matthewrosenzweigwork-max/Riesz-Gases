import HRS.MS.R26T8AW5
import HRS.MS.R26T8AZ5a1

/-!
# S8.2 T8A P29n: pointwise bound of `pairJ` for any pair kernel of class `Conormal 2 1 M (s-2)` (the `nonlocal` field of `PairCorrector`)
`r26t8a_P29_pairJ_bound`: `|pairJ G x y| ≤ C A pairWeight (M+2) x y (1 + smallRadius x y ^ (-s))`, `x ≠ y`.
Same proof as `r26t8a_newton_nonlocal_bound_same` (W2) but for an arbitrary kernel `G`: the two projected rows are `Conormal 0 2 (M+2) 0` (W1) and
the logarithmic factor is absorbed by the pole `r^(-s)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 3200000 in
theorem r26t8a_P29_pairJ_conormal (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ (G : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal 2 1 M (criticalS d - 2) A G →
      Conormal 0 2 (M + 2) 0 (C * A)
        (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_p11_Px_same d hd 0 0 a beta M (criticalS d) ha hbeta hM hsd hchi
  refine ⟨2 * C2, by positivity, fun rho hrho G A hA hG => ?_⟩
  have hA1 : 0 ≤ A := hA
  have P1 := hC2 rho hrho G A hA hG
  have hGs := r26t8a_f24_conormal_swap hchi hG
  have P2 := hC2 rho hrho (fun x y => G y x) A hA hGs
  have P2s := r26t8a_f24_conormal_swap hchi P2
  have hsum := r26t8a_conormal_add hchi P1 P2s
  have e0 : criticalS d - criticalS d = 0 := sub_self _
  rw [e0] at hsum
  refine r26t8a_conormal_congr (fun x y _ => ?_)
    (r26t8a_conormal_mono_sA (A' := (2 * C2) * A) (by positivity) (le_of_eq (by ring)) le_rfl hsum)
  simp only [pairJ, HRS.Whole.projMean, HRS.Whole.pair]

theorem r26t8a_P29_pairJ_bound (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ (G : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal 2 1 M (criticalS d - 2) A G →
      ∀ x y : Euc d, x ≠ y →
        |pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G x y| ≤
          C * A * HRS.MS.Phase2S82.pairWeight (M + 2) x y *
            (1 + HRS.MS.Phase2S82.smallRadius x y ^ (-criticalS d)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_P29_pairJ_conormal d hd a beta M ha hbeta hM chi hchi
  obtain ⟨c, hc0, hc⟩ := r26t8a_Z5a1_log_bound (a := criticalS d) hs0 2
  refine ⟨C1 * (1 + c), by positivity, fun rho hrho G A hA hG x y hxy => ?_⟩
  have hJ := hC1 rho hrho G A hA hG
  set X : Euc d := (1 / 2 : ℝ) • (x + y) with hX
  set z : Euc d := x - y with hz
  have hz0 : z ≠ 0 := sub_ne_zero.2 hxy
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have e1 : X + (1 / 2 : ℝ) • z = x := by rw [hX, hz]; module
  have e2 : X - (1 / 2 : ℝ) • z = y := by rw [hX, hz]; module
  have hb := hJ.2 0 0 (by norm_num) X z hz0
  have e0 : ‖mixedJet 0 0 (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G) X z‖ =
      |pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G x y| := by
    unfold mixedJet
    simp only [norm_iteratedFDeriv_zero, midPair, e1, e2, Real.norm_eq_abs]
  rw [e0, e1, e2] at hb
  set r : ℝ := min 1 ‖z‖ with hr
  have hr0 : 0 < r := lt_min one_pos hzn
  have hr1 : r ≤ 1 := min_le_left _ _
  have hw0 : 0 ≤ HRS.MS.Phase2S82.pairWeight (M + 2) x y := r26t8a_pairWeight_nonneg (d := d) (M + 2) x y
  have hlog : (1 + |Real.log r|) ^ 2 ≤ c * r ^ (-criticalS d) := by
    have h := hc r hr0 hr1
    have : (1 + |Real.log r|) ^ 2 = r ^ (-criticalS d) * (r ^ criticalS d * (1 + |Real.log r|) ^ 2) := by
      rw [← mul_assoc, ← Real.rpow_add hr0]; simp
    rw [this, mul_comm c]
    exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hr0.le _)
  have hrp : 0 ≤ r ^ (-criticalS d) := Real.rpow_nonneg hr0.le _
  have hfac : 1 + r ^ (-((0 : ℝ) + ((0 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ 2 ≤ (1 + c) * (1 + r ^ (-criticalS d)) := by
    have : r ^ (-((0 : ℝ) + ((0 : ℕ) : ℝ))) = 1 := by simp
    rw [this, one_mul]
    nlinarith [mul_nonneg hc0 hrp]
  have hAw : 0 ≤ C1 * A * HRS.MS.Phase2S82.pairWeight (M + 2) x y := mul_nonneg (mul_nonneg hC10 hA) hw0
  calc |pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G x y|
      ≤ C1 * A * HRS.MS.Phase2S82.pairWeight (M + 2) x y *
        (1 + r ^ (-((0 : ℝ) + ((0 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ 2) := hb
    _ ≤ C1 * A * HRS.MS.Phase2S82.pairWeight (M + 2) x y * ((1 + c) * (1 + r ^ (-criticalS d))) :=
        mul_le_mul_of_nonneg_left hfac hAw
    _ = _ := by unfold HRS.MS.Phase2S82.smallRadius; ring

end HRS.MS.R26T8A
