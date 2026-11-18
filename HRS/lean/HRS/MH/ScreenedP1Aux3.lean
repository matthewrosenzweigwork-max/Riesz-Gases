import HRS.MH.ScreenedP1Aux2
import HRS.MH.ScreenedA1
import HRS.MH.ScreenedA7
import HRS.MH.ScreenedK4
import HRS.MH.ScreenedK5
import HRS.MH.ScreenedL1Aux1

/-!
# Packet P1 (`screened_pairing_lt`): kernel splitting and the core `L²` estimate.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- Dominating function of the near part `|z| ≤ 1` of `|∂_i g|` (uniform in `i`). -/
def p1_D0 (d : ℕ) (s : ℝ) (z : Euc d) : ℝ≥0∞ :=
  (Metric.closedBall (0 : Euc d) 1).indicator
    (fun z => ENNReal.ofReal (max 1 s) * ENNReal.ofReal (‖z‖ ^ (-(s + 1)))) z

/-- Dominating function of the far part `|z| > 1` of `|∂_i g|` (uniform in `i`). -/
def p1_Dinf (d : ℕ) (s : ℝ) (z : Euc d) : ℝ≥0∞ :=
  (Metric.closedBall (0 : Euc d) 1)ᶜ.indicator
    (fun z => ENNReal.ofReal (max 1 s) * ENNReal.ofReal (‖z‖ ^ (-(s + 1)))) z

/-- The weight `⟨x⟩^{-(d+3)}` (as a nonnegative extended real). -/
def p1_G (d : ℕ) (x : Euc d) : ℝ≥0∞ := ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3)))

/-- The constant of the core estimate. -/
def p1_Q (d : ℕ) (s : ℝ) : ℝ≥0∞ :=
  2 * (∫⁻ z, p1_D0 d s z) ^ 2 + 2 * ((∫⁻ x, p1_G d x ^ 2) * ∫⁻ z, p1_Dinf d s z ^ 2)

/-- The near-part integral `Y_x = ∫ D0(x-y) |v(y)| dy`. -/
def p1_A (d : ℕ) (s : ℝ) (v : Euc d → ℝ) (x : Euc d) : ℝ≥0∞ :=
  ∫⁻ y, p1_D0 d s (x - y) * ‖v y‖ₑ

/-- The far-part integral `∫ D∞(x-y) |v(y)| dy`. -/
def p1_B (d : ℕ) (s : ℝ) (v : Euc d → ℝ) (x : Euc d) : ℝ≥0∞ :=
  ∫⁻ y, p1_Dinf d s (x - y) * ‖v y‖ₑ

lemma p1_D0_measurable (s : ℝ) : Measurable (p1_D0 d s) := by
  unfold p1_D0
  apply Measurable.indicator _ (Metric.isClosed_closedBall.measurableSet)
  fun_prop

lemma p1_Dinf_measurable (s : ℝ) : Measurable (p1_Dinf d s) := by
  unfold p1_Dinf
  apply Measurable.indicator _ (Metric.isClosed_closedBall.measurableSet.compl)
  fun_prop

lemma p1_G_measurable : Measurable (p1_G d) := by
  unfold p1_G
  have hjb : Measurable (fun x : Euc d => jbracket x) := by
    unfold jbracket
    fun_prop
  exact (hjb.pow_const _).ennreal_ofReal

lemma p1_G_le_one (x : Euc d) : p1_G d x ≤ 1 := by
  unfold p1_G
  exact ENNReal.ofReal_le_one.2
    (Real.rpow_le_one_of_one_le_of_nonpos (p1_one_le_jbracket x) (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith))

/-- Pointwise kernel domination: `|∂_i g(z)| ≤ D0(z) + D∞(z)` for `z ≠ 0`. -/
lemma p1_kernel_le {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    ‖rieszKernelGrad d s z i‖ₑ ≤ p1_D0 d s z + p1_Dinf d s z := by
  have hb : ‖rieszKernelGrad d s z‖ ≤ max 1 s * ‖z‖ ^ (-s - 1) := kernel_bound_proof hs0 z hz
  have hb' : ‖rieszKernelGrad d s z i‖ ≤ max 1 s * ‖z‖ ^ (-(s + 1)) := by
    have e : (-s - 1) = -(s + 1) := by ring
    rw [e] at hb
    exact le_trans (k4_comp_norm_le s z i) hb
  have hm0 : 0 ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have hK : ‖rieszKernelGrad d s z i‖ₑ ≤ ENNReal.ofReal (max 1 s) * ENNReal.ofReal (‖z‖ ^ (-(s + 1))) := by
    rw [← ENNReal.ofReal_mul hm0, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal hb'
  by_cases hzb : z ∈ Metric.closedBall (0 : Euc d) 1
  · refine le_trans hK (le_trans (le_of_eq ?_) le_self_add)
    unfold p1_D0
    rw [Set.indicator_of_mem hzb]
  · refine le_trans hK (le_trans (le_of_eq ?_) le_add_self)
    unfold p1_Dinf
    rw [Set.indicator_of_mem (show z ∈ (Metric.closedBall (0 : Euc d) 1)ᶜ from hzb)]

lemma p1_D0_lintegral_lt_top {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 1) :
    ∫⁻ z, p1_D0 d s z < ⊤ := by
  obtain ⟨CK, hCK0, hCK⟩ := lintegral_ball_rpow_le_proof (t := s + 1) hd (by linarith)
  have h1 : ∫⁻ z, p1_D0 d s z = ENNReal.ofReal (max 1 s) *
      ∫⁻ z in Metric.closedBall (0 : Euc d) 1, ENNReal.ofReal (‖z‖ ^ (-(s + 1))) := by
    unfold p1_D0
    rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [h1]
  have h2 := hCK 1 one_pos
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_of_le_of_lt (by simpa using h2) ENNReal.ofReal_lt_top)

lemma p1_Dinf_sq_lintegral_lt_top {s : ℝ} (hs0 : 0 ≤ s) (h2 : (d : ℝ) < 2 * (s + 1)) :
    ∫⁻ z, p1_Dinf d s z ^ 2 < ⊤ := by
  have hm0 : 0 ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have hpt : ∀ z : Euc d, p1_Dinf d s z ^ 2 ≤ ENNReal.ofReal (max 1 s) ^ 2 *
      (Metric.closedBall (0 : Euc d) 1)ᶜ.indicator
        (fun z => ENNReal.ofReal (‖z‖ ^ (-(2 * (s + 1))))) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : Euc d) 1
    · have : p1_Dinf d s z = 0 := by
        unfold p1_Dinf
        rw [Set.indicator_of_notMem (show z ∉ (Metric.closedBall (0 : Euc d) 1)ᶜ from fun h => h hz)]
      rw [this]
      simp
    · have hzc : z ∈ (Metric.closedBall (0 : Euc d) 1)ᶜ := hz
      unfold p1_Dinf
      rw [Set.indicator_of_mem hzc, Set.indicator_of_mem hzc]
      have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      have hsq : (‖z‖ ^ (-(s + 1))) ^ 2 = ‖z‖ ^ (-(2 * (s + 1))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz0]
        congr 1
        push_cast
        ring
      rw [mul_pow, ← ENNReal.ofReal_pow hm0, ← ENNReal.ofReal_pow (Real.rpow_nonneg hz0 _), hsq]
  calc ∫⁻ z, p1_Dinf d s z ^ 2
      ≤ ∫⁻ z, ENNReal.ofReal (max 1 s) ^ 2 *
          (Metric.closedBall (0 : Euc d) 1)ᶜ.indicator
            (fun z => ENNReal.ofReal (‖z‖ ^ (-(2 * (s + 1))))) z := lintegral_mono hpt
    _ = ENNReal.ofReal (max 1 s) ^ 2 *
          ∫⁻ z in (Metric.closedBall (0 : Euc d) 1)ᶜ, ENNReal.ofReal (‖z‖ ^ (-(2 * (s + 1)))) := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
          lintegral_indicator Metric.isClosed_closedBall.measurableSet.compl]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
        (p1_tail_lintegral_lt_top h2)

lemma p1_G_sq_lintegral_lt_top : ∫⁻ x, p1_G d x ^ 2 < ⊤ := by
  have hG2 : ∀ x : Euc d, p1_G d x ^ 2 = ENNReal.ofReal (jbracket x ^ (-(2 * ((d : ℝ) + 3)))) := by
    intro x
    unfold p1_G
    have hx : (0 : ℝ) ≤ jbracket x ^ (-((d : ℝ) + 3)) :=
      Real.rpow_nonneg (le_trans zero_le_one (p1_one_le_jbracket x)) _
    rw [← ENNReal.ofReal_pow hx, ← Real.rpow_natCast, ← Real.rpow_mul
      (le_trans zero_le_one (p1_one_le_jbracket x))]
    congr 1
    push_cast
    ring_nf
  simp_rw [hG2]
  apply p1_jb_rpow_lintegral_lt_top
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

end HRS.MH.Screened
