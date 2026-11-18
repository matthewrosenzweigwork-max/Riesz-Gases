import HRS.Whole.Basic

/-!
# S8P: Schur-type bound for the Riesz kernel against a bounded probability density (S8.7, packet E0)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For `0 < s < d`, `0 ≤ ρ ≤ M` integrable with `∫ ρ = 1`:
`sup_x ∫ g(x-y) ρ(y) dy ≤ C := M ∫_{B_1} g + 1` (`s8p_schur_sup`), and the kernel `g(x-y) √ρ(x) √ρ(y)` is bounded on `L²`
in the sense `∬ g(x-y) √ρ(x) √ρ(y) |v(x)| |w(y)| ≤ (C/2)(‖v‖² + ‖w‖²)` (`s8p_schur_double`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ}

theorem s8p_riesz_meas (s : ℝ) : Measurable (rieszKernel d s) := by
  unfold rieszKernel
  split_ifs
  · exact (Real.measurable_log.comp measurable_norm).neg
  · exact (measurable_norm.pow_const _ : Measurable fun x : Euc d => ‖x‖ ^ (-s))

/-- The (finite) mass of the Riesz kernel on the unit ball. -/
def s8p_Iball (d : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in ball (0 : Euc d) 1, ENNReal.ofReal (rieszKernel d s z)

theorem s8p_Iball_lt_top {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) : s8p_Iball d s < ⊤ := by
  have h := (rieszKernel_locallyIntegrable (d := d) hs0 hsd).integrableOn_isCompact
    (isCompact_closedBall (0 : Euc d) 1)
  have h1 : ∫⁻ z in closedBall (0 : Euc d) 1, ‖rieszKernel d s z‖ₑ < ⊤ := h.2
  refine lt_of_le_of_lt ?_ h1
  refine (lintegral_mono_set ball_subset_closedBall).trans ?_
  exact lintegral_mono fun z => Real.ofReal_le_enorm _

theorem s8p_riesz_le_one {s : ℝ} (hs0 : 0 < s) {z : Euc d} (hz : 1 ≤ ‖z‖) : rieszKernel d s z ≤ 1 := by
  unfold rieszKernel
  rw [if_neg hs0.ne']
  exact Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)

theorem s8p_riesz_nonneg {s : ℝ} (hs0 : 0 < s) (z : Euc d) : 0 ≤ rieszKernel d s z := by
  unfold rieszKernel
  rw [if_neg hs0.ne']
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem s8p_schur_sup {s : ℝ} (hs0 : 0 < s) (ρ : Euc d → ℝ) (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (hint : Integrable ρ)
    (hone : ∫ x, ρ x = 1) (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) * ρ y) ≤
      ENNReal.ofReal M * s8p_Iball d s + 1 := by
  set φ : Euc d → ℝ≥0∞ := (ball (0 : Euc d) 1).indicator (fun z => ENNReal.ofReal (rieszKernel d s z))
    with hφ
  have hφm : Measurable φ :=
    (ENNReal.measurable_ofReal.comp (s8p_riesz_meas s)).indicator measurableSet_ball
  have hM0 : 0 ≤ M := le_trans (hρ0 x) (hM x)
  have hpt : ∀ y, ENNReal.ofReal (rieszKernel d s (x - y) * ρ y) ≤
      ENNReal.ofReal M * φ (x - y) + ENNReal.ofReal (ρ y) := by
    intro y
    have hg0 := s8p_riesz_nonneg hs0 (x - y)
    by_cases hy : ‖x - y‖ < 1
    · have hmem : x - y ∈ ball (0 : Euc d) 1 := by simpa using hy
      rw [hφ, Set.indicator_of_mem hmem]
      calc ENNReal.ofReal (rieszKernel d s (x - y) * ρ y)
          ≤ ENNReal.ofReal (M * rieszKernel d s (x - y)) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [hM y])
        _ = ENNReal.ofReal M * ENNReal.ofReal (rieszKernel d s (x - y)) := ENNReal.ofReal_mul hM0
        _ ≤ _ := le_self_add
    · have hmem : x - y ∉ ball (0 : Euc d) 1 := by simpa using hy
      rw [hφ, Set.indicator_of_notMem hmem, mul_zero, zero_add]
      refine ENNReal.ofReal_le_ofReal ?_
      have := s8p_riesz_le_one hs0 (z := x - y) (not_lt.1 hy)
      nlinarith [hρ0 y]
  calc ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) * ρ y)
      ≤ ∫⁻ y, (ENNReal.ofReal M * φ (x - y) + ENNReal.ofReal (ρ y)) := lintegral_mono hpt
    _ = (∫⁻ y, ENNReal.ofReal M * φ (x - y)) + ∫⁻ y, ENNReal.ofReal (ρ y) := by
        have hm2 : Measurable fun y => φ (x - y) := hφm.comp (measurable_const.sub measurable_id)
        have hm1 : Measurable fun y => ENNReal.ofReal M * φ (x - y) := measurable_const.mul hm2
        exact lintegral_add_left hm1 _
    _ = ENNReal.ofReal M * s8p_Iball d s + 1 := by
        have hm2 : Measurable fun y => φ (x - y) := hφm.comp (measurable_const.sub measurable_id)
        have h3 : ∫⁻ y : Euc d, φ (x - y) = ∫⁻ y : Euc d, φ y := lintegral_sub_left_eq_self φ x
        have h4 : ∫⁻ y : Euc d, ENNReal.ofReal M * φ (x - y) = ENNReal.ofReal M * s8p_Iball d s := by
          have := lintegral_const_mul (μ := (volume : Measure (Euc d))) (ENNReal.ofReal M) hm2
          refine this.trans ?_
          rw [h3, hφ, lintegral_indicator measurableSet_ball]
          rfl
        have h5 : ∫⁻ y : Euc d, ENNReal.ofReal (ρ y) = 1 := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ0), hone]
          simp
        rw [h4, h5]

end HRS.MS.Spec
