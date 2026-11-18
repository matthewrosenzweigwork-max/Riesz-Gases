import HRS.MS.CritWholeTTDefs
import HRS.MS.CritWholeCap

/-!
# S8.1 XS, TT01: truncation rows for bounded probability densities at `s = d/2`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81b

variable {d : ℕ}

theorem s81b_critical_truncation_rows (hd : 2 ≤ d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ H : ℝ, 2 ≤ H → ∀ x : Euc d,
        Integrable (fun y => tailG d H (x - y)) (withDensityReal ρ) ∧
        Integrable (fun y => truncKernel d ((d : ℝ) / 2) H (x - y) ^ 2)
          (withDensityReal ρ) ∧
        (∫ y, tailG d H (x - y) ∂(withDensityReal ρ)) ≤ C / H ∧
        (∫ y, truncKernel d ((d : ℝ) / 2) H (x - y) ^ 2 ∂(withDensityReal ρ))
          ≤ C * Real.log H := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hA := Q34.sphereArea_nonneg hd1
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by positivity
  have hkern : ∀ z : Euc d, rieszKernel d ((d : ℝ) / 2) z = ‖z‖ ^ (-((d : ℝ) / 2)) :=
    Q34.rieszKernel_eq hs0
  have hMeas : Measurable (rieszKernel d ((d : ℝ) / 2)) := Q34.measurable_rieszKernel hs0
  refine ⟨4 * (max M 0 * sphereArea d / d) + 2 + 2 * (max M 0 * sphereArea d / ((d : ℝ) / 2)),
    by positivity, fun ρ hρ hbound H hH x => ?_⟩
  have hprob := Q34.isProbabilityMeasure_nu hρ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hbound 0)
  rw [max_eq_left hM0]
  have hH0 : 0 < H := by linarith
  have hk0 : ∀ z : Euc d, 0 ≤ rieszKernel d ((d : ℝ) / 2) z := fun z => by
    rw [hkern]; exact Real.rpow_nonneg (norm_nonneg _) _
  have hTm : Measurable (truncKernel d ((d : ℝ) / 2) H) := hMeas.min measurable_const
  have hT0 : ∀ z : Euc d, 0 ≤ truncKernel d ((d : ℝ) / 2) H z := fun z => le_min (hk0 z) hH0.le
  have hlogH : (1 : ℝ) / 2 ≤ Real.log H := by
    have := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) hH
    linarith
  -- tail
  have hsd : ((d : ℝ) / 2) < d := by linarith
  have htail : ∫⁻ z, ENNReal.ofReal (tailG d H (x - z)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (M * sphereArea d / ((d : ℝ) - (d : ℝ) / 2) * H ^ (1 - (d : ℝ) / ((d : ℝ) / 2))) := by
    have := Q34.trunc_diff_le hd1 (s := (d : ℝ) / 2) (by positivity) hsd hρ hbound (by linarith : 1 ≤ H) x
    refine le_trans (le_of_eq ?_) this
    refine lintegral_congr fun z => ?_
    simp only [tailG, truncKernel, hkern]
  have e1 : (d : ℝ) - (d : ℝ) / 2 = (d : ℝ) / 2 := by ring
  have e2 : 1 - (d : ℝ) / ((d : ℝ) / 2) = -1 := by field_simp; ring
  rw [e1, e2, Real.rpow_neg_one] at htail
  have htailm : Measurable (fun y => tailG d H (x - y)) :=
    (hMeas.sub hTm).comp (measurable_const.sub measurable_id)
  have htail0 : ∀ y, 0 ≤ tailG d H (x - y) := fun y => by
    simp only [tailG, truncKernel]
    linarith [min_le_left (rieszKernel d ((d : ℝ) / 2) (x - y)) H]
  have hc1 : 0 ≤ M * sphereArea d / ((d : ℝ) / 2) * H⁻¹ := by positivity
  obtain ⟨hI1, hV1⟩ := Q34.integrable_of_lintegral_le htailm htail0 hc1 htail
  -- squares
  set U : Euc d → ℝ := fun z => truncKernel d ((d : ℝ) / 2) H z ^ 2 with hU
  have hUmeas : Measurable U := hTm.pow_const 2
  have hU0 : ∀ z, 0 ≤ U z := fun z => sq_nonneg _
  have hUH : ∀ z, U z ≤ H ^ 2 := fun z =>
    pow_le_pow_left₀ (hT0 z) (min_le_right _ _) 2
  set R : ℝ := H ^ (-(2 : ℝ) / d) with hRdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos hH0 _
  have hR1 : R ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by
      have : 0 ≤ (2 : ℝ) / d := by positivity
      have e : -(2 : ℝ) / d = -((2 : ℝ) / d) := by ring
      linarith)
  have hRd : R ^ d * H ^ 2 = 1 := by
    have h1 : R ^ d = H ^ (-(2 : ℝ)) := by
      rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]
      congr 1
      field_simp
    rw [h1, show H ^ 2 = H ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hH0]
    simp
  have hRs : R ^ (-((d : ℝ) / 2)) = H := by
    rw [hRdef, ← Real.rpow_mul hH0.le]
    have : -(2 : ℝ) / d * -((d : ℝ) / 2) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hlogR : Real.log (1 / R) = (2 / (d : ℝ)) * Real.log H := by
    rw [one_div, Real.log_inv, hRdef, Real.log_rpow hH0]
    ring
  set S : Set (Euc d) := {z | ‖z‖ ∈ Set.Ico R 1} with hS
  have hSm : MeasurableSet S := measurable_norm measurableSet_Ico
  set B3 : Set (Euc d) := {z | 1 ≤ ‖z‖} with hB3
  have hU_S : ∀ z ∈ S, U z = ‖z‖ ^ (-(d : ℝ)) := by
    intro z hz
    have hz' : R ≤ ‖z‖ ∧ ‖z‖ < 1 := hz
    have hzpos : 0 < ‖z‖ := hRpos.trans_le hz'.1
    have hle : ‖z‖ ^ (-((d : ℝ) / 2)) ≤ H := by
      rw [← hRs]
      exact Real.rpow_le_rpow_of_nonpos hRpos hz'.1 (by linarith)
    simp only [hU, truncKernel, hkern, min_eq_left hle]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
    congr 1
    push_cast
    ring
  have hU_B3 : ∀ z ∈ B3, U z ≤ 1 := by
    intro z hz
    have hz' : 1 ≤ ‖z‖ := hz
    have hle : ‖z‖ ^ (-((d : ℝ) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hz' (by linarith)
    have h1 : truncKernel d ((d : ℝ) / 2) H z ≤ 1 := by
      simp only [truncKernel, hkern]
      exact (min_le_left _ _).trans hle
    calc U z = truncKernel d ((d : ℝ) / 2) H z ^ 2 := rfl
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (hT0 z) h1 2
      _ = 1 := one_pow 2
  set e : Euc d → ℝ≥0∞ := fun z =>
    (Metric.ball (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal (H ^ 2)) z +
    S.indicator (fun z => ENNReal.ofReal (‖z‖ ^ (-(d : ℝ)))) z with he
  have hem : Measurable e :=
    (measurable_const.indicator Metric.isOpen_ball.measurableSet).add
      ((ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)).indicator hSm)
  have hpt : ∀ z, ENNReal.ofReal (U z) ≤ e z + B3.indicator (fun _ => (1 : ℝ≥0∞)) z := by
    intro z
    by_cases hz1 : ‖z‖ < R
    · have hzB : z ∈ Metric.ball (0 : Euc d) R := by simpa using hz1
      calc ENNReal.ofReal (U z) ≤ ENNReal.ofReal (H ^ 2) := ENNReal.ofReal_le_ofReal (hUH z)
        _ = (Metric.ball (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal (H ^ 2)) z := by
            rw [Set.indicator_of_mem hzB]
        _ ≤ _ := le_trans (le_add_right le_rfl) (le_add_right le_rfl)
    · replace hz1 := not_lt.1 hz1
      by_cases hz2 : ‖z‖ < 1
      · have hzS : z ∈ S := ⟨hz1, hz2⟩
        calc ENNReal.ofReal (U z) = S.indicator (fun z => ENNReal.ofReal (‖z‖ ^ (-(d : ℝ)))) z := by
              rw [Set.indicator_of_mem hzS, hU_S z hzS]
          _ ≤ _ := le_trans (le_add_left le_rfl) (le_add_right le_rfl)
      · replace hz2 := not_lt.1 hz2
        have hzB : z ∈ B3 := hz2
        calc ENNReal.ofReal (U z) ≤ 1 := by
              rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hU_B3 z hzB)
          _ = B3.indicator (fun _ => (1 : ℝ≥0∞)) z := by rw [Set.indicator_of_mem hzB]
          _ ≤ _ := le_add_self
  have hlogR0 : 0 ≤ Real.log (1 / R) := Real.log_nonneg (by rw [le_div_iff₀ hRpos]; linarith)
  have hint_e : ∫⁻ z, e z = ENNReal.ofReal (sphereArea d / d + sphereArea d * (2 / (d : ℝ) * Real.log H)) := by
    have ma : Measurable ((Metric.ball (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal (H ^ 2))) :=
      measurable_const.indicator Metric.isOpen_ball.measurableSet
    have hsum : ∫⁻ z, e z = (∫⁻ z, (Metric.ball (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal (H ^ 2)) z) +
        ∫⁻ z, S.indicator (fun z : Euc d => ENNReal.ofReal (‖z‖ ^ (-(d : ℝ)))) z :=
      lintegral_add_left ma _
    rw [hsum, lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const,
      Q34.volume_ball_eq hd1 hRpos, lintegral_indicator hSm,
      BreakdownS81.s81bd_lintegral_shell_inv hd1 hRpos hR1, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), hlogR]
    congr 1
    have : R ^ d = (H ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hRd
    rw [this]
    field_simp
  have hlogpos : 0 ≤ Real.log H := by linarith
  have hsq : ∫⁻ z, ENNReal.ofReal (U (x - z)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (M * (sphereArea d / d + sphereArea d * (2 / (d : ℝ) * Real.log H)) + 1) := by
    calc ∫⁻ z, ENNReal.ofReal (U (x - z)) ∂(withDensityReal ρ)
        ≤ ∫⁻ z, (e (x - z) + B3.indicator (fun _ => (1 : ℝ≥0∞)) (x - z)) ∂(withDensityReal ρ) :=
          lintegral_mono fun z => hpt (x - z)
      _ = (∫⁻ z, e (x - z) ∂(withDensityReal ρ)) +
            ∫⁻ z, B3.indicator (fun _ => (1 : ℝ≥0∞)) (x - z) ∂(withDensityReal ρ) :=
          lintegral_add_left (hem.comp (measurable_const.sub measurable_id)) _
      _ ≤ ENNReal.ofReal M * (∫⁻ w, e w) + 1 := by
          refine add_le_add (Q34.lintegral_conv_le hρ hbound e hem x) ?_
          calc ∫⁻ z, B3.indicator (fun _ => (1 : ℝ≥0∞)) (x - z) ∂(withDensityReal ρ)
              ≤ ∫⁻ z, 1 ∂(withDensityReal ρ) :=
                lintegral_mono fun z => Set.indicator_le_self' (fun _ _ => bot_le) _
            _ = 1 := by simp
      _ = _ := by
          have hlog : 0 ≤ sphereArea d / d + sphereArea d * (2 / (d : ℝ) * Real.log H) := by
            positivity
          rw [hint_e, ← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add (mul_nonneg hM0 hlog) zero_le_one]
  have hc2 : 0 ≤ M * (sphereArea d / d + sphereArea d * (2 / (d : ℝ) * Real.log H)) + 1 := by
    positivity
  obtain ⟨hI2, hV2⟩ := Q34.integrable_of_lintegral_le (μ := withDensityReal ρ)
    (f := fun y => U (x - y)) (hUmeas.comp (measurable_const.sub measurable_id))
    (fun y => hU0 _) hc2 hsq
  refine ⟨hI1, hI2, ?_, ?_⟩
  · refine hV1.trans ?_
    have hK : 0 ≤ M * sphereArea d / ((d : ℝ) / 2) := by positivity
    have ha : 0 ≤ M * sphereArea d / d := by positivity
    calc M * sphereArea d / ((d : ℝ) / 2) * H⁻¹ = (M * sphereArea d / ((d : ℝ) / 2)) / H :=
          (div_eq_mul_inv _ _).symm
      _ ≤ _ := by gcongr; linarith
  · refine hV2.trans ?_
    have ha : 0 ≤ M * sphereArea d / d := by positivity
    have hb : 0 ≤ M * sphereArea d / ((d : ℝ) / 2) := by positivity
    have e3 : M * (sphereArea d / d + sphereArea d * (2 / (d : ℝ) * Real.log H)) =
        M * sphereArea d / d + 2 * (M * sphereArea d / d) * Real.log H := by ring
    rw [e3]
    nlinarith [mul_nonneg ha (by linarith : 0 ≤ 2 * Real.log H - 1), mul_nonneg hb hlogpos]

end HRS.Whole.S81b
