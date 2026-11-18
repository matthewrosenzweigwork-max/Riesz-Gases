import HRS.MH.ScreenedK3
import HRS.MH.ScreenedA7

/-! Helpers for packet K4 (`gk_rep_L1`) of `B:lem:screened` (S.B.4): the gradient kernel `∂_i g`
is integrable against a Schwartz function, uniformly in the translation `y`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma k4_comp_measurable (s : ℝ) (i : Fin d) :
    Measurable (fun u : Euc d => rieszKernelGrad d s u i) :=
  (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable.comp (movtr_rieszKernelGrad_measurable (d := d) s)

lemma k4_comp_norm_le (s : ℝ) (u : Euc d) (i : Fin d) :
    ‖rieszKernelGrad d s u i‖ ≤ ‖rieszKernelGrad d s u‖ :=
  PiLp.norm_apply_le (rieszKernelGrad d s u) i

/-- The ball part of the kernel bound: `∫⁻ H(x - y) dx ≤ C_K` uniformly in `y`, where
`H(u) = 1_{|u| ≤ 1} |u|^{-(s+1)}`. -/
lemma k4_ball_indicator_lintegral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ y : Euc d,
      ∫⁻ x, (Metric.closedBall (0 : Euc d) 1).indicator
        (fun u : Euc d => ENNReal.ofReal (‖u‖ ^ (-(s + 1)))) (x - y) ≤ ENNReal.ofReal CK := by
  obtain ⟨CK, hCK0, h⟩ := lintegral_ball_rpow_le_proof (d := d) hd (t := s + 1) (by linarith)
  refine ⟨CK, hCK0, fun y => ?_⟩
  rw [lintegral_sub_right_eq_self (fun u : Euc d =>
    (Metric.closedBall (0 : Euc d) 1).indicator
      (fun u : Euc d => ENNReal.ofReal (‖u‖ ^ (-(s + 1)))) u) y]
  rw [lintegral_indicator measurableSet_closedBall]
  simpa using h 1 one_pos

/-- Uniform `L¹` bound for the kernel against a bounded integrable function: for `φ` continuous,
bounded, with `‖φ‖ ∈ L¹`, the function `x ↦ ‖∇g(x-y)‖ ‖φ x‖` is integrable and its integral is bounded
independently of `y`. -/
lemma k4_kernel_L1_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (φ : Euc d → ℝ)
    (hφc : Continuous φ) (hφb : ∃ M : ℝ, ∀ x, ‖φ x‖ ≤ M) (hφi : Integrable (fun x => ‖φ x‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Euc d,
      Integrable (fun x => ‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖) ∧
      ∫ x, ‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖ ≤ C := by
  obtain ⟨M, hM⟩ := hφb
  obtain ⟨CK, hCK0, hCK⟩ := k4_ball_indicator_lintegral hd hs0 hs1
  have hAfin : ∫⁻ x, ENNReal.ofReal ‖φ x‖ ≠ ⊤ := by
    have h := (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => norm_nonneg (φ x)))).1 hφi.hasFiniteIntegral
    exact h.ne
  have hm0 : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  set E : ℝ≥0∞ := ENNReal.ofReal (max 1 s * M) * ENNReal.ofReal CK +
    ENNReal.ofReal (max 1 s) * (∫⁻ x, ENNReal.ofReal ‖φ x‖) with hE
  have hEfin : E ≠ ⊤ := by
    rw [hE]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin⟩
  set H : Euc d → ℝ≥0∞ := (Metric.closedBall (0 : Euc d) 1).indicator
      (fun u : Euc d => ENNReal.ofReal (‖u‖ ^ (-(s + 1)))) with hH
  have hHm : Measurable H :=
    Measurable.indicator (ENNReal.measurable_ofReal.comp (by fun_prop)) measurableSet_closedBall
  have hφm : Measurable (fun x => ‖φ x‖) := hφc.norm.measurable
  refine ⟨E.toReal, ENNReal.toReal_nonneg, fun y => ?_⟩
  have hKm : Measurable (fun x : Euc d => ‖rieszKernelGrad d s (x - y)‖) :=
    ((movtr_rieszKernelGrad_measurable (d := d) s).comp (measurable_id.sub measurable_const)).norm
  have hmeas : AEStronglyMeasurable (fun x => ‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖) volume :=
    (hKm.mul hφm).aestronglyMeasurable
  -- pointwise bound off the point `y`
  have hpt : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ENNReal.ofReal (‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖) ≤
        ENNReal.ofReal (max 1 s * M) * H (x - y) + ENNReal.ofReal (max 1 s) * ENNReal.ofReal ‖φ x‖ := by
    filter_upwards [k3_ae_ne hd y] with x hxy
    have hu : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hK := kernel_bound_proof hs0 (x - y) hu
    have hφx : ‖φ x‖ ≤ M := hM x
    have hφ0 : 0 ≤ ‖φ x‖ := norm_nonneg _
    by_cases hle : ‖x - y‖ ≤ 1
    · have hind : H (x - y) = ENNReal.ofReal (‖x - y‖ ^ (-(s + 1))) := by
        rw [hH]
        exact Set.indicator_of_mem (by simpa using hle) _
      rw [hind]
      have hexp : -s - 1 = -(s + 1) := by ring
      rw [hexp] at hK
      have hpos : 0 ≤ ‖x - y‖ ^ (-(s + 1)) := Real.rpow_nonneg (norm_nonneg _) _
      calc ENNReal.ofReal (‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖)
          ≤ ENNReal.ofReal (max 1 s * M * ‖x - y‖ ^ (-(s + 1))) := by
            apply ENNReal.ofReal_le_ofReal
            have h1 : ‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖ ≤
                (max 1 s * ‖x - y‖ ^ (-(s + 1))) * M :=
              mul_le_mul hK hφx hφ0 (by positivity)
            linarith [h1]
        _ = ENNReal.ofReal (max 1 s * M) * ENNReal.ofReal (‖x - y‖ ^ (-(s + 1))) := by
            rw [ENNReal.ofReal_mul (mul_nonneg hm0 (le_trans (norm_nonneg _) (hM x)))]
        _ ≤ _ := le_self_add
    · have hind : H (x - y) = 0 := by
        rw [hH]
        exact Set.indicator_of_notMem (by simpa using hle) _
      rw [hind, mul_zero, zero_add]
      have hge : 1 ≤ ‖x - y‖ := le_of_lt (lt_of_not_ge hle)
      have hpow : ‖x - y‖ ^ (-(s + 1)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hge (by linarith)
      have hK1 : ‖rieszKernelGrad d s (x - y)‖ ≤ max 1 s := by
        calc ‖rieszKernelGrad d s (x - y)‖ ≤ max 1 s * ‖x - y‖ ^ (-s - 1) := hK
          _ ≤ max 1 s * 1 := by
            apply mul_le_mul_of_nonneg_left _ hm0
            have hexp : -s - 1 = -(s + 1) := by ring
            rw [hexp]; exact hpow
          _ = max 1 s := mul_one _
      calc ENNReal.ofReal (‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖)
          ≤ ENNReal.ofReal (max 1 s * ‖φ x‖) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK1 hφ0)
        _ = ENNReal.ofReal (max 1 s) * ENNReal.ofReal ‖φ x‖ := ENNReal.ofReal_mul hm0
  -- lintegral bound
  have hlint : ∫⁻ x, ENNReal.ofReal (‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖) ≤ E := by
    calc ∫⁻ x, ENNReal.ofReal (‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖)
        ≤ ∫⁻ x, (ENNReal.ofReal (max 1 s * M) * H (x - y) + ENNReal.ofReal (max 1 s) * ENNReal.ofReal ‖φ x‖) :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal (max 1 s * M) * (∫⁻ x, H (x - y)) +
            ENNReal.ofReal (max 1 s) * (∫⁻ x, ENNReal.ofReal ‖φ x‖) := by
          have hm1 : Measurable (fun x => ENNReal.ofReal (max 1 s * M) * H (x - y)) :=
            (hHm.comp (measurable_sub_const y)).const_mul _
          rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ E := by
          have h1 : ENNReal.ofReal (max 1 s * M) * (∫⁻ x, H (x - y)) ≤
              ENNReal.ofReal (max 1 s * M) * ENNReal.ofReal CK :=
            mul_le_mul_of_nonneg_left (hCK y) (by positivity)
          exact add_le_add h1 le_rfl
  have hnn : ∀ x, 0 ≤ ‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖ := fun x => by positivity
  have hint : Integrable (fun x => ‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖) volume :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).2
      (lt_top_iff_ne_top.2 (ne_top_of_le_ne_top hEfin hlint))⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeas]
  exact ENNReal.toReal_mono hEfin hlint

end HRS.MH.Screened
