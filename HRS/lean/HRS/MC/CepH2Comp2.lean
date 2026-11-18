import HRS.MC.CepH2Comp1

/-!
# CEPH2, narrow convergence of the Gaussian mollification
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- Approximate identity: `∫ g_v(z) f(z + y) dz → f(y)` as `v → 0`. -/
theorem h2_mollify_tendsto {f : Ch N → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ z, |f z| ≤ C) (y : Ch N)
    {v : ℕ → ℝ} (hv : ∀ n, 0 < v n) (hv0 : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, h2_g (v n) z * f (z + y)) atTop (𝓝 (f y)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  rw [Metric.tendsto_atTop]
  intro η hη
  have hfc := hf.continuousAt (x := y)
  rw [Metric.continuousAt_iff] at hfc
  obtain ⟨δ, hδ, hδf⟩ := hfc (η / 2) (by positivity)
  set c : ℝ := 2 * C / δ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hmain : ∀ n, |(∫ z, h2_g (v n) z * f (z + y)) - f y| ≤ η / 2 + c * (N * v n) := by
    intro n
    have hvn := hv n
    have hgi := h2_integrable_g (N := N) hvn
    have hfi : Integrable (fun z : Ch N => h2_g (v n) z * f (z + y)) := by
      refine Integrable.mono' (hgi.mul_const C) ?_ (ae_of_all _ fun z => ?_)
      · exact ((h2_continuous_g _).mul (hf.comp (continuous_id.add continuous_const))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (h2_g_pos hvn z)]
        exact mul_le_mul_of_nonneg_left (hC _) (h2_g_pos hvn z).le
    have e : (∫ z, h2_g (v n) z * f (z + y)) - f y = ∫ z, h2_g (v n) z * (f (z + y) - f y) := by
      have h1 : ∫ z, h2_g (v n) z * (f (z + y) - f y) =
          (∫ z, h2_g (v n) z * f (z + y)) - ∫ z : Ch N, h2_g (v n) z * f y := by
        rw [← integral_sub hfi (hgi.mul_const _)]
        exact integral_congr_ae (ae_of_all _ fun z => by simp only [mul_sub])
      rw [h1, integral_mul_const, h2_g_integral hvn, one_mul]
    rw [e]
    have hb : ∀ z : Ch N, |f (z + y) - f y| ≤ η / 2 + c * ‖z‖ ^ 2 := by
      intro z
      by_cases hz : ‖z‖ < δ
      · have := hδf (x := z + y) (by simpa [dist_eq_norm] using hz)
        rw [Real.dist_eq] at this
        have : 0 ≤ c * ‖z‖ ^ 2 := by positivity
        linarith
      · push_neg at hz
        have h1 : |f (z + y) - f y| ≤ 2 * C := by
          calc |f (z + y) - f y| ≤ |f (z + y)| + |f y| := abs_sub _ _
            _ ≤ C + C := add_le_add (hC _) (hC _)
            _ = 2 * C := by ring
        have h2 : 2 * C ≤ c * ‖z‖ ^ 2 := by
          rw [hc, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hz 2) (by positivity)
        linarith
    have hbi : Integrable (fun z : Ch N => h2_g (v n) z * (η / 2 + c * ‖z‖ ^ 2)) := by
      have := (hgi.const_mul (η / 2)).add ((h2_integrable_sq_g hvn).const_mul c)
      refine this.congr (ae_of_all _ fun z => ?_)
      simp only [Pi.add_apply]; ring
    have hbv : ∫ z : Ch N, h2_g (v n) z * (η / 2 + c * ‖z‖ ^ 2) = η / 2 + c * (N * v n) := by
      have : ∀ z : Ch N, h2_g (v n) z * (η / 2 + c * ‖z‖ ^ 2) =
          η / 2 * h2_g (v n) z + c * (‖z‖ ^ 2 * h2_g (v n) z) := fun z => by ring
      simp_rw [this]
      rw [integral_add (hgi.const_mul _) ((h2_integrable_sq_g hvn).const_mul _), integral_const_mul,
        integral_const_mul, h2_g_integral hvn, h2_g_second hvn]
      ring
    calc |∫ z, h2_g (v n) z * (f (z + y) - f y)| ≤ ∫ z, |h2_g (v n) z * (f (z + y) - f y)| := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => h2_g (v n) z * (f (z + y) - f y))
      _ ≤ ∫ z, h2_g (v n) z * (η / 2 + c * ‖z‖ ^ 2) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) hbi (ae_of_all _ fun z => ?_)
          show |h2_g (v n) z * (f (z + y) - f y)| ≤ _
          rw [abs_mul, abs_of_pos (h2_g_pos (hv n) z)]
          exact mul_le_mul_of_nonneg_left (hb z) (h2_g_pos (hv n) z).le
      _ = η / 2 + c * (N * v n) := hbv
  have hsmall : ∀ᶠ n in atTop, c * (N * v n) < η / 2 := by
    have : Tendsto (fun n => c * (N * v n)) atTop (𝓝 (c * (N * 0))) :=
      (hv0.const_mul (N : ℝ)).const_mul c
    rw [mul_zero, mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hsmall
  refine ⟨n0, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have := hmain n
  have := hn0 n hn
  linarith

end HRS.MC.CepH2
