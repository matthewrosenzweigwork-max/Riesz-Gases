import HRS.MH.ScreenedK4
import HRS.MH.ScreenedA1
import HRS.MH.ScreenedA2
import HRS.PDE.ToolboxRd.Fourier

/-! Helpers for packet L1 (`screened_local_lt`) of `B:lem:screened` (S.B.4). -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- `(‖f‖_{L²})² = ∫⁻ ‖f‖ₑ²` for an a.e.-strongly measurable real function. -/
lemma l1_sq_eLpNorm_ae (f : Euc d → ℝ) (hf : AEStronglyMeasurable f volume) :
    (eLpNorm f 2 volume) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact a2_sq_sqrt _

/-- The representative `x ↦ ∫ ∂_i g(x-y) v(y) dy` is a.e.-strongly measurable. -/
lemma l1_w_aesm (s : ℝ) (i : Fin d) {v : Euc d → ℝ} (hv : AEStronglyMeasurable v volume) :
    AEStronglyMeasurable (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y) volume := by
  have h1 : Measurable (fun p : Euc d × Euc d => rieszKernelGrad d s (p.1 - p.2) i) :=
    (k4_comp_measurable s i).comp (measurable_fst.sub measurable_snd)
  have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => v p.2) (volume.prod volume) :=
    hv.comp_snd
  exact (h1.aestronglyMeasurable.mul h2).integral_prod_right'

/-- Truncated kernel: `∫⁻ |1_{|u| ≤ 5ρ} ∂_i g(u)| du ≤ C ρ^d` for `ρ ≥ 1`, uniformly in `i`. -/
lemma l1_kernel_trunc_lintegral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (ρ : ℝ), 1 ≤ ρ →
      ∫⁻ u, ‖(Metric.closedBall (0 : Euc d) (5 * ρ)).indicator (fun u => rieszKernelGrad d s u i) u‖ₑ ≤
        ENNReal.ofReal (C * ρ ^ (d : ℝ)) := by
  obtain ⟨CK, hCK0, hCK⟩ := lintegral_ball_rpow_le_proof (d := d) hd (t := s + 1) (by linarith)
  have hm0 : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  refine ⟨max 1 s * CK * (5 : ℝ) ^ (d : ℝ), mul_nonneg (mul_nonneg hm0 hCK0) (Real.rpow_nonneg (by norm_num) _),
    fun i ρ hρ => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  have h5 : (0 : ℝ) < 5 * ρ := by linarith
  have hpt : ∀ᵐ u ∂(volume : Measure (Euc d)),
      ‖(Metric.closedBall (0 : Euc d) (5 * ρ)).indicator (fun u => rieszKernelGrad d s u i) u‖ₑ ≤
        (Metric.closedBall (0 : Euc d) (5 * ρ)).indicator
          (fun u : Euc d => ENNReal.ofReal (max 1 s) * ENNReal.ofReal (‖u‖ ^ (-(s + 1)))) u := by
    filter_upwards [k3_ae_ne hd 0] with u hu
    by_cases hmem : u ∈ Metric.closedBall (0 : Euc d) (5 * ρ)
    · simp only [Set.indicator_of_mem hmem]
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hm0]
      apply ENNReal.ofReal_le_ofReal
      have hK := kernel_bound_proof hs0 u hu
      have hexp : -s - 1 = -(s + 1) := by ring
      rw [hexp] at hK
      exact le_trans (k4_comp_norm_le s u i) hK
    · simp [Set.indicator_of_notMem hmem]
  have hp5 : (5 * ρ) ^ (-(s + 1) : ℝ) = (5 * ρ) ^ (-(s + 1) : ℝ) := rfl
  calc ∫⁻ u, ‖(Metric.closedBall (0 : Euc d) (5 * ρ)).indicator (fun u => rieszKernelGrad d s u i) u‖ₑ
      ≤ ∫⁻ u, (Metric.closedBall (0 : Euc d) (5 * ρ)).indicator
          (fun u : Euc d => ENNReal.ofReal (max 1 s) * ENNReal.ofReal (‖u‖ ^ (-(s + 1)))) u :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (max 1 s) * ∫⁻ u in Metric.closedBall (0 : Euc d) (5 * ρ),
          ENNReal.ofReal (‖u‖ ^ (-(s + 1))) := by
        rw [lintegral_indicator measurableSet_closedBall, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (max 1 s) * ENNReal.ofReal (CK * (5 * ρ) ^ ((d : ℝ) - (s + 1))) :=
        mul_le_mul_of_nonneg_left (hCK (5 * ρ) h5) (by positivity)
    _ = ENNReal.ofReal (max 1 s * (CK * (5 * ρ) ^ ((d : ℝ) - (s + 1)))) := by
        rw [ENNReal.ofReal_mul hm0]
    _ ≤ ENNReal.ofReal (max 1 s * CK * (5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have he : (d : ℝ) - (s + 1) ≤ (d : ℝ) := by linarith
        have h5e : (5 : ℝ) ^ ((d : ℝ) - (s + 1)) ≤ (5 : ℝ) ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) he
        have hre : ρ ^ ((d : ℝ) - (s + 1)) ≤ ρ ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hρ he
        calc max 1 s * (CK * (5 * ρ) ^ ((d : ℝ) - (s + 1)))
            = (max 1 s * CK) * ((5 : ℝ) ^ ((d : ℝ) - (s + 1)) * ρ ^ ((d : ℝ) - (s + 1))) := by
              rw [Real.mul_rpow (by norm_num) hρ0.le]; ring
          _ ≤ (max 1 s * CK) * ((5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul h5e hre (by positivity) (by positivity))
                (mul_nonneg hm0 hCK0)
          _ = max 1 s * CK * (5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ) := by ring

/-- Plancherel at order zero: for `v ∈ L²`, `‖v‖_{H⁰} = ‖v‖_{L²}`. -/
lemma l1_sobolev_zero_eq {v : Euc d → ℝ} (hv : MemLp v 2 volume) :
    sobolevNormE 0 v = eLpNorm v 2 volume := by
  have hint : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (0 : ℝ) *
      ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖ ^ 2) := by
    simpa [Real.rpow_zero] using HRS.PDE.ToolboxRd.FourierAux.integrable_norm_sq_fourierL2 hv
  unfold sobolevNormE
  rw [if_pos (show HRS.PDE.ToolboxRd.MemSobolev 0 v from ⟨hv, hint⟩)]
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  simp only [Real.rpow_zero, one_mul]
  rw [HRS.PDE.ToolboxRd.FourierAux.integral_norm_sq_fourierL2 hv]
  rw [hv.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- Volume of a ball of radius `≤ ρ`: `vol(B(c, r)) ≤ ρ^d · vol(B(0,1))`. -/
lemma l1_vol_closedBall_le (c : Euc d) {r ρ : ℝ} (hr : r ≤ ρ) (hρ : 0 ≤ ρ) :
    volume (Metric.closedBall c r) ≤
      ENNReal.ofReal (ρ ^ (d : ℝ) * (volume (Metric.closedBall (0 : Euc d) 1)).toReal) := by
  calc volume (Metric.closedBall c r) ≤ volume (Metric.closedBall c ρ) :=
        measure_mono (Metric.closedBall_subset_closedBall hr)
    _ = ENNReal.ofReal (ρ ^ (Module.finrank ℝ (Euc d))) * volume (Metric.closedBall (0 : Euc d) 1) :=
        Measure.addHaar_closedBall' _ _ hρ
    _ = ENNReal.ofReal (ρ ^ (d : ℝ) * (volume (Metric.closedBall (0 : Euc d) 1)).toReal) := by
        rw [finrank_euclideanSpace_fin, ← Real.rpow_natCast, ENNReal.ofReal_mul (Real.rpow_nonneg hρ _),
          ENNReal.ofReal_toReal measure_closedBall_lt_top.ne]

/-- Cauchy-Schwarz for the `L¹` norm of a function supported in a set `B`:
`(∫⁻ ‖v‖ₑ)² ≤ |B| · ∫⁻ ‖v‖ₑ²`. -/
lemma l1_holder {v : Euc d → ℝ} (hvae : AEStronglyMeasurable v volume) {B : Set (Euc d)}
    (hB : MeasurableSet B) (hsupp : Function.support v ⊆ B) :
    (∫⁻ x, ‖v x‖ₑ) ^ 2 ≤ volume B * ∫⁻ x, ‖v x‖ₑ ^ 2 := by
  have hae := hvae.ae_eq_mk
  have hvm : Measurable (hvae.mk v) := hvae.stronglyMeasurable_mk.measurable
  have h := a2_cs volume (B.indicator 1) (fun x => ‖hvae.mk v x‖ₑ)
    (measurable_one.indicator hB) hvm.enorm
  have e1 : ∫⁻ x, B.indicator 1 x * ‖hvae.mk v x‖ₑ = ∫⁻ x, ‖v x‖ₑ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    by_cases hxB : x ∈ B
    · rw [Set.indicator_of_mem hxB, Pi.one_apply, one_mul, hx]
    · have hv0 : v x = 0 := by
        by_contra hne
        exact hxB (hsupp (Function.mem_support.2 hne))
      rw [Set.indicator_of_notMem hxB, zero_mul, hv0, enorm_zero]
  have e2 : ∫⁻ x, (B.indicator 1 x) ^ 2 = volume B := by
    rw [← lintegral_indicator_one hB]
    refine lintegral_congr fun x => ?_
    by_cases hxB : x ∈ B <;> simp [hxB]
  have e3 : ∫⁻ x, ‖hvae.mk v x‖ₑ ^ 2 = ∫⁻ x, ‖v x‖ₑ ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  simp only [e1, e2, e3] at h
  exact h

end HRS.MH.Screened
