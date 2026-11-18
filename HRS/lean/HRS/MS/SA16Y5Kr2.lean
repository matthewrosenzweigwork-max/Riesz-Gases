import HRS.MS.SA16Y5Kr1
import HRS.MS.SA16ZT3
import HRS.MS.CzPvAux1

/-!
# S.A.16 (SA16Y5) Kr2: `L^1` bounds of the near and far parts of the Riesz kernel (K1, part 2)

`ρ = |z|^{-s}` (`s > 0`), `χ_ε` the radial cutoff of `sa16z_chi`.  `rn = ρ (1 - χ_ε)` (near part, supported in `|z| ≤ √2 ε`):
`∫ |rn| ≤ Cn ε^{d-s}` (`s < d`).  `V_i = ∂_i (ρ χ_ε) = K_i χ_ε + ρ ∂_iχ_ε` (far part, `sa16z_H_fderiv`):
`∫ |V_i| ≤ Cf ε^{d-s-1}` (`s + 1 > d`).  Constants independent of `ε`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Kr2
variable {d : ℕ} {s : ℝ}

/-- the near part of the Riesz kernel -/
def sa16y5_rn (d : ℕ) (s ε : ℝ) (z : Euc d) : ℝ := rieszKernel d s z * (1 - sa16z_chi d ε z)

/-- `∂_i` of the far part `ρ χ_ε` -/
def sa16y5_V (d : ℕ) (s ε : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  sa16z_Kx s i z * sa16z_chi d ε z + rieszKernel d s z * sa16z_dchi d ε i z

lemma sa16y5_riesz_eq (hs : 0 < s) (z : Euc d) : rieszKernel d s z = ‖z‖ ^ (-s) := by
  simp [rieszKernel, hs.ne']

lemma sa16y5_rn_meas (ε : ℝ) : Measurable (sa16y5_rn d s ε) := by
  unfold sa16y5_rn rieszKernel
  have hc : Measurable (sa16z_chi d ε) := (sa16z_chi_smooth ε).continuous.measurable
  by_cases hs : s = 0
  · simp only [hs, if_true]
    exact ((measurable_norm.log).neg).mul (measurable_const.sub hc)
  · simp only [hs, if_false]
    exact (measurable_norm.pow_const _).mul (measurable_const.sub hc)

lemma sa16y5_rn_bound (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) (z : Euc d) :
    |sa16y5_rn d s ε z| ≤ if ‖z‖ ≤ Real.sqrt 2 * ε then ‖z‖ ^ (-s) else 0 := by
  unfold sa16y5_rn
  rw [sa16y5_riesz_eq hs]
  by_cases hz : ‖z‖ ≤ Real.sqrt 2 * ε
  · rw [if_pos hz, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have h1 := sa16z_chi_nonneg (d := d) ε z
    have h2 := sa16z_chi_le_one (d := d) ε z
    rw [abs_of_nonneg (by linarith)]
    calc ‖z‖ ^ (-s) * (1 - sa16z_chi d ε z) ≤ ‖z‖ ^ (-s) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := mul_one _
  · rw [if_neg hz]
    have h : 2 * ε ^ 2 ≤ ‖z‖ ^ 2 := by
      have h1 : Real.sqrt 2 * ε < ‖z‖ := not_le.1 hz
      have h2 : 0 ≤ Real.sqrt 2 * ε := by positivity
      have h3 := pow_lt_pow_left₀ h1 h2 (two_ne_zero)
      rw [mul_pow, Real.sq_sqrt (by norm_num)] at h3
      exact h3.le
    rw [sa16z_chi_one hε h]
    simp

lemma sa16y5_ite_int (hd : 1 ≤ d) (hsd : s < d) (R : ℝ) :
    Integrable (fun z : Euc d => if ‖z‖ ≤ R then ‖z‖ ^ (-s) else 0) := by
  have h := HRS.CZ.Pv.pvapi_integrableOn_ball_rpow (d := d) hd (α := s) hsd (|R| + 1)
  have h2 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (closedBall 0 R) :=
    h.mono_set (closedBall_subset_ball (by linarith [le_abs_self R]))
  have h3 := h2.integrable_indicator (measurableSet_closedBall (x := (0 : Euc d)) (ε := R))
  refine h3.congr (Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ ≤ R
  · simp [indicator, hz]
  · simp [indicator, hz]

theorem sa16y5_rn_L1 (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    Integrable (sa16y5_rn d s ε) ∧ ∫ z, |sa16y5_rn d s ε z| ≤
      ((d : ℝ) * volume.real (ball (0 : Euc d) 1) * ((Real.sqrt 2) ^ ((d : ℝ) - s) / ((d : ℝ) - s))) *
        ε ^ ((d : ℝ) - s) := by
  have hR : 0 < Real.sqrt 2 * ε := by positivity
  have hint := sa16y5_ite_int hd hsd (Real.sqrt 2 * ε)
  have hI : Integrable (sa16y5_rn d s ε) :=
    hint.mono' (sa16y5_rn_meas ε).aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact sa16y5_rn_bound hs hε z)
  refine ⟨hI, ?_⟩
  calc ∫ z, |sa16y5_rn d s ε z| ≤ ∫ z : Euc d, (if ‖z‖ ≤ Real.sqrt 2 * ε then ‖z‖ ^ (-s) else 0) :=
        integral_mono hI.abs hint (fun z => sa16y5_rn_bound hs hε z)
    _ = _ := by
        rw [sa16y5_radial_near hd hsd hR, Real.mul_rpow (Real.sqrt_nonneg _) hε.le]
        ring

end Kr2

end HRS.Whole.AppendixA.Phase2SA16R
