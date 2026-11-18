import HRS.MS.R26T6CI04
import HRS.MS.R26T6CI02

/-!
# S11.1 I07: positive-Riesz screened kernel maps L2 into L3

The L3 norm depends only on a uniform L-infinity bound for the density,
not on the position of the row. This is the positive-exponent ingredient
of the thermal screened third-moment estimate.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.Whole.Q34
variable {d : ℕ}

theorem r26t6c_positive_riesz_Kop_L2_L3
    (hd : 2 ≤ d) (s M : ℝ) (hs : 0 < s) (h2s : 2*s < d)
    (rho : Euc d → ℝ) (hrho : HRS.Whole.IsProbDensity rho)
    (hM : ∀ x, rho x ≤ M)
    (f : Euc d → ℝ)
    (hf : MemLp f 2 (HRS.Whole.withDensityReal rho)) :
    let mu := HRS.Whole.withDensityReal rho
    MemLp (HRS.Whole.Kop (HRS.Whole.rieszKernel d s) mu f) 3 mu ∧
    eLpNorm (HRS.Whole.Kop (HRS.Whole.rieszKernel d s) mu f) 3 mu ≤
      ENNReal.ofReal (2 * Real.sqrt (M * sphereArea d / ((d : ℝ) - 2*s) + 1)) *
        eLpNorm f 2 mu := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := Q34.isProbabilityMeasure_nu hrho
  let R : ℝ := Real.sqrt (M * sphereArea d / ((d : ℝ) - 2*s) + 1)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  let g : Euc d → ℝ := fun x => ∫ y, HRS.Whole.rieszKernel d s (x-y) * f y ∂mu
  have hk : Measurable (Function.uncurry
      (fun x y : Euc d => HRS.Whole.rieszKernel d s (x-y))) :=
    (Q34.measurable_rieszKernel (ne_of_gt hs)).comp
      (measurable_fst.sub measurable_snd)
  have hrow : ∀ x : Euc d,
      MemLp (fun y => HRS.Whole.rieszKernel d s (x-y)) 2 mu ∧
      eLpNorm (fun y => HRS.Whole.rieszKernel d s (x-y)) 2 mu ≤
        ENNReal.ofReal R :=
    fun x => r26t6c_riesz_row_L2 hd s M hs h2s rho hrho hM x
  have hmap := r26t6c_kernel_L2_L3 mu
    (fun x y => HRS.Whole.rieszKernel d s (x-y))
    hk (fun _ => R) (memLp_const R) (fun _ => hR0) hrow f hf
  have hconst : eLpNorm (fun _ : Euc d => R) 3 mu = ENNReal.ofReal R := by
    rw [eLpNorm_const' R (by norm_num) (by norm_num)]
    simp [measure_univ, Real.enorm_eq_ofReal_abs, abs_of_nonneg hR0]
  have hbound : eLpNorm g 3 mu ≤ ENNReal.ofReal R * eLpNorm f 2 mu := by
    simpa only [g, hconst] using hmap.2
  have hcenter := r26t6c_centered_L3 mu g hmap.1
  change MemLp (HRS.Whole.projMean mu g) 3 mu ∧
    eLpNorm (HRS.Whole.projMean mu g) 3 mu ≤
      ENNReal.ofReal (2 * R) * eLpNorm f 2 mu
  refine ⟨hcenter.1, ?_⟩
  calc
    _ ≤ 2 * eLpNorm g 3 mu := hcenter.2
    _ ≤ 2 * (ENNReal.ofReal R * eLpNorm f 2 mu) :=
      mul_le_mul' le_rfl hbound
    _ = ENNReal.ofReal (2 * R) * eLpNorm f 2 mu := by
      rw [← mul_assoc]
      congr 1
      have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      rw [htwo, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

end HRS.MS.R26T6C
