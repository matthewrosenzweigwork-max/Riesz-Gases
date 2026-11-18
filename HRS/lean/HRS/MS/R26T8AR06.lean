import HRS.MS.CritForceAssemblyMaj
import HRS.MS.S82P2Mom

/-!
# S8.2 observed-time layer, packet T8A.R06: normalized exponential tilts under an oscillation bound

If `(V x - W x) - (V y - W y) ≤ B` for almost all `x, y`, then the normalized tilt of `V` is dominated by
`e^B` times the normalized tilt of `W`. Pointwise: `exp(V x - W x) Z_W ≤ e^B Z_V` for a.e. `x`, by integrating the
oscillation bound against `exp W` in `y`; then the two densities are compared by `withDensity_mono`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.MS.Phase2S82

theorem r26t8a_tilt_comparison {E : Type*} [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu] (V W : E → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hV : Measurable V) (hW : Measurable W)
    (hVi : Integrable (fun x => Real.exp (V x)) mu)
    (hWi : Integrable (fun x => Real.exp (W x)) mu)
    (hZV : 0 < ∫ x, Real.exp (V x) ∂mu) (hZW : 0 < ∫ x, Real.exp (W x) ∂mu)
    (hosc : ∀ᵐ x ∂mu, ∀ᵐ y ∂mu, (V x - W x) - (V y - W y) ≤ B) :
    exponentialTilt mu V ≤ ENNReal.ofReal (Real.exp B) • exponentialTilt mu W := by
  -- pointwise comparison of the normalized densities for a.e. `x`
  have hpt : ∀ᵐ x ∂mu, (∫ y, Real.exp (V y) ∂mu)⁻¹ * Real.exp (V x) ≤
      Real.exp B * ((∫ y, Real.exp (W y) ∂mu)⁻¹ * Real.exp (W x)) := by
    filter_upwards [hosc] with x hx
    have h1 : (∫ y, Real.exp (W y) ∂mu) * Real.exp (V x - W x - B) ≤ ∫ y, Real.exp (V y) ∂mu := by
      have hint : ∫ y, Real.exp (W y) * Real.exp (V x - W x - B) ∂mu ≤ ∫ y, Real.exp (V y) ∂mu := by
        refine integral_mono_ae (hWi.mul_const _) hVi ?_
        filter_upwards [hx] with y hy
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        linarith
      rwa [integral_mul_const] at hint
    have hk : Real.exp (V x) * (∫ y, Real.exp (W y) ∂mu) ≤
        Real.exp B * Real.exp (W x) * (∫ y, Real.exp (V y) ∂mu) := by
      have hsplit : Real.exp (V x) = Real.exp (W x) * (Real.exp B * Real.exp (V x - W x - B)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc Real.exp (V x) * (∫ y, Real.exp (W y) ∂mu)
          = Real.exp (W x) * Real.exp B * ((∫ y, Real.exp (W y) ∂mu) * Real.exp (V x - W x - B)) := by
            rw [hsplit]; ring
        _ ≤ Real.exp (W x) * Real.exp B * (∫ y, Real.exp (V y) ∂mu) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Real.exp B * Real.exp (W x) * (∫ y, Real.exp (V y) ∂mu) := by ring
    have hZv := hZV
    have hZw := hZW
    rw [show (∫ y, Real.exp (V y) ∂mu)⁻¹ * Real.exp (V x) =
        Real.exp (V x) / (∫ y, Real.exp (V y) ∂mu) by ring,
      show Real.exp B * ((∫ y, Real.exp (W y) ∂mu)⁻¹ * Real.exp (W x)) =
        Real.exp B * Real.exp (W x) / (∫ y, Real.exp (W y) ∂mu) by ring,
      div_le_div_iff₀ hZv hZw]
    linarith [hk]
  -- measurability of the two densities
  have hfV : Measurable (fun x => ENNReal.ofReal (Real.exp (V x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hV)
  have hfW : Measurable (fun x => ENNReal.ofReal (Real.exp (W x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hW)
  unfold exponentialTilt
  rw [← withDensity_smul _ hfV, ← withDensity_smul _ hfW,
    ← withDensity_smul _ (hfW.const_smul _)]
  apply withDensity_mono
  filter_upwards [hpt] with x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  have hZv : 0 < ∫ y, Real.exp (V y) ∂mu := hZV
  have hZw : 0 < ∫ y, Real.exp (W y) ∂mu := hZW
  rw [← ENNReal.ofReal_inv_of_pos hZv, ← ENNReal.ofReal_inv_of_pos hZw,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hZv.le), ← ENNReal.ofReal_mul (inv_nonneg.2 hZw.le),
    ← ENNReal.ofReal_mul (Real.exp_nonneg B)]
  exact ENNReal.ofReal_le_ofReal hx

end HRS.MS.R26T8A

end
