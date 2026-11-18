import HRS.MS.TransOpAux21
import HRS.Main.Headline

/-!
# S611 packet P3b: transfer of the two path distances through a bounded linear map
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

theorem s611_dist_transfer {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
    (S : B →L[ℝ] B) {K : ℝ} (hK1 : 1 ≤ K) (hS : ‖S‖ ≤ K)
    (FY : Ω → B) (FY' : Ω' → B) (FX : Ω → B) (FX' : Ω' → B)
    (hFY : AEMeasurable FY P) (hFY' : AEMeasurable FY' P')
    (hX : ∀ ζ, FX ζ = S (FY ζ)) (hX' : ∀ ζ, FX' ζ = S (FY' ζ)) {ε ε' : ℝ}
    (h2 : HRS.smoothDist 2 (HRS.law P FY) (HRS.law P' FY') ≤ ε)
    (hW : HRS.wassersteinE 1 (HRS.law P FY) (HRS.law P' FY') ≤ ENNReal.ofReal ε') :
    AEMeasurable FX P ∧ AEMeasurable FX' P' ∧
      HRS.smoothDist 2 (HRS.law P FX) (HRS.law P' FX') ≤ K ^ 2 * ε ∧
      HRS.wassersteinE 1 (HRS.law P FX) (HRS.law P' FX') ≤ ENNReal.ofReal (K ^ 2 * ε') := by
  have hfx : FX = fun ζ => S (FY ζ) := funext hX
  have hfx' : FX' = fun ζ => S (FY' ζ) := funext hX'
  have hSm : Measurable S := S.continuous.measurable
  have hm1 : AEMeasurable FX P := by rw [hfx]; exact hSm.comp_aemeasurable hFY
  have hm2 : AEMeasurable FX' P' := by rw [hfx']; exact hSm.comp_aemeasurable hFY'
  refine ⟨hm1, hm2, ?_, ?_⟩
  · haveI : IsProbabilityMeasure (HRS.law P FY) := inferInstance
    haveI : IsProbabilityMeasure (HRS.law P' FY') := inferInstance
    have e1 : HRS.law P FX = (HRS.law P FY).map S := by
      rw [hfx]; exact (AEMeasurable.map_map_of_aemeasurable hSm.aemeasurable hFY).symm
    have e2 : HRS.law P' FX' = (HRS.law P' FY').map S := by
      rw [hfx']; exact (AEMeasurable.map_map_of_aemeasurable hSm.aemeasurable hFY').symm
    rw [e1, e2]
    refine (HRS.Main.smoothDist_map_clm_le S 2 _ _).trans ?_
    have hmax : max 1 (‖S‖ ^ 2) ≤ K ^ 2 :=
      max_le (by nlinarith) (pow_le_pow_left₀ (norm_nonneg _) hS 2)
    have hnn := HRS.smoothDist_nonneg (B := B) 2 (HRS.law P FY) (HRS.law P' FY')
    calc max 1 (‖S‖ ^ 2) * HRS.smoothDist 2 (HRS.law P FY) (HRS.law P' FY')
        ≤ K ^ 2 * HRS.smoothDist 2 (HRS.law P FY) (HRS.law P' FY') :=
          mul_le_mul_of_nonneg_right hmax hnn
      _ ≤ K ^ 2 * ε := mul_le_mul_of_nonneg_left h2 (sq_nonneg K)
  · haveI : IsProbabilityMeasure (HRS.law P FY) := inferInstance
    haveI : IsProbabilityMeasure (HRS.law P' FY') := inferInstance
    have e1 : HRS.law P FX = (HRS.law P FY).map S := by
      rw [hfx]; exact (AEMeasurable.map_map_of_aemeasurable hSm.aemeasurable hFY).symm
    have e2 : HRS.law P' FX' = (HRS.law P' FY').map S := by
      rw [hfx']; exact (AEMeasurable.map_map_of_aemeasurable hSm.aemeasurable hFY').symm
    rw [e1, e2]
    refine (HRS.Main.wassersteinE_map_clm_le S 1 le_rfl _ _).trans ?_
    have hK0 : 0 ≤ K := by linarith
    calc ENNReal.ofReal ‖S‖ * HRS.wassersteinE 1 (HRS.law P FY) (HRS.law P' FY')
        ≤ ENNReal.ofReal K * ENNReal.ofReal ε' := mul_le_mul' (ENNReal.ofReal_le_ofReal hS) hW
      _ = ENNReal.ofReal (K * ε') := (ENNReal.ofReal_mul hK0).symm
      _ ≤ ENNReal.ofReal (K ^ 2 * ε') := by
          rcases le_total 0 ε' with h | h
          · exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg h (mul_nonneg hK0 (sub_nonneg.2 hK1))])
          · rw [ENNReal.ofReal_of_nonpos (by nlinarith : K * ε' ≤ 0)]
            exact zero_le

end HRS.MS.TransOp

end
