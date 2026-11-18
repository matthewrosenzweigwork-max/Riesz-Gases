import HRS.MS.S111K4J01H
import HRS.MS.S111K3F

/-!
# S11.1 / J01 piece: the (unprojected) forcing of an `L¹` coefficient path is admissible for the covariance map B03 (S11K4)

For a strongly measurable `Q : ℝ → ℓ²` with `∫_{[0,H]} ‖Q‖ < ∞`, the field `zQ v f = ⟪Q v, E f⟫` is in `L¹([0,H];F_{r,Pw})`,
`dualNormE (zQ v) ≤ ‖Q v‖`, and (with `ChartedOrbits`) its covariance integrands are a.e. measurable.  The covariance map needs no
zero mass.  Two such fields that agree a.e. in time have the same B03 interval tensor (tensor coordinate uniqueness T08).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem zQ_L1F {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {H : ℝ} {Q : ℝ → Coeff}
    (hQ : StronglyMeasurable Q) (hint : ∫⁻ v in Set.Icc (0 : ℝ) H, ‖Q v‖ₑ < ⊤) :
    IsR2L1F r Pw H (coefficientField E Q) := by
  refine ⟨fun v _ => ⟨fun f g hf hg => ?_, fun c f hf => ?_, ⟨‖Q v‖, fun f hf => ?_⟩⟩, fun f hf => ?_, ?_⟩
  · exact k4j_coefField_add E Q v hf hg
  · exact k4j_coefField_smul E Q v c hf
  · unfold coefficientField
    rw [← E.norm f hf]
    exact abs_real_inner_le_norm _ _
  · exact (hQ.inner stronglyMeasurable_const).measurable
  · refine lt_of_le_of_lt (lintegral_mono fun v => dualNormE_coefficientField_le E Q v) ?_
    refine lt_of_le_of_lt (lintegral_mono fun v => ?_) hint
    rw [← ofReal_norm_eq_enorm]

theorem zQ_JMeas {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {C : WholeCoeff d} {H : ℝ}
    (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) H) {Q : ℝ → Coeff} (hQ : StronglyMeasurable Q) :
    R2JIntegrandMeas C (wholeSpaceIndex d : ℝ) H (coefficientField E Q) := by
  intro ta tb φa φb hφa hφb hta htb
  exact (hQ.aestronglyMeasurable.inner (hco.1 ta tb φa φb hφa hφb hta htb)).aemeasurable

end HRS.MS.S111K4J01
