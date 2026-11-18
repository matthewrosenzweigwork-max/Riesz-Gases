import HRS.MS.S111K4J01B
import HRS.MS.S111K2B04l

/-!
# S11.1 / J01 piece: the forcing of an `L¹` coefficient path satisfies the drift hypotheses of B04 (S11K4)

For `q ∈ L¹([0,H];ℓ²)` put `qr q v = PM E (q v)` (a strongly measurable representative with `⟪qr v, E 1⟫ = 0` for all `v`) and
`zq E q v f = ⟪qr q v, E f⟫`.  Then `zq` is in `L¹([0,H];F_{r,Pw})` with `dualNormE (zq v) ≤ ‖q v‖`, and the B04 structure
`S111k2Drift` holds for every `q`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

/-- The zero-mass representative of the time-coefficient path. -/
def qr {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {H : ℝ} (q : TimeCoeff H) : ℝ → Coeff :=
  fun v => PM E ((q : ℝ → Coeff) v)

/-- The forcing functional field. -/
def zq {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {H : ℝ} (q : TimeCoeff H) :
    ℝ → (Euc d → ℝ) → ℝ :=
  coefficientField E (qr E q)

theorem qr_sm {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {H : ℝ} (q : TimeCoeff H) :
    StronglyMeasurable (qr E q) :=
  (PM E).continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable q)

theorem zq_mass {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {H : ℝ} (q : TimeCoeff H) (v : ℝ) :
    zq E q v (fun _ => 1) = 0 := by
  unfold zq coefficientField qr
  exact PM_inner_mass E _

theorem dualNormE_coefficientField_le {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) (q : ℝ → Coeff)
    (v : ℝ) : dualNormE r Pw (coefficientField E q v) ≤ ENNReal.ofReal ‖q v‖ := by
  unfold dualNormE
  refine iSup_le fun f => iSup_le fun hf => ?_
  have hfin : weightedSobolevE r Pw f ≠ ⊤ := hf.2.2.2.ne
  have hw : IsR2WeightedTest r Pw f := ⟨contDiff_infty.1 hf.1 r, hf.2.2.2⟩
  refine ENNReal.div_le_of_le_mul ?_
  have h1 : |coefficientField E q v f| ≤ ‖q v‖ * (weightedSobolevE r Pw f).toReal := by
    unfold coefficientField
    rw [← E.norm f hw]
    exact abs_real_inner_le_norm _ _
  calc ENNReal.ofReal |coefficientField E q v f|
      ≤ ENNReal.ofReal (‖q v‖ * (weightedSobolevE r Pw f).toReal) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal ‖q v‖ * weightedSobolevE r Pw f := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_toReal hfin]

theorem zq_L1F {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {H : ℝ} (q : TimeCoeff H) :
    IsR2L1F r Pw H (zq E q) := by
  refine ⟨fun v _ => ⟨fun f g hf hg => ?_, fun c f hf => ?_, ⟨‖qr E q v‖, fun f hf => ?_⟩⟩, fun f hf => ?_, ?_⟩
  · exact k4j_coefField_add E (qr E q) v hf hg
  · exact k4j_coefField_smul E (qr E q) v c hf
  · unfold zq coefficientField
    rw [← E.norm f hf]
    exact abs_real_inner_le_norm _ _
  · exact ((qr_sm E q).inner stronglyMeasurable_const).measurable
  · refine lt_of_le_of_lt (lintegral_mono fun v => dualNormE_coefficientField_le E (qr E q) v) ?_
    have hint : Integrable (fun v => (q : ℝ → Coeff) v) (volume.restrict (Set.Icc (0 : ℝ) H)) :=
      Lp.memLp q |>.integrable le_rfl
    refine lt_of_le_of_lt (lintegral_mono fun v => ?_) hint.2
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (PM_norm_le E _)

end HRS.MS.S111K4J01
