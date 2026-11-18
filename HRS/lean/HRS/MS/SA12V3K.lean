import HRS.MS.SA12V3J
import HRS.MS.ThCorrSob
import HRS.MS.SobMul
import HRS.MS.UlocCut
import HRS.MS.UlNormAux1
import HRS.MS.QMul

/-!
# S.A.12 C2 (SA12V3 worker), part K: the C2 definitions (verbatim from the skeleton) and the mollifier bound

`mollify η ε u = G_ε * u`, `G_ε = ε^{-d} η(·/ε)`, and `‖G_ε * u‖_{H^r} ≤ ‖u‖_{H^r}` for every real `r` (`sobolevNormE`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

def IsMollifier (η : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
  tsupport η ⊆ Metric.closedBall (0 : Euc d) 1 ∧
  (∀ x, 0 ≤ η x) ∧ (∫ x, η x)=1

def mollify (η : Euc d → ℝ) (ε : ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y, ε^(-(d : ℤ))*η (ε⁻¹ • y)*u (x-y)

def periodicDatum (ζ η : Euc d → ℝ) (L ε : ℝ) (φ : Euc d → ℝ) : Euc d → ℝ :=
  HRS.Whole.AppendixALemmas.perL L
    (fun x => ζ (L⁻¹ • x)*mollify η (min ε 1) φ x)

end HRS.MH.AdjointRd.Phase2SA12Construction

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- The scaled mollifier `G_ε(y) = ε^{-d} η(y/ε)`. -/
def sa12v3_G (η : Euc d → ℝ) (ε : ℝ) (y : Euc d) : ℝ := ε ^ (-(d : ℤ)) * η (ε⁻¹ • y)

theorem sa12v3_G_nonneg {η : Euc d → ℝ} (hη : IsMollifier η) {ε : ℝ} (hε : 0 < ε) (y : Euc d) :
    0 ≤ sa12v3_G η ε y :=
  mul_nonneg (zpow_nonneg hε.le _) (hη.2.2.2.1 _)

theorem sa12v3_G_cont {η : Euc d → ℝ} (hη : IsMollifier η) (ε : ℝ) : Continuous (sa12v3_G η ε) :=
  continuous_const.mul (hη.1.continuous.comp (continuous_id.const_smul ε⁻¹))

theorem sa12v3_G_integral {η : Euc d → ℝ} (hη : IsMollifier η) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, sa12v3_G η ε y = 1 := by
  unfold sa12v3_G
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul (volume : Measure (Euc d)) η ε⁻¹
  rw [h, hη.2.2.2.2, finrank_euclideanSpace_fin, smul_eq_mul, mul_one, inv_pow, inv_inv,
    abs_of_pos (pow_pos hε _), zpow_neg, zpow_natCast]
  field_simp

theorem sa12v3_G_integrable {η : Euc d → ℝ} (hη : IsMollifier η) {ε : ℝ} (hε : 0 < ε) :
    Integrable (sa12v3_G η ε) volume := by
  have : Integrable (fun y : Euc d => η (ε⁻¹ • y)) volume :=
    (hη.1.continuous.integrable_of_hasCompactSupport hη.2.1).comp_smul (inv_ne_zero hε.ne')
  exact this.const_mul _

theorem sa12v3_mollify_eq (η : Euc d → ℝ) (ε : ℝ) (u : Euc d → ℝ) :
    mollify η ε u = HRS.Whole.convFun (sa12v3_G η ε) u := by
  funext x
  unfold mollify HRS.Whole.convFun sa12v3_G
  rw [← integral_sub_left_eq_self (fun y => ε ^ (-(d : ℤ)) * η (ε⁻¹ • y) * u (x - y)) volume x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp

theorem sa12v3_Ghat_le {η : Euc d → ℝ} (hη : IsMollifier η) {ε : ℝ} (hε : 0 < ε) (ξ : Euc d) :
    ‖HRS.MS.Tc3.tc3_Ghat (sa12v3_G η ε) ξ‖ ≤ 1 * HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ (-(0 : ℝ) / 2) := by
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ (Euc d)) (fun x => ((sa12v3_G η ε x : ℝ) : ℂ)) ξ
  have e : ∫ v : Euc d, ‖((sa12v3_G η ε v : ℝ) : ℂ)‖ = 1 := by
    simp_rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sa12v3_G_nonneg hη hε _)]
    exact sa12v3_G_integral hη hε
  rw [e] at h
  have h2 : ‖HRS.MS.Tc3.tc3_Ghat (sa12v3_G η ε) ξ‖ ≤ 1 := h
  simpa using h2

/-- Minkowski for the mollifier: `‖G_ε * u‖_{H^r} ≤ ‖u‖_{H^r}` (extended norm). -/
theorem sa12v3_mollify_sobolevNormE_le {η : Euc d → ℝ} (hη : IsMollifier η) {ε : ℝ} (hε : 0 < ε) (r : ℝ)
    (u : Euc d → ℝ) : sobolevNormE r (mollify η ε u) ≤ sobolevNormE r u := by
  rw [sa12v3_mollify_eq]
  have := HRS.MS.Tc3.tc3_sobolevNormE_gain (sa12v3_G_cont hη ε).measurable (sa12v3_G_integrable hη hε)
    (α := 0) (A := 1) one_pos (sa12v3_Ghat_le hη hε) r u
  simpa using this

end HRS.MH.AdjointRd.Phase2SA12V3
