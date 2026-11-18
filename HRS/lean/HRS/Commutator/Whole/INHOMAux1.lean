import HRS.Commutator.Whole.Defs
import HRS.PDE.ToolboxRd.Fourier

/-!
# CMX-INHOM auxiliary 1: Parseval and Cauchy-Schwarz with Sobolev weights

`inhom_pairing_le`: `|∫ u g| ≤ ‖u‖_{H^t} ‖g‖_{H^{-t}}` for real `L²` functions, in `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff ComplexConjugate

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma inhom_wt_pos (ξ : Euc d) : 0 < 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity

lemma inhom_weight_split (t : ℝ) (ξ : Euc d) :
    ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (t / 2)) *
      ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-t / 2)) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (inhom_wt_pos ξ).le _), ← Real.rpow_add (inhom_wt_pos ξ)]
  rw [show t / 2 + -t / 2 = 0 by ring]
  simp

lemma inhom_pairing_le {u g : Euc d → ℝ} (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) (t : ℝ) :
    ENNReal.ofReal |∫ x, u x * g x| ≤
      (sobSqE t (HRS.PDE.ToolboxRd.fourierL2 u)) ^ ((1 : ℝ) / 2) *
        (sobSqE (-t) (HRS.PDE.ToolboxRd.fourierL2 g)) ^ ((1 : ℝ) / 2) := by
  set U := HRS.PDE.ToolboxRd.fourierL2 u with hU
  set G := HRS.PDE.ToolboxRd.fourierL2 g with hG
  have hP := HRS.PDE.ToolboxRd.FourierAux.integral_fourierL2_mul_conj hu hg
  have hUm : AEStronglyMeasurable U volume :=
    HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hu
  have hGm : AEStronglyMeasurable G volume :=
    HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hg
  have h1 : ENNReal.ofReal |∫ x, u x * g x| ≤ ∫⁻ ξ, ‖U ξ‖ₑ * ‖G ξ‖ₑ := by
    have e : ENNReal.ofReal |∫ x, u x * g x| = ‖∫ ξ, U ξ * conj (G ξ)‖ₑ := by
      rw [hP, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
    rw [e]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun ξ => ?_
    rw [enorm_mul, RCLike.enorm_conj]
  refine h1.trans ?_
  set w : Euc d → ℝ := fun ξ => 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 with hw
  have hwm : ∀ r : ℝ, Measurable fun ξ : Euc d => ENNReal.ofReal (w ξ ^ r) := fun r =>
    (Measurable.pow_const (by simp only [hw]; fun_prop) _).ennreal_ofReal
  have e1 : ∀ ξ : Euc d, ‖U ξ‖ₑ * ‖G ξ‖ₑ =
      (ENNReal.ofReal (w ξ ^ (t / 2)) * ‖U ξ‖ₑ) * (ENNReal.ofReal (w ξ ^ (-t / 2)) * ‖G ξ‖ₑ) := by
    intro ξ
    have := inhom_weight_split t ξ
    calc ‖U ξ‖ₑ * ‖G ξ‖ₑ = (ENNReal.ofReal (w ξ ^ (t / 2)) * ENNReal.ofReal (w ξ ^ (-t / 2))) *
          (‖U ξ‖ₑ * ‖G ξ‖ₑ) := by rw [this, one_mul]
      _ = _ := by ring
  simp_rw [e1]
  have hHC := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    (f := fun ξ => ENNReal.ofReal (w ξ ^ (t / 2)) * ‖U ξ‖ₑ)
    (g := fun ξ => ENNReal.ofReal (w ξ ^ (-t / 2)) * ‖G ξ‖ₑ)
    ((hwm _).aemeasurable.mul hUm.enorm) ((hwm _).aemeasurable.mul hGm.enorm)
  refine le_trans (le_of_eq (lintegral_congr fun ξ => rfl)) (hHC.trans (le_of_eq ?_))
  have ea : ∀ (r : ℝ) (F : Euc d → ℂ), (∫⁻ ξ, (ENNReal.ofReal (w ξ ^ (r / 2)) * ‖F ξ‖ₑ) ^ (2 : ℝ)) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r) * ‖F ξ‖ₑ ^ 2 := by
    intro r F
    refine lintegral_congr fun ξ => ?_
    have hwpos : 0 < w ξ := inhom_wt_pos ξ
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ENNReal.rpow_two,
      ENNReal.rpow_two]
    congr 1
    rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hwpos.le _), ← Real.rpow_natCast,
      ← Real.rpow_mul hwpos.le]
    congr 2
    push_cast; ring
  have e3 : ∀ r : ℝ, (-r) / 2 = -r / 2 := fun r => rfl
  simp only [one_div]
  rw [ea t U, show -t / 2 = (-t) / 2 from rfl, ea (-t) G]
  simp only [sobSqE, one_div]
