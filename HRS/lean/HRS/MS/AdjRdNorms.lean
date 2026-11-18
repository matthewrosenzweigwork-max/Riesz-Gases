import HRS.Whole.AppendixA
import HRS.PDE.ToolboxRd.Fourier

/-!
# S.A.12 N1: the two uloc-norm interfaces needed by the uniqueness adapters

`sa12_uloc_mono` and `sa12_uloc_sub` for the conditional `ℝ≥0∞` uniformly local Sobolev norm.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.SA12BD

open HRS HRS.Whole HRS.Whole.AppendixA

/-- Minkowski in a weighted `L²` space, in the form needed for the Fourier side of `H^r`. -/
theorem sa12_mink {d : ℕ} (w : Euc d → ℝ) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hw : AEStronglyMeasurable w volume) (a b : Euc d → ℂ)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hA : Integrable (fun ξ => w ξ * ‖a ξ‖ ^ 2) volume)
    (hB : Integrable (fun ξ => w ξ * ‖b ξ‖ ^ 2) volume) :
    Integrable (fun ξ => w ξ * ‖a ξ - b ξ‖ ^ 2) volume ∧
      Real.sqrt (∫ ξ, w ξ * ‖a ξ - b ξ‖ ^ 2) ≤
        Real.sqrt (∫ ξ, w ξ * ‖a ξ‖ ^ 2) + Real.sqrt (∫ ξ, w ξ * ‖b ξ‖ ^ 2) := by
  set A := ∫ ξ, w ξ * ‖a ξ‖ ^ 2 with hAdef
  set B := ∫ ξ, w ξ * ‖b ξ‖ ^ 2 with hBdef
  have hmeasab : AEStronglyMeasurable (fun ξ => w ξ * (‖a ξ‖ * ‖b ξ‖)) volume :=
    hw.mul (ha.norm.mul hb.norm)
  have hC : Integrable (fun ξ => w ξ * (‖a ξ‖ * ‖b ξ‖)) volume := by
    refine Integrable.mono' ((hA.add hB)) hmeasab (Filter.Eventually.of_forall fun ξ => ?_)
    have h0 : 0 ≤ w ξ * (‖a ξ‖ * ‖b ξ‖) := mul_nonneg (hw0 ξ) (by positivity)
    rw [Real.norm_of_nonneg h0]
    have : ‖a ξ‖ * ‖b ξ‖ ≤ ‖a ξ‖ ^ 2 + ‖b ξ‖ ^ 2 := by
      nlinarith [sq_nonneg (‖a ξ‖ - ‖b ξ‖), norm_nonneg (a ξ), norm_nonneg (b ξ)]
    calc w ξ * (‖a ξ‖ * ‖b ξ‖) ≤ w ξ * (‖a ξ‖ ^ 2 + ‖b ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this (hw0 ξ)
      _ = _ := by simp only [Pi.add_apply]; ring
  set Cc := ∫ ξ, w ξ * (‖a ξ‖ * ‖b ξ‖) with hCdef
  have hint : Integrable (fun ξ => w ξ * ‖a ξ - b ξ‖ ^ 2) volume := by
    refine Integrable.mono' ((hA.add hB).const_mul 2) (hw.mul ((ha.sub hb).norm.pow 2))
      (Filter.Eventually.of_forall fun ξ => ?_)
    have h0 : 0 ≤ w ξ * ‖a ξ - b ξ‖ ^ 2 := mul_nonneg (hw0 ξ) (by positivity)
    rw [Real.norm_of_nonneg h0]
    have h1 : ‖a ξ - b ξ‖ ≤ ‖a ξ‖ + ‖b ξ‖ := norm_sub_le _ _
    have h2 : ‖a ξ - b ξ‖ ^ 2 ≤ 2 * (‖a ξ‖ ^ 2 + ‖b ξ‖ ^ 2) := by
      nlinarith [sq_nonneg (‖a ξ‖ - ‖b ξ‖), norm_nonneg (a ξ), norm_nonneg (b ξ),
        norm_nonneg (a ξ - b ξ)]
    calc w ξ * ‖a ξ - b ξ‖ ^ 2 ≤ w ξ * (2 * (‖a ξ‖ ^ 2 + ‖b ξ‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (hw0 ξ)
      _ = _ := by simp only [Pi.add_apply]; ring
  refine ⟨hint, ?_⟩
  have hA0 : 0 ≤ A := integral_nonneg fun ξ => mul_nonneg (hw0 ξ) (by positivity)
  have hB0 : 0 ≤ B := integral_nonneg fun ξ => mul_nonneg (hw0 ξ) (by positivity)
  -- the main bound: ∫ w ‖a-b‖² ≤ A + B + 2 C
  have hmain : ∫ ξ, w ξ * ‖a ξ - b ξ‖ ^ 2 ≤ A + B + 2 * Cc := by
    have : ∫ ξ, w ξ * (‖a ξ‖ ^ 2 + ‖b ξ‖ ^ 2 + 2 * (‖a ξ‖ * ‖b ξ‖)) = A + B + 2 * Cc := by
      have e : (fun ξ => w ξ * (‖a ξ‖ ^ 2 + ‖b ξ‖ ^ 2 + 2 * (‖a ξ‖ * ‖b ξ‖))) =
          fun ξ => (w ξ * ‖a ξ‖ ^ 2 + w ξ * ‖b ξ‖ ^ 2) + 2 * (w ξ * (‖a ξ‖ * ‖b ξ‖)) := by
        ext ξ; ring
      have hAB : Integrable (fun ξ => w ξ * ‖a ξ‖ ^ 2 + w ξ * ‖b ξ‖ ^ 2) volume := hA.add hB
      rw [e, integral_add hAB (hC.const_mul 2), integral_add hA hB, integral_const_mul]
    rw [← this]
    refine integral_mono hint ?_ fun ξ => ?_
    · have e : (fun ξ => w ξ * (‖a ξ‖ ^ 2 + ‖b ξ‖ ^ 2 + 2 * (‖a ξ‖ * ‖b ξ‖))) =
          fun ξ => (w ξ * ‖a ξ‖ ^ 2 + w ξ * ‖b ξ‖ ^ 2) + 2 * (w ξ * (‖a ξ‖ * ‖b ξ‖)) := by
        ext ξ; ring
      rw [e]
      have hAB : Integrable (fun ξ => w ξ * ‖a ξ‖ ^ 2 + w ξ * ‖b ξ‖ ^ 2) volume := hA.add hB
      exact hAB.add (hC.const_mul 2)
    · have h1 : ‖a ξ - b ξ‖ ≤ ‖a ξ‖ + ‖b ξ‖ := norm_sub_le _ _
      have h2 : ‖a ξ - b ξ‖ ^ 2 ≤ ‖a ξ‖ ^ 2 + ‖b ξ‖ ^ 2 + 2 * (‖a ξ‖ * ‖b ξ‖) := by
        nlinarith [norm_nonneg (a ξ - b ξ), norm_nonneg (a ξ), norm_nonneg (b ξ)]
      exact mul_le_mul_of_nonneg_left h2 (hw0 ξ)
  -- Cauchy-Schwarz: C² ≤ A B via the discriminant of t ↦ ∫ w (t‖a‖ - ‖b‖)²
  have hquad : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * Cc) * t + B := by
    intro t
    have hnn : 0 ≤ ∫ ξ, w ξ * (t * ‖a ξ‖ - ‖b ξ‖) ^ 2 :=
      integral_nonneg fun ξ => mul_nonneg (hw0 ξ) (sq_nonneg _)
    have e : (fun ξ => w ξ * (t * ‖a ξ‖ - ‖b ξ‖) ^ 2) =
        fun ξ => (t ^ 2 * (w ξ * ‖a ξ‖ ^ 2) + w ξ * ‖b ξ‖ ^ 2) - (2 * t) * (w ξ * (‖a ξ‖ * ‖b ξ‖)) := by
      ext ξ; ring
    have h1 : Integrable (fun ξ => t ^ 2 * (w ξ * ‖a ξ‖ ^ 2)) volume := hA.const_mul _
    have h2 : Integrable (fun ξ => t ^ 2 * (w ξ * ‖a ξ‖ ^ 2) + w ξ * ‖b ξ‖ ^ 2) volume := h1.add hB
    rw [e, integral_sub h2 (hC.const_mul _), integral_add h1 hB,
      integral_const_mul, integral_const_mul] at hnn
    nlinarith [hnn]
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  have hC2 : Cc ^ 2 ≤ A * B := by nlinarith [hdisc]
  have hCle : Cc ≤ Real.sqrt A * Real.sqrt B := by
    rw [← Real.sqrt_mul hA0]
    exact Real.le_sqrt_of_sq_le hC2
  have hsq : A + B + 2 * Cc ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
    have := Real.sq_sqrt hA0
    have := Real.sq_sqrt hB0
    nlinarith
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hmain.trans hsq⟩

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem sa12_sobolevNormE_sub {d : ℕ} (r : ℝ) (u v : Euc d → ℝ) :
    HRS.Whole.sobolevNormE r (fun x => u x - v x) ≤
      HRS.Whole.sobolevNormE r u + HRS.Whole.sobolevNormE r v := by
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev r u
  swap
  · simp [HRS.Whole.sobolevNormE, hu]
  by_cases hv : HRS.PDE.ToolboxRd.MemSobolev r v
  swap
  · simp [HRS.Whole.sobolevNormE, hv]
  have hsub : MemLp (fun x => u x - v x) 2 volume := hu.1.sub hv.1
  have hF := fourierL2_sub hu.1 hv.1
  have hwm : AEStronglyMeasurable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r) volume :=
    (continuous_wt_rpow (d := d) r).aestronglyMeasurable
  have hw0 : ∀ ξ : Euc d, 0 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r := fun ξ =>
    Real.rpow_nonneg (by positivity) _
  obtain ⟨hint, hle⟩ := sa12_mink _ hw0 hwm (fourierL2 u) (fourierL2 v)
    (aestronglyMeasurable_fourierL2 hu.1) (aestronglyMeasurable_fourierL2 hv.1) hu.2 hv.2
  have hcongr : (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r *
      ‖fourierL2 (fun x => u x - v x) ξ‖ ^ 2) =ᵐ[volume]
      fun ξ => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r * ‖fourierL2 u ξ - fourierL2 v ξ‖ ^ 2 := by
    filter_upwards [hF] with ξ hξ
    rw [hξ]
  have hmem : HRS.PDE.ToolboxRd.MemSobolev r (fun x => u x - v x) := ⟨hsub, hint.congr hcongr.symm⟩
  have hnorm : HRS.PDE.ToolboxRd.sobolevNormSq r (fun x => u x - v x) =
      ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r * ‖fourierL2 u ξ - fourierL2 v ξ‖ ^ 2 :=
    integral_congr_ae hcongr
  simp only [HRS.Whole.sobolevNormE, hu, hv, hmem, ite_true]
  rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [hnorm]
  exact hle

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem sa12_sobolevNormE_mono {d : ℕ} {r r' : ℝ} (h : r' ≤ r) (u : Euc d → ℝ) :
    HRS.Whole.sobolevNormE r' u ≤ HRS.Whole.sobolevNormE r u := by
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev r u
  swap
  · simp [HRS.Whole.sobolevNormE, hu]
  have hu' : HRS.PDE.ToolboxRd.MemSobolev r' u := HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono h hu
  simp only [HRS.Whole.sobolevNormE, hu, hu', ite_true]
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  refine integral_mono hu'.2 hu.2 fun ξ => ?_
  have hn : 0 ≤ ‖fourierL2 u ξ‖ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (one_le_wt ξ) h) hn

theorem sa12_uloc_mono (d m m' : ℕ) (h : m' ≤ m) (χ u : Euc d → ℝ) :
    ulocNormE m' χ u ≤ ulocNormE m χ u := by
  unfold ulocNormE
  refine iSup_mono fun z => ?_
  exact sa12_sobolevNormE_mono (by exact_mod_cast h) _

theorem sa12_uloc_sub (d m : ℕ) (χ u v : Euc d → ℝ) :
    ulocNormE m χ (fun x => u x - v x) ≤
      ulocNormE m χ u + ulocNormE m χ v := by
  unfold ulocNormE
  refine iSup_le fun z => ?_
  have e : (fun x => χ (x - z) * (u x - v x)) =
      fun x => χ (x - z) * u x - χ (x - z) * v x := by ext x; ring
  rw [e]
  exact (sa12_sobolevNormE_sub _ _ _).trans
    (add_le_add (le_iSup (fun z => HRS.Whole.sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) z)
      (le_iSup (fun z => HRS.Whole.sobolevNormE (m : ℝ) fun x => χ (x - z) * v x) z))

end HRS.MS.SA12BD
