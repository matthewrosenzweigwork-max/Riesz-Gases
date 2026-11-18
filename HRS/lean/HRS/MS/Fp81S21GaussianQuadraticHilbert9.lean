import HRS.MS.Fp81S21GaussianQuadraticHilbert8
import HRS.MS.ProClosureS111PairingLimits
import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators RealInnerProductSpace
open HRS HRS.MC.E213U13 HRS.MS.R26T6 HRS.MS.ProClosureS111
namespace HRS.Fp81.S21

local instance fp81s21_GaussianQuadraticHilbert9_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianQuadraticHilbert9_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Every Hilbert coordinate of the retained time-L² representative is in
the same scalar second chaos. -/
theorem fp81s21_TimeL2Rep_InQ2_inner
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hcoord : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧ ∀ j, InQ2 hξ (fun ω => q u ω j))
    (v : Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) :
    InQ2 hξ (fun ω => inner ℝ v (U ω)) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff := HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff := UniformSpace.secondCountable_of_separable _
  have hdense := BoundedContinuousFunction.toLp_denseRange r26t6_Coeff dt ℝ (p := 2) (by norm_num)
  obtain ⟨vn, hvn, hlim⟩ := mem_closure_iff_seq_limit.1 (hdense v)
  choose f hf using hvn
  have hfn : ∀ n, MemLp (f n : ℝ → r26t6_Coeff) 2 dt := fun n =>
    (f n).memLp_top.mono_exponent (by simp)
  have hfeq : ∀ n, (hfn n).toLp (f n) = vn n := by
    intro n
    rw [← hf n]
    apply Lp.ext
    exact ((hfn n).coeFn_toLp).trans (BoundedContinuousFunction.coeFn_toLp 2 dt ℝ (f n)).symm
  have hQn : ∀ n, InQ2 hξ (fun ω => inner ℝ (vn n) (U ω)) := by
    intro n
    rw [← hfeq n]
    apply fp81s21_TimeL2Rep_InQ2_bounded_test hξ q M a H ha hH U hq hrep hcoord
      (f n) (f n).continuous.measurable (hfn n) ‖f n‖ (norm_nonneg _)
    exact (f n).norm_coe_le_norm
  let Yn : ℕ → Ω → ℝ := fun n ω => inner ℝ (vn n) (U ω)
  let Y : Ω → ℝ := fun ω => inner ℝ v (U ω)
  have hYn : ∀ n, MemLp (Yn n) 2 P := fun n =>
    hrep.2.1.continuousLinearMap_comp (innerSL ℝ (vn n))
  have hY : MemLp Y 2 P := hrep.2.1.continuousLinearMap_comp (innerSL ℝ v)
  have hsquare : Tendsto (fun n => ∫ ω, (Yn n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [Yn, Y, real_inner_comm] using
      inner_pairing_square_tendsto P U hrep.2.1 v vn hlim
  apply InQ2.of_tendsto (l := atTop) hQn hY.aestronglyMeasurable
  have ht := (ENNReal.continuous_ofReal.tendsto 0).comp hsquare
  simp only [Function.comp_def, ENNReal.ofReal_zero] at ht
  refine ht.congr fun n => ?_
  have hi : Integrable (fun ω => (Yn n ω - Y ω) ^ 2) P := ((hYn n).sub hY).integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  apply lintegral_congr
  intro ω
  rw [ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    Real.norm_eq_abs, sq_abs]

#print axioms fp81s21_TimeL2Rep_InQ2_inner
end HRS.Fp81.S21
end
