import HRS.MS.Fp81S21GaussianQuadraticHilbert5
import HRS.MS.Fp81S21TimeRep9

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators RealInnerProductSpace
open HRS HRS.MS.R26T6
namespace HRS.Fp81.S21

local instance fp81s21_GaussianQuadraticHilbert6_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianQuadraticHilbert6_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The finite-horizon representative supplies the time-integral domination
needed for scalar second-chaos closure. -/
theorem fp81s21_TimeL2Rep_norm_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U) :
    (∀ᵐ ω ∂P, Integrable (fun t => ‖q (a + t) ω‖)
      (volume.restrict (Set.Icc (0 : ℝ) H))) ∧
    MemLp (fun ω => ∫ t, ‖q (a + t) ω‖
      ∂(volume.restrict (Set.Icc (0 : ℝ) H))) 2 P := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : Ω × ℝ → r26t6_Coeff := fun z => q (a + z.2) z.1
  have hg : Measurable g :=
    hq.comp ((measurable_const.add measurable_snd).prodMk measurable_fst)
  have hi : ∀ᵐ ω ∂P, Integrable (fun t => ‖g (ω, t)‖) dt := by
    filter_upwards [hrep.2.2.2] with ω hω
    exact memLp_one_iff_integrable.mp (hω.1.norm.mono_exponent (by norm_num))
  have hb : ∀ᵐ ω ∂P, (∫ t, ‖g (ω, t)‖ ∂dt) ≤ Real.sqrt H * ‖U ω‖ := by
    filter_upwards [hrep.2.2.2] with ω hω
    have hf : MemLp (fun t => ‖g (ω, t)‖) (ENNReal.ofReal (2 : ℝ)) dt := by
      simpa [g] using hω.1.norm
    have hc : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) dt := memLp_const 1
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := dt)
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun t => norm_nonneg (g (ω, t)))
      (Filter.Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1)) hf hc
    have he : (∫ t, ‖g (ω, t)‖ ^ 2 ∂dt) = ‖U ω‖ ^ 2 := by
      calc
        _ = ∫ t, inner ℝ ((U ω : ℝ → r26t6_Coeff) t) ((U ω : ℝ → r26t6_Coeff) t) ∂dt := by
          apply integral_congr_ae
          filter_upwards [hω.2] with t ht
          rw [real_inner_self_eq_norm_sq, ht]
        _ = inner ℝ (U ω) (U ω) := (L2.inner_def _ _).symm
        _ = ‖U ω‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hh' : (∫ t, ‖g (ω, t)‖ ∂dt) ≤
        Real.sqrt (∫ t, ‖g (ω, t)‖ ^ 2 ∂dt) * Real.sqrt H := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_two, dt, Measure.real,
        Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal hH] using hh
    rw [he, Real.sqrt_sq (norm_nonneg _)] at hh'
    simpa [mul_comm] using hh'
  refine ⟨hi, ?_⟩
  have hm : AEStronglyMeasurable (fun ω => ∫ t, ‖g (ω, t)‖ ∂dt) P :=
    hg.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  apply (hrep.2.1.norm.const_mul (Real.sqrt H)).mono' hm
  filter_upwards [hb] with ω hω
  rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
  exact hω

#print axioms fp81s21_TimeL2Rep_norm_integral
end HRS.Fp81.S21
end
