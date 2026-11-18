import HRS.MS.Fp81S21TimeRep12

/-! Time integration of fixed-time mean-square errors. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MS.R26T6

local instance fp81s21_wickApprox_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_wickApprox_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- A uniform fixed-time squared-error estimate lifts to the measurable time-L²
sections. The fixed-time hypothesis includes actual integrability. -/
theorem fp81s21_time_sqerr_of_section_sqerr
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q r : ℝ → Ω → r26t6_Coeff) (Mq Mr a H : ℝ)
    (U V : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hr : Measurable (Function.uncurry r))
    (hU : fp81s21_TimeL2Rep P q Mq a H U)
    (hV : fp81s21_TimeL2Rep P r Mr a H V)
    (ha : 0 ≤ a) (hH : 0 ≤ H) (ε : ℝ)
    (herr : ∀ u, 0 ≤ u → fp81s21_SqErr P (q u) (r u) ε) :
    fp81s21_SqErr P U V (Real.sqrt H * ε) := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun z => q (a + z.1) z.2 - r (a + z.1) z.2
  have hqm : Measurable (fun z : ℝ × Ω => q (a + z.1) z.2) :=
    hq.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hrm : Measurable (fun z : ℝ × Ω => r (a + z.1) z.2) :=
    hr.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hgm : Measurable g := hqm.sub hrm
  have hsec : ∀ᵐ t ∂dt, MemLp (fun ω => g (t, ω)) 2 P ∧
      (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) ≤ ε ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hh := herr (a + t) (add_nonneg ha ht.1)
    exact ⟨(memLp_two_iff_integrable_sq_norm
      (hgm.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable).2 hh.1, hh.2⟩
  obtain ⟨hg, hb⟩ := fp81s21_memLp_prod_of_section_bound dt P g hgm (ε ^ 2) hsec
  let Z : Ω → Lp r26t6_Coeff 2 dt := fun ω => U ω - V ω
  have hZL : MemLp Z 2 P := hU.2.1.sub hV.2.1
  have hZeq : ∀ᵐ ω ∂P, ⇑(Z ω) =ᵐ[dt] fun t => g (t, ω) := by
    filter_upwards [hU.2.2.2, hV.2.2.2] with ω hωq hωr
    filter_upwards [hωq.2, hωr.2, Lp.coeFn_sub (U ω) (V ω)] with t hq' hr' hs
    change (U ω - V ω) t = _
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hq', hr']
  obtain ⟨_, heq⟩ := fp81s21_time_section_moment P H g Z hZL.aestronglyMeasurable hg hZeq
  refine ⟨hZL.norm.integrable_sq, ?_⟩
  calc
    _ = ∫ z, ‖g z‖ ^ 2 ∂dt.prod P := heq
    _ ≤ (dt Set.univ).toReal * ε ^ 2 := hb
    _ = (Real.sqrt H * ε) ^ 2 := by
      simp [dt, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal hH,
        mul_pow, Real.sq_sqrt hH]

#print axioms fp81s21_time_sqerr_of_section_sqerr
end HRS.Fp81.S21
end
