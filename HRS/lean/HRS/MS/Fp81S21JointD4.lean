import HRS.MS.Fp81S21JointD3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS.MS.R26T6

local instance fp81s21_jointD4_measurable (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_jointD4_borel (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- A uniform second-moment bound for the time sections of a jointly
measurable difference passes to its time-L² classes. This is the Fubini step
used to turn the particle's per-time diagonal estimate into `SqErr`. -/
theorem fp81s21_TimeL2Rep_SqErr_of_section_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q r : ℝ → Ω → r26t6_Coeff) (Mq Mr a H C : ℝ)
    (U V : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hr : Measurable (Function.uncurry r))
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hU : fp81s21_TimeL2Rep P q Mq a H U)
    (hV : fp81s21_TimeL2Rep P r Mr a H V)
    (hbound : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) H),
      MemLp (fun ω => q (a + t) ω - r (a + t) ω) 2 P ∧
        (∫ ω, ‖q (a + t) ω - r (a + t) ω‖ ^ 2 ∂P) ≤ C) :
    fp81s21_SqErr P U V (Real.sqrt (H * C)) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun z => q (a + z.1) z.2 - r (a + z.1) z.2
  have hg : Measurable g := by
    exact (hq.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)).sub
      (hr.comp ((measurable_const.add measurable_fst).prodMk measurable_snd))
  have hsec : ∀ᵐ t ∂dt,
      MemLp (fun ω => g (t, ω)) 2 P ∧
        (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) ≤ C := by
    filter_upwards [hbound] with t ht
    exact ht
  have hprod := fp81s21_memLp_prod_of_section_bound dt P g hg C hsec
  obtain ⟨W, hWmeas, hWmem, hWeq, hWin⟩ :=
    fp81s21_time_section_exists P H g hg hprod.1
  have hdt : (dt Set.univ).toReal = H := by
    simp [dt, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hH]
  have hWbound : (∫ ω, ‖W ω‖ ^ 2 ∂P) ≤ H * C := by
    rw [hWin]
    calc
      _ ≤ (dt Set.univ).toReal * C := hprod.2
      _ = H * C := by rw [hdt]
  have hEq : (fun ω => U ω - V ω) =ᵐ[P] W := by
    filter_upwards [hU.2.2.2, hV.2.2.2, hWeq] with ω hωU hωV hωW
    apply Lp.ext
    filter_upwards [hωU.2, hωV.2, hωW,
      Lp.coeFn_sub (U ω) (V ω)] with t hUt hVt hWt hsub
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hUt, hVt, hWt]
  have hdiff : MemLp (fun ω => U ω - V ω) 2 P := hU.2.1.sub hV.2.1
  have hdiffInt : Integrable (fun ω => ‖U ω - V ω‖ ^ 2) P :=
    hdiff.integrable_norm_pow (by norm_num)
  have hErrInt : Integrable (fun ω => ‖U ω - V ω‖ ^ 2) P := hdiffInt
  have hErrBound : (∫ ω, ‖U ω - V ω‖ ^ 2 ∂P) ≤ (Real.sqrt (H * C)) ^ 2 := by
    calc
      _ = ∫ ω, ‖W ω‖ ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hEq] with ω hω
        rw [← hω]
      _ ≤ H * C := hWbound
      _ = (Real.sqrt (H * C)) ^ 2 := by
        symm
        exact Real.sq_sqrt (mul_nonneg hH hC)
  exact ⟨hErrInt, hErrBound⟩

#print axioms fp81s21_TimeL2Rep_SqErr_of_section_bound

end HRS.Fp81.S21
end
