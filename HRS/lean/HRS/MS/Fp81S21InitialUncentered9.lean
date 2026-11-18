import HRS.MS.Fp81S21InitialUncentered7

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS.Whole
open HRS (Euc)

/-- The shifted-log kernel differs from the Riesz kernel by its two one-variable terms. -/
theorem fp81s21_initial_log_kernel_decomp {d : ℕ} (x y : Euc d) :
    HRS.Whole.rieszKernel d 0 (x - y) =
      HRS.MS.Thm.t67K d x y - (1 / 2) * HRS.MS.Thm.t67l x -
        (1 / 2) * HRS.MS.Thm.t67l y - (1 / 2) * Real.log 2 := by
  unfold HRS.MS.Thm.t67K
  ring

/-- The log-case convolution symmetry. The centered generator has zero mean; the
one-variable corrections in the shifted-log kernel therefore cancel exactly. -/
theorem fp81s21_initial_log_kernel_gen_symm
    {d : ℕ} {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {Mg : ℝ}
    (hk : HRS.MS.TcR.TcKer ν (HRS.MS.Thm.t67K d) Mg)
    (hl2 : MemLp (HRS.MS.Thm.t67l : Euc d → ℝ) 2 ν)
    {g : Euc d → ℝ} (hg : Measurable g) (hg2 : MemLp g 2 ν)
    (hmean : ∫ x, g x ∂ν = 0) :
    ∫ x, (∫ y, HRS.Whole.rieszKernel d 0 (x - y) * g y ∂ν) ∂ν =
      ∫ y, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d 0) ν y * g y ∂ν := by
  have h1m : Measurable (fun _ : Euc d => (1 : ℝ)) := measurable_const
  have h12 : MemLp (fun _ : Euc d => (1 : ℝ)) 2 ν := memLp_const 1
  have hlI : Integrable (HRS.MS.Thm.t67l : Euc d → ℝ) ν :=
    hl2.integrable one_le_two
  have hlg : Integrable (fun y => HRS.MS.Thm.t67l y * g y) ν :=
    hl2.integrable_mul hg2
  let c1 : ℝ := (1 / 2) * ∫ y, HRS.MS.Thm.t67l y * g y ∂ν
  have hraw : ∀ᵐ x ∂ν,
      (∫ y, HRS.Whole.rieszKernel d 0 (x - y) * g y ∂ν) =
        HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) g x - c1 := by
    filter_upwards [HRS.MS.TcR.tc2_T_ae_integrable hk hg hg2] with x hx
    have e : ∀ y, HRS.Whole.rieszKernel d 0 (x - y) * g y =
        (HRS.MS.Thm.t67K d x y * g y -
          ((1 / 2) * HRS.MS.Thm.t67l x + (1 / 2) * Real.log 2) * g y) -
            (1 / 2) * (HRS.MS.Thm.t67l y * g y) := by
      intro y
      rw [fp81s21_initial_log_kernel_decomp x y]
      ring
    have i1 : Integrable (fun y => HRS.MS.Thm.t67K d x y * g y -
        ((1 / 2) * HRS.MS.Thm.t67l x + (1 / 2) * Real.log 2) * g y) ν :=
      hx.sub ((hg2.integrable one_le_two).const_mul
        ((1 / 2) * HRS.MS.Thm.t67l x + (1 / 2) * Real.log 2))
    have i2 : Integrable (fun y => (1 / 2 : ℝ) *
        (HRS.MS.Thm.t67l y * g y)) ν := hlg.const_mul _
    simp_rw [e]
    rw [integral_sub i1 i2, integral_sub hx
      ((hg2.integrable one_le_two).const_mul
        ((1 / 2) * HRS.MS.Thm.t67l x + (1 / 2) * Real.log 2)),
      integral_const_mul, integral_const_mul, hmean]
    dsimp [c1]
    unfold HRS.MS.TcR.tc2_T
    ring
  have hrawInt : Integrable
      (fun x => ∫ y, HRS.Whole.rieszKernel d 0 (x - y) * g y ∂ν) ν := by
    have hrawEq : (fun x => HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) g x - c1) =ᵐ[ν]
        (fun x => ∫ y, HRS.Whole.rieszKernel d 0 (x - y) * g y ∂ν) :=
      hraw.mono fun x hx => hx.symm
    exact ((HRS.MS.TcR.tc2_T_memLp hk hg hg2).1.integrable one_le_two
      |>.sub (integrable_const c1)).congr hrawEq
  have hUrow : ∀ᵐ x ∂ν,
      HRS.Whole.convMeasure (HRS.Whole.rieszKernel d 0) ν x =
        HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) (fun _ => (1 : ℝ)) x -
          (1 / 2) * HRS.MS.Thm.t67l x -
          (1 / 2) * ∫ y, HRS.MS.Thm.t67l y ∂ν -
          (1 / 2) * Real.log 2 := by
    filter_upwards [HRS.MS.TcR.tc2_T_ae_integrable hk h1m h12] with x hx
    have e : ∀ y, HRS.Whole.rieszKernel d 0 (x - y) =
        HRS.MS.Thm.t67K d x y * (1 : ℝ) -
          ((1 / 2) * HRS.MS.Thm.t67l x +
            ((1 / 2) * HRS.MS.Thm.t67l y + (1 / 2) * Real.log 2)) := by
      intro y
      rw [fp81s21_initial_log_kernel_decomp x y]
      ring
    have iLog : Integrable (fun y => (1 / 2 : ℝ) * HRS.MS.Thm.t67l y) ν :=
      hlI.const_mul _
    have iConst : Integrable (fun _ : Euc d => (1 / 2 : ℝ) * Real.log 2) ν :=
      integrable_const _
    have iConstX : Integrable (fun _ : Euc d =>
        (1 / 2 : ℝ) * HRS.MS.Thm.t67l x) ν := integrable_const _
    have hcoeff : Integrable (fun y : Euc d =>
        (1 / 2) * HRS.MS.Thm.t67l x +
          ((1 / 2) * HRS.MS.Thm.t67l y + (1 / 2) * Real.log 2)) ν :=
      iConstX.add (iLog.add iConst)
    have i1 : Integrable (fun y => HRS.MS.Thm.t67K d x y * (1 : ℝ) -
        ((1 / 2) * HRS.MS.Thm.t67l x +
          ((1 / 2) * HRS.MS.Thm.t67l y + (1 / 2) * Real.log 2))) ν := hx.sub hcoeff
    calc
      HRS.Whole.convMeasure (HRS.Whole.rieszKernel d 0) ν x =
          ∫ y, HRS.MS.Thm.t67K d x y * (1 : ℝ) -
            ((1 / 2) * HRS.MS.Thm.t67l x +
              ((1 / 2) * HRS.MS.Thm.t67l y + (1 / 2) * Real.log 2)) ∂ν := by
        unfold HRS.Whole.convMeasure
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        change HRS.Whole.rieszKernel d 0 (x - y) = _
        exact e y
      _ = (∫ y, HRS.MS.Thm.t67K d x y * (1 : ℝ) ∂ν) -
            ((1 / 2) * HRS.MS.Thm.t67l x +
              ((1 / 2) * ∫ y, HRS.MS.Thm.t67l y ∂ν +
                (1 / 2) * Real.log 2)) := by
        rw [integral_sub hx hcoeff]
        have hcoeffInt :
            (∫ y, (1 / 2) * HRS.MS.Thm.t67l x +
              ((1 / 2) * HRS.MS.Thm.t67l y + (1 / 2) * Real.log 2) ∂ν) =
              (1 / 2) * HRS.MS.Thm.t67l x +
                ((1 / 2) * ∫ y, HRS.MS.Thm.t67l y ∂ν +
                  (1 / 2) * Real.log 2) := by
          calc
            _ = (∫ y, (1 / 2) * HRS.MS.Thm.t67l x ∂ν) +
                (∫ y, (1 / 2) * HRS.MS.Thm.t67l y +
                  (1 / 2) * Real.log 2 ∂ν) :=
              integral_add iConstX (iLog.add iConst)
            _ = (1 / 2) * HRS.MS.Thm.t67l x +
                ((1 / 2) * ∫ y, HRS.MS.Thm.t67l y ∂ν +
                  (1 / 2) * Real.log 2) := by
              rw [integral_const, integral_add iLog iConst,
                integral_const_mul, integral_const_mul]
              simp
        rw [hcoeffInt]
      _ = HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) (fun _ => (1 : ℝ)) x -
            (1 / 2) * HRS.MS.Thm.t67l x -
            (1 / 2) * ∫ y, HRS.MS.Thm.t67l y ∂ν -
            (1 / 2) * Real.log 2 := by
        unfold HRS.MS.TcR.tc2_T
        ring
  have hsym := HRS.MS.TcR.tc2_T_symm hk hg h1m hg2 h12
  have hTg : Integrable (HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) g) ν :=
    (HRS.MS.TcR.tc2_T_memLp hk hg hg2).1.integrable one_le_two
  have hT1g : Integrable (fun x =>
      HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) (fun _ => (1 : ℝ)) x * g x) ν :=
    (HRS.MS.TcR.tc2_T_memLp hk h1m h12).1.integrable_mul hg2
  have hconst : Integrable (fun x =>
      ((1 / 2) * ∫ y, HRS.MS.Thm.t67l y ∂ν +
        (1 / 2) * Real.log 2) * g x) ν := (hg2.integrable one_le_two).const_mul _
  have hprod : (fun x => HRS.Whole.convMeasure (HRS.Whole.rieszKernel d 0) ν x * g x) =ᵐ[ν]
      fun x => (HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) (fun _ => (1 : ℝ)) x -
        (1 / 2) * HRS.MS.Thm.t67l x -
        (1 / 2) * ∫ y, HRS.MS.Thm.t67l y ∂ν -
        (1 / 2) * Real.log 2) * g x := by
    filter_upwards [hUrow] with x hx
    rw [hx]
  calc
    ∫ x, (∫ y, HRS.Whole.rieszKernel d 0 (x - y) * g y ∂ν) ∂ν =
        ∫ x, HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) g x - c1 ∂ν :=
      integral_congr_ae hraw
    _ = (∫ x, HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) g x ∂ν) - c1 := by
      rw [integral_sub hTg (integrable_const c1), integral_const]
      simp
    _ = (∫ x, g x * HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d)
          (fun _ => (1 : ℝ)) x ∂ν) - c1 := by
      simpa only [mul_one] using congrArg (fun z : ℝ => z - c1) hsym
    _ = ∫ x, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d 0) ν x * g x ∂ν := by
      have hA : Integrable (fun x =>
          HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) (fun _ => (1 : ℝ)) x * g x -
            (1 / 2) * (HRS.MS.Thm.t67l x * g x)) ν :=
        hT1g.sub (hlg.const_mul _)
      have hExp :
          (∫ x, (HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) (fun _ => (1 : ℝ)) x -
            (1 / 2) * HRS.MS.Thm.t67l x -
            (1 / 2) * ∫ y, HRS.MS.Thm.t67l y ∂ν -
            (1 / 2) * Real.log 2) * g x ∂ν) =
          ∫ x, (HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d) (fun _ => (1 : ℝ)) x * g x -
            (1 / 2) * (HRS.MS.Thm.t67l x * g x)) -
            ((1 / 2) * ∫ y, HRS.MS.Thm.t67l y ∂ν +
              (1 / 2) * Real.log 2) * g x ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards with x
        ring
      have hUint := integral_congr_ae hprod
      rw [hUint, hExp, integral_sub hA hconst,
        integral_sub hT1g (hlg.const_mul _), integral_const_mul]
      have hcomm :
          (∫ x, g x * HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d)
            (fun _ => (1 : ℝ)) x ∂ν) =
          ∫ x, HRS.MS.TcR.tc2_T ν (HRS.MS.Thm.t67K d)
            (fun _ => (1 : ℝ)) x * g x ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
      rw [hcomm, integral_const_mul, hmean]
      dsimp [c1]
      ring

#print axioms fp81s21_initial_log_kernel_decomp
#print axioms fp81s21_initial_log_kernel_gen_symm

end HRS.Fp81.S21

end
