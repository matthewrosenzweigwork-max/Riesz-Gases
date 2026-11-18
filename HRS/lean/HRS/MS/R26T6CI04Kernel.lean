import HRS.MS.R26T6CI04KernelAux

/-! R26-T6C.I04: a measurable row-L2 kernel maps L2 into L3. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_kernel_L2_L3 (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (k : Euc d → Euc d → ℝ)
    (hk : Measurable (Function.uncurry k)) (R : Euc d → ℝ)
    (hR : MemLp R 3 mu) (hR0 : ∀ x, 0 ≤ R x)
    (hrow : ∀ x, MemLp (k x) 2 mu ∧ eLpNorm (k x) 2 mu ≤ ENNReal.ofReal (R x))
    (f : Euc d → ℝ) (hf : MemLp f 2 mu) :
    MemLp (fun x => ∫ y, k x y * f y ∂mu) 3 mu ∧
    eLpNorm (fun x => ∫ y, k x y * f y ∂mu) 3 mu ≤
      eLpNorm R 3 mu * eLpNorm f 2 mu := by
  let g : Euc d → ℝ := fun x => ∫ y, k x y * f y ∂mu
  have hfg : AEStronglyMeasurable
      (fun z : Euc d × Euc d => k z.1 z.2 * f z.2) (mu.prod mu) :=
    hk.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd
  have hgm : AEStronglyMeasurable g mu :=
    hfg.integral_prod_right'
  let C : ℝ := (eLpNorm f 2 mu).toReal
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
  have hCf : ENNReal.ofReal C = eLpNorm f 2 mu := ENNReal.ofReal_toReal hf.ne
  have hpoint : ∀ x, ‖g x‖ₑ ≤ ENNReal.ofReal (R x * C) := by
    intro x
    have hh := (r26t6c_kernel_row_holder mu k x (hrow x).1 f hf).2
    calc
      ‖g x‖ₑ ≤ eLpNorm (k x) 2 mu * eLpNorm f 2 mu := hh
      _ ≤ ENNReal.ofReal (R x) * eLpNorm f 2 mu := by
        gcongr
        exact (hrow x).2
      _ = ENNReal.ofReal (R x * C) := by
        rw [← hCf, ENNReal.ofReal_mul (hR0 x)]
  have hnorm : ∀ x, ‖g x‖ ≤ R x * C := by
    intro x
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hpoint x)
    simpa only [toReal_enorm, ENNReal.toReal_ofReal (mul_nonneg (hR0 x) hC0)]
      using hh
  have hdom : eLpNorm g 3 mu ≤ eLpNorm (fun x => R x * C) 3 mu :=
    eLpNorm_mono_ae_real hgm (ae_of_all _ hnorm)
  have hscale : eLpNorm (fun x => R x * C) 3 mu =
      eLpNorm R 3 mu * eLpNorm f 2 mu := by
    have heq : (fun x : Euc d => R x * C) = C • R := by
      funext x
      simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hC0, hCf]
    exact mul_comm _ _
  have hbound := hdom.trans_eq hscale
  have hG : MemLp g 3 mu :=
    hbound.trans_lt (ENNReal.mul_lt_top hR hf)
  exact ⟨hG, hbound⟩

end HRS.MS.R26T6C
