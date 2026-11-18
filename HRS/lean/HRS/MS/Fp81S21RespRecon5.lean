import HRS.MS.Fp81S21RespRecon4
import HRS.MS.R26T8AS04a

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter
namespace HRS.Fp81.S21

/-- Interchange a bounded operator and a pointwise integral through L² classes.
The two joint measurability assumptions permit Fubini without selecting a
common null set for the representatives at all times. -/
theorem fp81s21_respRecon_interchange_L2
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (ν : Measure A) [SFinite ν] (μ : Measure X) [IsFiniteMeasure μ]
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : A → Lp ℝ 2 μ) (hV : Integrable V ν)
    (g h : A → X → ℝ)
    (hg : AEStronglyMeasurable (Function.uncurry g) (ν.prod μ))
    (hh : AEStronglyMeasurable (Function.uncurry h) (ν.prod μ))
    (hVg : ∀ᵐ t ∂ν, ⇑(V t) =ᵐ[μ] g t)
    (hTh : ∀ᵐ t ∂ν, ⇑(T (V t)) =ᵐ[μ] h t)
    (hq : MemLp (fun x => ∫ t, g t x ∂ν) 2 μ) :
    ⇑(T (hq.toLp (fun x => ∫ t, g t x ∂ν))) =ᵐ[μ]
      fun x => ∫ t, h t x ∂ν := by
  have hgint := HRS.MS.R26T8A.r26t8a_s04a_integral_ae ν μ V hV g hg hVg
  have hclass : hq.toLp (fun x => ∫ t, g t x ∂ν) = ∫ t, V t ∂ν := by
    apply Lp.ext
    exact hq.coeFn_toLp.trans hgint.symm
  rw [hclass, ← T.integral_comp_comm hV]
  exact HRS.MS.R26T8A.r26t8a_s04a_integral_ae ν μ (fun t => T (V t))
    (T.integrable_comp hV) h hh hTh

#print axioms fp81s21_respRecon_interchange_L2

end HRS.Fp81.S21
end
