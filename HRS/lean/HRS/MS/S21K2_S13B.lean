import HRS.MS.S21K2_S13A
import HRS.Whole.Round2

/-!
# S21K2 S13B -- the canonically centred pair kernel is in `L²(μ ⊗ μ)` (R26-T3.S13, second step)

For a probability measure `μ` and a kernel `k` with `k ∈ L²(μ ⊗ μ)`, the centred kernel `r2CenterKernel μ k` (defined in
`HRS/Whole/Round2.lean`) is in `L²(μ ⊗ μ)`: it is `k` minus its two marginals plus the total integral.
Helper prefix `s21k2_s13_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory
noncomputable section
namespace HRS.MS.R26T3

theorem s21k2_s13_center_memLp {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {k : HRS.Euc d → HRS.Euc d → ℝ}
    (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) 2 (μ.prod μ)) :
    MemLp (fun z : HRS.Euc d × HRS.Euc d => HRS.Whole.r2CenterKernel μ k z.1 z.2) 2 (μ.prod μ) := by
  have hk' : MemLp (fun z : HRS.Euc d × HRS.Euc d => (fun a b => k b a) z.1 z.2) 2 (μ.prod μ) :=
    hk.comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  have hA : MemLp (fun z : HRS.Euc d × HRS.Euc d => ∫ y, k z.1 y ∂μ) 2 (μ.prod μ) :=
    (s21k2_s13_marg_memLp hk).comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := μ))
  have hB : MemLp (fun z : HRS.Euc d × HRS.Euc d => ∫ x, k x z.2 ∂μ) 2 (μ.prod μ) :=
    (s21k2_s13_marg_memLp (k := fun a b => k b a) hk').comp_measurePreserving
      (measurePreserving_snd (μ := μ) (ν := μ))
  have hC : MemLp (fun _ : HRS.Euc d × HRS.Euc d => ∫ x, ∫ y, k x y ∂μ ∂μ) 2 (μ.prod μ) :=
    memLp_const _
  have h := ((hk.sub hA).sub hB).add hC
  unfold HRS.Whole.r2CenterKernel
  exact h

end HRS.MS.R26T3
