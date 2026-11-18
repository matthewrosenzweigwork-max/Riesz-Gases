import HRS.MH.PairingRdDefs
import HRS.Whole.MovtrAux4

/-!
# PairingRd packet PR6 (`measurable_conv_rd`): measurability of the cancellation convolution

Statement copied verbatim from `HRS/MH/PairingRdSpec.lean`. Route: the jointly measurable integrand
`(x, y) ↦ convInt G h x y` (`Measurable.ite`, `movtr_rieszKernelGrad_measurable`), then
`StronglyMeasurable.integral_prod_right'` (template `HRS.Duality.measurable_conv`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- **PR6** `measurable_conv_rd` (proof). -/
theorem measurable_conv_rd {s : ℝ} {h : Euc d → ℝ} (hh : Measurable h) :
    Measurable (fun x => Whole.convGradConvW (Whole.rieszKernelGrad d s) h x) := by
  have hG : Measurable (fun z : Euc d => Whole.rieszKernelGrad d s z) :=
    Whole.movtr_rieszKernelGrad_measurable s
  have hj : Measurable (fun p : Euc d × Euc d => convInt (Whole.rieszKernelGrad d s) h p.1 p.2) := by
    unfold convInt
    refine Measurable.ite (measurableSet_le (measurable_norm.comp (measurable_fst.sub measurable_snd))
      measurable_const) ?_ ?_
    · exact ((hh.comp measurable_snd).sub (hh.comp measurable_fst)).smul
        (hG.comp (measurable_fst.sub measurable_snd))
    · exact (hh.comp measurable_snd).smul (hG.comp (measurable_fst.sub measurable_snd))
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

end HRS.MH.PairingRdP
