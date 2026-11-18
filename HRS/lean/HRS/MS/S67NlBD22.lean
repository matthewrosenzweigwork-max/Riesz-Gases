import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOpAux1
import HRS.MS.MovThermAux2
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD14B
import HRS.MS.S67NlBD21

/-!
# S6.7nl.22: Gaussian multiplier converts the local output to oscillator space

`s67bd_local_gaussian_output`.  Route: packet 21 places the local force in `H^t`, `t = r - (movA - 1)`,
with the stated `H^r + L¹` bound.  The thermal Gaussian derivative bounds of `√ρ₀`
(`mv0_sqrt_gauss_thermal`) make `√ρ₀` a Gaussian-class multiplier (`MovcG`), for which `mo_bridge2`
(packaged as `movc1_B2G`) gives `H^t → Σ^t` with a constant fixed before `h`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

theorem s67bd_local_gaussian_output (H : Mov2dTh d s β q ρ₀) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Euc d → ℝ, ContDiff ℝ 1 h →
      Integrable h volume → HRS.PDE.ToolboxRd.MemSobolev r h → ∀ i : Fin d,
      MemOsc (r - (movA d s - 1)) (fun x => Real.sqrt (ρ₀ x) * s67bd_local d s h i x) ∧
      oscNorm (r - (movA d s - 1))
        (fun x => Real.sqrt (ρ₀ x) * s67bd_local d s h i x) ≤
          C * (s67bd_Hnorm r h + ∫ x, |h x|) := by
  obtain ⟨C21, hC21, h21⟩ := s67bd_local_multiplier H.hd H.hs0 H.hsd r hr
  have hG : HRS.MS.MovC1.MovcG (fun x => Real.sqrt (ρ₀ x)) := by
    obtain ⟨h1, -, c, hc, hk⟩ :=
      HRS.MS.Mov0.mv0_sqrt_gauss_thermal H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
    exact ⟨h1, c, hc, hk⟩
  obtain ⟨CB, hCB, hB⟩ := HRS.MS.MovC1.movc1_B2G hG (r - (movA d s - 1))
  refine ⟨CB * C21, mul_nonneg hCB hC21, fun h hh hI hH i => ?_⟩
  obtain ⟨hm, hn⟩ := h21 h hh hI hH i
  obtain ⟨h1, h2⟩ := hB _ hm
  refine ⟨h1, h2.trans ?_⟩
  unfold s67bd_Hnorm at hn
  calc CB * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r - (movA d s - 1)) (s67bd_local d s h i))
      ≤ CB * (C21 * (s67bd_Hnorm r h + ∫ x, |h x|)) := mul_le_mul_of_nonneg_left hn hCB
    _ = _ := by ring

end HRS.MS.BreakdownS67
