import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD14B
import HRS.MS.S67NlBD15E
import HRS.MS.S67NlBD21A
import HRS.MS.S67NlBD21B
import HRS.MS.S67NlBD21C
import HRS.MS.S67NlBD21D

/-!
# S6.7nl.21: local force Sobolev multiplier on actual C1 sources
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Aggregate of the producer packets 21A-21D; the proof body is the existing glue.
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

/-- S6.7nl.21: the local force is bounded in the Sobolev norm of order `r - (movA - 1)`. -/
theorem s67bd_local_multiplier (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Euc d → ℝ, ContDiff ℝ 1 h →
      Integrable h volume → HRS.PDE.ToolboxRd.MemSobolev r h → ∀ i : Fin d,
      HRS.PDE.ToolboxRd.MemSobolev (r - (movA d s - 1)) (s67bd_local d s h i) ∧
      s67bd_Hnorm (r - (movA d s - 1)) (s67bd_local d s h i) ≤
        C * (s67bd_Hnorm r h + ∫ x, |h x|) := by
  obtain ⟨Cd, hCd, hder⟩ := s67bd_weak_derivative_sobolev d r hr
  obtain ⟨Cg, hCg, hgain⟩ := s67bd_local_convolution_gain hd hs0 hsd r hr
  refine ⟨Cg * Cd, mul_nonneg hCg hCd, fun h hh hI hH i => ?_⟩
  have hdc : Continuous (s67bd_D i h) :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdH := hder h (s67bd_D i h) i hH hdc (s67bd_classical_weak_derivative d h hh i)
  have hg := hgain h hh hI i hdH.1
  have hl := s67bd_local_loss_conversion hd hs0 hsd r hr _ hg.1
  refine ⟨hl.1, hl.2.trans (hg.2.trans ?_)⟩
  calc Cg * s67bd_Hnorm (r - 1) (s67bd_D i h)
      ≤ Cg * (Cd * s67bd_Hnorm r h) := mul_le_mul_of_nonneg_left hdH.2 hCg
    _ = (Cg * Cd) * s67bd_Hnorm r h := (mul_assoc _ _ _).symm
    _ ≤ (Cg * Cd) * (s67bd_Hnorm r h + ∫ x, |h x|) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (integral_nonneg (fun x => abs_nonneg (h x))))
        (mul_nonneg hCg hCd)

end HRS.MS.BreakdownS67
