import HRS.MS.S111K4R8
import HRS.MS.S111TermAux2

/-!
# S11.1 assembly of the frozen `r2_tensor_relaxation` (S11K4)

The repo already contains `S111t.s111t_tensor_relaxation_of_producers`: clause (a) is the proved `s111x2_clauseA`
(finite covariance, Gaussian window, Poincaré decay), and clause (b) follows from V02 and V01 by T05 and T10.
V02 (`S111tV02`) is closed by `k4_v02_contract` (S11K4).  The only remaining input is V01
(`S111tV01`, Pro `paired_physical_sources`), taken here as the hypothesis `K4V01All`.
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.S111K4
open HRS.Whole HRS.MS.S111T

/-- V01 for all admissible parameters (the only open input of the frozen tensor relaxation). -/
def K4V01All : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (s a β γ T lam : ℝ), 0 ≤ s → s < (d : ℝ) / 2 → 0 < a → 0 < β → 0 ≤ γ →
    0 < T → 0 < lam → S111tV01 d s a β γ T lam

theorem k4_tensor_relaxation_of_V01 (hV01 : K4V01All) :
    type_of% @HRS.Whole.r2_tensor_relaxation := by
  intro d hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam
  exact s111t_tensor_relaxation_of_producers hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam
    (hV01 d hd s a β γ T lam hs0 hs ha hβ hγ hT hlam) (k4_v02_contract hd s hs0 hs a β ha hβ T)

end HRS.MS.S111K4
