import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie

/-!
# S6.7nl.00: constructed stationary semigroup, uniqueness agreement, adjoint smoothing
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
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

/-- The actual Hilbert adjoint of the constructed semigroup. -/
def s67bd_Tdag (H : Mov2dTh d s β q ρ₀) (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x)) (t : ℝ) :
    MovL2Zero ρ₀ →L[ℝ] MovL2Zero ρ₀ :=
  ContinuousLinearMap.adjoint (mov2d_T H g hg t)

set_option maxHeartbeats 1600000 in
/-- S6.7nl.00: existence, uniqueness agreement and adjoint smoothing for the constructed semigroup. -/
theorem s67bd_semigroup_data (H : Mov2dTh d s β q ρ₀)
    (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x)) :
    MovIsSemigroup d s β ρ₀ (mov2d_T H g hg) ∧
    (∀ S : ℝ → (MovL2Zero ρ₀ →L[ℝ] MovL2Zero ρ₀),
      MovIsSemigroup d s β ρ₀ S → ∀ t : ℝ, 0 ≤ t → S t = mov2d_T H g hg t) ∧
    HsOK (s67bd_Tdag H g hg) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ σ : ℝ, movA d s ≤ σ → ∃ C : ℝ, 1 ≤ C ∧
      MovSmoothingBounds d s ρ₀ σ c C (s67bd_Tdag H g hg) := by
  -- Smoothing bounds depend only on the values at nonnegative times.
  have transp : ∀ (U V : ℝ → (MovL2Zero ρ₀ →L[ℝ] MovL2Zero ρ₀)) (σ' C' c' : ℝ),
      (∀ t : ℝ, 0 ≤ t → U t = V t) →
      MovSmoothingBounds d s ρ₀ σ' c' C' U → MovSmoothingBounds d s ρ₀ σ' c' C' V := by
    intro U V σ' C' c' h hb
    obtain ⟨h1, h2⟩ := hb
    refine ⟨fun t ht v hv => ?_, fun t ht v hv => ?_⟩
    · have key := h1 t ht v hv
      rw [h t ht] at key
      exact key
    · have key := h2 t ht v hv
      rw [h t ht.le] at key
      exact key
  obtain ⟨T, hT, -, c, hc, hsm⟩ :=
    mov_linear_proof H.hd H.hs0 H.hsd β q H.hβ H.hq ρ₀ H.hρ
  have hTg : ∀ t : ℝ, 0 ≤ t → T t = mov2d_T H g hg t :=
    fun t ht => movlin_uniq H g hg hT ht
  have hadj : ∀ t : ℝ, 0 ≤ t →
      ContinuousLinearMap.adjoint (T t) = s67bd_Tdag H g hg t := by
    intro t ht
    unfold s67bd_Tdag
    rw [hTg t ht]
  refine ⟨mov2d_isSemigroup H g hg,
    fun S hS t ht => movlin_uniq H g hg hS ht,
    movlin_Hs_adj H g hg, c, hc, fun σ hσ => ?_⟩
  obtain ⟨C, -, hC2⟩ := hsm σ hσ
  exact ⟨max 1 C, le_max_left _ _,
    transp (fun t => ContinuousLinearMap.adjoint (T t)) (s67bd_Tdag H g hg) σ (max 1 C) c hadj
      (movlin_smoothing_mono (le_max_right _ _) hC2)⟩

end HRS.MS.BreakdownS67
