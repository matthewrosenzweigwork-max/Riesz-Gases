import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD62
import HRS.MS.S67NlBD63
import HRS.MS.S67NlBD65

/-!
# S6.7nl.64: finite global gradient norm of the classical adjoint solution
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: packet 63 gives the reversed parabolic data of `u(τ) = f(T - τ)` with finite coefficient bounds;
packet 62 (`ν = β⁻¹ > 0`) gives the finite `cb` gradient norm for every reversed time; the terminal
datum `u 0 = φ` carries the assumed finite gradient norm, and `Y` (packet 65) is the real part.
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

theorem s67bd_classical_cb_finite (H : Mov2dTh d s β q ρ₀)
    (j M m : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M)
    (hm : (d : ℝ) / 2 + 7 < m) (hmM : (M : ℝ) + 4 < m)
    (R0 c0 : ℝ) (hR0 : 0 ≤ R0) (hR1 : R0 ≤ 1) (hc0 : 0 ≤ c0)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f)
    (hφreg : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ)
    (hφ : MemOsc (M : ℝ) (s67psi ρ₀ φ))
    (hφfin : cbNormVecE j (fun x => gradient φ x) < ⊤) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc (0 : ℝ) T,
      cbNormVecE j (fun x => gradient (f r) x) < ⊤ ∧ s67bd_Y j f r ≤ B := by
  obtain ⟨hPD, hreg, Mb, MJ, hMb0, hMJ0, hBb, hJb⟩ :=
    s67bd_classical_parabolic_data H j M m hM hm hmM R0 c0 hR0 hR1 hc0 f0 ρ hρ T φ f hT hf hφ
  have hinit : cbNormVecE j (fun x => gradient
      ((fun τ x => f (T - τ) x) 0 : Euc d → ℝ) x) < ⊤ := by
    have e : ((fun τ x => f (T - τ) x) 0 : Euc d → ℝ) = φ := by
      funext x; show f (T - 0) x = φ x
      rw [sub_zero]; exact congrFun hf.terminal x
    rw [e]; exact hφfin
  obtain ⟨C, hC0, hC⟩ := s67bd_parabolic_finite d j β⁻¹ q T Mb MJ (inv_pos.2 H.hβ) H.hq hT hMb0 hMJ0
    _ _ _ _ hPD (fun t ht => ⟨(hBb t ht).1, (hBb t ht).2⟩) hJb hreg hinit
  refine ⟨C, hC0, fun r hr => ?_⟩
  have hmem : T - r ∈ Icc (0 : ℝ) T := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  obtain ⟨h1, h2⟩ := hC (T - r) hmem
  have e : (fun x => f (T - (T - r)) x) = f r := by
    funext x; rw [sub_sub_cancel]
  simp only [e] at h1 h2
  exact ⟨h1, ENNReal.toReal_le_of_le_ofReal hC0 h2⟩

end HRS.MS.BreakdownS67
