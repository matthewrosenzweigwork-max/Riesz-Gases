import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovThermAux1
import HRS.MS.MovThermAux2

/-!
# S6.7 nonlinear, packet S6.7nl.40: qualitative regularity of the actual continuous representative

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4811-4819, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
The representative embedding `HRS.MS.Mov63.mn_sobolev_emb_gen` is applied at order `j + 5`;
the continuous representative is identified everywhere, and `u` is recovered by dividing by the
positive thermal square root `sqrt (rho0)`.
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

/-- **`s67bd_qualitative_regular`.** For a thermal solution `ρ₀` and a `C²` amplitude `u` with
`s67psi ρ₀ u` in the oscillator class of index `M > d/2 + j + 5`, the function `u`, the weighted
function `s67psi ρ₀ u`, and the gradient of `u` are regular of the stated classes. -/
theorem s67bd_qualitative_regular (H : Mov2dTh d s β q ρ₀)
    (j M : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M)
    (u : Euc d → ℝ) (hu : ContDiff ℝ 2 u)
    (hm : MemOsc (M : ℝ) (s67psi ρ₀ u)) :
    ContDiff ℝ ((j + 5 : ℕ) : WithTop ℕ∞) u ∧
    ContDiff ℝ ((j + 5 : ℕ) : WithTop ℕ∞) (s67psi ρ₀ u) ∧
    ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient u x) := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hpos : ∀ x, 0 < ρ₀ x := hR.pos
  have hsqrt : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ₀ x)) :=
    (HRS.MS.Mov0.mv0_sqrt_gauss (mul_pos H.hβ H.hq) hR).1
  have hcf : Continuous (s67psi ρ₀ u) := by
    unfold s67psi
    exact hsqrt.continuous.mul (hu.continuous.sub continuous_const)
  obtain ⟨C, -, hemb⟩ := HRS.MS.Mov63.mn_sobolev_emb_gen (d := d) (j + 5) M
    (by push_cast; linarith)
  obtain ⟨g, hg, hfg, -⟩ := hemb (s67psi ρ₀ u) hm
  have hfeq : s67psi ρ₀ u = g := HRS.MS.Mov63.mn_ae_eq_cont hcf hg.continuous hfg
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = ∫ y, u y * ρ₀ y := ⟨_, rfl⟩
  have key : ∀ x, u x = g x / Real.sqrt (ρ₀ x) + m := by
    intro x
    have h1 : Real.sqrt (ρ₀ x) * (u x - m) = g x := by
      have h0 := congrFun hfeq x
      unfold s67psi at h0
      rw [hm_def]
      exact h0
    have hs : Real.sqrt (ρ₀ x) ≠ 0 := (Real.sqrt_pos.2 (hpos x)).ne'
    rw [← h1, mul_div_cancel_left₀ _ hs]
    ring
  have hueq : u = fun x => g x / Real.sqrt (ρ₀ x) + m := funext key
  have hsqrt_j : ContDiff ℝ ((j + 5 : ℕ) : WithTop ℕ∞) (fun x => Real.sqrt (ρ₀ x)) :=
    hsqrt.of_le (by first | exact WithTop.coe_le_coe.2 le_top | (simp; done) | (norm_cast; done))
  have hdiv : ContDiff ℝ ((j + 5 : ℕ) : WithTop ℕ∞) (fun x => g x / Real.sqrt (ρ₀ x)) :=
    hg.div hsqrt_j (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  have hcu : ContDiff ℝ ((j + 5 : ℕ) : WithTop ℕ∞) u := by
    rw [hueq]
    exact hdiv.add contDiff_const
  refine ⟨hcu, ?_, ?_⟩
  · rw [hfeq]
    exact hg
  · unfold gradient
    exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv.contDiff).comp
      (hcu.fderiv_right (m := j) (by exact_mod_cast (show j + 1 ≤ j + 5 by omega)))

end HRS.MS.BreakdownS67

end
