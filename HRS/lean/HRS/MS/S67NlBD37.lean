import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovLinAux15
import HRS.MS.S67NlBD00
import HRS.MS.S67NlBD33
import HRS.MS.S67NlBD34
import HRS.MS.S67NlBD35
import HRS.MS.S67NlBD36

/-!
# S6.7 nonlinear, packet S6.7nl.37: finite-horizon source convolution gains less than two orders

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4764-4771, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). No owned definitions.
Route: take the constant and the lifted-integral bounds from `s67bd_lift_integrable`; the
off-diagonal memberships from `s67bd_lift_measurable`; the higher representative and L^2
compatibility from `s67bd_lift_compatibility`. The higher representative of the integral is the
integral of the lift (`movlin_memOsc_of_lev`), whose norm is bounded by the integral of the lifted
norms, hence by `C * B`.
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

theorem s67bd_convolution_gain (H : Mov2dTh d s β q ρ₀)
    (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x))
    (p qlev T : ℝ) (hp : 0 ≤ p) (hpq : p ≤ qlev) (hgain : qlev - p < 2)
    (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 0 ≤ B → ∀ h : ℝ → MovL2Zero ρ₀,
      ContinuousOn h (Icc (0 : ℝ) T) →
      (∀ v ∈ Icc (0 : ℝ) T, MemOsc p (movFun (h v)) ∧ oscNorm p (movFun (h v)) ≤ B) →
      ∀ r ∈ Icc (0 : ℝ) T,
        MemOsc qlev (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v))) ∧
        oscNorm qlev (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v))) ≤ C * B := by
  obtain ⟨C, hC, hint⟩ := s67bd_lift_integrable H g hg p qlev T hp hpq hgain hT
  refine ⟨C, hC, fun B hB h hc hbd r hr => ?_⟩
  obtain ⟨hI, hnorm, hL⟩ := hint B hB h hc hbd r hr
  have hm0 : ∀ v ∈ Icc (0 : ℝ) T, MemOsc p (movFun (h v)) := fun v hv => (hbd v hv).1
  obtain ⟨hm, -⟩ := s67bd_lift_measurable H g hg p qlev T hp hpq hgain hT h hc hm0 r hr
  obtain ⟨hcomp1, hcomp2⟩ :=
    s67bd_lift_compatibility H g hg qlev r T (by linarith) hr.2 h hm hI hL
  have hf : MemLp (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v)))
      2 (volume : Measure (Euc d)) := Lp.memLp _
  have hcoe : (∫ v in Icc r T, ((s67bd_Tdag H g hg (v - r) (h v) : MovL2Zero ρ₀) :
      Lp ℝ 2 (volume : Measure (Euc d)))) =
      ((∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v) : MovL2Zero ρ₀) :
        Lp ℝ 2 (volume : Measure (Euc d))) :=
    (MovL2Zero ρ₀).subtypeL.integral_comp_comm hL
  have hz : mov2d_j (le_trans hp hpq) (∫ v in Icc r T, s67bd_lift H g hg qlev r h v) =
      OscSpace.ofFun 0 (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v))) := by
    apply (mov2d_Phi d).injective
    rw [hcomp1, mov2d_Phi_ofFun hf, hcoe]
    exact (Lp.toLp_coeFn _ hf).symm
  obtain ⟨-, hofs⟩ := movlin_memOsc_of_lev (le_trans hp hpq) hf hz
  refine ⟨hcomp2, ?_⟩
  rw [← OscSpace.norm_ofFun (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (h v))) hcomp2, hofs]
  exact (norm_integral_le_integral_norm _).trans hnorm
