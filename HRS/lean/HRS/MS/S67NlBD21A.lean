import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD03

/-!
# S6.7nl.21A: classical derivative identified by compact-test weak integration by parts
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

/-- Weak derivative of `h` in coordinate `i` equal to `v`: compact-test integrability and the signed identity. -/
def s67bd_WeakDerivative (i : Fin d) (h v : Euc d → ℝ) : Prop :=
  ∀ φ : Euc d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    Integrable (fun x => h x * s67bd_D i φ x) volume ∧
    Integrable (fun x => v x * φ x) volume ∧
    (∫ x, h x * s67bd_D i φ x) = -(∫ x, v x * φ x)

/-- Product of a continuous function with a continuous compactly supported function is integrable. -/
theorem s67bd_wd_int {u ψ : Euc d → ℝ} (hu : Continuous u) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) : Integrable (fun x => u x * ψ x) volume :=
  Continuous.integrable_of_hasCompactSupport (hu.mul hψ) hc.mul_left

/-- S6.7nl.21A: the classical derivative of a `C^1` function is its weak derivative. -/
theorem s67bd_classical_weak_derivative (d : ℕ) (h : Euc d → ℝ)
    (hh : ContDiff ℝ 1 h) :
    ∀ i : Fin d, s67bd_WeakDerivative i h (s67bd_D i h) := by
  intro i φ hφ hc
  have hφc : Continuous φ := hφ.continuous
  have hhc : Continuous h := hh.continuous
  have hDφc : Continuous (fun x => s67bd_D i φ x) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDφcs : HasCompactSupport (fun x => s67bd_D i φ x) :=
    hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hDhc : Continuous (fun x => s67bd_D i h x) :=
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have I1 : Integrable (fun x => h x * s67bd_D i φ x) volume :=
    s67bd_wd_int hhc hDφc hDφcs
  have I2 : Integrable (fun x => s67bd_D i h x * φ x) volume :=
    s67bd_wd_int hDhc hφc hc
  have I3 : Integrable (fun x => h x * φ x) volume :=
    s67bd_wd_int hhc hφc hc
  refine ⟨I1, I2, ?_⟩
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := EuclideanSpace.single i 1)
    I2 I1 I3
    (fun x _ => hh.differentiable (by simp) x)
    (fun x _ => hφ.differentiable (by simp) x)
  exact hIBP

end HRS.MS.BreakdownS67
