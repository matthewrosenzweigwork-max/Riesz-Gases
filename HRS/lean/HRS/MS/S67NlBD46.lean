import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovThermAux1
import HRS.MS.MovAdjAux1
import HRS.MS.MovAdjAux10
import HRS.MS.S67NlBD13

/-!
# S6.7nl.46: pointwise moving density-gradient product identity
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

/-- The gradient component equals the coordinate derivative. -/
theorem s67bd_grad_comp (u : Euc d → ℝ) (y : Euc d) (j : Fin d) :
    gradient u y j = fderiv ℝ u y (EuclideanSpace.single j 1) := by
  have h : fderiv ℝ u y (EuclideanSpace.single j 1) =
      inner ℝ (gradient u y) (EuclideanSpace.single j 1) := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [h, EuclideanSpace.inner_single_right]
  simp

/-- Algebra for the product rule: with `rho = a^2`, the square-root and logarithm terms cancel. -/
theorem s67bd_alg (a ρx Dρ Du w : ℝ) (ha : 0 < a) (hρ : ρx = a ^ 2) :
    a * Du + w * ((1 / (2 * a)) * Dρ) - (ρx⁻¹ * Dρ) * (a * w) / 2 = a * Du := by
  have := ha.ne'
  subst hρ
  field_simp
  ring

/-- The conjugated gradient of the square-root weighted centred function is `sqrt(rho) D_i u`. -/
theorem s67bd_W_sqrt (ρ : Euc d → ℝ) (hpos : ∀ x, 0 < ρ x) (hdiff : Differentiable ℝ ρ)
    (u : Euc d → ℝ) (hu : Differentiable ℝ u) (i : Fin d) (x : Euc d) :
    s67bd_W ρ i (s67psi ρ u) x = Real.sqrt (ρ x) * s67bd_D i u x := by
  have hη : HasFDerivAt (fun y => Real.sqrt (ρ y))
      ((1 / (2 * Real.sqrt (ρ x))) • fderiv ℝ ρ x) x :=
    (hdiff x).hasFDerivAt.sqrt (hpos x).ne'
  have hlog : HasFDerivAt (fun y => Real.log (ρ y)) ((ρ x)⁻¹ • fderiv ℝ ρ x) x :=
    (hdiff x).hasFDerivAt.log (hpos x).ne'
  have hψ : HasFDerivAt (s67psi ρ u)
      (Real.sqrt (ρ x) • fderiv ℝ u x +
        (u x - ∫ y, u y * ρ y) • ((1 / (2 * Real.sqrt (ρ x))) • fderiv ℝ ρ x)) x :=
    hη.mul ((hu x).hasFDerivAt.sub_const _)
  have e1 : fderiv ℝ (s67psi ρ u) x (EuclideanSpace.single i 1) =
      Real.sqrt (ρ x) * fderiv ℝ u x (EuclideanSpace.single i 1) +
        (u x - ∫ y, u y * ρ y) * ((1 / (2 * Real.sqrt (ρ x))) * fderiv ℝ ρ x (EuclideanSpace.single i 1)) := by
    rw [hψ.fderiv]
    simp [smul_eq_mul]
  have e2 : fderiv ℝ (fun y => Real.log (ρ y)) x (EuclideanSpace.single i 1) =
      (ρ x)⁻¹ * fderiv ℝ ρ x (EuclideanSpace.single i 1) := by
    rw [hlog.fderiv]
    simp [smul_eq_mul]
  have ha2 : ρ x = Real.sqrt (ρ x) ^ 2 := (Real.sq_sqrt (hpos x).le).symm
  have ha0 : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hpos x)
  have e3 : s67psi ρ u x = Real.sqrt (ρ x) * (u x - ∫ y, u y * ρ y) := rfl
  unfold s67bd_W s67bd_D
  rw [e1, e2, e3]
  exact s67bd_alg _ _ _ _ _ ha0 ha2

/-- Pointwise product identity: `rho_r D_i u = (sqrt(rho0) + movV) * W_i(psi)`. -/
theorem s67bd_J_pointwise (ρ : ℝ → Euc d → ℝ) (r : ℝ) (hpos : ∀ x, 0 < ρ₀ x)
    (hdiff : Differentiable ℝ ρ₀) (u : Euc d → ℝ) (hu : Differentiable ℝ u)
    (i : Fin d) (x : Euc d) :
    ρ r x * s67bd_D i u x =
      (Real.sqrt (ρ₀ x) + movV ρ₀ ρ r x) * s67bd_W ρ₀ i (s67psi ρ₀ u) x := by
  rw [s67bd_W_sqrt ρ₀ hpos hdiff u hu i x]
  unfold movV
  have ha0 : 0 < Real.sqrt (ρ₀ x) := Real.sqrt_pos.2 (hpos x)
  have key : (Real.sqrt (ρ₀ x) + (ρ r x - ρ₀ x) / Real.sqrt (ρ₀ x)) *
      (Real.sqrt (ρ₀ x) * s67bd_D i u x) =
      (Real.sqrt (ρ₀ x) ^ 2 + (ρ r x - ρ₀ x)) * s67bd_D i u x := by
    field_simp
  rw [key, Real.sq_sqrt (hpos x).le]
  ring

/-- S6.7nl.46: the pointwise density-gradient identity and its summed form for the actual `s67J`. -/
theorem s67bd_J_identity (H : Mov2dTh d s β q ρ₀)
    (ρ : ℝ → Euc d → ℝ) (r : ℝ) (u : Euc d → ℝ) (hu : ContDiff ℝ 1 u) :
    (∀ i : Fin d, ∀ x : Euc d, ρ r x * s67bd_D i u x =
      (Real.sqrt (ρ₀ x) + movV ρ₀ ρ r x) * s67bd_W ρ₀ i (s67psi ρ₀ u) x) ∧
    ∀ x : Euc d, s67J d s (ρ r) u x =
      ∑ i : Fin d, movForce d s
        (fun y => (Real.sqrt (ρ₀ y) + movV ρ₀ ρ r y) * s67bd_W ρ₀ i (s67psi ρ₀ u) y) x i := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hpos : ∀ x, 0 < ρ₀ x := hR.pos
  have hdiff : Differentiable ℝ ρ₀ := hR.smooth.differentiable (by simp)
  have hud : Differentiable ℝ u := hu.differentiable (by simp)
  refine ⟨fun i x => s67bd_J_pointwise ρ r hpos hdiff u hud i x, fun x => ?_⟩
  unfold s67J movForce
  refine Finset.sum_congr rfl fun j _ => ?_
  have hF : (fun y => ρ r y * (gradient u y) j) =
      (fun y => (Real.sqrt (ρ₀ y) + movV ρ₀ ρ r y) * s67bd_W ρ₀ j (s67psi ρ₀ u) y) := by
    funext y
    rw [s67bd_grad_comp u y j]
    exact s67bd_J_pointwise ρ r hpos hdiff u hud j y
  rw [hF]

end HRS.MS.BreakdownS67
