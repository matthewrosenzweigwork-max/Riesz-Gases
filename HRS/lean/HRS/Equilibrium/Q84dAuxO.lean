/-
# HRS.Equilibrium.Q84dAuxO — packet Q84d: calculus along coordinate lines (single-particle pieces)
-/
import HRS.Equilibrium.Q84dAuxN

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_slice_eq (f : Torus d → ℝ) (x : Torus d) :
    (fun u : Euc d => f (x + Torus.mk u)) = fun u => Torus.lift f (Torus.rep x + u) := by
  funext u
  simp [Torus.lift, Function.comp, Q84a.q84a_mk_add, Torus.mk_rep]

theorem q84d_fderiv_slice (f : Torus d → ℝ) (x : Torus d) :
    fderiv ℝ (fun u : Euc d => f (x + Torus.mk u)) 0 = fderiv ℝ (Torus.lift f) (Torus.rep x) := by
  rw [q84d_slice_eq]
  have := fderiv_comp_add_left (𝕜 := ℝ) (f := Torus.lift f) (Torus.rep x) (x := (0 : Euc d))
  simpa using this

theorem q84d_slice_grad_comp (f : Torus d → ℝ) (x : Torus d) (k : Fin d) :
    fderiv ℝ (fun u : Euc d => f (x + Torus.mk u)) 0 (ek k) = (Torus.grad f x) k := by
  rw [q84d_fderiv_slice]
  unfold Torus.grad gradient
  rw [q84d_toDual_symm_apply]

theorem q84d_slice_lap (f : Torus d → ℝ) (x : Torus d) :
    Laplacian.laplacian (fun u : Euc d => f (x + Torus.mk u)) 0 = Torus.laplacian f x := by
  rw [q84d_slice_eq]
  unfold Torus.laplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_comp_add_left]
  simp

/-- Derivative of the Riesz kernel along a coordinate line through `z ≠ 0`. -/
theorem q84d_g_line_deriv (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {z : Torus d} (hz : z ≠ 0)
    (k : Fin d) (c : ℝ) :
    HasDerivAt (fun τ : ℝ => periodicRiesz d s (z + Torus.mk ((c * τ) • ek k)))
      (c * (periodicRieszGrad d s z) k) 0 := by
  have hz' : Torus.mk (Torus.rep z) ≠ 0 := by rw [Torus.mk_rep]; exact hz
  have hG := periodicRieszGrad_hasGradientAt hd hs0 hsd (s := s) (Torus.rep z) hz'
  rw [Torus.mk_rep] at hG
  have hF := hG.hasFDerivAt
  have hline : HasDerivAt (fun τ : ℝ => Torus.rep z + (c * τ) • ek k) (c • ek k) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => (c * τ) • ek k) (c • ek k) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_mul c).smul_const (ek k)
      simpa using this
    exact h1.const_add (Torus.rep z)
  have hF' : HasFDerivAt (Torus.lift (periodicRiesz d s))
      ((InnerProductSpace.toDual ℝ (Euc d)) (periodicRieszGrad d s z))
      (Torus.rep z + (c * 0) • ek k) := by simpa using hF
  have hcomp := hF'.comp_hasDerivAt (0 : ℝ) hline
  have e : (fun τ : ℝ => periodicRiesz d s (z + Torus.mk ((c * τ) • ek k))) =
      (Torus.lift (periodicRiesz d s)) ∘ fun τ : ℝ => Torus.rep z + (c * τ) • ek k := by
    funext τ
    simp [Torus.lift, Function.comp, Q84a.q84a_mk_add, Torus.mk_rep]
  rw [e]
  convert hcomp using 1
  rw [InnerProductSpace.toDual_apply_apply, inner_smul_right, ek, EuclideanSpace.inner_single_right]
  simp [mul_comm]

end HRS.Q84d

end
