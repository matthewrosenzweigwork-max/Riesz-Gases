import HRS.MS.SA12W2O

/-!
# S.A.12 C5 (SA12W2 worker), part P: generator conjugacy (`R26-T5.T05`)

`sa12w2_key`: for `F(x) = u(x/L)` the periodic operator `νΔF + ⟨b,∇F⟩ - 𝒢_L[F]` at `x` is the lift of the unit-torus
`backwardGenerator D₁ ρ u` at `x/L` (`D₁.M = L^{-s-2}M`, `D₁.invβ = ν/L²`, `D₁.V = V(L·)/L²`, `ρ = L^d μ(L·)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12w2_lap_dil {f : Euc d → ℝ} {c : ℝ} (hc : c ≠ 0) (x : Euc d) :
    Laplacian.laplacian (fun y => f (c • y)) x = c ^ 2 * Laplacian.laplacian f (c • x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y => f (c • y))
    (EuclideanSpace.basisFun (Fin d) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [HRS.MS.Ker1.ker1_iteratedFDeriv_comp_smul f hc 2 x, smul_apply,
    smul_eq_mul, Finset.mul_sum]

theorem sa12w2_lap_lift (u : Torus d → ℝ) (y : Euc d) :
    Torus.laplacian u (Torus.mk y) = Laplacian.laplacian (Torus.lift u) y := by
  obtain ⟨m0, hm0⟩ := HRS.KernelAux.rep_mk_eq y
  unfold Torus.laplacian
  rw [hm0, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift u)
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  beta_reduce
  simp only [HRS.KernelGrad.iteratedFDeriv_lift_add]

theorem sa12w2_grad_dil {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) {c : ℝ} (hc : c ≠ 0) (x : Euc d) :
    gradient (fun y => f (c • y)) x = c • gradient f (c • x) := by
  ext j
  rw [sa12v_grad_coord, sa12w2_fderiv_dil hf hc, PiLp.smul_apply, sa12v_grad_coord, smul_eq_mul]

theorem sa12w2_grad_V {V : Euc d → ℝ} (hV : ContDiff ℝ 1 V) {L : ℝ} (hL : 0 < L) (y : Euc d) :
    gradient (fun y => V (L • y) / L ^ 2) y = L⁻¹ • gradient V (L • y) := by
  ext j
  rw [sa12v_grad_coord]
  have : (fun y => V (L • y) / L ^ 2) = fun y => (L ^ 2)⁻¹ * V (L • y) := by funext z; ring
  have hd : DifferentiableAt ℝ (fun y : Euc d => V (L • y)) y :=
    ((hV.differentiable (by simp)).comp (differentiable_id.const_smul L)) y
  rw [this, fderiv_const_mul hd, smul_apply, sa12w2_fderiv_dil hV hL.ne', PiLp.smul_apply, sa12v_grad_coord,
    smul_eq_mul, smul_eq_mul]
  field_simp

theorem sa12w2_eq_of_lift {φ ψ : Torus d → ℝ} (h : Torus.lift φ = Torus.lift ψ) : φ = ψ := by
  funext x
  have := congrFun h (Torus.rep x)
  simpa [Torus.lift, Torus.mk_rep] using this

end HRS.PDE.SA12W2
