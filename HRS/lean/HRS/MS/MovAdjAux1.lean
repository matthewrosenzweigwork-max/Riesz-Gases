import HRS.MS.MovLinTie
import HRS.MS.Mov63Aux3
import HRS.MS.PoisHighAux3
import HRS.MH.DualityRdDefs

/-!
# S6.7 `mov_global_adjoint_stationary` / `mov_global_adjoint_nonlinear`: PLAN (packet P0) and basic lemmas

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement rows `S:W:lem:r2mov-global-adjoint`
(`HRS.Whole.mov_global_adjoint_stationary`, `HRS.Whole.mov_global_adjoint_nonlinear`, `HRS/Whole/MovingDyn.lean`).
The relevant part of the plan is given below.

## Verdict on the statements

Both frozen statements are TRUE and NON-VACUOUS (classical adjoint solutions exist: `ul_adjoint_fixed_viscosity_proof`),
and no junk value changes their meaning:
* `∫ y, φ y * ρ₀ y` is the honest mean: if `φ ρ₀ ∉ L¹` the integral is `0`, `MemOsc` gives `√ρ₀ φ ∈ L²`, hence
  `φ ρ₀ = √ρ₀ (√ρ₀ φ) ∈ L¹` (`√ρ₀ ∈ L²`): contradiction.  `ψ_t = √ρ₀ Πφ ∈ L²_0`.
* `oscNorm` is guarded by `MemOsc`; `cbNormVecE` is `⊤` when a derivative of `∇φ` is unbounded (then the right side is `⊤`
  because `C > 0`, and only `ContDiff ℝ j (∇ f r)` has content).  `C ≥ 1` is needed at `r = t`.
* `φ = f t` is bounded with bounded `∇φ, ∇²φ` (field `bdd` of `IsClassicalAdjointW` at `r = t`); `t = 0` is trivial.
* The nonlinear row also needs the constants `ε_*, r` of S6.3 SHRUNK (allowed: they are existentially quantified).

## Route for the stationary row (`ν = β⁻¹`, `b = -(qx + F_*) = ν∇log ρ₀`, `𝓛 u = νΔu + b·∇u + J u`)

* Step A (bridge): `ψ_r = √ρ₀ (f_r - ∫ f_r ρ₀) = T(t-r)† ψ_t` in `L²_0`: `g(σ) = ⟨f_{r+σ}√ρ₀, T(σ)v₀⟩` is constant (right derivative `0`),
  by the duality identity `∫ (𝓛 u) √ρ₀ φ = -∫ u √ρ₀ S φ` (`u ∈ C_b²`, `φ` Schwartz) and `mov2d_T_core/gen`.  Then the merged S6.2 bounds give `ψ_r ∈ Σ^M`
  with `‖ψ_r‖_{Σ^M} ≤ C e^{-c(t-r)}‖ψ_t‖_{Σ^M}` and `f_r = c_r + ψ_r/√ρ₀ ∈ C^{j+5}`.
* Step B: `J f_r ∈ C_b^{j+1}`, `‖J f_r‖ ≤ C ‖ψ_r‖_{Σ^M}` (`mov_operators_force_gen` for `w_k = √ρ₀ ∂_k f_r = ∂_kψ - ½ψ ∂_k log ρ₀`).
* Step C: Duhamel `f_r = P_{t-r} φ + ∫_r^t P_{v-r} J f_v dv` with the POIS semigroup (`pois_shorttime`, `pois_longtime`), derivative bounds, convolution.
* Step D: assembly and `type_of%` tie (`MovAdjTie`).

## This file

* `s67_norm_iter_grad`: `‖D^i (∇u)(x)‖ = ‖D^{i+1} u(x)‖`;
* `s67J`: the nonlocal term `J u = ∑_j (convGradConvW ∇g (ρ ∂_j u))_j`;
* `s67_gen_eq`: `generatorW` of the stationary coefficient of `quadraticGradientDyn` is `νΔu + ⟨-qx - F_*, ∇u⟩ + J u`;
* `s67_drift_eq`: `-qx - F_* = ν ∇log ρ₀` (Euler equation).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd

variable {d : ℕ}

/-! ### Gradient and iterated derivatives -/

/-- `‖D^i (∇u)(x)‖ = ‖D^{i+1} u(x)‖` for `u ∈ C^{i+1}`. -/
theorem s67_norm_iter_grad {u : Euc d → ℝ} {i : ℕ} (hu : ContDiff ℝ ((i + 1 : ℕ) : WithTop ℕ∞) u)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ i (fun y => gradient u y) x‖ = ‖iteratedFDeriv ℝ (i + 1) u x‖ := by
  have e : (fun y => gradient u y) = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ u := by
    funext y; rfl
  rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

/-! ### The generator of the stationary coefficient -/

/-- The nonlocal term `J u = ∑_j (∇g ⋆ (ρ ∂_j u))_j` (cancellation convention). -/
def s67J (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun y => ρ y * (gradient u y) j) x) j

theorem s67_matVec_neg_one (y : Euc d) :
    Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose y = -y := by
  simp [Torus.matVec]

theorem s67_conv_neg (G : Euc d → Euc d) (h : Euc d → ℝ) (x : Euc d) :
    convGradConvW G (fun y => -h y) x = -convGradConvW G h x := by
  unfold convGradConvW
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : ‖x - y‖ ≤ 1 / 4
  · simp only [hy, if_true]
    rw [← neg_smul]
    congr 1; ring
  · simp only [hy, if_false]
    rw [← neg_smul]

theorem s67_nlTerm_eq (s q β : ℝ) (ρ u : Euc d → ℝ) (x : Euc d) :
    nlTermRd (quadraticGradientDyn d s q β) ρ u x = -s67J d s ρ u x := by
  unfold nlTermRd s67J
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hM : ∀ y : Euc d, Torus.matVec (quadraticGradientDyn d s q β).M.transpose y = -y := by
    intro y
    have : (quadraticGradientDyn d s q β).M = -1 := rfl
    rw [this]
    exact s67_matVec_neg_one y
  have e : (fun y => ρ y * (Torus.matVec (quadraticGradientDyn d s q β).M.transpose (gradient u y)) j) =
      fun y => -(ρ y * (gradient u y) j) := by
    funext y
    rw [hM]; simp
  rw [e, s67_conv_neg]
  simp
  rfl

/-- **The generator of the stationary coefficient.** -/
theorem s67_gen_eq (s q β : ℝ) (ρ : Euc d → ℝ) (r : ℝ) (u : Euc d → ℝ) (x : Euc d) :
    generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) r u x =
      β⁻¹ * Laplacian.laplacian u x +
        inner ℝ (-(q • x) - movForce d s ρ x) (gradient u x) + s67J d s ρ u x := by
  rw [generatorW_coeff, s67_nlTerm_eq]
  have hM : ∀ y : Euc d, Torus.matVec (quadraticGradientDyn d s q β).M y = -y := by
    intro y
    have : (quadraticGradientDyn d s q β).M = -1 := rfl
    rw [this]
    simp [Torus.matVec]
  have hdr : meanFieldDriftW (quadraticGradientDyn d s q β) ρ x = -(q • x) - movForce d s ρ x := by
    unfold meanFieldDriftW
    rw [hM]
    have hV : gradient (quadraticGradientDyn d s q β).V x = q • x := movtr_gradient_confinement q x
    rw [hV]
    have : (quadraticGradientDyn d s q β).s = s := rfl
    rw [this]
    unfold movForce
    abel
  rw [hdr]
  show β⁻¹ * _ + _ - -s67J d s ρ u x = _
  ring

/-- The Euler equation in the form `-qx - F_* = β⁻¹ ∇log ρ₀`. -/
theorem s67_drift_eq (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hb : 0 < β)
    {ρ : Euc d → ℝ} (h : IsThermalEquilibrium d s q β ρ) (x : Euc d) :
    -(q • x) - movForce d s ρ x = β⁻¹ • gradient (fun y => Real.log (ρ y)) x := by
  have := HRS.MS.Mov0.mv0_thermal_force hd hs0 hsd hq hb h x
  unfold movForce
  have h2 : -(q • x) - convGradConvW (rieszKernelGrad d s) ρ x =
      β⁻¹ • gradient (fun y => Real.log (ρ y)) x ↔
      β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + convGradConvW (rieszKernelGrad d s) ρ x = 0 := by
    constructor
    · intro h3; rw [← h3]; abel
    · intro h3
      have : β⁻¹ • gradient (fun y => Real.log (ρ y)) x =
          -(q • x) - convGradConvW (rieszKernelGrad d s) ρ x := by
        rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← h3]; abel
      exact this.symm
  exact h2.2 this

end HRS.MS.MovAdj
