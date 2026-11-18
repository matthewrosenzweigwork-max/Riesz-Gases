import HRS.Dynamics.Setup
import HRS.PDE.Fourier
import HRS.Kernel.GradConv

/-!
# Torus PDE layer II: torus metric notions, the `s ≥ d-1` proviso, and the kernel inputs
linking the cancellation convention with the Fourier representation

Sources (HRS periodic main paper):
* `B:eq:nabla-g-convolution` (lines 10091–10101): for `d-1 ≤ s < d` the force is defined for
  `μ ∈ C^{0,α}`, `α > s+1-d`, by
  `∇g*μ(x) := ∫ ∇g(x-y)(μ(y)-μ(x)) 1_{|x-y|≤1/4} dy + ∫ ∇g(x-y) 1_{|x-y|>1/4} dμ(y)`;
  for `0 ≤ s < d-1` the plain integral converges absolutely for `μ ∈ 𝒫 ∩ L^∞` and the two agree
  (the subtracted constant contributes zero by oddness, line 10096).  The formula "agrees with
  distributional convolution" (lines 10099–10101).
* The `s ≥ d-1` proviso of `(r,Λ)`-regularity (lines 10085–10088):
  `sup_N sup_{[0,T]} ‖ |∇|^{s-d} ∇μ^t ‖_∞ ≤ Λ`.
* Definition 3.2 `B:def:adjoint-operator` (lines 1587–1593) and Definition 3.5
  `B:def:adjoint-solution` (lines 1633–1635).

## Relation to `HRS/Dynamics/Setup.lean` (ISSUES §K3, resolved)

The cancellation convention is `HRS.convGradConv G ρ x` of the Setup file (cube cut-off
`‖x-y‖ ≤ 1/4` in the torus sup-norm, equal to the source's ball cut-off by oddness of `∇g`),
and `meanFieldDrift`, `backwardGenerator`, `IsClassicalAdjointSolution`, `propagator` are built
on it, hence correct for all `0 ≤ s < d`.  This file only adds (i) torus-metric notions
(`tdist`, Lipschitz / `C^{0,1}` norms, smoothness off the origin) used by Appendix C, (ii) the
`s ≥ d-1` proviso (`IsRegularMFProviso`; `HRS.IsRegularMF` lacks it), and (iii) the sorried kernel
facts that identify `convGradConv (periodicRieszGrad d s)` with the Fourier multiplier
`2πi k ĝ(k)` (`gradRieszCoeff`) — the "agrees with distributional convolution" clause of the
source.

The function `|∇|^{s-d}∇μ` of the proviso is the Fourier multiplier with symbol
`(2π|k|)^{s-d}·2πi k = c_{d,s}^{-1} · (2πi k ĝ(k))`, i.e. exactly `c_{d,s}^{-1} ∇g*μ`
(`H:eq:kernel`); it is *defined* here through the real-space convention (`fracForce`) so that the
bound `≤ Λ` is never vacuous.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Torus

variable {d : ℕ}

/-- The centered representative in `(-1/2, 1/2]^d` of a point of the torus. -/
def centeredRep (z : Torus d) : Euc d :=
  WithLp.toLp 2 fun i => if (rep z) i ≤ 1 / 2 then (rep z) i else (rep z) i - 1

/-- The Euclidean distance `|x - y|` on the torus: the norm of the centered representative of
`x - y` (this is the quotient distance, and `{|x-y| ≤ 1/4}` is the ball used in
`B:eq:nabla-g-convolution`). -/
def tdist (x y : Torus d) : ℝ := ‖centeredRep (x - y)‖

/-- The `C^{0,1}` (Lipschitz) norm `‖a‖_{C^{0,1}} = ‖a‖_∞ + [a]_{C^{0,1}}`. -/
def c01Norm (a : Torus d → ℝ) : ℝ := supNorm a + holderSeminorm 1 a

/-- A Lipschitz function on the torus with constant `L`. -/
def IsLipschitz (L : ℝ) (a : Torus d → ℝ) : Prop := ∀ x y, |a x - a y| ≤ L * tdist x y

/-- Smoothness away from the origin (for kernels): `C^∞` on `{z ≠ 0}` through the lift
(`((⊤ : ℕ∞) : WithTop ℕ∞)` is `C^∞`; `⊤ : WithTop ℕ∞` would be analyticity, ISSUES §E). -/
def IsSmoothOffZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : Torus d → E) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift κ) {x : Euc d | mk x ≠ 0}

end Torus

namespace PDE

variable {d : ℕ}

/-- `|∇|^{s-d} ∇μ = c_{d,s}^{-1} ∇g * μ` (symbols `(2π|k|)^{s-d} 2πi k` and `2πi k ĝ(k)`,
`H:eq:kernel`), realised through the cancellation convention `HRS.convGradConv`. -/
def fracForce (d : ℕ) (s : ℝ) (μ : Torus d → ℝ) (x : Torus d) : Euc d :=
  (rieszConst d s)⁻¹ • convGradConv (periodicRieszGrad d s) μ x

/-- `(r,Λ)`-regularity on `[0,T]` **with the `s ≥ d-1` proviso** (`B:eq:mf-regularity`,
lines 10082–10088): `sup_t ‖μ^t‖_{C^r} ≤ Λ` and, when `d-1 ≤ s`,
`sup_t ‖ |∇|^{s-d}∇μ^t ‖_∞ ≤ Λ`.  (`HRS.IsRegularMF` of the Setup file lacks the proviso.) -/
def IsRegularMFProviso (s : ℝ) (r : ℕ) (Λ T : ℝ) (ρ : ℝ → Torus d → ℝ) : Prop :=
  IsRegularMF r Λ T ρ ∧
    ((d : ℝ) - 1 ≤ s → ∀ t ∈ Set.Icc 0 T, ∀ x, ‖fracForce d s (ρ t) x‖ ≤ Λ)

/-- The nonlocal term `Div g*(ρ M^*∇φ) = ∑_{i,j} M^*_{ij} ∂_i g*(ρ ∂_j φ)` of `B:eq:G-def`
(lines 1723–1725), with `M^* = Mᵀ`: the last term of `HRS.backwardGenerator` (with the opposite
sign).  Each convolution `∂_i g * (ρ (Mᵀ∇φ)_i)` is taken with the cancellation convention. -/
def nonlocalTerm (D : DynData d) (ρ : Torus d → ℝ) (φ : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∑ j : Fin d, (convGradConv (periodicRieszGrad d D.s)
      (fun y => ρ y * (Torus.matVec D.M.transpose (Torus.grad φ y)) j) x) j

/-- `HRS.backwardGenerator` is `β⁻¹Δφ + b·∇φ - 𝒢φ` (Definition 3.2, `B:eq:adjoint-def`,
line 1590; `B:eq:adjoint-forward`, line 1722), by definition. -/
theorem backwardGenerator_eq (D : DynData d) (ρ : Torus d → ℝ) (φ : Torus d → ℝ) (x : Torus d) :
    backwardGenerator D ρ φ x =
      D.invβ * Torus.laplacian φ x + inner ℝ (meanFieldDrift D ρ x) (Torus.grad φ x) -
        nonlocalTerm D ρ φ x := rfl

/-! ### Required kernel facts linking the convention with the Fourier representation
(sorried; extend KERN-01's `periodicRiesz_fourierCoeff`, `periodicRiesz_grad_bound`) -/

section KernelInputs

variable {s : ℝ}

/-- `∇g` is odd (the regularised gradients are odd, `heatRieszGrad`), for `s < d`.  (For `s ≥ d`
the heat limit defining `periodicRieszGrad` need not exist and both sides are junk values, so
the hypothesis `s < d` is required; ISSUES §E.) -/
theorem periodicRieszGrad_neg (hsd : s < d) (x : Torus d) :
    periodicRieszGrad d s (-x) = -periodicRieszGrad d s x :=
  KernelGrad.periodicRieszGrad_neg_of_lt hsd x

/-- `∇g` is smooth away from the origin. -/
theorem periodicRieszGrad_smoothOffZero (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Torus.IsSmoothOffZero (periodicRieszGrad d s) :=
  KernelGrad.periodicRieszGrad_smoothOffZero hd hs0 hsd

/-- Kernel bound in torus-distance form: `|∇g(z)| ≤ C(|z|^{-s-1} + 1)` for `z ≠ 0`
(KERN-01 `periodicRiesz_grad_bound` restated with `tdist`). -/
theorem periodicRieszGrad_bound_tdist (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      ‖periodicRieszGrad d s z‖ ≤ C * (Torus.tdist z 0 ^ (-s - 1) + 1) :=
  KernelGrad.periodicRieszGrad_bound_tdist hd hs0 hsd

/-- The cancellation convention agrees with the plain integral for `0 ≤ s < d-1` and bounded
measurable `h` (line 10092: absolute convergence; line 10096: oddness). -/
theorem convGradConv_eq_plain (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 1)
    (h : Torus d → ℝ) (hm : Measurable h) (hb : ∃ B, ∀ x, |h x| ≤ B) (x : Torus d) :
    convGradConv (periodicRieszGrad d s) h x = ∫ y, h y • periodicRieszGrad d s (x - y) :=
  KernelGrad.convGradConv_eq_plain hd hs0 hsd h hm hb x

/-- **Required kernel fact.** The convention "agrees with distributional convolution"
(lines 10099–10101): for `0 ≤ s < d` and `C¹` `h`, the Fourier coefficients of the `i`-th
component of `∇g * h` are `2πi k_i ĝ(k) ĥ(k)` (`gradRieszCoeff`).  Extends KERN-01's
`periodicRiesz_fourierCoeff`. -/
theorem convGradConv_coeff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (h : Torus d → ℝ)
    (hh : Torus.IsCk 1 h) (i : Fin d) :
    coeffOf (fun x => convGradConv (periodicRieszGrad d s) h x i) =
      gradRieszCoeff d s i (coeffOf h) :=
  KernelGrad.convGradConv_coeff hd hs0 hsd h hh i

/-- **Required kernel fact.** For `C¹` `h` the convention yields a bounded continuous vector field
(lines 10097–10099). -/
theorem convGradConv_continuous (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (h : Torus d → ℝ)
    (hh : Torus.IsCk 1 h) : Continuous (convGradConv (periodicRieszGrad d s) h) :=
  KernelGrad.convGradConv_continuous hd hs0 hsd h hh

/-- **Required kernel fact** (Lemma C.1 input, lines 12229–12233): for `h ∈ C^{m+1}`, `∇g * h` is
`C^m` with `‖∇g*h‖_{C^m} ≤ C ‖h‖_{C^{m+1}}` (the convention loses at most one derivative,
uniformly in `0 ≤ s < d`). -/
theorem convGradConv_cbNorm (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) :
    ∃ C : ℝ, ∀ h : Torus d → ℝ, Torus.IsCk (m + 1) h →
      Torus.IsCk m (convGradConv (periodicRieszGrad d s) h) ∧
        Torus.cbNorm m (convGradConv (periodicRieszGrad d s) h) ≤ C * Torus.cbNorm (m + 1) h :=
  KernelGrad.convGradConv_cbNorm hd hs0 hsd m

end KernelInputs

end PDE

end HRS
