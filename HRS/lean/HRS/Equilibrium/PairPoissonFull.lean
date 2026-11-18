import HRS.Equilibrium.PairCorrection

/-!
# Proposition 4.13 with all clauses (packet PX-FID, specification 2026-10-15)

`HRS.pair_poisson` (proved as `pair_poisson_proof`) encodes the pointwise off-diagonal equation, the
bounds `Q:eq:psi-size`, the `𝒥ψ` clauses and the `a_f` bounds of Proposition 4.13 (`M:Q:prop:poisson`,
TeX L4729-4735).  The source also asserts (L4734):
* the equation `-(𝒜_x + 𝒜_y)ψ_f = H_f` **in distributions** (not only off the diagonal), and
* the bounds `Q:eq:psi-size` with constant `C|f|_K` for **tangential derivatives up to order four**.

Both are stated here in `pair_poisson_full`, which contains `pair_poisson` verbatim as its first conjuncts.

Representation decisions (orchestrator; ISSUES §I):
* Tangential derivative: `∂^tan_e ψ(x,y) = d/dt ψ(x + te, y + te)|_{t=0}`, i.e. differentiation in `x`
  at fixed relative coordinate `x - y` (the source's usage, L4815, L4837), through the lift `lift2`;
  iterated along a list of directions, with constant `C|f|_K ∏‖e_i‖` (multilinearity).
* Distributions: the weak form against smooth test kernels `φ` on `𝕋^d × 𝕋^d`, with respect to `μ ⊗ μ`
  (`μ = ρ dx`, `ρ` smooth positive, so this is equivalent to testing against Lebesgue).  The local part `B`
  is `μ`-symmetric for a thermal density (`∇ρ = -βρ(∇V + F_μ)`), so `∫(B_xψ)φ dμ = -β⁻¹∫∇_xψ·∇_xφ dμ`
  and the distributional `μ`-mean of `B_xψ(·,y)` is `0`; the nonlocal and projected part is
  `𝒥ψ = (P_xJ_x + P_yJ_y)ψ` (`Jpair`), an integrable function.  Together with the pointwise equation
  this excludes a diagonal flux.  Integrability conjuncts rule out junk Bochner values.
* `gradFst`, `Jpair`, `Hsource` take junk values only on the diagonal, a `μ ⊗ μ`-null set; the tangential
  clause bounds the full gradient and Hessian (`PsiSize`) of each `∂^tan` derivative, off the diagonal only.
* Independent statement review (2026-10-15): ACCEPT.
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS

variable {d : ℕ}

section Critical

variable {s : ℝ}

/-- Tangential derivative `∂^tan_e ψ(x,y) = D(lift2 ψ)(x̃,ỹ)·(e,e)`, `x̃, ỹ` the representatives. -/
def tanDeriv (e : Euc d) (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep y) (e, e)

/-- Iterated tangential derivative `∂^tan_{e₁} ⋯ ∂^tan_{e_k} ψ`. -/
def tanIter : List (Euc d) → (Torus d → Torus d → ℝ) → Torus d → Torus d → ℝ
  | [], ψ => ψ
  | e :: es, ψ => tanDeriv e (tanIter es ψ)

/-- The equation `-(𝒜_x + 𝒜_y)ψ = H_f` in distributions on `𝕋^d × 𝕋^d` (weak form w.r.t. `μ ⊗ μ`). -/
structure IsWeakPairPoisson (d : ℕ) (s : ℝ) (β : ℝ) (ρ : Torus d → ℝ) (f : Torus d → ℝ)
    (ψ : Torus d → Torus d → ℝ) : Prop where
  int_grad : Integrable (fun p : Torus d × Torus d => ‖gradFst ψ p.1 p.2‖ + ‖gradSnd ψ p.1 p.2‖)
    ((withDensityReal ρ).prod (withDensityReal ρ))
  int_J : Integrable (fun p : Torus d × Torus d => Jpair d s ρ ψ p.1 p.2)
    ((withDensityReal ρ).prod (withDensityReal ρ))
  int_H : Integrable (fun p : Torus d × Torus d => Hsource d s ρ f p.1 p.2)
    ((withDensityReal ρ).prod (withDensityReal ρ))
  weak : ∀ φ : Torus d → Torus d → ℝ, ContDiff ℝ ∞ (lift2 φ) →
    ∫ p : Torus d × Torus d, (β⁻¹ * (inner ℝ (gradFst ψ p.1 p.2) (gradFst φ p.1 p.2) +
        inner ℝ (gradSnd ψ p.1 p.2) (gradSnd φ p.1 p.2)) - Jpair d s ρ ψ p.1 p.2 * φ p.1 p.2)
      ∂((withDensityReal ρ).prod (withDensityReal ρ)) =
    ∫ p : Torus d × Torus d, Hsource d s ρ f p.1 p.2 * φ p.1 p.2
      ∂((withDensityReal ρ).prod (withDensityReal ρ))

/-- Proposition 4.13 `M:Q:prop:poisson` (TeX L4729-4735) with all clauses: the conclusions of
`pair_poisson`, plus `Q:eq:psi-size` with constant `C|f|_K ∏‖e_i‖` for every iterated tangential
derivative of order at most four, plus the equation in distributions. -/
theorem pair_poisson_full (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ (Ψ : (Torus d → ℝ) → Torus d → Torus d → ℝ) (C : ℝ),
      (∀ (f f' : Torus d → ℝ) (a b : ℝ), Torus.IsSmooth f → Torus.IsSmooth f' →
        Ψ (a • f + b • f') = a • Ψ f + b • Ψ f') ∧
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
        IsPairCorrector d s V β ρ f (C * posSeminorm (8 * d + 80) f) (Ψ f) ∧
        (∃ M : ℝ, ∀ x, |aCoef d s ρ f x| ≤ M) ∧
        eLpNorm (aCoef d s ρ f) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * posSeminorm (8 * d + 80) f) ∧
        (∀ es : List (Euc d), es.length ≤ 4 →
          PsiSize s (C * posSeminorm (8 * d + 80) f * (es.map fun e => ‖e‖).prod) (tanIter es (Ψ f))) ∧
        IsWeakPairPoisson d s β ρ f (Ψ f) := by
  sorry

end Critical

end HRS

end
