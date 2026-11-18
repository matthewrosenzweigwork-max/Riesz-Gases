import HRS.Whole.AppendixALemmas2
import HRS.Main.A34Aux14
import HRS.Main.A9Final
import HRS.Main.A8Final

/-!
# Chunk F (`MP:`), finite-dimensional convergence for Theorem A.11: shared definitions

* `etaF R γ ηF`: the realization `R` with the random functional `η` replaced by the evaluation of the A.5 field
  `ηF` (`0` on tests outside `H^γ`).  Assumption A.5 controls `η` only on mean-zero tests, whereas the
  transported tests `U^{0,t}φ` of a trigonometric polynomial may have a nonzero mean; `NegSobolev.eval` drops
  the zero mode, so working with `etaF` removes the issue.  `P` and `X` are unchanged.
* `statVec`: the statistic vector `(A ⟨F, U^{0,t_a}φ_a⟩)_a` of a field `F`.
* `fieldSurr`: the surrogate law written on the field space, `(νin ∘ statVec⁻¹) ∗ N(0, surrogateCov)`.
-/

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Main HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.MP.FidiDefs

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open Classical in
/-- the realization with `η` replaced by the evaluation of the A.5 field (zero on non-`H^γ` tests). -/
def etaF (R : ∀ N, Realization d N) (γ : ℕ) (ηF : ∀ N, (R N).Ω → NegSobolev d (γ : ℝ)) :
    ∀ N, Realization d N :=
  fun N => { R N with η := fun ω ψ => if MemSobolev (γ : ℝ) ψ then NegSobolev.eval (ηF N ω) ψ else 0 }

theorem etaF_P_X (R : ∀ N, Realization d N) (γ : ℕ) (ηF : ∀ N, (R N).Ω → NegSobolev d (γ : ℝ))
    (N : ℕ) : (etaF R γ ηF N).P = (R N).P ∧ (etaF R γ ηF N).X = (R N).X := ⟨rfl, rfl⟩

theorem fi1_standing {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime}
    {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ} {m : ℕ} (γ : ℕ)
    (ηF : ∀ N, (R N).Ω → NegSobolev d (γ : ℝ))
    (h : TorusStanding S R Rg ν₀ MB Λ VB m C₀ Cc 𝔈) :
    TorusStanding S (etaF R γ ηF) Rg ν₀ MB Λ VB m C₀ Cc 𝔈 :=
  { flow := h.flow, regime := h.regime, mean_field := h.mean_field, matrix_bound := h.matrix_bound,
    potential := h.potential,
    energy := ⟨h.energy.completion, h.energy.pos, h.energy.bound, h.energy.small⟩,
    filtered := h.filtered }

/-- the statistic vector of a field `F`: `(A ⟨F, U^{0,t_a} φ_a⟩)_a`. -/
def statVec (D : DynData d) (ρ : ℝ → Torus d → ℝ) (A : ℝ) {p : ℕ} (ts : Fin p → ℝ)
    (φ : Fin p → Torus d → ℝ) (γ : ℝ) (F : NegSobolev d γ) : ℝ^p :=
  WithLp.toLp 2 fun a => A * NegSobolev.eval F (propagator D ρ 0 (ts a) (φ a))

/-- the surrogate law written on the field space: `(νin ∘ statVec⁻¹) ∗ N(0, surrogateCov)`. -/
def fieldSurr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (A q : ℝ) {p : ℕ} (ts : Fin p → ℝ)
    (φ : Fin p → Torus d → ℝ) (γ : ℝ) (νin : Measure (NegSobolev d γ)) : Measure (ℝ^p) :=
  (νin.map (statVec D ρ A ts φ γ)) ∗ multivariateGaussian 0 (surrogateCov D ρ q ts φ)

end HRS.MP.FidiDefs
