import HRS.MC.CepaDefs

/-!
# Packet CEPH2: vocabulary (definitions only, no sorry)

SPECIFICATION FILE (sorried sub-lemmas, plan in `HRS/MC/CepH2Plan.md`).  Route: no Fokker-Planck existence
theory.  (1) Itô/Dynkin gives the weak Fokker-Planck equation for the folded laws `μ_t`; (2) Gaussian mollification
`u = Ĝ_ε * μ_t` of the folded law is smooth and positive, solves `∂_t u = div (θ∇u + u∇U + r_ε)` with an explicit
commutator `r_ε`, `∫ |r_ε|²/u ≤ 2 N θ ε K²`; (3) the free energy `∫ u log u + u U/θ` of `u` is differentiated on the
cylinder (cut-off in the transverse variables); (4) `ε → 0` by lower semicontinuity; (5) a `C²` potential is reduced
to one with Lipschitz gradient by freezing it outside the tube `|P⊥ z| < n` (same strong solution up to the exit time).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-! ### Vocabulary -/

/-- The component of `z` orthogonal to the diagonal `(1,…,1)`. -/
def h2_perp (z : Ch N) : Ch N := z - ((∑ k, z k) / (N : ℝ)) • cep_diag N

/-- The Laplacian `∑_k ∂_k² g`. -/
def h2_lap (g : Ch N → ℝ) (z : Ch N) : ℝ :=
  ∑ k : Fin N, fderiv ℝ (fderiv ℝ g) z (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)

/-- The generator `L g = θ Δ g - ⟨∇U, ∇g⟩` of `dZ = -∇U dt + √(2θ) dW`. -/
def h2_gen (θ : ℝ) (U g : Ch N → ℝ) (z : Ch N) : ℝ :=
  θ * h2_lap g z - inner ℝ (gradient U z) (gradient g z)

/-- Test functions of the weak Fokker-Planck equation: `C²`, diagonally periodic, with `g`, `∇²g` bounded and
`‖∇g(z)‖ (1 + ‖P⊥ z‖)` bounded (so that `⟨∇U, ∇g⟩` is bounded when `∇U` is Lipschitz). -/
structure H2Test (g : Ch N → ℝ) : Prop where
  smooth : ContDiff ℝ 2 g
  periodic : ∀ z, g (z + cep_diag N) = g z
  bdd : ∃ C : ℝ, ∀ z, |g z| ≤ C ∧ ‖fderiv ℝ g z‖ * (1 + ‖h2_perp z‖) ≤ C ∧ ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ C

/-- Weak Fokker-Planck equation for a family of (folded) laws on `t ≥ 0`. -/
def H2WeakFP (θ : ℝ) (U : Ch N → ℝ) (μ : ℝ → Measure (Ch N)) : Prop :=
  ∀ g : Ch N → ℝ, H2Test g → ∀ t : ℝ, 0 ≤ t →
    ∫ z, g z ∂(μ t) = ∫ z, g z ∂(μ 0) + ∫ s in Icc (0 : ℝ) t, ∫ z, h2_gen θ U g z ∂(μ s)

/-- Gaussian of variance `2θε` per coordinate. -/
def h2_gauss (θ ε : ℝ) (w : Ch N) : ℝ :=
  (4 * Real.pi * θ * ε) ^ (-(N : ℝ) / 2) * Real.exp (-‖w‖ ^ 2 / (4 * θ * ε))

/-- The diagonally periodised Gaussian. -/
def h2_kern (θ ε : ℝ) (w : Ch N) : ℝ := ∑' k : ℤ, h2_gauss θ ε (w + (k : ℝ) • cep_diag N)

/-- Mollified density `u(x) = ∫ Ĝ_ε(x - y) dμ(y)` (diagonally periodic, smooth, positive). -/
def h2_mol (θ ε : ℝ) (μ : Measure (Ch N)) (x : Ch N) : ℝ := ∫ y, h2_kern θ ε (x - y) ∂μ

/-- Free energy `∫_cell u log u + u U/θ` of a density on the cell. -/
def h2_free [NeZero N] (θ : ℝ) (U : Ch N → ℝ) (u : Ch N → ℝ) : ℝ :=
  ∫ x in cep_cell N, (u x * Real.log (u x) + u x * U x / θ)

/-- Dissipation `∫_cell u ‖∇ log u + ∇U/θ‖²`. -/
def h2_diss [NeZero N] (θ : ℝ) (U : Ch N → ℝ) (u : Ch N → ℝ) : ℝ :=
  ∫ x in cep_cell N, u x * ‖(u x)⁻¹ • gradient u x + (1 / θ) • gradient U x‖ ^ 2

end HRS.MC.CepH2
