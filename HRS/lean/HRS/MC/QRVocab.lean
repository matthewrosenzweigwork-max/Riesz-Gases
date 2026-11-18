import HRS.Sections.Sec7Fields

/-!
# Vocabulary for the quadratic-relaxation packets (sorry-free)

Definitions used by the statements in `HRS.MC.QRSpec` (which is sorried and never imported by a packet) and by the
proofs.  Namespace `HRS.MC.QRSpec` is kept so that the statements and the proofs refer to the same names.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MC

namespace QRSpec

open HRS.Sec7

variable {d : ℕ}

/-! ### Vocabulary -/

/-- The finite-dimensional marginals of the real Fourier coordinates `F̂(k) = F(e_k)` of an `E_r`-valued random variable
are centred Gaussian vectors: for every finite set `S` of nonzero frequencies the random vector
`(F̂(k))_{k∈S}` has a Gaussian law (`HasGaussianLaw`) and every coordinate has mean zero.  This is the (weakest) form of
"`F` is a centred Gaussian field" that the mild form of the linear equation actually provides
(`IsLinearFluctuationSolution.gaussian_part`: Gaussian only after testing against finitely many test functions). -/
def HasFiniteGaussianCoeffs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ}
    (X : Ω → NegSobolev d r) : Prop :=
  ∀ S : Finset (NonzeroLattice d),
    HasGaussianLaw (fun ω (k : S) => NegSobolev.fourierCoeff (X ω) k.1) P ∧
      ∀ k : NonzeroLattice d, ∫ ω, NegSobolev.fourierCoeff (X ω) k ∂P = 0

/-- Operator bound `‖Σ‖_{op} ≤ K` for the (positive semidefinite) covariance matrix `Σ_{kl} = E[X̂_kX̂_l]` of the real
Fourier coordinates of `X`, in the form `aᵀΣa ≤ K|a|²` for finitely supported `a`.  It is literally the conclusion of
`HRS.MC.L2Cov.l2cs_mode_form`, so a uniform `L²` covariance bound `E[X(φ)²] ≤ K‖φ‖²` gives it. -/
def ModeCovBound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ} (X : Ω → NegSobolev d r)
    (K : ℝ) : Prop :=
  ∀ (S : Finset (NonzeroLattice d)) (a : NonzeroLattice d → ℝ),
    ∫ ω, (∑ k ∈ S, a k * NegSobolev.fourierCoeff (X ω) k) ^ 2 ∂P ≤ K * ∑ k ∈ S, a k ^ 2

/-- The finite section `½ ∑_{k,l∈F} ĥ°_{kl}(η̂_kη̂_l - E[η̂_kη̂_l])` of the Wick quadratic form; for `F = S` this is the
expression inside `IsHalfWick`, with `Q` the `L²` limit as `S ↑`. -/
def wickSection {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ} (η : Ω → NegSobolev d r)
    (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (F : Finset (NonzeroLattice d)) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ k ∈ F, ∑ l ∈ F, wickCoeff μ h k l * (NegSobolev.fourierCoeff (η ω) k *
    NegSobolev.fourierCoeff (η ω) l - ∫ ω', NegSobolev.fourierCoeff (η ω') k *
      NegSobolev.fourierCoeff (η ω') l ∂P)

open Classical in
/-- The Hilbert-Schmidt mass `∑_{(a,b) ∉ F×F} A_{ab}²` of a matrix outside `F × F` (the tail `A - P_F A P_F` of the
projection of the bilinear kernel; `tsum`, to be used only with a `Summable` hypothesis on `A²`). -/
def tailHS {ι : Type*} (A : ι → ι → ℝ) (F : Finset ι) : ℝ :=
  ∑' p : ι × ι, if p.1 ∈ F ∧ p.2 ∈ F then 0 else A p.1 p.2 ^ 2

end QRSpec

end MC

end HRS

end
