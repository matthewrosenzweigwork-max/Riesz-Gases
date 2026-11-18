import HRS.Whole.Adjoint
import HRS.Kernel.Riesz
import HRS.PDE.ForwardEq
import HRS.Torus.Basic

/-!
# `(r,Λ)`-regularity of whole-space mean-field paths (moved from `HRS.Whole.AppendixA`)

`fracForceRd` and `IsRegularMFRd` are defined here (unchanged, same namespace `HRS.Whole.AppendixA`) so that the
statement of S6.8 `mov_translation` (`HRS/Whole/MovingDyn.lean`, imported by `AppendixA`) can use them.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff MeasureTheory

namespace HRS.Whole.AppendixA

variable {d : ℕ}

/-- The singular force `|∇|^{s-d}∇μ = c_{d,s}^{-1} ∇g*μ` on `ℝ^d` (cf. `HRS.PDE.fracForce`), with the
cancellation convention `convGradConvW`. -/
def fracForceRd (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (x : Euc d) : Euc d :=
  (rieszConst d s)⁻¹ • convGradConvW (rieszKernelGrad d s) ρ x

/-- `(r,Λ)`-regularity on `[0,T]` in the whole-space form `S:eq:mf-regularity-whole` (S L9660-9665), including the
proviso for `d-1 ≤ s < d` (the singular-force bound stated after `B:eq:mf-regularity`, M L10082-10089):
`sup_{t≤T}(‖ρ^t‖_{C_b^r} + max_{j≤r}‖⟨x⟩^{d+3}∇^{⊗j}ρ^t‖_∞) ≤ Λ` (the norm `‖·‖_{C_b^r}` is the project's SUM
convention `HRS.cbNorm`, and `max_{j≤r}‖⟨x⟩^{d+3}∇^{⊗j}ρ‖_∞` is `weightedSupE r (d+3) ρ` (max over partial
derivatives), both equivalent to the source's norms up to constants depending on `d, r`) and, if `d-1 ≤ s`,
`‖|∇|^{s-d}∇ρ^t‖_∞ ≤ Λ`. -/
def IsRegularMFRd (s : ℝ) (r : ℕ) (Λ T : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, MemCb r (ρ t) ∧ weightedSupE r ((d : ℝ) + 3) (ρ t) < ⊤ ∧
    cbNorm r (ρ t) + (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ) ∧
  ((d : ℝ) - 1 ≤ s → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, ‖fracForceRd d s (ρ t) x‖ ≤ Λ)

/-! ### Regime predicates (moved from `AppendixA`/`AppendixAAdjoint` so that `Orbits` can use them) -/

/-- The adjoint regimes of Assumption A.2 (`B:ass:regime`) read on `𝔻 = ℝ^d`: `R1`, `R2a`, `R2c`, `R3` as in
`HRS.PDE.Regime.Holds` (the conditions on `s, M, β_N⁻¹, ν₀`), and `R2b` is not available on `ℝ^d` (it is a
condition on `inf μ` over `𝕋^d`, and `B:thm:adjoint-rd` lists only `R1, R2a, R2c, R3`, S L10090). -/
def RdRegimeHolds (R : PDE.Regime) (d : ℕ) (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (invβ ν₀ : ℝ) :
    Prop :=
  match R with
  | .R1 => s ≤ (d : ℝ) - 2
  | .R2a => (d : ℝ) - 2 < s ∧ Torus.symPart M = 0
  | .R2b _ => False
  | .R2c => (d : ℝ) - 2 < s ∧ s ≤ (d : ℝ) - 1 ∧ Torus.SymNonpos M
  | .R3 => (d : ℝ) - 2 < s ∧ 0 < ν₀ ∧ ν₀ ≤ invβ

/-- The three cases of `B:thm:adjoint-lp` (S L10272-10278). -/
inductive LpCase
  | sub
  | iso
  | hilbert

/-- The conditions of the case (for the exponent `p` and the matrix `M`):
(i) `sub`: `0 ≤ s ≤ d-2`, `M` arbitrary, `p(s+1) > d`;
(ii) `iso`: `d-2 < s < d`, `M = -λI`, `λ > 0` (`p ≥ 2`);
(iii) `hilbert`: `d-2 < s < d`, `M = -λI + 𝒜`, `λ ≥ 0`, `𝒜* = -𝒜`, at the Hilbert exponent `p = 2`. -/
def LpCase.Holds (d : ℕ) (s p : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : LpCase → Prop
  | .sub => s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)
  | .iso => (d : ℝ) - 2 < s ∧ ∃ lam : ℝ, 0 < lam ∧ M = -(lam • 1)
  | .hilbert => (d : ℝ) - 2 < s ∧ p = 2 ∧
      ∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧ M = -(lam • 1) + A

end HRS.Whole.AppendixA
