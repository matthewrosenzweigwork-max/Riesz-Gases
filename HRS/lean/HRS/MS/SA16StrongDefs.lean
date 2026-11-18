import HRS.Whole.AppendixAAdjoint

/-!
# S.A.16 strong-limit cores: literal definitions

Literal copies of `fracCut`, `oddCut` and `StrongUniformLimit` from `skeleton/cores/SA16-STRONG-LIMIT.lean`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

/-- The same full-tail radial cutoff as the frozen fractional operator.
Only the ball at the origin is removed; no large-radius truncation. -/
def fracCut (d : ℕ) (θ δ : ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ z in {z : Euc d | δ < ‖z‖},
    (u x - u (x-z)) / ‖z‖ ^ ((d : ℝ) + θ)

/-- Coordinate odd kernel with the same spherical cutoff. -/
def oddCut (d : ℕ) (θ δ : ℝ) (i : Fin d)
    (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ z in {z : Euc d | δ < ‖z‖},
    (‖z‖⁻¹ • z) i / ‖z‖ ^ ((d : ℝ) + θ - 1) * u (x-z)

/-- Uniform strong convergence on a bounded time interval. -/
def StrongUniformLimit {X : Type*} [NormedAddCommGroup X]
    (T : ℝ) (f : ℕ → ℝ → X) (g : ℝ → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (0 : ℝ) T,
    ‖f n t-g t‖ < ε

end HRS.Whole.AppendixA.Phase2SA16
