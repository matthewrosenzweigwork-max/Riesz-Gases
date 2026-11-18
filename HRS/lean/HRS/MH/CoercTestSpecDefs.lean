import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs

/-!
# CoercTest: definitions for the statement-only specification of the `ℝ^d` test-function bound

Sorry-free companion of `HRS/MH/CoercTestSpec.lean` (see `docs/MAIN_H_COERC_TEST_SCOPE.md`, packet W0).
Everything here is a definition, or a one-line `Iff.rfl`, so that workers can import this file.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

variable {d N : ℕ}

/-- `ν̂(ξ) = N⁻¹ ∑_i e^{-2πi⟨x_i,ξ⟩} - 𝓕ρ(ξ)`: the Fourier transform (Mathlib convention `e^{-2πi⟨x,ξ⟩}`) of the
signed measure `ν = μ_N - ρ dx`. -/
def nuHat (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ) (ξ : Euc d) : ℂ :=
  (1 / (N : ℂ)) * ∑ i, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ (X i) ξ : ℝ) : ℂ))) -
    𝓕 (fun x : Euc d => ((ρ x : ℝ) : ℂ)) ξ

/-- Weight of the Gaussian mixture: `w_s(t) = t^{s/2-1}/Γ(s/2)` for `s ≠ 0`, `w_0(t) = 1/(2t)`. -/
def wS (s t : ℝ) : ℝ :=
  if s = 0 then 1 / (2 * t) else t ^ (s / 2 - 1) / Real.Gamma (s / 2)

/-- The truncated kernel `gT = ∫_{(0,T]} w_s(t) gaussK t dt` (modulo the constant `e^{-t}` at `s = 0`):
`gTpos s T` for `s ≠ 0`, `gTlog T` for `s = 0`. -/
def gTs (d : ℕ) (s T : ℝ) : Euc d → ℝ :=
  if s = 0 then HRS.MH.CoercLower.gTlog T else HRS.MH.CoercLower.gTpos s T

/-- The spectral multiplier `M_T(ξ) = ∫_{(0,T]} w_s(t) (π/t)^{d/2} e^{-π²‖ξ‖²/t} dt` of `gT`
(junk value `0` at `ξ = 0`, where the integral diverges for `s < d`). -/
def Mhat (d : ℕ) (s T : ℝ) (ξ : Euc d) : ℝ :=
  ∫ t in Set.Ioc (0 : ℝ) T,
    wS s t * ((Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / t))

/-- The normalised Gaussian mollifier `G_b(x) = (b/π)^{d/2} e^{-b‖x‖²}` (integral one). -/
def molK (b : ℝ) (x : Euc d) : ℝ := (b / Real.pi) ^ ((d : ℝ) / 2) * HRS.MH.CoercLower.gaussK b x

/-- The mollified signed measure `u_b = (μ_N - ρ) * G_b`, written (as `gaussU`) with the argument `x_i - z`, `y - z`:
`u_b(z) = N⁻¹ ∑_i G_b(x_i - z) - ∫ G_b(y - z) ρ(y) dy`. -/
def uMol (b : ℝ) (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ) (z : Euc d) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, molK b (X i - z) - ∫ y, molK b (y - z) * ρ y

/-- The test-function clause of `HRS.Whole.AppendixALemmas.WholeCoercivityPair d s C₀ C` (its third conjunct, verbatim). -/
def TestBoundClause (d : ℕ) (s C₀ C : ℝ) : Prop :=
  ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
    (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ)) →
    ∀ X : HRS.Whole.EucConfig d N, Function.Injective X →
    ∀ (ψ : Euc d → ℝ) (L : ℝ), 0 ≤ L → HRS.PDE.ToolboxRd.IsLipschitz L ψ → HasCompactSupport ψ →
      HRS.Whole.AppendixALemmas.HasFiniteHomSobolevRd (((d : ℝ) - s) / 2) ψ →
        |HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ| ≤
          C * HRS.smearScale d N Λ * L + C * HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
            Real.sqrt (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + HRS.oNΛ d s C₀ Λ N)

/-- `WholeCoercivityPair` is the lower bound, `0 < C`, and the test-function clause. -/
theorem wholeCoercivityPair_iff (d : ℕ) (s C₀ C : ℝ) :
    HRS.Whole.AppendixALemmas.WholeCoercivityPair d s C₀ C ↔
      HRS.Whole.AppendixA.CompletionNonnegRd d s C₀ ∧ 0 < C ∧ TestBoundClause d s C₀ C :=
  Iff.rfl

end HRS.MH.CoercTest
