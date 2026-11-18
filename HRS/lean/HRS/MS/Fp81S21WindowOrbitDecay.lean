import HRS.MS.Fp81S21LeadingAdapter2
import HRS.MS.R2GenInitAux20

/-!
# HRS S2.1(iii), SOL40 packet 15b: common moving orbit gradient decay

The common-radius orbit claims give exponential gradient decay along each actual
`Trajectory`.  The observation-window exports in the companion file use the same
constants and the square-summable oscillator amplitudes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.R2WinOrbNL
open HRS.MS.R2WinErr

/-- Moving orbit gradient estimates along the `Trajectory` structure, with
constants fixed before the terminal datum and time variables. -/
theorem fp81s21_moving_orbit_gradient_decay (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ Cs0 cdec : ℝ, 0 ≤ Cs0 ∧ 0 < cdec ∧ Summable (s104_b p.d) ∧
          ∀ α : MultiIndex p.d,
            (∀ t : ℝ, 0 ≤ t →
              R2OrbitGrad (r26t3_coeff R) (4 * p.d + 42) t
                (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)
                (Cs0 * s104_b p.d α) cdec) ∧
            (∀ t : ℝ, 0 ≤ t →
              R2OrbitGrad (r26t3_coeff R) (4 * p.d + 42) t
                (generatorW (r26t3_coeff R) t
                  (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α))
                (Cs0 * s104_b p.d α) cdec) := by
  obtain ⟨δ0, Co, co, hδ0, hδ0half, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hOrbit : ∀ ρβ : Euc p.d → ℝ,
      IsThermalEquilibrium p.d p.s p.a p.β ρβ →
      S103nOrbitClaims p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ Co co := by
    intro ρβ hρβ
    exact (hcommon δ hδ hδle ρβ hρβ).1
  obtain ⟨Cs0, cdec, hCs0, hcdec, hsum, hgrad⟩ :=
    fp81s21_orbitGrad_commonRadius p (H := p.T) p.hT hco hOrbit
  have htraj : IsR2WindowTrajectory p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ R.ρ :=
    Or.inr ⟨R.ε, R.ψ, R.admissible, R.resulting⟩
  have hgradR := hgrad R.ρβ R.thermal R.ρ htraj
  refine ⟨Cs0, cdec, hCs0, hcdec, hsum, ?_⟩
  intro α
  simpa only [r26t3_coeff] using hgradR α

/-- The common summable oscillator envelope is square summable, since each
nonnegative coordinate is at most one. -/
private theorem fp81s21_s104b_square_summable (d : ℕ)
    (hsum : Summable (s104_b d)) :
    Summable (fun α : MultiIndex d => (s104_b d α) ^ 2) :=
  HRS.MS.R2GenInit.s105_b_sq_summable hsum

#print axioms fp81s21_moving_orbit_gradient_decay
#print axioms fp81s21_s104b_square_summable

end HRS.Fp81.S21

end
