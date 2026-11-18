import HRS.MS.R2WinOrbNLAux19

/-!
# S10.3, part 20: the ED13 form of `r2_window_orbits`, and the tie modulo the nonlinear window-test clause

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.

* `R2WinOrbED13 d s a β T`: the conclusion of `HRS.Whole.r2_window_orbits` (with its hypotheses `2 ≤ d`, `0 ≤ s < d`, `0 < a, β, T`) written out explicitly with the right
  derivative `derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t` in the fifth orbit claim (repair ED13).  After ED13 is applied to `Window.lean`,
  `HRS.Whole.r2_window_orbits hd s hs0 hs a β ha hβ T hT : R2WinOrbED13 d s a β T` by `exact`.
* `S103nOrbitClaims`, `S103nWindowClause`: the five orbit claims along the nonlinear class (proved: `s103n_orbits_nonlinear`), and the window-test clause along the class (OPEN).
* `s103n_tie`: `R2WinOrbED13` follows from the stationary branch `s103_stationary`, the nonlinear orbit claims, and a hypothesis `hW` deriving the nonlinear window tests from the
  orbit claims (the only missing ingredient).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Ul HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.Who HRS.MS.BreakdownS67
  HRS.MS.MovAdj HRS.MS.R2WinOrb

variable {d : ℕ}

/-- The conclusion of `HRS.Whole.r2_window_orbits` in the ED13 form (right derivative in the fifth orbit claim) and the D2/ED14 form
(class constants `(c₁, C₁)` universally quantified before `εstar`, no `R2ClassExists`). -/
def R2WinOrbED13 (d : ℕ) (s a β T : ℝ) : Prop :=
  ∀ c₁ C₁ : ℝ, ∃ εstar : ℝ, 0 < εstar ∧
    ∃ C c : ℝ, 0 < c ∧
    (Summable fun α : MultiIndex d =>
      oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2)) ∧
    ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
      IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ → ∀ α : MultiIndex d,
      let Cf := (quadraticGradientDyn d s a β).coeff ρ
      let bα := oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2)
      let φ := oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α
      (∀ t : ℝ, 0 ≤ t →
        R2OrbitSup Cf (4 * d + 42) t φ (C * bα) ∧ R2OrbitGrad Cf (4 * d + 42) t φ (C * bα) c ∧
        R2OrbitSup Cf (4 * d + 42) t (generatorW Cf t φ) (C * bα) ∧
        R2OrbitGrad Cf (4 * d + 42) t (generatorW Cf t φ) (C * bα) c ∧
        R2OrbitSup Cf (4 * d + 42) t (fun x => generatorW Cf t (generatorW Cf t φ) x +
          derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t) (C * bα)) ∧
      ((∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW Cf t φ f) →
        ∀ (b : ℝ), 0 ≤ b → ∀ n : ℕ,
          MemCb (4 * d + 42) (r2WindowTest Cf (((24 * d + 240 : ℕ)) : ℝ) T b n α) ∧
          cbNorm (4 * d + 42) (r2WindowTest Cf (((24 * d + 240 : ℕ)) : ℝ) T b n α) ≤
            C * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα)

/-- The five orbit claims (ED13 form) along the nonlinear class `(ε_*, c₁, C₁)` with constants `C, c` (proved in `s103n_orbits_nonlinear`). -/
def S103nOrbitClaims (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (εstar c₁ C₁ C c : ℝ) : Prop :=
  ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
    IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
    ∀ (α : MultiIndex d) (t : ℝ), 0 ≤ t →
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) (C * s103_b d α) ∧
      R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) (C * s103_b d α) c ∧
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α))
        (C * s103_b d α) ∧
      R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α))
        (C * s103_b d α) c ∧
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (fun x => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
            (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
              (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α)) x +
          derivWithin (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t'
            (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) x) (Set.Ici t) t) (C * s103_b d α)

/-- The window-test clause of `r2_window_orbits` along the nonlinear class (OPEN: the nonlinear branch needs the terminal-time regularity of `U(0,t)φ_α`). -/
def S103nWindowClause (d : ℕ) (s a β T : ℝ) (ρβ : Euc d → ℝ) (εstar c₁ C₁ : ℝ) : Prop :=
  ∃ Cw : ℝ, ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
    IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
    ∀ (α : MultiIndex d),
      (∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
        (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) f) →
        ∀ (b : ℝ), 0 ≤ b → ∀ n : ℕ,
          MemCb (4 * d + 42) (r2WindowTest ((quadraticGradientDyn d s a β).coeff ρ)
            (((24 * d + 240 : ℕ)) : ℝ) T b n α) ∧
          cbNorm (4 * d + 42) (r2WindowTest ((quadraticGradientDyn d s a β).coeff ρ)
            (((24 * d + 240 : ℕ)) : ℝ) T b n α) ≤ Cw * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b d α

theorem s103n_orbitGrad_mono_c {C : WholeCoeff d} {k : ℕ} {t : ℝ} {g : Euc d → ℝ} {A c c' : ℝ}
    (h : R2OrbitGrad C k t g A c) (hc : c' ≤ c) (hA : 0 ≤ A) : R2OrbitGrad C k t g A c' := by
  intro f hf r hr
  obtain ⟨h1, h2⟩ := h f hf r hr
  refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (by nlinarith [hr.2])) hA))⟩

theorem s103n_orbits_nonlinear' {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (c₁ C₁ : ℝ) :
    ∃ εstar : ℝ, 0 < εstar ∧
      ∃ C c : ℝ, 0 < c ∧ S103nOrbitClaims d s a β ρβ εstar c₁ C₁ C c := by
  obtain ⟨εstar, hε, C, c, hc, h⟩ := s103n_orbits_nonlinear H c₁ C₁
  exact ⟨εstar, hε, C, c, hc, h⟩

end HRS.MS.R2WinOrbNL

end
