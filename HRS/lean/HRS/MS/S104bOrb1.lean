import HRS.MS.R2WinErrNL6
import HRS.MS.R2WinOrbNLAux22

/-!
# S10.4 (nonlinear), packet S104b-1: `S104nAllOrb` from the general-initial-time version of the S10.3 terminal-time regularity

`S104bTermRegGen`: the general-initial-time analogue of `S103nTermReg` (S10.3), stated for `propagatorW` directly:
for every trajectory of the class, every `α` and horizon `T0`,
* (`ex`) classical adjoint solutions exist for the three terminal data `φ_α`, `L_tφ_α`, `L_t²φ_α + ∂_tL_tφ_α` (`s103nData`) at every terminal time `t ≤ T0`,
* (`dq`) for every initial time `r ≤ t` the terminal-time difference quotients `h⁻¹(U(r,t+h)D_a(t+h) - U(r,t)D_a(t))` converge in every `C^j` sup
  norm (`j ≤ 4d+42`) to `U(r,t)D_{a+1}(t)` (`a = 0, 1`),
* (`jcont`) `(t,r,x) ↦ ∇U(r,t)L_tφ_α(x)` is jointly continuous on `{0 ≤ r ≤ t ≤ T0}`.
`S103nTermReg` is the case `r = 0`; this is the (only) analytic input of the nonlinear branch of S10.4/S10.5 on the adjoint orbit.
`s104b_allOrb_of_termRegGen`: `S104nAllOrb d s a β εstar c₁ C₁` from `S104bTermRegGen` along every thermal equilibrium.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S53 HRS.MS.R2WinOrbNL

variable {d : ℕ}

/-- The general-initial-time terminal-time regularity of the nonlinear adjoint orbit (see the module docstring). -/
def S104bTermRegGen (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (εstar c₁ C₁ : ℝ) : Prop :=
  ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
    IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
    ∀ (α : MultiIndex d) (T0 : ℝ), 0 ≤ T0 →
      (∀ a' : Fin 3, ∀ t ∈ Icc (0 : ℝ) T0, ∃ f : ℝ → Euc d → ℝ,
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
          (s103nData ((quadraticGradientDyn d s a β).coeff ρ) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) a' t) f) ∧
      (∀ a' : Fin 3, ∀ ha2 : (a' : ℕ) < 2, ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T0 → ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, h ≠ 0 → |h| < δ → r ≤ t + h → t + h ≤ T0 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (t + h)
              (s103nData ((quadraticGradientDyn d s a β).coeff ρ) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) a' (t + h)) y -
            propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r t
              (s103nData ((quadraticGradientDyn d s a β).coeff ρ) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) a' t) y) -
            propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r t
              (s103nData ((quadraticGradientDyn d s a β).coeff ρ) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)
                ⟨(a' : ℕ) + 1, by omega⟩ t) y) x‖ ≤ e) ∧
      ContinuousOn (fun q : ℝ × ℝ × Euc d => gradient (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) q.2.1 q.1
        (generatorW ((quadraticGradientDyn d s a β).coeff ρ) q.1 (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) q.2.2)
        {q : ℝ × ℝ × Euc d | 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.1 ≤ T0}

/-- The quotient clause of `S104bTermRegGen` is the `S53Diff` clause of `S104nOrbit` (shift `τ = t - r`, `j ≤ 2`). -/
lemma s104b_S53Diff {G G' : ℝ → Euc d → ℝ} {r T0 : ℝ}
    (hdq : ∀ t : ℝ, r ≤ t → t ≤ T0 → ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, h ≠ 0 → |h| < δ → r ≤ t + h → t + h ≤ T0 → ∀ j ≤ 2, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (G (t + h - r) y - G (t - r) y) - G' (t - r) y) x‖ ≤ e) :
    S53Diff (T0 - r) G G' := by
  intro τ hτ e he
  obtain ⟨δ, hδ, hh⟩ := hdq (r + τ) (by linarith [hτ.1]) (by linarith [hτ.2]) e he
  refine ⟨δ, hδ, fun h h0 hhd hτh j hj x => ?_⟩
  have := hh h h0 hhd (by linarith [hτh.1]) (by linarith [hτh.2]) j hj x
  have e1 : r + τ + h - r = τ + h := by ring
  have e2 : r + τ - r = τ := by ring
  rw [e1, e2] at this
  exact this

theorem s104b_orbit_of_termRegGen {s a β : ℝ} {ρβ : Euc d → ℝ} {εstar c₁ C₁ : ℝ}
    (hR : S104bTermRegGen d s a β ρβ εstar c₁ C₁) {ε : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hadm : IsAdmissiblePerturbation ρβ εstar ε ψ) (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ)
    (α : MultiIndex d) (T0 : ℝ) (hT0 : 0 ≤ T0) :
    S104nOrbit ((quadraticGradientDyn d s a β).coeff ρ) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) T0 := by
  obtain ⟨hex, hdq, hjc⟩ := hR ε ψ ρ hadm hres α T0 hT0
  set C := (quadraticGradientDyn d s a β).coeff ρ with hC
  set φ := oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α with hφ
  have hd01 : ∀ r ∈ Icc (0 : ℝ) T0, S53Diff (T0 - r) (fun τ => propagatorW C r (r + τ) φ)
      (fun τ => propagatorW C r (r + τ) (generatorW C (r + τ) φ)) := by
    intro r hr
    refine s104b_S53Diff fun t hrt htT e he => ?_
    obtain ⟨δ, hδ, hh⟩ := hdq 0 (by norm_num) r t hr.1 hrt htT e he
    refine ⟨δ, hδ, fun h h0 hhd h1 h2 j hj x => ?_⟩
    have := hh h h0 hhd h1 h2 j (hj.trans (by omega)) x
    simp only [add_sub_cancel]
    exact this
  refine ⟨fun t ht => hex 0 t ht, fun t ht => hex 1 t ht, hd01, fun r hr => ?_, hjc⟩
  refine ⟨fun τ => propagatorW C r (r + τ) (s103nData C φ 2 (r + τ)), fun τ hτ => ?_, ?_⟩
  · exact s104n_memCb_prop (hex 2 (r + τ) ⟨by linarith [hr.1, hτ.1], by linarith [hτ.2]⟩) ⟨hr.1, by linarith [hτ.1]⟩
  · refine s104b_S53Diff fun t hrt htT e he => ?_
    obtain ⟨δ, hδ, hh⟩ := hdq 1 (by norm_num) r t hr.1 hrt htT e he
    refine ⟨δ, hδ, fun h h0 hhd h1 h2 j hj x => ?_⟩
    have := hh h h0 hhd h1 h2 j (hj.trans (by omega)) x
    simp only [add_sub_cancel]
    exact this

/-- `S104nAllOrb` from the general-initial-time terminal-time regularity along every thermal equilibrium. -/
theorem s104b_allOrb_of_termRegGen {s a β εstar c₁ C₁ : ℝ}
    (hR : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → S104bTermRegGen d s a β ρβ εstar c₁ C₁) :
    S104nAllOrb d s a β εstar c₁ C₁ :=
  fun ρβ hρβ ε ψ ρ hadm hres α T0 hT0 => s104b_orbit_of_termRegGen (hR ρβ hρβ) hadm hres α T0 hT0

end HRS.MS.R2WinErr
