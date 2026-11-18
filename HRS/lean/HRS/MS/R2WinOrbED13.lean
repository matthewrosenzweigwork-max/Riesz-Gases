import HRS.MS.R2WinOrbAux15

/-!
# ED13: derivWithin form of the stationary branch of `r2_window_orbits`

Repair ED13 (2026-10-25, approved): the fifth orbit claim of `HRS.Whole.r2_window_orbits` uses the right derivative
`derivWithin _ (Set.Ici t) t`.  `s103_stationary` proves the two-sided `deriv` form.  For the stationary coefficient
`fun _ => ρβ` the map `t' ↦ generatorW Cf t' φ x` is constant (definitionally), so both derivatives are `0` and the
two forms agree.  This file transfers `s103_stationary` to the derivWithin form.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole

variable {d : ℕ}

theorem ed13_derivWithin_stationary (s a β : ℝ) (ρβ φ : Euc d → ℝ) (t : ℝ) (x : Euc d) :
    derivWithin (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t' φ x) (Set.Ici t) t =
      deriv (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t' φ x) t := by
  have hc : (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t' φ x) =
      fun _ => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) 0 φ x := rfl
  rw [hc, deriv_const, derivWithin_fun_const, Pi.zero_apply]

theorem ed13_stationary (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < c ∧
      (Summable fun α : MultiIndex d =>
        oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2)) ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ α : MultiIndex d,
        let Cf := (quadraticGradientDyn d s a β).coeff (fun _ => ρβ)
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
              C * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα) := by
  obtain ⟨C, c, hc, hsum, h⟩ := s103_stationary hd s hs0 hs a β ha hβ T hT
  refine ⟨C, c, hc, hsum, fun ρβ hρ α => ?_⟩
  obtain ⟨h1, h2⟩ := h ρβ hρ α
  dsimp only
  refine ⟨fun t ht => ?_, h2⟩
  obtain ⟨s0, g0, s1, g1, s2⟩ := h1 t ht
  refine ⟨s0, g0, s1, g1, ?_⟩
  simp only [ed13_derivWithin_stationary]
  exact s2

end HRS.MS.R2WinOrb

end
