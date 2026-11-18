import HRS.MS.R2WinOrbAux14

/-!
# S10.3 (stationary half), part 15: `s103_stationary`

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  The stationary branch of `HRS.Whole.r2_window_orbits`: the conclusion for
`ρ = fun _ => ρ_β` with constants `C, c` chosen before `ρ_β` (a thermal equilibrium is unique, `mv0_rho_eq`; if none exists the
statement is vacuous).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole

variable {d : ℕ}

theorem s103_stationary (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
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
            deriv (fun t' => generatorW Cf t' φ x) t) (C * bα)) ∧
        ((∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW Cf t φ f) →
          ∀ (b : ℝ), 0 ≤ b → ∀ n : ℕ,
            MemCb (4 * d + 42) (r2WindowTest Cf (((24 * d + 240 : ℕ)) : ℝ) T b n α) ∧
            cbNorm (4 * d + 42) (r2WindowTest Cf (((24 * d + 240 : ℕ)) : ℝ) T b n α) ≤
              C * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα) := by
  have hsum : Summable fun α : MultiIndex d =>
      oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2) :=
    s103_summable (by omega)
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d s a β ρ0
  swap
  · refine ⟨1, 1, one_pos, hsum, fun ρβ hρ => absurd ⟨ρβ, hρ⟩ hex⟩
  obtain ⟨ρ0, hρ0⟩ := hex
  obtain ⟨Cc, cc, hcc, hcl⟩ := s103_orbit_claims hd hs0 hs ha hβ hρ0
  obtain ⟨Cw, hCw, hw⟩ := s103_window_tests hd hs0 hs ha hβ hρ0 hT
  refine ⟨max Cc Cw, cc, hcc, hsum, fun ρβ hρ α => ?_⟩
  have hρeq : ρβ = ρ0 := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hs ha hβ hρ, HRS.MS.Mov0.mv0_rho_eq hd hs0 hs ha hβ hρ0]
  subst hρeq
  intro Cf bα φ
  have hb0 : 0 ≤ bα := s103_b_nonneg α
  have hm : Cc * bα ≤ max Cc Cw * bα := mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  refine ⟨fun t ht => ?_, fun _ b hb n => ?_⟩
  · obtain ⟨s0, g0, s1, g1, s2⟩ := hcl α t ht
    exact ⟨s103_orbitSup_mono s0 hm, s103_orbitGrad_mono g0 hm, s103_orbitSup_mono s1 hm,
      s103_orbitGrad_mono g1 hm, s103_orbitSup_mono s2 hm⟩
  · obtain ⟨h1, h2⟩ := hw α b hb n
    refine ⟨h1, h2.trans ?_⟩
    have hx : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by positivity
    calc Cw * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b d α ≤
        max Cc Cw * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b d α := by
          gcongr; exact le_max_right _ _
      _ = _ := rfl

end HRS.MS.R2WinOrb

end
