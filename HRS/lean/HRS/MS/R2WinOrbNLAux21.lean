import HRS.MS.R2WinOrbNLAux20

/-!
# S10.3, part 21: the tie modulo the nonlinear window-test clause

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_tie`: `R2WinOrbED13 d s a β T` (the ED13 form of `HRS.Whole.r2_window_orbits`) follows from the stationary branch
(`HRS.MS.R2WinOrb.s103_stationary`, the derivative `deriv` replaced by `derivWithin` since the stationary map `t' ↦ generatorW Cf t' φ x` is constant), the proved nonlinear orbit
claims (`s103n_orbits_nonlinear'`) and the hypothesis `hW` that the window tests along the nonlinear class follow from the orbit claims (OPEN: `S103nWindowClause`).
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

theorem s103n_derivWithin_stationary (s a β : ℝ) (ρβ φ : Euc d → ℝ) (t : ℝ) (x : Euc d) :
    derivWithin (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t' φ x) (Set.Ici t) t =
      deriv (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t' φ x) t := by
  have hc : (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t' φ x) =
      fun _ => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) 0 φ x := rfl
  rw [hc, deriv_const, derivWithin_fun_const, Pi.zero_apply]

theorem s103n_tie (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ) (hT : 0 < T)
    (hW : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ εstar c₁ C₁ C c : ℝ,
      0 < εstar → 0 < c₁ → 0 < c → S103nOrbitClaims d s a β ρβ εstar c₁ C₁ C c →
      S103nWindowClause d s a β T ρβ εstar c₁ C₁) :
    R2WinOrbED13 d s a β T := by
  obtain ⟨Cs, cs, hcs, hsum, hstat⟩ := s103_stationary hd s hs0 hs a β ha hβ T hT
  intro c₁ C₁
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d s a β ρ0
  swap
  · exact ⟨1, one_pos, 1, 1, one_pos, hsum, fun ρβ hρ => absurd ⟨ρβ, hρ⟩ hex⟩
  obtain ⟨ρ0, hρ0⟩ := hex
  have H : Mov2dTh d s β a ρ0 := ⟨hd, hs0, hs, hβ, ha, hρ0⟩
  obtain ⟨εstar, hε, C, c, hc, hOrb⟩ := s103n_orbits_nonlinear' H c₁ C₁
  have hWc : S103nWindowClause d s a β T ρ0 εstar c₁ C₁ := by
    by_cases hc₁ : 0 < c₁
    · exact hW ρ0 hρ0 εstar c₁ C₁ C c hε hc₁ hc hOrb
    · exact ⟨0, fun ε ψ ρ _ hres => absurd hres.cpos hc₁⟩
  obtain ⟨Cw, hCw⟩ := hWc
  have huniq : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ρβ = ρ0 := fun ρβ hρ => by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hs ha hβ hρ, HRS.MS.Mov0.mv0_rho_eq hd hs0 hs ha hβ hρ0]
  refine ⟨εstar, hε, max (max (max Cs C) Cw) 0, min cs c, lt_min hcs hc, hsum, ?_⟩
  · intro ρβ hρβ ρ hρ α
    obtain rfl := huniq ρβ hρβ
    intro Cf bα φ
    have hb0 : 0 ≤ bα := s103_b_nonneg (d := d) α
    have hCm : 0 ≤ max (max (max Cs C) Cw) 0 * bα := mul_nonneg (le_max_right _ _) hb0
    rcases hρ with rfl | ⟨ε, ψ, hψ, hres'⟩
    · obtain ⟨h1, h2⟩ := hstat ρβ hρβ α
      have hm : Cs * bα ≤ max (max (max Cs C) Cw) 0 * bα :=
        mul_le_mul_of_nonneg_right (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)) hb0
      refine ⟨fun t ht => ?_, fun hex b hb n => ?_⟩
      · obtain ⟨c1, c2, c3, c4, c5⟩ := h1 t ht
        refine ⟨s103_orbitSup_mono c1 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c2 hm) (min_le_left _ _) hCm,
          s103_orbitSup_mono c3 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c4 hm) (min_le_left _ _) hCm, ?_⟩
        refine s103_orbitSup_mono ?_ hm
        have e : (fun x => generatorW Cf t (generatorW Cf t φ) x +
            derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t) =
            fun x => generatorW Cf t (generatorW Cf t φ) x + deriv (fun t' => generatorW Cf t' φ x) t := by
          funext x; rw [s103n_derivWithin_stationary]
        rw [e]; exact c5
      · obtain ⟨w1, w2⟩ := h2 hex b hb n
        refine ⟨w1, w2.trans ?_⟩
        have hx : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by positivity
        calc Cs * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα ≤
            max (max (max Cs C) Cw) 0 * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα := by
              gcongr; exact ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
          _ = _ := rfl
    · have hm : C * bα ≤ max (max (max Cs C) Cw) 0 * bα :=
        mul_le_mul_of_nonneg_right (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)) hb0
      refine ⟨fun t ht => ?_, fun hex b hb n => ?_⟩
      · obtain ⟨c1, c2, c3, c4, c5⟩ := hOrb ε ψ _ hψ hres' α t ht
        exact ⟨s103_orbitSup_mono c1 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c2 hm) (min_le_right _ _) hCm,
          s103_orbitSup_mono c3 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c4 hm) (min_le_right _ _) hCm,
          s103_orbitSup_mono c5 hm⟩
      · obtain ⟨w1, w2⟩ := hCw ε ψ _ hψ hres' α hex b hb n
        refine ⟨w1, w2.trans ?_⟩
        have hx : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by positivity
        calc Cw * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα ≤
            max (max (max Cs C) Cw) 0 * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα := by
              gcongr; exact (le_max_right _ _).trans ((le_max_left _ _))
          _ = _ := rfl

end HRS.MS.R2WinOrbNL

end
