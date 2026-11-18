import HRS.MS.R2WinOrbNLAux6

/-!
# S10.3 (nonlinear branch), part 7: the first four orbit claims

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_claims1234`: for every trajectory `ρ` of the S6.3 small class (radius `r ≤ 1`) with the
gradient estimate and the zeroth-order bound (`S103nGrad`, `S103nZero`), and every `α`, `t ≥ 0`: the claims `R2OrbitSup`/`R2OrbitGrad` for the
terminal data `φ_α` and `L_tφ_α` with one constant `C` independent of the trajectory, `α`, `t`.  (The fifth claim, for `L_t²φ_α + ∂_tL_tφ_α`,
is not part of this file.)
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc
open HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s103n_claims1234 {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {Cg cg Cz : ℝ}
    (hCg : 0 ≤ Cg) (hcg : 0 < cg) (hCz : 0 ≤ Cz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r c₁ : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ c₁ →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s a β ρβ (102 * d + 1020) r c₁ f0 ρ →
      S103nGrad d s a β ρβ ρ Cg cg → S103nZero d s a β ρβ ρ Cz →
      ∀ (α : MultiIndex d) (t : ℝ), 0 ≤ t →
        R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
          (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) (C * s103_b d α) ∧
        R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
          (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) (C * s103_b d α) cg ∧
        R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
          (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α))
          (C * s103_b d α) ∧
        R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
          (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α))
          (C * s103_b d α) cg := by
  obtain ⟨C12, hC120, hC12⟩ := s103n_claims12 H.hd H.hs0 H.hsd H.hq H.hβ H.hρ hCg hcg hCz
  obtain ⟨K1, hK10, hK1⟩ := s103n_g1_data H
  refine ⟨max C12 (max (2 * Cg * K1) ((1 + 2 * Cz) * K1 + 2 * Cg * K1)), by positivity,
    fun r c₁ hr0 hr1 hc₁ f0 ρ hρ hG hZ α t ht => ?_⟩
  have hb0 := s103_b_nonneg (d := d) α
  have hB0 : 0 ≤ K1 * s103_b d α := mul_nonneg hK10 hb0
  obtain ⟨s0, g0⟩ := hC12 ρ hG hZ α t ht
  obtain ⟨k1, k2, k3, k4, k5⟩ := hK1 r c₁ hr0 hr1 hc₁ f0 ρ hρ t ht α
  obtain ⟨g1, s1⟩ := s103n_orbit_of_data hCg hcg hCz hG hZ _ _ hB0 k1 k2 k3 k4 k5 t ht
  have hm0 : C12 * s103_b d α ≤
      max C12 (max (2 * Cg * K1) ((1 + 2 * Cz) * K1 + 2 * Cg * K1)) * s103_b d α :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  have hm1 : 2 * Cg * (K1 * s103_b d α) ≤
      max C12 (max (2 * Cg * K1) ((1 + 2 * Cz) * K1 + 2 * Cg * K1)) * s103_b d α := by
    calc 2 * Cg * (K1 * s103_b d α) = (2 * Cg * K1) * s103_b d α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hb0
  have hm2 : (1 + 2 * Cz) * (K1 * s103_b d α) + 2 * Cg * (K1 * s103_b d α) ≤
      max C12 (max (2 * Cg * K1) ((1 + 2 * Cz) * K1 + 2 * Cg * K1)) * s103_b d α := by
    calc (1 + 2 * Cz) * (K1 * s103_b d α) + 2 * Cg * (K1 * s103_b d α) =
        ((1 + 2 * Cz) * K1 + 2 * Cg * K1) * s103_b d α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hb0
  exact ⟨s103_orbitSup_mono s0 hm0, s103_orbitGrad_mono g0 hm0, s103_orbitSup_mono s1 hm2,
    s103_orbitGrad_mono g1 hm1⟩

end HRS.MS.R2WinOrbNL

end
