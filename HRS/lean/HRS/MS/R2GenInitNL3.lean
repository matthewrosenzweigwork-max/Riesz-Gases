import HRS.MS.R2GenInitNL2

/-!
# S10.5, nonlinear branch, part 3: `S105Entropy` and `S105Moment` for the whole class `IsR2WindowTrajectory`

From `MovEntAt d s 1 (d/2+8)` (no repair of `mov_entropy` needed, `R2GenInitNL1`): there are `ε_s, r_s > 0` (depending on `d,s,a,β` only) such that for every
`ε_* ≤ ε_s` and `C₁ ε_* ≤ r_s` and every `c₁` the class `IsR2WindowTrajectory d s a β ρβ ε_* c₁ C₁` satisfies `S105Entropy` and `S105Moment`
(stationary branch: `s105_hent_stat`, `s105_hmom_stat`; nonlinear branch: `s105n_hent`, `s105n_hmom`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.Whole.AppendixA HRS.MS.R2WinErr

variable {d : ℕ}

theorem s105_hent_class (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ εs rr : ℝ, 0 < εs ∧ 0 < rr ∧ ∀ εstar c₁ C₁ : ℝ, εstar ≤ εs → C₁ * εstar ≤ rr →
      S105Entropy d s a β εstar c₁ C₁ := by
  obtain ⟨εs, rr, Cent, hεs, hrr, hCent, h⟩ := s105n_hent hd hs0 hsd ha hβ
  refine ⟨εs, rr, hεs, hrr, fun εstar c₁ C₁ h1 h2 => ⟨max Cent 1, le_trans zero_le_one (le_max_right _ _), ?_⟩⟩
  intro ρβ hρβ ρ htraj N hN hGib Ω _ P _ X₀ W X hreal hfin t ht
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := mul_nonneg (Nat.cast_nonneg _) hδ
  have hH : 0 ≤ (HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal (ρ 0)))).toReal + N * deltaN d s N := by
    have := ENNReal.toReal_nonneg (a := HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs
      (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ 0))))
    linarith
  rcases htraj with rfl | ⟨ε, ψ, hadm, hres⟩
  · refine (s105_hent_stat hd hs0 hsd ha hβ hρβ hN hGib P hreal hfin t ht).trans
      (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [le_max_right Cent 1]
  · refine (h εstar c₁ C₁ h1 h2 ρβ hρβ ε ψ ρ hadm hres N hN hGib P X₀ W X hreal hfin t ht).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hH

theorem s105_hmom_class (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ εs rr : ℝ, 0 < εs ∧ 0 < rr ∧ ∀ εstar c₁ C₁ : ℝ, εstar ≤ εs → C₁ * εstar ≤ rr →
      S105Moment d s a β εstar c₁ C₁ := by
  obtain ⟨εs, rr, Cent, hεs, hrr, hCent, h⟩ := s105n_hent hd hs0 hsd ha hβ
  obtain ⟨Cs, hCs0, hCs⟩ := s105_hmom_stat hd hs0 hsd ha hβ
  refine ⟨εs, rr, hεs, hrr, fun εstar c₁ C₁ h1 h2 => ?_⟩
  obtain ⟨Cn, hCn0, hCn⟩ := s105n_hmom hd hs0 hsd ha hβ εstar c₁ C₁ Cent hCent
  refine ⟨max Cs Cn, le_trans hCs0 (le_max_left _ _), ?_⟩
  intro ρβ hρβ ρ htraj N hN hGib Ω _ P _ X₀ W X hreal hfin t ht
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := mul_nonneg hN0.le hδ
  have hH : 0 ≤ 1 + (1 + (HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal (ρ 0)))).toReal + N * deltaN d s N) / N := by
    have := ENNReal.toReal_nonneg (a := HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs
      (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ 0))))
    positivity
  rcases htraj with rfl | ⟨ε, ψ, hadm, hres⟩
  · refine (hCs ρβ hρβ N hN hGib P X₀ W X hreal hfin t ht).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hH
  · refine (hCn ρβ hρβ ε ψ ρ hadm hres N hN P X₀ W X hreal hfin
      (fun t' ht' => h εstar c₁ C₁ h1 h2 ρβ hρβ ε ψ ρ hadm hres N hN hGib P X₀ W X hreal hfin t' ht') t ht).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hH

end HRS.MS.R2GenInit
