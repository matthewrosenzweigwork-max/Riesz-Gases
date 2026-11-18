import HRS.MS.S104bNL9
import HRS.MS.R2GenInitNL5

/-!
# S10.5 (nonlinear), packet S104b-NL10: `r2_window_general_initial` from the reduced analytic inputs

`s104b_general_initial_of_inputs`: the frozen statement `type_of% @HRS.Whole.r2_window_general_initial` from
* `h103 : type_of% @HRS.Whole.r2_window_orbits` (S10.3),
* `hTR`: `S104bTermRegGen` (general-initial-time terminal-time regularity of the nonlinear adjoint orbit) for small `ε_*`,
* `hReg`: `S105nReg` (`IsRegularMFRd` of the resulting solutions) for small `ε_*`.
Everything else (the stationary window comparison, the entropy and moment bounds, the master window comparison along the moving reference) is proved.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.R2WinErr HRS.MS.R2GenInit

variable {d : ℕ}

theorem s104b_general_initial_of_inputs
    (h103 : type_of% @HRS.Whole.r2_window_orbits)
    (hTR : ∀ {d : ℕ}, 2 ≤ d → ∀ (s a β c₁ C₁ : ℝ), 0 ≤ s → s < d → 0 < a → 0 < β → ∃ εn : ℝ, 0 < εn ∧
      ∀ εstar : ℝ, εstar ≤ εn → ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
        S104bTermRegGen d s a β ρβ εstar c₁ C₁)
    (hReg : ∀ {d : ℕ}, 2 ≤ d → ∀ (s a β c₁ C₁ : ℝ), 0 ≤ s → s < d → 0 < a → 0 < β → ∃ εn : ℝ, 0 < εn ∧
      ∀ εstar : ℝ, εstar ≤ εn → S105nReg d s a β εstar c₁ C₁) :
    type_of% @HRS.Whole.r2_window_general_initial := by
  intro d hd s hs0 hs a β ha hβ T hT c₁ C₁
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ε0, hε0, Cs0, cdec, hcdec, hsum, hmain⟩ := h103 hd s hs0 hsd a β ha hβ T hT c₁ C₁
  obtain ⟨εn, hεn, hTR'⟩ := hTR hd s a β c₁ C₁ hs0 hsd ha hβ
  obtain ⟨εc, hεc, hReg'⟩ := hReg hd s a β c₁ C₁ hs0 hsd ha hβ
  obtain ⟨εs, rr, hεs, hrr, hent'⟩ := s105_hent_class hd hs0 hsd ha hβ
  obtain ⟨εs2, rr2, hεs2, hrr2, hmom'⟩ := s105_hmom_class hd hs0 hsd ha hβ
  set Cp : ℝ := |C₁| + 1 with hCp
  have hCp0 : 0 < Cp := by positivity
  set εstar : ℝ := min ε0 (min εn (min εc (min εs (min εs2 (min (rr / Cp) (rr2 / Cp)))))) with hεstar
  have hεpos : 0 < εstar := by
    refine lt_min hε0 (lt_min hεn (lt_min hεc (lt_min hεs (lt_min hεs2 (lt_min ?_ ?_))))) <;> positivity
  have hle0 : εstar ≤ ε0 := min_le_left _ _
  have hlen : εstar ≤ εn := (min_le_right _ _).trans (min_le_left _ _)
  have hlec : εstar ≤ εc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hles : εstar ≤ εs := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hles2 : εstar ≤ εs2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hler : εstar ≤ rr / Cp := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hler2 : εstar ≤ rr2 / Cp := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hC1ε : C₁ * εstar ≤ Cp * εstar := mul_le_mul_of_nonneg_right ((le_abs_self C₁).trans (by rw [hCp]; linarith)) hεpos.le
  have hsm1 : C₁ * εstar ≤ rr := hC1ε.trans (by
    have := mul_le_mul_of_nonneg_left hler hCp0.le
    rwa [mul_div_cancel₀ _ hCp0.ne'] at this)
  have hsm2 : C₁ * εstar ≤ rr2 := hC1ε.trans (by
    have := mul_le_mul_of_nonneg_left hler2 hCp0.le
    rwa [mul_div_cancel₀ _ hCp0.ne'] at this)
  refine ⟨εstar, hεpos, ?_⟩
  refine r2_window_general_initial_core hd s hs0 hs a β ha hβ T hT εstar c₁ C₁ (s104b_allOrb_of_termRegGen (hTR' _ hlen)) Cs0 cdec hcdec hsum ?_
    (hent' εstar c₁ C₁ hles hsm1) (hmom' εstar c₁ C₁ hles2 hsm2)
    (s105_compare_class (s105_compare_stat hd hs0 hsd ha hβ hT)
      (HRS.MS.S104b.s104b_compare_NL hd hs0 hsd ha hβ hT (s104b_allOrb_of_termRegGen (hTR' _ hlen)) Cs0 cdec hcdec hsum
        (fun ρβ hρβ ε ψ ρ hadm hres α => by
          have hm' := hmain ρβ hρβ ρ (s104_traj_mono hd hs0 hsd ha hβ hρβ hle0 (Or.inr ⟨ε, ψ, hadm, hres⟩)) α
          dsimp only at hm'
          exact ⟨fun t ht => (hm'.1 t ht).2.1, fun t ht => (hm'.1 t ht).2.2.2.1⟩)
        (hReg' _ hlec)))
  intro ρβ hρβ ρ htraj α
  have hm' := hmain ρβ hρβ ρ (s104_traj_mono hd hs0 hsd ha hβ hρβ hle0 htraj) α
  dsimp only at hm'
  exact ⟨fun t ht => (hm'.1 t ht).2.1, fun t ht => (hm'.1 t ht).2.2.2.1⟩



end HRS.MS.S104b
