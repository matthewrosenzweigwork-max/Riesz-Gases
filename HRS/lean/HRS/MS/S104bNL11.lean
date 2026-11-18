import HRS.MS.S104bNL10

/-!
# S10.4 (nonlinear), packet S104b-NL11: `r2_window_errors` from `r2_window_orbits` and the general-initial-time terminal-time regularity

`s104b_errors_of_inputs`: `type_of% @HRS.Whole.r2_window_errors` from `h103 : type_of% @HRS.Whole.r2_window_orbits` and `hTR` (`S104bTermRegGen` for small `ε_*`).
-/

noncomputable section

namespace HRS.MS.S104b

open HRS HRS.Whole HRS.MS.R2WinErr

theorem s104b_errors_of_inputs
    (h103 : type_of% @HRS.Whole.r2_window_orbits)
    (hTR : ∀ {d : ℕ}, 2 ≤ d → ∀ (s a β c₁ C₁ : ℝ), 0 ≤ s → s < d → 0 < a → 0 < β → ∃ εn : ℝ, 0 < εn ∧
      ∀ εstar : ℝ, εstar ≤ εn → ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
        S104bTermRegGen d s a β ρβ εstar c₁ C₁) :
    type_of% @HRS.Whole.r2_window_errors := by
  intro d hd s hs0 hs a β ha hβ T hT c₁ C₁
  obtain ⟨ε0, hε0, Cs0, cdec, hcdec, hsum, hmain⟩ := h103 hd s hs0 hs a β ha hβ T hT c₁ C₁
  obtain ⟨εn, hεn, hTR'⟩ := hTR hd s a β c₁ C₁ hs0 hs ha hβ
  refine ⟨min ε0 εn, lt_min hε0 hεn, ?_⟩
  refine r2_window_errors_core hd s hs0 hs a β ha hβ T hT (min ε0 εn) c₁ C₁
    (s104b_allOrb_of_termRegGen (hTR' _ (min_le_right _ _))) Cs0 cdec hcdec hsum ?_
  intro ρβ hρβ ρ htraj α
  have hm' := hmain ρβ hρβ ρ (s104_traj_mono hd hs0 hs ha hβ hρβ (min_le_left _ _) htraj) α
  dsimp only at hm'
  exact ⟨fun t ht => (hm'.1 t ht).2.1, fun t ht => (hm'.1 t ht).2.2.2.1⟩

end HRS.MS.S104b
