import HRS.MS.R2GenInitNL4
import HRS.MS.R2WinErrNL7
import HRS.MS.R2GenInitAux43

/-!
# S10.5, nonlinear branch, part 5: `r2_window_general_initial` (D2 form) from the stationary comparison and the nonlinear inputs

`s105_compare_class`: `S105Compare` from `s105_compare_stat` and `S105CompareNL`.
`r2_window_general_initial_of_NL`: the frozen statement from `r2_window_orbits` (S10.3), `S104nAllOrb` (S10.4 nonlinear orbit regularity)
and `S105CompareNL` (the nonlinear window comparison), the last two
only for small `ε_*` (the class constants `(c₁,C₁)` are fixed first and `ε_*` is chosen after them).  Everything else is proved: the stationary window
comparison (`s105_compare_stat`), `hjmNL`, the nonlinear `hobs`/`hdyn` (from `S104nAllOrb`), the entropy and moment bounds (from `MovEntAt d s 1 (d/2+8)`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.Whole.AppendixA HRS.MS.R2WinErr

variable {d : ℕ}

theorem s105_compare_class {s a β T εstar c₁ C₁ : ℝ} (hstat : S105CompareStat d s a β T)
    (hnl : S105CompareNL d s a β T εstar c₁ C₁) : S105Compare d s a β T εstar c₁ C₁ := by
  obtain ⟨C1, h10, h1⟩ := hstat
  obtain ⟨C2, h20, h2⟩ := hnl
  refine ⟨max C1 C2, le_trans h10 (le_max_left _ _), ?_⟩
  intro ρβ hρβ ρ htraj N hN hGib Ω _ P _ X₀ W X hreal hfin η₀ hind Y hY hcont b hb F Wt hF hW
  have hm1 : ENNReal.ofReal C1 ≤ ENNReal.ofReal (max C1 C2) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hm2 : ENNReal.ofReal C2 ≤ ENNReal.ofReal (max C1 C2) := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  rcases htraj with rfl | hnl'
  · obtain ⟨a1, a2, a3, a4⟩ := h1 ρβ hρβ N hN hGib P X₀ W X hreal hfin η₀ hind Y hY hcont b hb F Wt hF hW
    exact ⟨a1, a2, a3.trans (by gcongr), a4.trans (by gcongr)⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h2 ρβ hρβ ρ hnl' N hN hGib P X₀ W X hreal hfin η₀ hind Y hY hcont b hb F Wt hF hW
    exact ⟨a1, a2, a3.trans (by gcongr), a4.trans (by gcongr)⟩

theorem r2_window_general_initial_of_NL
    (h103 : type_of% @HRS.Whole.r2_window_orbits)
    (hNL : ∀ {d : ℕ} (s a β c₁ C₁ : ℝ), ∃ εn : ℝ, 0 < εn ∧ ∀ εstar : ℝ, εstar ≤ εn → S104nAllOrb d s a β εstar c₁ C₁)
    (hcmpNL : ∀ {d : ℕ} (s a β T c₁ C₁ : ℝ), ∃ εn : ℝ, 0 < εn ∧ ∀ εstar : ℝ, εstar ≤ εn →
      S105CompareNL d s a β T εstar c₁ C₁) :
    type_of% @HRS.Whole.r2_window_general_initial := by
  intro d hd s hs0 hs a β ha hβ T hT c₁ C₁
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ε0, hε0, Cs0, cdec, hcdec, hsum, hmain⟩ := h103 hd s hs0 hsd a β ha hβ T hT c₁ C₁
  obtain ⟨εn, hεn, hNL'⟩ := hNL (d := d) s a β c₁ C₁
  obtain ⟨εc, hεc, hcmp'⟩ := hcmpNL (d := d) s a β T c₁ C₁
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
  refine r2_window_general_initial_core hd s hs0 hs a β ha hβ T hT εstar c₁ C₁ (hNL' _ hlen) Cs0 cdec hcdec hsum ?_
    (hent' εstar c₁ C₁ hles hsm1) (hmom' εstar c₁ C₁ hles2 hsm2)
    (s105_compare_class (s105_compare_stat hd hs0 hsd ha hβ hT) (hcmp' _ hlec))
  intro ρβ hρβ ρ htraj α
  have hm' := hmain ρβ hρβ ρ (s104_traj_mono hd hs0 hsd ha hβ hρβ hle0 htraj) α
  dsimp only at hm'
  exact ⟨fun t ht => (hm'.1 t ht).2.1, fun t ht => (hm'.1 t ht).2.2.2.1⟩

end HRS.MS.R2GenInit
