import HRS.MS.R2WinErrNL6

/-!
# S10.4, nonlinear branch, part 7: monotonicity of the class in `ε_*` and the frozen statement (D2 form)

`s104_traj_mono`: `IsR2WindowTrajectory` is monotone in `ε_*` (smaller `ε_*` gives a smaller class).
`r2_window_errors_of_NLorb`: `HRS.Whole.r2_window_errors` from `r2_window_orbits` (S10.3) and the nonlinear terminal-time regularity `S104nAllOrb`
(required only for small `ε_*`, as the class constants `(c₁,C₁)` are fixed first).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.Whole.AppendixA

theorem s104_C1_nonneg {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {εstar ε c₁ C₁ : ℝ} {ψ : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ} (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) : 0 ≤ C₁ := by
  have h1 := (hres.ratio 0 le_rfl 0).2
  have h2 : 0 ≤ ρ 0 0 := ((hres.global 0).density 0 ⟨le_rfl, le_rfl⟩).nonneg 0
  have h3 : 0 < ρβ 0 := HRS.Whole.u4_thermal_pos hρβ 0
  by_contra h
  push_neg at h
  nlinarith

theorem s104_traj_mono {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {εstar ε0 c₁ C₁ : ℝ} (hle : εstar ≤ ε0)
    {ρ : ℝ → Euc d → ℝ} (htraj : IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ) :
    IsR2WindowTrajectory d s a β ρβ ε0 c₁ C₁ ρ := by
  rcases htraj with h | ⟨ε, ψ, hadm, hres⟩
  · exact Or.inl h
  · refine Or.inr ⟨ε, ψ, ⟨hadm.smooth, hadm.compactSupport, hadm.nonzero, hadm.meanZero, hadm.small.trans hle⟩, ?_⟩
    have hC := s104_C1_nonneg hd hs0 hsd ha hβ hρβ hres
    refine ⟨hres.cpos, hres.global, hres.init, hres.ratio, fun t ht => ?_, fun t ht => ?_, hres.cont, hres.regular⟩
    · obtain ⟨h1, h2⟩ := hres.weighted t ht
      refine ⟨h1, h2.trans ?_⟩
      have := Real.exp_pos (-c₁ * t)
      nlinarith [mul_nonneg hC this.le]
    · refine (hres.velocity t ht).trans (ENNReal.ofReal_le_ofReal ?_)
      have := Real.exp_pos (-c₁ * t)
      nlinarith [mul_nonneg hC this.le]

/-- `r2_window_errors` from `r2_window_orbits` and the nonlinear orbit regularity (needed for small `ε_*` only). -/
theorem r2_window_errors_of_NLorb
    (h103 : type_of% @HRS.Whole.r2_window_orbits)
    (hNL : ∀ {d : ℕ} (s a β c₁ C₁ : ℝ), ∃ εn : ℝ, 0 < εn ∧ ∀ εstar : ℝ, εstar ≤ εn → S104nAllOrb d s a β εstar c₁ C₁) :
    type_of% @HRS.Whole.r2_window_errors := by
  intro d hd s hs0 hs a β ha hβ T hT c₁ C₁
  obtain ⟨ε0, hε0, Cs0, cdec, hcdec, hsum, hmain⟩ := h103 hd s hs0 hs a β ha hβ T hT c₁ C₁
  obtain ⟨εn, hεn, hNL'⟩ := hNL (d := d) s a β c₁ C₁
  refine ⟨min ε0 εn, lt_min hε0 hεn, ?_⟩
  refine r2_window_errors_core hd s hs0 hs a β ha hβ T hT (min ε0 εn) c₁ C₁ (hNL' _ (min_le_right _ _)) Cs0 cdec hcdec
    hsum ?_
  intro ρβ hρβ ρ htraj α
  have hm' := hmain ρβ hρβ ρ (s104_traj_mono hd hs0 hs ha hβ hρβ (min_le_left _ _) htraj) α
  dsimp only at hm'
  exact ⟨fun t ht => (hm'.1 t ht).2.1, fun t ht => (hm'.1 t ht).2.2.2.1⟩

end HRS.MS.R2WinErr
