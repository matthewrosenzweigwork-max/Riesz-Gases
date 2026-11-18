import HRS.MS.R2WinErrAux20

/-!
# S10.4 input `hdyn` for the stationary trajectory (part 1): the integrated evolution inequality

`s104_hevol_stat`: for the stationary coefficient, `ofReal|Fm(t,r)| ≤ ofReal|Fm(t₀,r)| + ∫⁻_{(t₀,t]} ofReal|F2(s',r)| ds'` for `0 ≤ r ≤ t₀ ≤ t ≤ b+T`
(`Fm = r2CommForcingMov`, `F2 = s104_F2`), from the pathwise Duhamel formula `s53_ftc` for the commutator functional along the orbit family
`G0 τ = U(0,τ)φ_α → G1 τ = U(0,τ)Lφ_α` and time homogeneity `U(r,t) = U(0,t-r)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.S53

variable {d N : ℕ}

/-- Translation of a lower integral over an interval. -/
lemma s104_lintegral_Ioc_sub (f : ℝ → ℝ≥0∞) (a b r : ℝ) :
    ∫⁻ σ in Set.Ioc (a - r) (b - r), f σ = ∫⁻ s' in Set.Ioc a b, f (s' - r) := by
  have h1 : ∫⁻ x, (Set.Ioc (a - r) (b - r)).indicator f (x - r) = ∫⁻ x, (Set.Ioc (a - r) (b - r)).indicator f x :=
    lintegral_sub_right_eq_self (μ := volume) ((Set.Ioc (a - r) (b - r)).indicator f) r
  have h2 : ∀ x, (Set.Ioc (a - r) (b - r)).indicator f (x - r) = (Set.Ioc a b).indicator (fun s' => f (s' - r)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioc a b
    · have : x - r ∈ Set.Ioc (a - r) (b - r) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hx]
    · have : x - r ∉ Set.Ioc (a - r) (b - r) := fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hx]
  simp_rw [h2] at h1
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
  exact h1.symm

/-- The Duhamel formula between two terminal times. -/
lemma s104_stat_ftc {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) {T0 : ℝ}
    {G0 G1 : ℝ → Euc d → ℝ} (hG0 : ∀ τ ∈ Icc (0 : ℝ) T0, MemCb 2 (G0 τ))
    (hG1 : ∀ τ ∈ Icc (0 : ℝ) T0, MemCb 2 (G1 τ)) (hd01 : S53Diff T0 G0 G1) (hc1 : S53Cont T0 G1)
    (Z : EucConfig d N) {τ0 τ : ℝ} (h0 : 0 ≤ τ0) (h01 : τ0 ≤ τ) (hτ : τ ≤ T0) :
    s53_Dk s ρ (G0 τ) Z = s53_Dk s ρ (G0 τ0) Z + ∫ σ in Ioc τ0 τ, s53_Dk s ρ (G1 σ) Z := by
  have hτ0 : τ0 ∈ Icc (0 : ℝ) T0 := ⟨h0, h01.trans hτ⟩
  have hτm : τ ∈ Icc (0 : ℝ) T0 := ⟨h0.trans h01, hτ⟩
  have e1 := s53_ftc ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN hG0 hG1 hd01 hc1 Z hτm
  have e0 := s53_ftc ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN hG0 hG1 hd01 hc1 Z hτ0
  have hcont := s53_Dk_continuousOn ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN hG1 hc1 Z
  have hi1 : IntervalIntegrable (fun σ => s53_Dk s ρ (G1 σ) Z) volume 0 τ0 :=
    (hcont.mono (Icc_subset_Icc_right (h01.trans hτ))).intervalIntegrable_of_Icc h0
  have hi2 : IntervalIntegrable (fun σ => s53_Dk s ρ (G1 σ) Z) volume τ0 τ :=
    (hcont.mono (Icc_subset_Icc h0 hτ)).intervalIntegrable_of_Icc h01
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [intervalIntegral.integral_of_le h0, intervalIntegral.integral_of_le h01,
    intervalIntegral.integral_of_le (h0.trans h01)] at hadd
  rw [e1, e0, ← hadd]
  ring

end HRS.MS.R2WinErr
