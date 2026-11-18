import HRS.Main.ThermLin2Fu16

/-!
# THERMLIN2 Fu17: smoothness of `U^{r,t}φ`, dual decay in `H^m`, and the `H^{m-a₀}` bound of `ψ_r`

The `H^{m-a₀}` bound uses the plan statement `tl2_Delta_bound` (B2) as a black box.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

theorem tl2fu_hadm (n : ℕ) : ∃ j' : ℕ, n ≤ j' ∧ (PDE.mStar d ≤ j') ∧ (d : ℝ) / 2 + 2 < j' := by
  refine ⟨n + PDE.mStar d + d + 4, by omega, by omega, ?_⟩
  have : d + 4 ≤ n + PDE.mStar d + d + 4 := by omega
  have h2 : ((d + 4 : ℕ) : ℝ) ≤ ((n + PDE.mStar d + d + 4 : ℕ) : ℝ) := by exact_mod_cast this
  have h3 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  push_cast at h2 ⊢
  linarith

open HRS.PDE HRS.PDE.MFAdjoint in
/-- `U^{r,t}φ` is smooth for smooth `φ`, `t > 0`, `r ∈ [0,t]`. -/
theorem tl2fu_prop_smooth (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    Torus.IsSmooth (propagator S.dyn S.ρ r t φ) := by
  obtain ⟨j0, -, hj0ms, hj0d⟩ := tl2fu_hadm (d := d) 0
  obtain ⟨_, _, hf0⟩ := tl2dy_moving_facts S h j0 hj0ms hj0d hφ ht
  obtain ⟨-, hC2, -⟩ := hf0 r hr
  have hcont : Continuous (propagator S.dyn S.ρ r t φ) := PDE.continuous_of_isCkU (m := 2) hC2
  refine tl2fu_smooth_of_sobolev hcont fun N => ?_
  obtain ⟨j'', hj''N, hj''ms, hj''d⟩ := tl2fu_hadm (d := d) N
  obtain ⟨_, _, hf''⟩ := tl2dy_moving_facts S h j'' hj''ms hj''d hφ ht
  obtain ⟨-, -, hmem, -⟩ := hf'' r hr
  refine tl2dy_memSob_mono ?_ hmem
  have : (N : ℝ) ≤ j'' := by exact_mod_cast hj''N
  push_cast
  linarith

/-- Dual decay: `‖U^{r,t}φ‖_{H^m} ≤ K e^{-c(t-r)} ‖φ‖_{H^m}` (in terms of `lpFun`), from the decay of `Vev`. -/
theorem tl2fu_dual_decay (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hVd : IsDualEvolution S.dyn S.ρ m Vev)
    {K c T' : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T' → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u)))
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 < t) (htT : t ≤ T') {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) :
    ‖lpFun m (propagator S.dyn S.ρ r t φ)‖ ≤ K * Real.exp (-c * (t - r)) * ‖lpFun m φ‖ := by
  have hfs := tl2fu_prop_smooth S h hφ ht hr
  have hfm : MemSobolev m (propagator S.dyn S.ρ r t φ) := PDE.MFSemigroup.memSobolev_of_isSmooth hfs m
  have hφm : MemSobolev m φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ m
  set z := lpFun m (propagator S.dyn S.ρ r t φ) with hz
  have e1 : NegSobolev.eval z (propagator S.dyn S.ρ r t φ) = ‖z‖ ^ 2 := by
    rw [eval_lpFun z hfm, ← hz, real_inner_self_eq_norm_sq]
  have e2 := hVd r t hr.1 hr.2 z φ hφ
  rw [← e2, eval_lpFun _ hφm] at e1
  have hb := hdec r t hr.1 hr.2 htT
  have h1 : ‖z‖ ^ 2 ≤ K * Real.exp (-c * (t - r)) * ‖lpFun m φ‖ * ‖z‖ := by
    rw [← e1]
    calc inner ℝ (Vev t r z) (lpFun m φ) ≤ ‖Vev t r z‖ * ‖lpFun m φ‖ := real_inner_le_norm _ _
      _ ≤ (‖Vev t r‖ * ‖z‖) * ‖lpFun m φ‖ :=
          mul_le_mul_of_nonneg_right ((Vev t r).le_opNorm z) (norm_nonneg _)
      _ ≤ (K * Real.exp (-c * (t - r)) * ‖z‖) * ‖lpFun m φ‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  rcases (norm_nonneg z).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith [h1, hpos]

end HRS.ThermLin.Plan2
