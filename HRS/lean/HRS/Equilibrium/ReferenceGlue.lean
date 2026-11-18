/-
# HRS.Equilibrium.ReferenceGlue -- glue between the two weak references (REF-GLUE)

Joins `HRS.External.Calib` (`CalibratedReference`: `R0`, `tN`, `RN`, `Xi`, `RefHyp`) with
`HRS.External.RefSmall` (`ReferenceSmallness`: `R0small`, `sup_calibration_field_le_one`).

1. `R0_eq_R0small`: the two weak references agree as measures;
2. `meanFeature_Xi_eq`: the mean feature of `Xi` is the expectation of `empXi`;
3. `eventually_hsmall`: `sup_t |t_N . Xi| <= 1` for all large `N` (fixed density `ρ`);
4. the two transfer theorems with `hsmall` replaced by `N₀ ≤ N`.
-/
import HRS.Equilibrium.CalibratedReference
import HRS.Equilibrium.ReferenceSmallness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.External.Glue

open HRS HRS.External.HeatSplit

variable {d : ℕ}

/-- `tiltMeasure P w = P.tilted w` for every measurable `w`: the two normalisations agree in the
integrable case, and both sides vanish otherwise. -/
theorem tiltMeasure_eq_tilted_of_measurable {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (w : α → ℝ) (hw : Measurable w) :
    tiltMeasure P w = P.tilted w := by
  by_cases hint : Integrable (fun a => Real.exp (w a)) P
  · have hZ : 0 < ∫ a, Real.exp (w a) ∂P := integral_exp_pos hint
    have hZl : ∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P = ENNReal.ofReal (∫ a, Real.exp (w a) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun a => (Real.exp_pos _).le)).symm
    unfold tiltMeasure Measure.tilted
    rw [hZl]
    ext s hs
    rw [Measure.smul_apply, withDensity_apply _ hs, withDensity_apply _ hs, smul_eq_mul]
    have hmeas : Measurable fun a => ENNReal.ofReal (Real.exp (w a)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw)
    have : ∀ a, ENNReal.ofReal (Real.exp (w a) / ∫ a, Real.exp (w a) ∂P) =
        (ENNReal.ofReal (∫ a, Real.exp (w a) ∂P))⁻¹ * ENNReal.ofReal (Real.exp (w a)) := by
      intro a
      rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hZ.le), ENNReal.ofReal_inv_of_pos hZ]
    simp_rw [this]
    rw [lintegral_const_mul _ hmeas]
  · rw [tilted_of_not_integrable hint]
    have hl : ∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P = ⊤ := by
      by_contra h
      apply hint
      have hm : Measurable fun a => ENNReal.ofReal (Real.exp (w a)) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw)
      have := integrable_toReal_of_lintegral_ne_top hm.aemeasurable h
      simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this
    unfold tiltMeasure
    rw [hl, ENNReal.inv_top, zero_smul]

/-- `R_N^0` (`CalibratedReference`) and `R⁰_N` (`ReferenceSmallness`) agree as measures: the pair
term `(β/N)·½∑_{i≠j} q(x_i - x_j)` equals `(β/N)·∑_{i<j} q(x_i - x_j)` for an even `q`, and the
two tilts (`Measure.tilted` and `tiltMeasure`) coincide. No sign or integrability condition on `β`
is needed. -/
theorem R0_eq_R0small {q : Torus d → ℝ} (hqm : Measurable q) (hq : ∀ x, q (-x) = q x)
    (β : ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ) :
    Calib.R0 q μ β N = RefSmall.R0small q β μ N := by
  have hE : Calib.E0 q μ β N = RefSmall.R0w q β μ N := by
    funext X
    unfold Calib.E0 RefSmall.R0w
    rw [RefSmall.pairSum_eq_half hq X]
    simp only [Finset.mul_sum]
  have hm : Measurable (RefSmall.R0w q β μ N) := by
    unfold RefSmall.R0w
    refine Measurable.sub ?_ ?_
    · exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        (HRS.PoleCavityAux.measurable_convMeasure hqm μ).comp (measurable_pi_apply i))
    · exact measurable_const.mul (HRS.PoleCavityAux.measurable_pairSum hqm)
  rw [RefSmall.R0small_eq]
  unfold Calib.R0
  rw [hE]
  exact (tiltMeasure_eq_tilted_of_measurable _ _ hm).symm

/-! ### The mean feature -/

/-- The mean feature `E_P[μ_N(Ξ)]` of `Ξ = Ψ - μ(Ψ)` (`ReferenceSmallness.meanFeature`) is the
expectation of the empirical average `empXi` (`CalibratedReference`), for `N > 0`. -/
theorem meanFeature_Xi_eq {M : ℕ} {μ : Measure (Torus d)} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)}
    (hΞm : Measurable (Calib.Xi μ Ψ)) {N : ℕ} (hN : 0 < N) (P : Measure (Config d N)) :
    RefSmall.meanFeature (Calib.Xi μ Ψ) P = ∫ X, Calib.empXi μ Ψ X ∂P := by
  unfold RefSmall.meanFeature
  congr 1
  funext X
  rw [RefSmall.integral_empirical_vec hN X hΞm]
  unfold Calib.empXi
  rw [one_div]

/-! ### Smallness of the calibration field on the weak split -/

/-- **Eventual smallness** `‖t_N·Ξ‖_∞ ≤ 1` (the hypothesis `hsmall` of `riesz_Q_le_smul_RN`) for the
weak split `weakSplit d s τ L`, with any features `Ψ` of `g_L` (e.g. the continuous ones of
`exists_continuous_features_weakSplit`), `Ξ = Ψ - μ(Ψ)` and a fixed probability density `ρ ≤ Λ`.
The threshold `N₀` depends on `ρ` (it comes from `sup_calibration_field_le_one`, which is not uniform
in `ρ`). -/
theorem eventually_hsmall {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ}
    (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) {β : ℝ} (hβ : 0 < β) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ x : Torus d,
      |∑ m, (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N).ofLp m *
        (Calib.Xi (withDensityReal ρ) Ψ x).ofLp m| ≤ 1 := by
  have := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  have hΛ1 : 1 ≤ Λ := by
    have hint : Integrable ρ := Integrable.of_bound hρ.measurable.aestronglyMeasurable Λ
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
        exact hρΛ x)
    have h1 : ∫ x, ρ x ≤ ∫ _x : Torus d, Λ := integral_mono hint (integrable_const Λ) hρΛ
    rw [hρ.integral_one] at h1
    simpa using h1
  have hΞm : Measurable (Calib.Xi (withDensityReal ρ) Ψ) := hRH.measurable_Xi
  have hB : ∀ x, ‖Calib.Xi (withDensityReal ρ) Ψ x‖ ≤ 2 * Real.sqrt ((weakSplit d s τ L).gL 0) :=
    hRH.norm_Xi_le
  have hΞ0 : ∫ x, Calib.Xi (withDensityReal ρ) Ψ x ∂(withDensityReal ρ) = 0 := hRH.integral_Xi
  have ht : ∀ n : ℕ, 1 ≤ n →
      ‖Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β n‖ ≤
        β * ‖RefSmall.meanFeature (Calib.Xi (withDensityReal ρ) Ψ)
          (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) n)‖ := by
    intro n hn
    have hnpos : 0 < n := by omega
    rw [meanFeature_Xi_eq hΞm hnpos, ← R0_eq_R0small hRH.q_meas hRH.q_even β (withDensityReal ρ) n]
    exact hRH.tN_norm_le hβ hnpos
  obtain ⟨n₀, hn₀⟩ := RefSmall.sup_calibration_field_le_one hd hs0 hsd hτ L hρ hΛ1 hρΛ hβ.le hΞm hB hΞ0
    (fun n => Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β n) ht
  refine ⟨n₀, fun N hN x => ?_⟩
  have h := hn₀ N hN x
  rw [← Calib.inner_eq_sum]
  exact h

/-! ### The transfer theorems with eventual smallness -/

/-- `riesz_Q_le_smul_RN` with the hypothesis `hsmall` replaced by `N₀ ≤ N`. -/
theorem riesz_Q_le_smul_RN_eventually {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ}
    (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y))
    {β : ℝ} (hβ : 0 < β) (hκ : Calib.KappaSmall β (Λ * (weakSplit d s τ L).c)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) ≤
        ENNReal.ofReal (Real.exp (4 * β * (weakSplit d s τ L).gL 0)) •
          Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N := by
  obtain ⟨N₀, hN₀⟩ := eventually_hsmall hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  exact Calib.riesz_Q_le_smul_RN hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ (by omega) hκ
    (fun x => hN₀ N (by omega) x)

/-- `riesz_variance_transfer` with the hypothesis `hsmall` replaced by `N₀ ≤ N`. -/
theorem riesz_variance_transfer_eventually {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ}
    (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y))
    {β : ℝ} (hβ : 0 < β) (hκ : Calib.KappaSmall β (Λ * (weakSplit d s τ L).c)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ F : Config d N → ℝ,
      MemLp F 2 (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) →
      variance F (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        Real.exp (4 * β * (weakSplit d s τ L).gL 0) *
          variance F (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) := by
  obtain ⟨N₀, hN₀⟩ := eventually_hsmall hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ
  refine ⟨max N₀ 1, fun N hN F hF => ?_⟩
  exact Calib.riesz_variance_transfer hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ (by omega) hκ
    (fun x => hN₀ N (by omega) x) F hF

end HRS.External.Glue

end
