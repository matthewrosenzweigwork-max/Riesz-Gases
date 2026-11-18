import HRS.ME.NfUPU2a
import HRS.ME.NfUPU5b

/-!
# Packet PU6 (uniform-in-`β` reference marginal density: `small_field`, `tv_R0_mu`,
`reference_marginal_density_L2`, `reference_marginal_density_uniform`)

Each `_unif` lemma copies the original statement (cited in its docstring) with the fixed data
`βm βp` (`0 < βm ≤ βp`), the constants chosen before `β ∈ [βm, βp]` and the hypothesis `KappaSmall`
replaced by `∀ β ∈ Icc βm βp, KappaSmall β (Λ c)`.

* `small_field_unif` (original `RefMarg.small_field`, ReferenceMarginal:2671): `sup_calibration_field_unif`.
* `tv_R0_mu_unif` (original `RefMarg.tv_R0_mu`, ReferenceMarginal:2931): the explicit bound
  `Real.sqrt (βp * C * aN d s (n+1) / 2)` (β bounded by βp, so that the bound is a fixed sequence).
  Proof: the original proof with `klDiv_R0small_weakSplit_le_unif`, `β ≤ βp` in the klDiv bound.
* `reference_marginal_density_L2_unif` (original `RefMarg.reference_marginal_density_L2`,
  ReferenceMarginal:2755): `core_L2_unif` and `small_field_unif` (with `ε = 1`).
* `reference_marginal_density_uniform_unif` (original `RefMarg.reference_marginal_density_uniform`,
  ReferenceMarginal:3401): `core_unif_unif`, `small_field_unif`, `tv_R0_mu_unif`; the sequence
  `ε₀ N = Real.sqrt (βp * C₃ * aN N / 2)` tends to `0` and does not depend on `β`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.NfU

open HRS HRS.External HRS.External.Calib HeatSplit HRS.External.RefMarg InformationTheory

variable {d : ℕ}

/-- Uniform version of `RefMarg.small_field` (`HRS/Equilibrium/ReferenceMarginal.lean:2671`). -/
theorem small_field_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ} (hβm : 0 < βm) (hββ : βm ≤ βp)
    {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₀ ≤ N → ∀ x : Torus d,
        |inner ℝ (tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) (Xi (withDensityReal ρ) Ψ x)| ≤ ε :=
  sup_calibration_field_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ Ψ hΨ

/-- Uniform version of `RefMarg.tv_R0_mu` (`HRS/Equilibrium/ReferenceMarginal.lean:2931`): the
constants `C, N₁` are chosen before `β ∈ [βm, βp]`, and the bound uses `βp` in place of `β`. -/
theorem tv_R0_mu_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ} (hβm : 0 < βm) (hββ : βm ≤ βp)
    {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∃ (C : ℝ) (N₁ : ℕ), 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ n : ℕ, N₁ ≤ n + 1 →
      HRS.External.Entropy.tvDist ((R0 (weakSplit d s τ L).q (withDensityReal ρ) β (n + 1)).map
          (fun X => X ⟨0, Nat.succ_pos n⟩)) (withDensityReal ρ) ≤
        Real.sqrt (βp * C * aN d s (n + 1) / 2) := by
  obtain ⟨C, hC0, N₁, hN₁2, hKL⟩ := klDiv_R0small_weakSplit_le_unif hd hs0 hsd hτ L hΛ1
  refine ⟨C, N₁, hC0, fun β hβ ρ hρ hΛρ n hN1 => ?_⟩
  have hβ0 : 0 ≤ β := le_trans hβm.le hβ.1
  have hβpβ : β ≤ βp := hβ.2
  have hβp0 : 0 ≤ βp := le_trans hβ0 hβpβ
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have h := refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  have hq := RefSmall.smallKernel_weakSplit hd hs0 hsd hτ L
  set P := RefSmall.R0small (weakSplit d s τ L).q β μ (n + 1) with hP
  haveI : IsProbabilityMeasure P := hq.isProb_R0small hρ hΛρ hβ0 (n + 1)
  have hPex := RefSmall.R0small_isExchangeable hq.meas hq.even β μ (n + 1)
  have hR0 : R0 (weakSplit d s τ L).q μ β (n + 1) = P := RefMarg.R0_eq_R0small h hβ0 (n + 1)
  rw [hR0]
  set π0 := P.map (fun X => X ⟨0, Nat.succ_pos n⟩) with hπ0
  have hmul := hPex.mul_klDiv_marginal_le μ ⟨0, Nat.succ_pos n⟩ P
  have hK := hKL β hβ0 ρ hρ hΛρ (n + 1) hN1
  have ha0 : 0 ≤ aN d s (n + 1) := aN_nonneg_unif (d := d) (s := s) (N := n + 1) (by omega)
  have hCa : 0 ≤ C * aN d s (n + 1) := mul_nonneg hC0 ha0
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have e : ENNReal.ofReal (β * ((n + 1 : ℕ) : ℝ) * (C * aN d s (n + 1))) =
      ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (β * (C * aN d s (n + 1))) := by
    rw [show β * ((n + 1 : ℕ) : ℝ) * (C * aN d s (n + 1)) =
      ((n + 1 : ℕ) : ℝ) * (β * (C * aN d s (n + 1))) by ring,
      ENNReal.ofReal_mul hn0.le, ENNReal.ofReal_natCast]
  have hK2 : InformationTheory.klDiv π0 μ ≤ ENNReal.ofReal (βp * (C * aN d s (n + 1))) := by
    rw [e] at hK
    have h3 := (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 (hmul.trans hK)
    exact h3.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hβpβ hCa))
  have hKne : InformationTheory.klDiv π0 μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK2
  refine (HRS.External.Entropy.tvDist_le_sqrt_klDiv π0 μ hKne).trans (Real.sqrt_le_sqrt ?_)
  have htoR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hK2
  rw [ENNReal.toReal_ofReal (mul_nonneg hβp0 hCa)] at htoR
  linarith

/-- Uniform version of `RefMarg.reference_marginal_density_L2`
(`HRS/Equilibrium/ReferenceMarginal.lean:2755`). -/
theorem reference_marginal_density_L2_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp)
    (hκ : ∀ β ∈ Set.Icc βm βp, KappaSmall β (Λ * (weakSplit d s τ L).c))
    {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₀ ≤ N →
      firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)).rnDeriv
            (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10, -, -, h13, -, h15, -, -⟩ :=
    weakSplit_spec hd hs0 hsd hτ hτ1 L
  set c : ℝ := (weakSplit d s τ L).c with hc
  set q : Torus d → ℝ := (weakSplit d s τ L).q with hq
  set gL : Torus d → ℝ := (weakSplit d s τ L).gL with hgL
  obtain ⟨B, hB0, hB⟩ := h15
  obtain ⟨K0, hK0, hw⟩ := weakLp_of_envelope hd hs0 hsd hB0 hB
  have hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c := by
    have := ofReal_integral_eq_lintegral_ofReal h7 (Filter.Eventually.of_forall h6)
    rw [h8] at this
    exact le_of_eq this.symm
  have hkm : Measurable (fun w => gL w + q w) := h13.measurable.add h5
  have hgLi : Integrable gL := h13.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace gL)
  have hki : Integrable (fun w => gL w + q w) := hgLi.add h7
  set ĝ : Lattice d → ℝ := fun n => rieszCoeff d s n + (if n = 0 then c else 0) with hĝdef
  have hĝ : ∀ n, 0 ≤ ĝ n := by
    intro n
    by_cases hn : n = 0
    · simp [hĝdef, hn, rieszCoeff, h10]
    · have := rieszCoeff_pos hd hs0 hsd n hn
      simp [hĝdef, hn]; exact this.le
  have hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (((gL x + q x : ℝ)) : ℂ) = (ĝ n : ℂ) := by
    intro n
    have e1 : ∫ x, Torus.mode (-n) x * (((gL x + q x : ℝ)) : ℂ) =
        ∫ x, (Torus.mode (-n) x * ((periodicRiesz d s x : ℝ) : ℂ) + Torus.mode (-n) x * (c : ℂ)) := by
      refine integral_congr_ae ?_
      filter_upwards [h4] with x hx
      rw [← mul_add]
      congr 1
      rw [hx]; push_cast; ring
    rw [e1]
    have hgi : Integrable (fun x => Torus.mode (-n) x * ((periodicRiesz d s x : ℝ) : ℂ)) := by
      have := (KernelAux.integrable_periodicRiesz hd hs0 hsd).ofReal (𝕜 := ℂ)
      exact this.bdd_mul (c := 1) (Torus.continuous_mode (-n)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-n) x).le)
    have hci : Integrable (fun x => Torus.mode (-n) x * (c : ℂ)) := by
      have : Integrable (fun x => Torus.mode (-n) x) :=
        (integrable_const (1 : ℂ)).bdd_mul (c := 1) (Torus.continuous_mode (-n)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-n) x).le) |>.congr
          (Filter.Eventually.of_forall fun x => by simp)
      exact this.mul_const _
    rw [integral_add hgi hci, KernelAux.integral_periodicRiesz_mode hd hs0 hsd n, integral_mul_const,
      Torus.integral_mode (-n)]
    by_cases hn : n = 0
    · simp [hĝdef, hn, rieszCoeff]
    · have : -n ≠ 0 := neg_ne_zero.2 hn
      simp [hĝdef, hn, this]
  have hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q gL Ψ (Λ * c) := fun ρ hρ hΛρ =>
    refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  obtain ⟨C, N₁, hcore⟩ := core_L2_unif hd hs0 hsd hΛ1 hβm hββ h10 hRef h5 h6 (hQ_even hd hs0 hsd τ L) h7
    hqc hK0 hw hkm hki ĝ hĝ hcoef hκ
  obtain ⟨N₂, hsmall⟩ := small_field_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ Ψ hΨ 1 one_pos
  refine ⟨C, max N₁ N₂, fun β hβ ρ hρ hΛρ N hN => ?_⟩
  exact hcore β hβ ρ hρ hΛρ N (le_trans (le_max_left _ _) hN)
    (fun x => hsmall β hβ ρ hρ hΛρ N (le_trans (le_max_right _ _) hN) x)

/-- Uniform version of `RefMarg.reference_marginal_density_uniform`
(`HRS/Equilibrium/ReferenceMarginal.lean:3401`). -/
theorem reference_marginal_density_uniform_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ}
    (hβm : 0 < βm) (hββ : βm ≤ βp)
    (hκ : ∀ β ∈ Set.Icc βm βp, KappaSmall β (Λ * (weakSplit d s τ L).c))
    {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₀ ≤ N →
      firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          |((firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ ε := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10, -, -, h13, -, h15, -, -⟩ :=
    weakSplit_spec hd hs0 hsd hτ hτ1 L
  set c : ℝ := (weakSplit d s τ L).c with hc
  set q : Torus d → ℝ := (weakSplit d s τ L).q with hq
  obtain ⟨B, hB0, hB⟩ := h15
  obtain ⟨K0, hK0, hw⟩ := weakLp_of_envelope hd hs0 hsd hB0 hB
  have hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c := by
    have := ofReal_integral_eq_lintegral_ofReal h7 (Filter.Eventually.of_forall h6)
    rw [h8] at this
    exact le_of_eq this.symm
  have hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q (weakSplit d s τ L).gL Ψ (Λ * c) := fun ρ hρ hΛρ =>
    refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  obtain ⟨C₃, N₃, hC₃0, hTV3⟩ := tv_R0_mu_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ Ψ hΨ
  have hε₀ : Tendsto (fun N : ℕ => Real.sqrt (βp * C₃ * aN d s N / 2)) atTop (𝓝 0) := by
    have h1 := (RefSmall.tendsto_aN (by omega : 1 ≤ d) hs0 hsd)
    have h2 : Tendsto (fun N : ℕ => βp * C₃ * aN d s N / 2) atTop (𝓝 0) := by
      simpa using (h1.const_mul (βp * C₃)).div_const 2
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at this
    exact this
  intro ε hε
  exact core_unif_unif hd hs0 hsd hΛ1 hβm hββ h10 hRef h5 h6 (hQ_even hd hs0 hsd τ L) hqc hK0 hw hκ
    (small_field_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ Ψ hΨ) hε₀ (N₃ := N₃)
    (fun β hβ ρ hρ hΛρ n hN3 _ => hTV3 β hβ ρ hρ hΛρ n hN3) ε hε

end HRS.ME.NfU

end
