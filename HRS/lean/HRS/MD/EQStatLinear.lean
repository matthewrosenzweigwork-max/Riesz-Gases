import HRS.MD.EQStatQuadratic
import HRS.Equilibrium.Q32cAux1

/-!
# EQ-STATIC-U, part 8: `eq_static_linear`, uniform in `β ∈ [β₋,β₊]` and the thermal density family

The linear variance bound of `HRS.Q32c` (`q32c_main`, fixed `β`, uniform in `ρ ≤ Λ`) with every `β`-dependent constant replaced
by its monotone bound at `β₊`: the weak split `(τ, L, Λ, Ψ)` with `β₊ γ` small comes from `EqMarg.eqmarg_split_params`; the
threshold of the calibration smallness from `EqMarg.eqmarg_small_calib` (uniform in `β ∈ (0, β₊]` and `ρ ≤ Λ`); the transfer constants
`e^{4βg_L(0)}`, `e^{8βNg_L(0)}` and the marginal constant `e^{2βγ+1}` are bounded at `β₊`, and `KappaSmall` is monotone in `β`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.MD.EQStat

open Function
open HRS HRS.Quad HRS.External HRS.External.RefMarg HRS.External.PoleVar HRS.External.HeatSplit HRS.External.Calib

variable {d : ℕ} {s : ℝ}

/-- **Crude linear bound for a fixed `N`**, uniform in `β ∈ [β₋,β₊]` and `ρ ≤ Λ₀`. -/
theorem eqstat_lin_crude (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ0 : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ C : ℝ, ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ y, ρ y ≤ Λ0) →
      ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρ) →
      (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  have hN0 : 0 < N := by omega
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ0le, hΨ, hc0, hg0, hκ⟩ :=
    HRS.EqMarg.eqmarg_split_params hd hs0 hsd βp hβp Λ0
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  set gL0 : ℝ := (weakSplit d s τ L).gL 0 with hgL0
  have hγ0 : 0 ≤ γ := mul_nonneg (by linarith) hc0
  set K0 : ℝ := max 1 (4 * βp * gL0) with hK0
  set K' : ℝ := Real.exp (8 * βp * N * gL0) with hK'
  set Ep : ℝ := Real.exp ((βp * γ + K0) + 0 + βp * γ) with hEp
  have hK'0 : 0 < K' := Real.exp_pos _
  refine ⟨N * (K' * Ep), ?_⟩
  intro β hβ1 hβ2 ρ hρ hρΛ0 f hf hf2
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hρΛ : ∀ y, ρ y ≤ Λ := fun y => (hρΛ0 y).trans hΛ0le
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  have ht0 : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ K0 :=
    fun x => (abs_tN_inner_le hRH hβ hN0 x).trans
      ((mul_le_mul_of_nonneg_right (by linarith) hg0).trans (le_max_right _ _))
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ht0 with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N =
      pinnedLaw V (β / ((N : ℕ) : ℝ)) N (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht0, pinnedLaw_empty]
  have hQK : modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) ≤
      ENNReal.ofReal K' • Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N := by
    have hle : Real.exp (8 * β * N * gL0) ≤ K' := by
      refine Real.exp_le_exp.2 ?_
      have : 8 * β * (N : ℝ) ≤ 8 * βp * (N : ℝ) := by
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
        nlinarith
      exact mul_le_mul_of_nonneg_right this hg0
    exact (HRS.Q32c.q32c_Q_le_smul_RN_crude hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ hN0).trans
      (eqstat_smul_mono hle)
  have hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ hN0
  have hEpβ : Real.exp ((β * γ + K0) + 0 + β * γ) ≤ Ep := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hm : ∀ i : Fin N, (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)).map (fun X => X i) ≤
      ENNReal.ofReal (K' * Ep) • withDensityReal ρ := by
    intro i
    have h1 : (pinnedLaw V (β / ((N : ℕ) : ℝ)) N (fun e : Empty => e.elim)).map (fun y => y i) ≤
        ENNReal.ofReal (Real.exp ((β * γ + K0) + 0 + β * γ)) • withDensityReal ρ :=
      marginal_le_smul (B := Empty) V hβ.le hN0 (n := N) (by simp) (fun e => e.elim) i
    rw [← hRN] at h1
    refine (Measure.map_mono hQK (measurable_pi_apply i)).trans ?_
    rw [Measure.map_smul _ (measurable_pi_apply i).aemeasurable]
    refine Measure.le_iff'.2 fun A => ?_
    have h2 := h1 A
    rw [Measure.smul_apply, smul_eq_mul] at h2
    rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal K' * (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N).map (fun X => X i) A
        ≤ ENNReal.ofReal K' * (ENNReal.ofReal (Real.exp ((β * γ + K0) + 0 + β * γ)) * withDensityReal ρ A) :=
          mul_le_mul' le_rfl h2
      _ ≤ ENNReal.ofReal K' * (ENNReal.ofReal Ep * withDensityReal ρ A) :=
          mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hEpβ) le_rfl)
      _ = _ := by rw [← mul_assoc, ENNReal.ofReal_mul hK'0.le]
  exact HRS.Q32b.q32b_marg_bound hN0 (mul_nonneg hK'0.le (Real.exp_pos _).le) hm hf hf2

/-- **Large-`N` linear bound**, uniform in `β ∈ [β₋,β₊]` and `ρ ≤ Λ₀`. -/
theorem eqstat_lin_large (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ y, ρ y ≤ Λ0) →
      ∀ N : ℕ, N₁ ≤ N → 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρ) →
      (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ0Λ, hΨ, hc0, hgL00, hκβp⟩ :=
    HRS.EqMarg.eqmarg_split_params hd hs0 hsd βp hβp Λ0
  have hΛ0 : 0 ≤ Λ := by linarith
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  have hγ0 : 0 ≤ γ := mul_nonneg hΛ0 hc0
  set gL0 : ℝ := (weakSplit d s τ L).gL 0 with hgL0
  have hκall : ∀ β : ℝ, 0 < β → β ≤ βp → KappaSmall β γ := fun β hβ hβ2 =>
    kappaSmall_of_le hβ hγ0 ((mul_le_mul_of_nonneg_right hβ2 hγ0).trans hκβp)
  obtain ⟨n₀, hn₀⟩ := HRS.EqMarg.eqmarg_small_calib hd hs0 hsd hτ hτ1 L hΛ1 Ψ hΨ βp hβp
  set KQ : ℝ := Real.exp (4 * βp * gL0) with hKQ
  have hKQ0 : 0 < KQ := Real.exp_pos _
  set E : ℝ := Real.exp ((βp * γ + 1) + 0 + βp * γ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨2 * KQ * E, max n₀ 2, ?_⟩
  intro β hβ1 hβ2 ρ hρ hρΛ0 N hN hN2 f hf hf2
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hρΛ : ∀ y, ρ y ≤ Λ := fun y => (hρΛ0 y).trans hΛ0Λ
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  have hκ : KappaSmall β γ := hκall β hβ hβ2
  have hNN₀ : n₀ ≤ N := le_trans (le_max_left _ _) hN
  have hβγ : β * γ ≤ βp * γ := mul_le_mul_of_nonneg_right hβ2 hγ0
  have hEβ : Real.exp ((β * γ + 1) + 0 + β * γ) ≤ E := Real.exp_le_exp.2 (by linarith)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hNn : 0 < n + 1 := Nat.succ_pos n
  have ht : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1))
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ 1 := fun x =>
    hn₀ β hβ hβ2 ρ hρ hρΛ (n + 1) hNN₀ x
  have hsmall : ∀ x, |∑ m, (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)).ofLp m *
      (Calib.Xi (withDensityReal ρ) Ψ x).ofLp m| ≤ 1 := fun x => by
    have := ht x
    rwa [Calib.inner_eq_sum] at this
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) ht with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1) =
      pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht, pinnedLaw_empty]
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le hRH hβ.le ht hκ
  have hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ hNn
  have hQK0 := Calib.riesz_Q_le_smul_RN hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ hNn hκ hsmall
  have hQK1 : modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤
      ENNReal.ofReal KQ • Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1) := by
    refine hQK0.trans (eqstat_smul_mono (Real.exp_le_exp.2 ?_))
    have : 4 * β * gL0 ≤ 4 * βp * gL0 := by nlinarith [hgL00]
    exact this
  rw [hRN] at hQK1
  set R0 := pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) with hR0
  have hRp : IsProbabilityMeasure (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) :=
    hRH.isProb_RN hβ.le
  have hR0p : IsProbabilityMeasure R0 := by rw [← hRN]; exact hRp
  set π0 : Measure (Torus d) := R0.map (fun X => X 0) with hπ0
  have hπ0p : IsProbabilityMeasure π0 := inferInstance
  have hπ0le : π0 ≤ ENNReal.ofReal E • withDensityReal ρ :=
    (marginal_le_smul (B := Empty) V hβ.le hNn (n := n + 1) (by simp) (fun e => e.elim) ⟨0, hNn⟩).trans
      (eqstat_smul_mono hEβ)
  have hS : Measurable fun X : Config d (n + 1) => ∑ i, f (X i) :=
    Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)
  have hI : ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(withDensityReal ρ) = ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal ρ)) :=
    lintegral_enorm_sq_eq_ofReal hf2
  have hπ2 : evariance f π0 ≤ ENNReal.ofReal E * ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal ρ)) := by
    refine (HRS.External.evariance_le_lintegral_sub π0 hf.aestronglyMeasurable 0).trans ?_
    simp only [sub_zero]
    calc ∫⁻ z, ‖f z‖ₑ ^ 2 ∂π0 ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(ENNReal.ofReal E • withDensityReal ρ) :=
          lintegral_mono' hπ0le le_rfl
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul, hI]
  have hlin := weak_linear_variance_symm (B := Empty) V hβ.le hNn (n := n + 1) (by simp)
    (fun e : Empty => e.elim) hκV f hf
  have hQR := evariance_le_of_le_smul hQK1 hS
  have hc : evariance (fun X : Config d (n + 1) => (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, f (X i))
      (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) =
      ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) ^ 2) * evariance (fun X : Config d (n + 1) => ∑ i, f (X i))
        (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) := evariance_mul _ _ _
  rw [hc]
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hNn
  calc ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) ^ 2) *
        evariance (fun X : Config d (n + 1) => ∑ i, f (X i))
          (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)))
      ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) ^ 2) *
          (ENNReal.ofReal KQ * (2 * ((n + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal E * ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal ρ)))))) := by
        gcongr
        refine hQR.trans ?_
        gcongr
        exact hlin.trans (by gcongr)
    _ = ENNReal.ofReal (2 * KQ * E * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- The linear variance bound, uniform in `β ∈ [β₋,β₊]` and in `ρ ≤ Λ₀`. -/
theorem eqstat_lin_main (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C : ℝ, ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ y, ρ y ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρ) →
        (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
  obtain ⟨C₁, N₁, h1⟩ := eqstat_lin_large hd hs0 hsd hβm hββ Λ0
  have hc : ∀ N : ℕ, ∃ C : ℝ, 2 ≤ N → ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ y, ρ y ≤ Λ0) → ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρ) →
        (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨C, hC⟩ := eqstat_lin_crude hd hs0 hsd hβm hββ Λ0 hN
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Cs hCs using hc
  refine ⟨|C₁| + ∑ N ∈ Finset.range N₁, |Cs N|, ?_⟩
  intro β hβ1 hβ2 ρ hρ hρΛ N hN f hf hf2
  have hI : 0 ≤ ∫ x, f x ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun _ => sq_nonneg _
  by_cases hNN : N₁ ≤ N
  · refine (h1 hβ1 hβ2 ρ hρ hρΛ N hNN hN f hf hf2).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : C₁ ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have := le_abs_self C₁
      have : 0 ≤ ∑ N ∈ Finset.range N₁, |Cs N| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    exact mul_le_mul_of_nonneg_right h2 hI
  · have hlt : N < N₁ := not_le.1 hNN
    refine (hCs N hN hβ1 hβ2 ρ hρ hρΛ f hf hf2).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : Cs N ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have h3 : |Cs N| ≤ ∑ N ∈ Finset.range N₁, |Cs N| :=
        Finset.single_le_sum (f := fun N => |Cs N|) (fun M _ => abs_nonneg (Cs M)) (Finset.mem_range.2 hlt)
      have := le_abs_self (Cs N)
      have := abs_nonneg C₁
      linarith
    exact mul_le_mul_of_nonneg_right h2 hI

theorem eq_static_linear_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρβ) →
        evariance (fun X : Config d N => pair (empirical X) f)
            (canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal (C * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)) := by
  obtain ⟨Lam, hLam⟩ := eqstat_thermal_setup hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨C, hCU⟩ := eqstat_lin_main hd hs0 hsd hβm hββ Lam
  refine ⟨|C| + 1, by positivity, fun β hβ ρβ hρ N hN f hf hf2 => ?_⟩
  obtain ⟨hρs, hΛ, hP⟩ := hLam β hβ ρβ hρ
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hF : (fun X : Config d N => pair (empirical X) f) = fun X => (1 / (N : ℝ)) * ∑ i, f (X i) := by
    funext X
    rw [pair_empirical hN0, one_div]
  rw [hF, hP N]
  have hmain := hCU hβ.1 hβ.2 ρβ hρs.density hΛ N hN f hf hf2
  have hI : 0 ≤ ∫ x, f x ^ 2 ∂(withDensityReal ρβ) := integral_nonneg fun _ => sq_nonneg _
  have hev : evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ)) =
      ENNReal.ofReal ((N : ℝ)⁻¹) * ((N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ))) := by
    rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hNR.ne', ENNReal.ofReal_one, one_mul]
  rw [hev]
  calc ENNReal.ofReal ((N : ℝ)⁻¹) * ((N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ)))
      ≤ ENNReal.ofReal ((N : ℝ)⁻¹) * ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)) := by
        gcongr
    _ = ENNReal.ofReal ((N : ℝ)⁻¹ * (C * ∫ x, f x ^ 2 ∂(withDensityReal ρβ))) := by
        exact (ENNReal.ofReal_mul (inv_nonneg.2 hNR.le)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hNi : 0 ≤ (N : ℝ)⁻¹ := by positivity
        have h1 : C ≤ |C| + 1 := by linarith [le_abs_self C]
        nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg hNi hI)]

end HRS.MD.EQStat

end
