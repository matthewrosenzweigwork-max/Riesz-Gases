import HRS.MD.EQStatQuadLarge
import HRS.Equilibrium.Q32cAux1

/-!
# EQ-STATIC-U, part 6: the crude quadratic bound for a fixed `N`, uniform in `β ∈ [β₋,β₊]` and `ρ ≤ Λ₀`

`HRS.Quad.quad_crude_Q` with the constant chosen before `β ∈ [β₋,β₊]` and before the density: the (non-explicit) transfer
constant `K_N` of `riesz_Q_le_smul_RN_crude` is replaced by the explicit `e^{8βNg_L(0)}` of `Q32c.q32c_Q_le_smul_RN_crude`
(monotone in `β`), and the weak-ensemble constant by `eqstat_quad_crude_weak`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.MD.EQStat

open Function
open HRS HRS.Quad HRS.External HRS.External.RefMarg HRS.External.PoleVar HRS.External.HeatSplit HRS.External.Calib

variable {d : ℕ} {s : ℝ}

theorem eqstat_smul_mono {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal a • μ ≤ ENNReal.ofReal b • μ := by
  refine Measure.le_iff'.2 fun A => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hab) le_rfl

/-- **Crude bound for a fixed `N`** (no smallness), uniform in `β ∈ [β₋,β₊]` and `ρ ≤ Λ₀`:
`N Var_Q D_N(h;ν) ≤ C_N B² δ_N`. -/
theorem eqstat_quad_crude_Q (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ0 : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ C : ℝ, ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ (ρ : Torus d → ℝ), SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ (B : ℝ) (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ ν ∈ ({withDensityReal ρ,
          firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))} :
            Set (Measure (Torus d))),
        (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  have hN0 : 0 < N := by omega
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ0le, hΨ, hc0, hg0, hκ⟩ :=
    HRS.EqMarg.eqmarg_split_params hd hs0 hsd βp hβp Λ0
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  set gL0 : ℝ := (weakSplit d s τ L).gL 0 with hgL0
  have hγ0 : 0 ≤ γ := mul_nonneg (by linarith) hc0
  set K0 : ℝ := max 1 (4 * βp * gL0) with hK0
  have hρ1 : IsProbDensity (fun _ : Torus d => (1 : ℝ)) := ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  obtain ⟨Cq, hCq0, hCq⟩ := q_lower_env hd hs0 hsd hτ hτ1 L hρ1 (Λ := Λ) (fun _ => hΛ1) Ψ hΨ
  set K' : ℝ := Real.exp (8 * βp * (N : ℝ) * gL0) with hK'
  have hK'0 : 0 < K' := Real.exp_pos _
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨Cc, hCc0, hCc⟩ := eqstat_quad_crude_weak hd hs0 hsd hβm hββ hΛ0 (βp * γ + K0) 0 γ Cq hCq0 (n := n)
    (by omega)
  set Cp : ℝ := max 1 (K' * Real.exp ((βp * γ + K0) + 0 + βp * γ)) with hCp
  have hCp0 : 0 ≤ Cp := le_trans zero_le_one (le_max_left _ _)
  have hδ := deltaN_pos hd hs0 hsd (N := n + 1) hN0
  refine ⟨((n + 1 : ℕ) : ℝ) * K' * Cc * (1 + Cp ^ 2) / deltaN d s (n + 1), ?_⟩
  intro β hβ1 hβ2 ρ hρ hΛρ B h hm hh ν hν
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hΛ : ∀ x, ρ x ≤ Λ := fun x => (hΛρ x).trans hΛ0le
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ
  have ht0 : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1))
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ K0 :=
    fun x => (abs_tN_inner_le hRH hβ hN0 x).trans
      ((mul_le_mul_of_nonneg_right (by linarith) hg0).trans (le_max_right _ _))
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) ht0 with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1) =
      pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht0, pinnedLaw_empty]
  have hQK : modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤
      ENNReal.ofReal K' • Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1) := by
    have hle : Real.exp (8 * β * ((n + 1 : ℕ) : ℝ) * gL0) ≤ K' := by
      refine Real.exp_le_exp.2 ?_
      have : 8 * β * ((n + 1 : ℕ) : ℝ) ≤ 8 * βp * ((n + 1 : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith
      exact mul_le_mul_of_nonneg_right this hg0
    exact (HRS.Q32c.q32c_Q_le_smul_RN_crude hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hN0).trans
      (eqstat_smul_mono hle)
  have hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hN0
  have hπR := firstMarginal_RN_leK hRH hβ (N := n + 1) hN0 ht0
  have hexp : Real.exp ((β * γ + K0) + 0 + β * γ) ≤ Real.exp ((βp * γ + K0) + 0 + βp * γ) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hπQ : firstMarginal (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
      ENNReal.ofReal Cp • withDensityReal ρ := by
    refine (firstMarginal_mono hN0 hQK).trans ?_
    rw [firstMarginal_smul hN0]
    refine Measure.le_iff'.2 fun A => ?_
    have h1 := hπR A
    rw [Measure.smul_apply, smul_eq_mul] at h1 ⊢
    rw [Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal K' * firstMarginal (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) A
        ≤ ENNReal.ofReal K' * (ENNReal.ofReal (Real.exp ((β * γ + K0) + 0 + β * γ)) * withDensityReal ρ A) :=
          mul_le_mul' le_rfl h1
      _ ≤ ENNReal.ofReal K' * (ENNReal.ofReal (Real.exp ((βp * γ + K0) + 0 + βp * γ)) * withDensityReal ρ A) :=
          mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) le_rfl)
      _ = ENNReal.ofReal (K' * Real.exp ((βp * γ + K0) + 0 + βp * γ)) * withDensityReal ρ A := by
          rw [← mul_assoc, ENNReal.ofReal_mul hK'0.le]
      _ ≤ ENNReal.ofReal Cp * withDensityReal ρ A :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  have hB : 0 ≤ B := nonneg_of_env_bound (by omega) hh
  have hVM : V.M ≤ βp * γ + K0 := by
    show β * γ + K0 ≤ βp * γ + K0
    nlinarith
  have key : ∀ ν : Measure (Torus d), IsProbabilityMeasure ν → ν ≤ ENNReal.ofReal Cp • withDensityReal ρ →
      ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
          (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * K' * Cc * (1 + Cp ^ 2) / deltaN d s (n + 1) * B ^ 2 *
          deltaN d s (n + 1)) := by
    intro ν hνp hνle
    have hbd := hCc hβ1 hβ2 ρ hρ.density hΛ V hVM (le_refl _) (le_refl _)
      (fun x y hxy => hCq (x - y) (sub_ne_zero.2 hxy)) B hB h hm hh hCp0 ν hνle
    rw [← hRN] at hbd
    have hF : Measurable (fun X : Config d (n + 1) => quadStat h ν X) := measurable_quadStat hm ν
    have h1 : evariance (fun X : Config d (n + 1) => quadStat h ν X)
        (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
        ∫⁻ X, ‖quadStat h ν X‖ₑ ^ 2 ∂(modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) := by
      have := evariance_le_lintegral_sub (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        hF.aestronglyMeasurable 0
      simpa using this
    have h2 : ∫⁻ X, ‖quadStat h ν X‖ₑ ^ 2 ∂(modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ENNReal.ofReal K' * ∫⁻ X, ‖quadStat h ν X‖ₑ ^ 2
          ∂(Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) := by
      calc _ ≤ ∫⁻ X, ‖quadStat h ν X‖ₑ ^ 2 ∂(ENNReal.ofReal K' • Calib.RN (weakSplit d s τ L).q
              (withDensityReal ρ) Ψ β (n + 1)) := lintegral_mono' hQK le_rfl
        _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
    calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
          (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal K' * ENNReal.ofReal (Cc * (1 + Cp ^ 2) * B ^ 2)) := by
          gcongr
          exact h1.trans (h2.trans (by gcongr))
      _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * K' * Cc * (1 + Cp ^ 2) / deltaN d s (n + 1) * B ^ 2 *
          deltaN d s (n + 1)) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hK'0.le, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  rcases hν with rfl | rfl
  · refine key _ inferInstance (Measure.le_iff'.2 fun A => ?_)
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 (le_max_left _ _))
  · exact key _ (isProb_firstMarginal hN0 _) hπQ

end HRS.MD.EQStat

end
