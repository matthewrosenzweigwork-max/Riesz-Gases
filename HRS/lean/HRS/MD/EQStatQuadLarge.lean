import HRS.MD.EQStatQuadWeak
import HRS.MD.EQStatQuadCrude
import HRS.MD.EQStatRefMarg2
import HRS.MD.EQStatMarg

/-!
# EQ-STATIC-U, part 5: the quadratic variance for large `N`, uniform in `β ∈ [β₋,β₊]` and `ρ ≤ Λ₀`

`HRS.Quad.quad_large` (Proposition 4.3 for `N ≥ N₁`) with the constants chosen before `β ∈ [β₋,β₊]` and before the smooth
positive density `ρ ≤ Λ₀`: the split `(τ, L, Λ, Ψ)` comes from `EqMarg.eqmarg_split_params` (smallness at `β₊`), the threshold of
the calibration smallness from `EqMarg.eqmarg_small_calib`, the Gibbs marginal from `EqMarg.eqmarg_marginal_unif`, the reference
marginal from `eqstat_reference_marginal_L2`, the weak-ensemble bound from `eqstat_quad_weak_bound`.
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

set_option maxHeartbeats 1600000 in
theorem eqstat_quad_large (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ (ρ : Torus d → ℝ), SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ0) → ∀ N : ℕ, N₁ ≤ N → 2 ≤ N → ∀ (B : ℝ) (h : Torus d → Torus d → ℝ),
      Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ ν ∈ ({withDensityReal ρ,
          firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))} :
            Set (Measure (Torus d))),
        (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ0Λ, hΨ, hc0, hgL00, hκβp⟩ :=
    HRS.EqMarg.eqmarg_split_params hd hs0 hsd βp hβp Λ0
  have hΛ0 : 0 ≤ Λ := by linarith
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  have hγ0 : 0 ≤ γ := mul_nonneg hΛ0 hc0
  set gL0 : ℝ := (weakSplit d s τ L).gL 0 with hgL0
  have hρ1 : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  have hκall : ∀ β : ℝ, 0 < β → β ≤ βp → KappaSmall β γ := fun β hβ hβ2 =>
    kappaSmall_of_le hβ hγ0 ((mul_le_mul_of_nonneg_right hβ2 hγ0).trans hκβp)
  obtain ⟨n₀, hn₀⟩ := HRS.EqMarg.eqmarg_small_calib hd hs0 hsd hτ hτ1 L hΛ1 Ψ hΨ βp hβp
  obtain ⟨CR, N₃, hR2⟩ := eqstat_reference_marginal_L2 hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ
    (hκall βp hβp le_rfl) Ψ hΨ
  obtain ⟨CF, hCF0, hF2⟩ := eqstat_marginal_unif hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Cq, hCq0, hCq⟩ := q_lower_env hd hs0 hsd hτ hτ1 L hρ1 (Λ := Λ) (fun _ => hΛ1) Ψ hΨ
  obtain ⟨CW, hCW0, hCW⟩ := eqstat_quad_weak_bound hd hs0 hsd hβm hββ hΛ0 (βp * γ + 1) 0 γ Cq hCq0
  obtain ⟨cch, hcch, hch⟩ := change_term_le hd hs0 hsd
  set KQ : ℝ := Real.exp (4 * βp * gL0) with hKQ
  have hKQ1 : 1 ≤ KQ := Real.one_le_exp (by positivity)
  set E : ℝ := Real.exp ((βp * γ + 1) + 0 + βp * γ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set Cp : ℝ := max 1 (KQ * E) with hCp
  have hCp0 : 0 ≤ Cp := le_trans zero_le_one (le_max_left _ _)
  set Cb : ℝ := max CR 0 + max CF 0 with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨KQ * (2 * CW + 16 * (cch * Cp * Λ ^ 2 * Cb ^ 2)) + 1, max (max n₀ N₃) 2, ?_⟩
  intro β hβ1 hβ2 ρ hρ hΛρ N hN hN2 B h hm hsym hh ν hν
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hΛ : ∀ x, ρ x ≤ Λ := fun x => (hΛρ x).trans hΛ0Λ
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ
  have hκ : KappaSmall β γ := hκall β hβ hβ2
  have hβγ : β * γ ≤ βp * γ := mul_le_mul_of_nonneg_right hβ2 hγ0
  have hEβ : Real.exp ((β * γ + 1) + 0 + β * γ) ≤ E := Real.exp_le_exp.2 (by linarith)
  have hNN₀ : n₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₃ : N₃ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN0 : 0 < N := by omega
  have hB : 0 ≤ B := nonneg_of_env_bound (by omega) hh
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hNn : 0 < n + 1 := Nat.succ_pos n
  have hδ0 : 0 < deltaN d s (n + 1) := deltaN_pos hd hs0 hsd hNn
  have hδ1 : deltaN d s (n + 1) ≤ 1 := deltaN_le_one hd hs0 hsd hNn
  have ht : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1))
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ 1 := fun x => by
    exact hn₀ β hβ hβ2 ρ hρ.density hΛ (n + 1) hNN₀ x
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) ht with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1) =
      pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht, pinnedLaw_empty]
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le hRH hβ.le ht hκ
  have hVM : V.M ≤ βp * γ + 1 := by
    show β * γ + 1 ≤ βp * γ + 1
    linarith
  haveI hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hNn
  have hsmall' : ∀ x, |∑ m, (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)).ofLp m *
      (Calib.Xi (withDensityReal ρ) Ψ x).ofLp m| ≤ 1 := fun x => by
    have := ht x
    rwa [Calib.inner_eq_sum] at this
  have hQK0 := Calib.riesz_Q_le_smul_RN hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hNn hκ hsmall'
  have hQK : modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤
      ENNReal.ofReal KQ • Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1) := by
    refine hQK0.trans (Measure.le_iff'.2 fun A => ?_)
    simp only [Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
    have : 4 * β * gL0 ≤ 4 * βp * gL0 := by nlinarith [hgL00]
    exact this
  haveI hRp : IsProbabilityMeasure (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) :=
    hRH.isProb_RN hβ.le
  have hπeq : firstMarginal (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) =
      (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map (fun X => X 0) := by
    unfold firstMarginal
    rw [dif_pos hNn, hRN]
    rfl
  set R0 := pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) with hR0
  haveI hR0p : IsProbabilityMeasure R0 := by rw [← hRN]; exact hRp
  set π0 : Measure (Torus d) := R0.map (fun X => X 0) with hπ0
  haveI hπ0p : IsProbabilityMeasure π0 := inferInstance
  have hπ0le : π0 ≤ ENNReal.ofReal Cp • withDensityReal ρ := by
    have h1 := firstMarginal_RN_leK hRH hβ (N := n + 1) hNn ht
    rw [hπeq] at h1
    refine h1.trans ?_
    refine Measure.le_iff'.2 fun A => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    refine le_trans ?_ (le_max_right _ _)
    nlinarith [hE0, hEβ, hKQ1]
  have hπNle : firstMarginal (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
      ENNReal.ofReal Cp • withDensityReal ρ := by
    refine (firstMarginal_mono hNn hQK).trans ?_
    rw [firstMarginal_smul hNn]
    have h1 := firstMarginal_RN_leK hRH hβ (N := n + 1) hNn ht
    refine Measure.le_iff'.2 fun A => ?_
    have h2 := h1 A
    rw [Measure.smul_apply, smul_eq_mul] at h2 ⊢
    rw [Measure.smul_apply, smul_eq_mul]
    have h2' : firstMarginal (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) A ≤
        ENNReal.ofReal E * withDensityReal ρ A :=
      h2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hEβ) le_rfl)
    calc ENNReal.ofReal KQ * firstMarginal (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) A
        ≤ ENNReal.ofReal KQ * (ENNReal.ofReal E * withDensityReal ρ A) := mul_le_mul' le_rfl h2'
      _ = ENNReal.ofReal (KQ * E) * withDensityReal ρ A := by rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal Cp * withDensityReal ρ A := mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  -- the density estimates
  obtain ⟨hπRac, hπR2⟩ := hR2 hβ1 hβ2 ρ hρ.density hΛ (n + 1) hNN₃
  rw [hπeq] at hπRac hπR2
  obtain ⟨hπNac, hπN2⟩ := hF2 β hβ1 hβ2 ρ hρ hΛρ (n + 1) hN2
  have hνfacts : IsProbabilityMeasure ν ∧ ν ≤ ENNReal.ofReal Cp • withDensityReal ρ ∧ ν ≪ withDensityReal ρ ∧
      eLpNorm (fun y => (ν.rnDeriv (withDensityReal ρ) y).toReal -
        (π0.rnDeriv (withDensityReal ρ) y).toReal) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (Cb * deltaN d s (n + 1)) := by
    have hgm : Measurable fun y => (π0.rnDeriv (withDensityReal ρ) y).toReal :=
      (Measure.measurable_rnDeriv _ _).ennreal_toReal
    rcases hν with rfl | rfl
    · refine ⟨inferInstance, Measure.le_iff'.2 fun A => ?_, Measure.AbsolutelyContinuous.refl _, ?_⟩
      · rw [Measure.smul_apply, smul_eq_mul]
        exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 (le_max_left _ _))
      · have e : (fun y => ((withDensityReal ρ).rnDeriv (withDensityReal ρ) y).toReal -
            (π0.rnDeriv (withDensityReal ρ) y).toReal) =ᵐ[withDensityReal ρ]
            fun y => -((π0.rnDeriv (withDensityReal ρ) y).toReal - 1) := by
          filter_upwards [Measure.rnDeriv_self (withDensityReal ρ)] with y hy
          simp [hy]
        rw [eLpNorm_congr_ae e]
        refine (le_of_eq (eLpNorm_neg _ _ _)).trans (hπR2.trans (ENNReal.ofReal_le_ofReal ?_))
        refine mul_le_mul_of_nonneg_right ?_ hδ0.le
        have := le_max_left CR 0
        have := le_max_right CF 0
        rw [hCb]; linarith
    · refine ⟨isProb_firstMarginal hNn _, hπNle, hπNac, ?_⟩
      set gN : Torus d → ℝ := fun y => ((firstMarginal (modulatedGibbs (periodicRiesz d s) (n + 1) β
        (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal with hgN
      have hgNm : Measurable gN := (Measure.measurable_rnDeriv _ _).ennreal_toReal
      have e : (fun y => gN y - (π0.rnDeriv (withDensityReal ρ) y).toReal) =
          (fun y => gN y - 1) - fun y => (π0.rnDeriv (withDensityReal ρ) y).toReal - 1 := by
        funext y; simp
      rw [e]
      refine (eLpNorm_sub_le (by norm_num)).trans ?_
      refine (add_le_add hπN2 hπR2).trans ?_
      have hCF : CF * deltaN d s (n + 1) ≤ max CF 0 * deltaN d s (n + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le
      have hCR : CR * deltaN d s (n + 1) ≤ max CR 0 * deltaN d s (n + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le
      calc ENNReal.ofReal (CF * deltaN d s (n + 1)) + ENNReal.ofReal (CR * deltaN d s (n + 1))
          ≤ ENNReal.ofReal (max CF 0 * deltaN d s (n + 1)) + ENNReal.ofReal (max CR 0 * deltaN d s (n + 1)) :=
            add_le_add (ENNReal.ofReal_le_ofReal hCF) (ENNReal.ofReal_le_ofReal hCR)
        _ = ENNReal.ofReal (Cb * deltaN d s (n + 1)) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), hCb]
            congr 1; ring
  obtain ⟨hνp, hνle, hνac, hνL2⟩ := hνfacts
  have hF : Measurable (fun X : Config d (n + 1) => quadStat h ν X) := measurable_quadStat hm ν
  rw [hRN] at hQK
  have step1 : ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
        (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
      ENNReal.ofReal KQ * (((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X) R0) := by
    have h1 := evariance_le_of_le_smul hQK hF
    calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
          (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal KQ * evariance (fun X : Config d (n + 1) => quadStat h ν X) R0) := by
          gcongr
      _ = _ := by ring
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have step2 := evariance_quad_change (N := n + 1) V hβ.le hκV hm ν
  have step3 := hCW hβ1 hβ2 ρ hρ.density hΛ V hVM (le_refl _) (le_refl _) (fun x y hxy => hCq (x - y) (sub_ne_zero.2 hxy))
    hn1 hκV B hB h hm hsym hh
  have step4 := hch hΛ hΛ0 hCp0 hB hm hh (π := π0) (ν := ν) hπ0le hνle hπRac hνac
  have step5 : (eLpNorm (fun y => (ν.rnDeriv (withDensityReal ρ) y).toReal -
        (π0.rnDeriv (withDensityReal ρ) y).toReal) 2 (withDensityReal ρ)) ^ 2 ≤
      ENNReal.ofReal (Cb ^ 2 * deltaN d s (n + 1)) := by
    refine (pow_le_pow_left' hνL2 2).trans ?_
    rw [← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (Cb * deltaN d s (n + 1)) ^ 2 = Cb ^ 2 * (deltaN d s (n + 1) * deltaN d s (n + 1)) := by ring
    rw [this]
    have h2 : deltaN d s (n + 1) * deltaN d s (n + 1) ≤ deltaN d s (n + 1) := by nlinarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hcomb := ofReal_comb (K := KQ) (a := CW * B ^ 2 * deltaN d s (n + 1)) (b := cch * Cp * Λ ^ 2 * B ^ 2)
    (c := Cb ^ 2 * deltaN d s (n + 1)) (by positivity) (by positivity) (by positivity) (by positivity)
  calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
        (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
      ≤ ENNReal.ofReal KQ * (((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X) R0) := step1
    _ ≤ ENNReal.ofReal KQ * (2 * ENNReal.ofReal (CW * B ^ 2 * deltaN d s (n + 1)) +
          16 * (ENNReal.ofReal (cch * Cp * Λ ^ 2 * B ^ 2) * ENNReal.ofReal (Cb ^ 2 * deltaN d s (n + 1)))) := by
        refine mul_le_mul' le_rfl (step2.trans ?_)
        refine add_le_add ?_ ?_
        · rw [mul_assoc]
          exact mul_le_mul' le_rfl step3
        · exact mul_le_mul' le_rfl (step4.trans (mul_le_mul' le_rfl step5))
    _ = ENNReal.ofReal (KQ * (2 * (CW * B ^ 2 * deltaN d s (n + 1)) +
          16 * ((cch * Cp * Λ ^ 2 * B ^ 2) * (Cb ^ 2 * deltaN d s (n + 1))))) := hcomb
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 0 ≤ B ^ 2 * deltaN d s (n + 1) := by positivity
        nlinarith [h1]

end HRS.MD.EQStat

end
