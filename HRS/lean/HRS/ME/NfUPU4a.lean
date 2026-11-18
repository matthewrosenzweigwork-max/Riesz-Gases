import HRS.Equilibrium.PinLinf
import HRS.ME.NfUPU3b
import HRS.ME.NfUPU5a

/-!
# Packet PU4a (uniform `cavD_const` and `linf_one_step`)

* `cavD_const_unif` is `HRS.PinAux.cavD_const` (`HRS/Equilibrium/PinLinf.lean:150`). The constant
  `(CD, N₁)` is chosen after the kernel data `q, Cq, hdec` and `βm, βp, c₀, Λ₀` and before `β, ρ`.
  The envelope constants are taken at the fixed threshold `pinGamma βp` (instead of `pinGamma β`),
  the density bound is `max Λ₀ 1` from `RhoU`, and `Cν := exp 10` (`β * pinGamma β ≤ 1/16`).
  The per-`β` equalities `V.γ = pinGamma β`, `V.M = β * pinGamma β + 1`, `V.M' = 1` stay per `β`.
* `linf_one_step_unif` is `HRS.PinAux.linf_one_step` (`PinLinf.lean:266`). The constant `Eδ` and
  `N₁` are chosen before `β, ρ`; `Eδ` bounds the per-`β` constant
  `β Kd γ + β² C3 γ + β Ck C₁' + CD`, using `β γ = 1/(16 exp 10)` (`beta_mul_pinGamma`),
  `Kd ≤ exp 10` and `β ≤ βp`. The row hypothesis is the single threshold `pinGamma βp`, which
  implies `pinGamma β` for `β ≤ βp` (`pinGamma_le_of_le`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.NfU

open HRS HRS.PinAux HRS.External HRS.External.RefMarg HRS.ME.PmU

variable {d : ℕ}

/-- `β · pinGamma β ≤ 1/16` for `β > 0`. -/
theorem beta_mul_pinGamma_le_unif {β : ℝ} (hβ : 0 < β) : β * pinGamma β ≤ 1 / 16 := by
  rw [beta_mul_pinGamma hβ, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.add_one_le_exp (10 : ℝ)]

section CavConstU

/-- Uniform-in-`β` version of `cavD_const` (`HRS/Equilibrium/PinLinf.lean:150`). -/
theorem cavD_const_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {βm βp c₀ Λ₀ : ℝ}
    (hβm : 0 < βm) (hββ : βm ≤ βp)
    (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q) (hqe : ∀ z, q (-z) = q z)
    (Cq : ℝ) (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c) :
    ∃ (CD : ℝ) (N₁ : ℕ), 0 ≤ CD ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)) (_ : ∀ x y, V.q x y = q (x - y))
        (_ : V.γ = pinGamma β) (_ : V.M = β * pinGamma β + 1) (_ : V.M' = 1)
        (N n : ℕ) [NeZero n], N₁ ≤ N → n ≤ N → ∀ x : Torus d,
        0 ≤ Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ∧
        Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ≤ CD * deltaN d s N := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  have hγ₁ : 0 < pinGamma βp := pinGamma_pos hβp
  obtain ⟨C0, C1, C2, cl, Cw, A', hE⟩ := exists_env hd hcrit q hq0 Cq hqenv hdec (pinGamma βp) hγ₁.le
  obtain ⟨K0, hK0, hw⟩ := weakLp_of_envelope (d := d) (s := s) hd hs0.le hsd (B := max Cq 0)
    (le_max_right _ _) (q := q) (fun x hx => by
      refine (hqenv x hx).trans ?_
      have hsing : singEnvelope s (Torus.eucDist x 0) = 1 + Torus.eucDist x 0 ^ (-s) := by
        unfold singEnvelope; rw [if_neg hs0.ne']
      rw [hsing]
      refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
      have : 0 ≤ Torus.eucDist x 0 ^ (-s) := Real.rpow_nonneg (PairCorrAux.eucDist_nonneg' _ _) _
      linarith)
  have hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal (Cw * C0) := by
    calc ∫⁻ z, ENNReal.ofReal (q z) ≤ ∫⁻ z, ENNReal.ofReal Cw * ENNReal.ofReal (wEnv s 0 z) := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_mul hE.Cw_nn]
          refine ENNReal.ofReal_le_ofReal ?_
          have := hE.kern z 0
          have h2 : wEnv s z 0 = wEnv s 0 z := PairCorrAux.wEnv_symm s z 0
          rw [sub_zero, h2] at this
          linarith [hγ₁.le]
      _ = ENNReal.ofReal Cw * ∫⁻ z, ENNReal.ofReal (wEnv s 0 z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Cw * ENNReal.ofReal C0 := by gcongr; exact hE.int_w 0
      _ = _ := (ENNReal.ofReal_mul hE.Cw_nn).symm
  obtain ⟨CD, N₁, hCD0, hCD⟩ := cavD_torus_unif hd hs0.le hsd (Λ := max Λ₀ 1) (le_max_right _ _)
    hqm hq0 hqe (c := Cw * C0) (mul_nonneg hE.Cw_nn hE.C0_nn) hqc hK0 hw hβm hββ
    (Cν := Real.exp 10) (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 10))
  refine ⟨CD, N₁, hCD0, ?_⟩
  intro β hβI ρ U V hVq hVγ hVM hVM' N n _ hN1 hnN x
  have hβ : 0 < β := U.hβpos
  refine hCD β hβI ρ U.rho.density (fun y => (U.hup y).trans (le_max_left _ _)) V hVq ?_ ?_ N n hN1 hnN x
  · rw [hVM, hVM', hVγ]
    have hg := beta_mul_pinGamma_le_unif hβ
    apply Real.exp_le_exp.2
    linarith
  · have hg := beta_mul_pinGamma_le_unif hβ
    unfold weakKappa
    rw [hVM, hVM', hVγ]
    have hex : Real.exp ((β * pinGamma β + 1) + 1 + β * pinGamma β) ≤ Real.exp 10 :=
      Real.exp_le_exp.2 (by linarith)
    have hpos : 0 ≤ β * pinGamma β := mul_nonneg hβ.le (pinGamma_pos hβ).le
    calc 4 * Real.exp ((β * pinGamma β + 1) + 1 + β * pinGamma β) * (β * pinGamma β)
        ≤ 4 * Real.exp 10 * (β * pinGamma β) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex (by norm_num)) hpos
      _ = 1 / 4 := by rw [beta_mul_pinGamma hβ]; field_simp; ring
      _ ≤ 1 / 2 := by norm_num

end CavConstU

section OneStepU

/-- Uniform-in-`β` version of `linf_one_step` (`HRS/Equilibrium/PinLinf.lean:266`). The constants
`Eδ, N₁` are chosen after the kernel data, `k, Ck, C₁` and before `β, ρ`; the row hypothesis uses the
single threshold `pinGamma βp`; the per-`β` equality of `V.γ, V.M` is internal (`exists_weakPotential`). -/
theorem linf_one_step_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {βm βp c₀ Λ₀ : ℝ}
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ0 : 0 ≤ Λ₀)
    (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q) (hqe : ∀ z, q (-z) = q z)
    (Cq : ℝ) (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c)
    (k : Torus d → ℝ) (Ck : ℝ) (hkm : Measurable k) (hkb : ∀ z, |k z| ≤ Ck) (C₁ : ℝ) :
    ∃ (Eδ : ℝ) (N₁ : ℕ), 0 ≤ Eδ ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      RhoU d βm βp c₀ Λ₀ β ρ →
      (∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (pinGamma βp)) →
      ∀ (h : Torus d → ℝ), Measurable h → (∀ x, |h x| ≤ 1) →
      ∀ N : ℕ, N₁ ≤ N → 2 ≤ N → ∀ cN : ℝ,
      (∀ x, h x = -β * ∫ y, k (x - y) *
          (((weakRefMarginal q h (withDensityReal ρ) β N).rnDeriv (withDensityReal ρ) y).toReal - 1)
            ∂(withDensityReal ρ) + cN) →
      eLpNorm (fun y => ((weakRefMarginal q h (withDensityReal ρ) β N).rnDeriv
          (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤ ENNReal.ofReal (C₁ * deltaN d s N) →
      Eδ * deltaN d s N ≤ 1 / 16 → ∀ M : ℝ, 0 ≤ M → M ≤ 1 / 2 →
      (∀ᵐ y ∂(withDensityReal ρ), |((weakRefMarginal q h (withDensityReal ρ) β N).rnDeriv
          (withDensityReal ρ) y).toReal - 1| ≤ M) →
      ∀ᵐ x ∂(withDensityReal ρ), |((weakRefMarginal q h (withDensityReal ρ) β N).rnDeriv
          (withDensityReal ρ) x).toReal - 1| ≤ 4 * (β * pinGamma β * M + Eδ * deltaN d s N) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  have hκ0 : 0 < 1 / (16 * Real.exp 10) := by positivity
  obtain ⟨CD, N₁c, hCD0, hCD⟩ := cavD_const_unif hd hcrit hβm hββ q hq0 hqm hqe Cq hqenv hdec
  obtain ⟨C3, hC3, hchain⟩ := chain_unpinned_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ0 q hq0 hqm Cq
    hqenv hdec 0
  have hCk : 0 ≤ Ck := (abs_nonneg _).trans (hkb 0)
  set C₁' : ℝ := max C₁ 0 with hC₁'
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  obtain ⟨Eu, hEu⟩ : ∃ Eu : ℝ, Eu = Real.exp 10 * (1 / (16 * Real.exp 10))
      + βp * C3 * (1 / (16 * Real.exp 10)) + βp * Ck * C₁' + CD := ⟨_, rfl⟩
  have hEu0 : 0 ≤ Eu := by
    rw [hEu]
    have h1 : 0 ≤ βp * C3 * (1 / (16 * Real.exp 10)) := mul_nonneg (mul_nonneg hβp.le hC3) hκ0.le
    have h2 : 0 ≤ βp * Ck * C₁' := mul_nonneg (mul_nonneg hβp.le hCk) hC₁'0
    have h0 : 0 ≤ Real.exp 10 * (1 / (16 * Real.exp 10)) :=
      mul_nonneg (Real.exp_pos 10).le hκ0.le
    linarith
  refine ⟨Eu, N₁c, hEu0, ?_⟩
  intro β hβI ρ U hrowp h hhm hh1 N hN1 hN2 cN hcal hL2 hsmall M hM0 hM1 hMae
  have hβ : 0 < β := U.hβpos
  have hβle : β ≤ βp := U.hβle
  have hprob : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu U.rho
  have hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (pinGamma β) :=
    fun x => (hrowp x).trans (ENNReal.ofReal_le_ofReal (pinGamma_le_of_le hβ hβle))
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  have hgβ : β * γ₀ ≤ 1 / 16 := beta_mul_pinGamma_le_unif hβ
  have hbg : β * γ₀ = 1 / (16 * Real.exp 10) := beta_mul_pinGamma hβ
  set Kd : ℝ := Real.exp ((β * γ₀ + 1) + 1 + β * (1 + 0) * γ₀) with hKd
  have hKd0 : 0 < Kd := Real.exp_pos _
  have hKdu : Kd ≤ Real.exp 10 := by
    rw [hKd]
    apply Real.exp_le_exp.2
    have e : β * (1 + 0) * γ₀ = β * γ₀ := by ring
    rw [e]
    linarith
  have hEβ : β * Kd * γ₀ + β * β * C3 * γ₀ + β * Ck * C₁' + CD ≤ Eu := by
    have e1 : β * Kd * γ₀ = Kd * (1 / (16 * Real.exp 10)) := by rw [← hbg]; ring
    have e2 : β * β * C3 * γ₀ = β * C3 * (1 / (16 * Real.exp 10)) := by rw [← hbg]; ring
    have f1 : Kd * (1 / (16 * Real.exp 10)) ≤ Real.exp 10 * (1 / (16 * Real.exp 10)) :=
      mul_le_mul_of_nonneg_right hKdu hκ0.le
    have f2 : β * C3 * (1 / (16 * Real.exp 10)) ≤ βp * C3 * (1 / (16 * Real.exp 10)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβle hC3) hκ0.le
    have f3 : β * Ck * C₁' ≤ βp * Ck * C₁' :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβle hCk) hC₁'0
    rw [e1, e2, hEu]
    linarith
  have hCD' := hCD β hβI ρ U
  have hchain' := hchain β hβI ρ U
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨V, hVq, hVφ, hVγ, hVM, hVM'⟩ := exists_weakPotential (withDensityReal ρ) β γ₀ hγ₀ q h
    hqm hq0 hqe hrow hhm hh1 hβ
  have hNpos : 0 < n + 1 := by omega
  have hNr : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hNpos
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlamdef
  have hlam : 0 ≤ lam := by positivity
  set E0 : Empty → Torus d := fun e => e.elim with hE0
  have hid2 : weakRefMarginal q h (withDensityReal ρ) β (n + 1)
      = (pinnedLaw V lam (n + 1) E0).map (fun y => y ⟨0, hNpos⟩) := by
    unfold weakRefMarginal firstMarginal
    rw [dif_pos hNpos, pinnedReference_eq_pinnedLaw (withDensityReal ρ) V q _ hVq hVφ (n + 1) hlam,
      pinnedLaw_isEmpty V lam (n + 1) (Fin.elim0 : Fin 0 → Torus d), pinnedLaw_isEmpty V lam (n + 1) E0]
  rw [hid2] at hcal hL2 hMae ⊢
  have hP := isProb_pinnedLaw V hlam (n + 1) E0
  have hP0 := isProb_pinnedLaw V hlam n E0
  set π := (pinnedLaw V lam (n + 1) E0).map (fun y => y ⟨0, hNpos⟩) with hπ
  set p : Torus d → ℝ := fun x => (π.rnDeriv (withDensityReal ρ) x).toReal with hpdef
  have hπK : π ≤ ENNReal.ofReal Kd • withDensityReal ρ := by
    have := pinned_marginal_le (μ := withDensityReal ρ) V hβ.le hNpos (le_refl (n + 1)) E0 ⟨0, hNpos⟩
    have e : V.M + V.M' + β * (1 + (Fintype.card Empty : ℝ)) * V.γ
        = (β * γ₀ + 1) + 1 + β * (1 + 0) * γ₀ := by rw [hVM, hVM', hVγ]; simp
    rw [e] at this
    exact this
  have hπac : π ≪ withDensityReal ρ := Measure.absolutelyContinuous_of_le_smul hπK
  have hpm : Measurable p := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hp0nn : ∀ x, 0 ≤ p x := fun x => ENNReal.toReal_nonneg
  have hpK : ∀ᵐ x ∂(withDensityReal ρ), p x ≤ Kd := ae_rnDeriv_le_of_le hπac hKd0.le hπK
  -- the cavity marginal
  set ν := cavMarg V lam n with hν
  have hνK : ν ≤ ENNReal.ofReal Kd • withDensityReal ρ := by
    have := pinned_marginal_le (μ := withDensityReal ρ) V hβ.le hNpos (by omega : n ≤ n + 1) E0
      (⟨0, by omega⟩ : Fin n)
    have e : V.M + V.M' + β * (1 + (Fintype.card Empty : ℝ)) * V.γ
        = (β * γ₀ + 1) + 1 + β * (1 + 0) * γ₀ := by rw [hVM, hVM', hVγ]; simp
    rw [e] at this
    have e2 : ν = (pinnedLaw V lam n E0).map (fun y => y ⟨0, by omega⟩) := by
      rw [hν]; unfold cavMarg
      exact (pinnedLaw_marginal_eq V (lam := lam) n ⟨0, by omega⟩).symm ▸ rfl
    rw [e2]
    exact this
  have hνac : ν ≪ withDensityReal ρ := Measure.absolutelyContinuous_of_le_smul hνK
  haveI : IsProbabilityMeasure ν := by
    have e2 : ν = (pinnedLaw V lam n E0).map (fun y => y 0) := rfl
    rw [e2]; infer_instance
  set pt : Torus d → ℝ := fun x => (ν.rnDeriv (withDensityReal ρ) x).toReal with hptdef
  have hptm : Measurable pt := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hptK : ∀ᵐ x ∂(withDensityReal ρ), pt x ≤ Kd := ae_rnDeriv_le_of_le hνac hKd0.le hνK
  -- closeness of the densities (unpinned comparison)
  have hclose : ∀ᵐ x ∂(withDensityReal ρ), |p x - pt x| ≤ C3 * lam := by
    have hset : ∀ B, MeasurableSet B → |π.real B - ν.real B|
        ≤ ∫ z in B, (C3 * lam) ∂(withDensityReal ρ) := by
      intro B hB
      have hch := hchain' V hVq hVγ hVM hVM' hrow (n + 1) n 1 (by omega) hn1 (by omega) B hB
      have e1 : cavM V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) B = π.real B := by
        unfold cavM; rw [dif_pos hNpos]
      have e2 : cavM V (β / ((n + 1 : ℕ) : ℝ)) n B = ν.real B := by
        rw [← coord_eq_cavM V lam (⟨0, by omega⟩ : Fin n) B]
        have e3 : ν = (pinnedLaw V lam n E0).map (fun y => y ⟨0, by omega⟩) := by
          rw [hν]; unfold cavMarg
          exact (pinnedLaw_marginal_eq V (lam := lam) n ⟨0, by omega⟩).symm ▸ rfl
        rw [e3]
      rw [e1, e2] at hch
      rw [setIntegral_const, smul_eq_mul]
      refine hch.trans (le_of_eq ?_)
      rw [hlamdef]; push_cast; ring
    exact ae_abs_rnDeriv_sub_le (μ := withDensityReal ρ) hνac hπac
      (Ψ := fun _ => C3 * lam) (integrable_const _) hset
  -- cavity formula
  have hcav := rnDeriv_marginal_ae V hlam n ⟨0, hNpos⟩
  set Z : ℝ := ∫ x', cavTheta V lam n E0 x' ∂(withDensityReal ρ) with hZ
  have hZpos : 0 < Z := integral_cavTheta_pos V hlam E0 n
  have hcavD := hCD' V hVq hVγ hVM hVM' (n + 1) n hN1 (by omega)
  have hγnn : 0 ≤ γ₀ := hγ₀.le
  have hδ0 : 0 ≤ deltaN d s (n + 1) := deltaN_nonneg hcrit (by omega)
  have hδ1 : 1 / ((n + 1 : ℕ) : ℝ) ≤ deltaN d s (n + 1) := deltaN_ge_inv hcrit (by omega)
  set δ : ℝ := deltaN d s (n + 1) with hδ
  -- the functions
  obtain ⟨Qd, hQd⟩ : ∃ f : Torus d → ℝ, f = fun x => ∫ y, q (x - y) ∂(withDensityReal ρ) := ⟨_, rfl⟩
  obtain ⟨Qp, hQp⟩ : ∃ f : Torus d → ℝ, f = fun x => ∫ y, q (x - y) * p y ∂(withDensityReal ρ) := ⟨_, rfl⟩
  obtain ⟨Rr, hRr⟩ : ∃ f : Torus d → ℝ, f = fun x => ∫ y, q (x - y) * (pt y - p y) ∂(withDensityReal ρ) := ⟨_, rfl⟩
  obtain ⟨Qb, hQb⟩ : ∃ f : Torus d → ℝ, f = fun x => ∫ y, q (x - y) * (p y - 1) ∂(withDensityReal ρ) := ⟨_, rfl⟩
  obtain ⟨Kb, hKb⟩ : ∃ f : Torus d → ℝ, f = fun x => ∫ y, k (x - y) * (p y - 1) ∂(withDensityReal ρ) := ⟨_, rfl⟩
  obtain ⟨Dd, hDd⟩ : ∃ f : Torus d → ℝ, f = fun x => Real.log (cavU V lam n E0 x)
    + β / ((n + 1 : ℕ) : ℝ) * n * ∫ y, V.q y x ∂ν := ⟨_, rfl⟩
  -- integrability / bounds from the row bound
  have hpa : ∀ᵐ y ∂(withDensityReal ρ), |p y| ≤ Kd := by
    filter_upwards [hpK] with y hy; rw [abs_of_nonneg (hp0nn y)]; exact hy
  have hq1 := fun x => abs_integral_q_mul_le hqm hq0 hγnn hrow hpm hKd0.le hpa x
  have hq2 : ∀ x, Integrable (fun y => q (x - y) * (pt y - p y)) (withDensityReal ρ) ∧
      |∫ y, q (x - y) * (pt y - p y) ∂(withDensityReal ρ)| ≤ (C3 * lam) * γ₀ := by
    intro x
    refine abs_integral_q_mul_le hqm hq0 hγnn hrow (hptm.sub hpm) (by positivity) ?_ x
    filter_upwards [hclose] with y hy
    show |pt y - p y| ≤ C3 * lam
    rw [abs_sub_comm]; exact hy
  have hq3 : ∀ x, Integrable (fun y => q (x - y) * (p y - 1)) (withDensityReal ρ) ∧
      |∫ y, q (x - y) * (p y - 1) ∂(withDensityReal ρ)| ≤ M * γ₀ :=
    fun x => abs_integral_q_mul_le hqm hq0 hγnn hrow (hpm.sub measurable_const) hM0 hMae x
  have hqd : ∀ x, Integrable (fun y => q (x - y)) (withDensityReal ρ) ∧
      ∫ y, q (x - y) ∂(withDensityReal ρ) ≤ γ₀ := fun x => integrable_q_row hqm hq0 hγnn hrow x
  have eQd : ∀ x, Qd x = ∫ y, q (x - y) ∂(withDensityReal ρ) := fun x => by rw [hQd]
  have eQp : ∀ x, Qp x = ∫ y, q (x - y) * p y ∂(withDensityReal ρ) := fun x => by rw [hQp]
  have eRr : ∀ x, Rr x = ∫ y, q (x - y) * (pt y - p y) ∂(withDensityReal ρ) := fun x => by rw [hRr]
  have eQb : ∀ x, Qb x = ∫ y, q (x - y) * (p y - 1) ∂(withDensityReal ρ) := fun x => by rw [hQb]
  have eKb : ∀ x, Kb x = ∫ y, k (x - y) * (p y - 1) ∂(withDensityReal ρ) := fun x => by rw [hKb]
  have eDd : ∀ x, Dd x = Real.log (cavU V lam n E0 x)
      + β / ((n + 1 : ℕ) : ℝ) * n * ∫ y, V.q y x ∂ν := fun x => by rw [hDd]
  have h7 : β / ((n + 1 : ℕ) : ℝ) * n = β - β / ((n + 1 : ℕ) : ℝ) := by
    field_simp; push_cast; ring
  have hlog : ∀ᵐ x ∂(withDensityReal ρ), Real.log (p x) = (cN - Real.log Z) - β * Qb x
      + (β / ((n + 1 : ℕ) : ℝ) * Qp x - (β - β / ((n + 1 : ℕ) : ℝ)) * Rr x - β * Kb x + Dd x) := by
    filter_upwards [hcav] with x hx
    have hΘpos := cavTheta_pos V hlam E0 n x
    have h1 : Real.log (p x) = V.φ x + Real.log (cavU V lam n E0 x) - Real.log Z := by
      have : p x = cavTheta V lam n E0 x / Z := hx
      rw [this, Real.log_div hΘpos.ne' hZpos.ne']
      unfold cavTheta
      rw [Real.log_mul (Real.exp_pos _).ne' (cavU_pos V hlam E0 n x).ne', Real.log_exp]
      simp [pinField]
    have h2 : V.φ x = β * Qd x + h x := by rw [eQd]; exact congrFun hVφ x
    have h3 : h x = -β * Kb x + cN := by rw [eKb]; exact hcal x
    have h5 : ∫ y, V.q y x ∂ν = Qp x + Rr x := by
      have e1 : ∫ y, V.q y x ∂ν = ∫ y, q (x - y) ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        have := hqe (x - y)
        rw [neg_sub] at this
        simp only [hVq]; exact this
      rw [e1, ← integral_toReal_rnDeriv_mul hνac]
      have e2 : ∀ y, (ν.rnDeriv (withDensityReal ρ) y).toReal * q (x - y)
          = q (x - y) * p y + q (x - y) * (pt y - p y) := fun y => by
        simp only [hptdef]; ring
      simp_rw [e2]
      rw [eQp, eRr]
      exact integral_add (hq1 x).1 (hq2 x).1
    have h6 : Qb x = Qp x - Qd x := by
      rw [eQb, eQp, eQd]
      have : ∀ y, q (x - y) * (p y - 1) = q (x - y) * p y - q (x - y) := fun y => by ring
      simp_rw [this]
      exact integral_sub (hq1 x).1 (hqd x).1
    have h4 : Real.log (cavU V lam n E0 x)
        = Dd x - β / ((n + 1 : ℕ) : ℝ) * n * ∫ y, V.q y x ∂ν := by rw [eDd]; ring
    rw [h1, h2, h3, h4, h5, h6, h7]
    ring
  -- bounds
  have hpint : Integrable p (withDensityReal ρ) := Measure.integrable_toReal_rnDeriv
  have hL1 : ∫ y, |p y - 1| ∂(withDensityReal ρ) ≤ C₁' * δ :=
    integral_abs_le_of_eLpNorm_two (hpm.sub measurable_const) (mul_nonneg hC₁'0 hδ0)
      (hL2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0)))
  have hKb' : ∀ x, |Kb x| ≤ Ck * (C₁' * δ) := by
    intro x
    rw [eKb]
    have hint2 : Integrable (fun y => Ck * |p y - 1|) (withDensityReal ρ) :=
      ((hpint.sub (integrable_const 1)).abs).const_mul Ck
    have hb : ∀ y, ‖k (x - y) * (p y - 1)‖ ≤ Ck * |p y - 1| := fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hkb _) (abs_nonneg _)
    have := norm_integral_le_of_norm_le hint2 (Filter.Eventually.of_forall hb)
    rw [Real.norm_eq_abs, integral_const_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_left hL1 hCk)
  have ha0 : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := by positivity
  have haδ : β / ((n + 1 : ℕ) : ℝ) ≤ β * δ := by
    have := mul_le_mul_of_nonneg_left hδ1 hβ.le
    rw [mul_one_div] at this
    exact this
  have haβ : β / ((n + 1 : ℕ) : ℝ) ≤ β := by
    rw [div_le_iff₀ hNr]
    have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hNpos
    nlinarith
  have hDd' : ∀ x, 0 ≤ Dd x ∧ Dd x ≤ CD * δ := fun x => by
    rw [eDd]; exact hcavD x
  have hEb : ∀ x, |β / ((n + 1 : ℕ) : ℝ) * Qp x - (β - β / ((n + 1 : ℕ) : ℝ)) * Rr x - β * Kb x + Dd x|
      ≤ (β * Kd * γ₀ + β * β * C3 * γ₀ + β * Ck * C₁' + CD) * δ := by
    intro x
    have b1 : |β / ((n + 1 : ℕ) : ℝ) * Qp x| ≤ β * Kd * γ₀ * δ := by
      rw [abs_mul, abs_of_nonneg ha0, eQp]
      calc β / ((n + 1 : ℕ) : ℝ) * |∫ y, q (x - y) * p y ∂(withDensityReal ρ)|
          ≤ (β * δ) * (Kd * γ₀) :=
            mul_le_mul haδ (hq1 x).2 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have b2 : |(β - β / ((n + 1 : ℕ) : ℝ)) * Rr x| ≤ β * β * C3 * γ₀ * δ := by
      rw [abs_mul, abs_of_nonneg (sub_nonneg.2 haβ), eRr]
      calc (β - β / ((n + 1 : ℕ) : ℝ)) * |∫ y, q (x - y) * (pt y - p y) ∂(withDensityReal ρ)|
          ≤ β * ((C3 * lam) * γ₀) :=
            mul_le_mul (by linarith) (hq2 x).2 (abs_nonneg _) hβ.le
        _ ≤ β * ((C3 * (β * δ)) * γ₀) := by
            have : C3 * lam ≤ C3 * (β * δ) := mul_le_mul_of_nonneg_left haδ hC3
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hγnn) hβ.le
        _ = _ := by ring
    have b3 : |β * Kb x| ≤ β * Ck * C₁' * δ := by
      rw [abs_mul, abs_of_pos hβ]
      calc β * |Kb x| ≤ β * (Ck * (C₁' * δ)) := mul_le_mul_of_nonneg_left (hKb' x) hβ.le
        _ = _ := by ring
    have b4 := hDd' x
    rw [abs_le] at b1 b2 b3 ⊢
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]
  have hTb : ∀ x, |β * Qb x| ≤ β * γ₀ * M := fun x => by
    rw [abs_mul, abs_of_pos hβ, eQb]
    calc β * |∫ y, q (x - y) * (p y - 1) ∂(withDensityReal ρ)| ≤ β * (M * γ₀) :=
          mul_le_mul_of_nonneg_left (hq3 x).2 hβ.le
      _ = _ := by ring
  have hp0 : ∀ᵐ x ∂(withDensityReal ρ), 0 < p x := by
    filter_upwards [hcav] with x hx
    have : p x = cavTheta V lam n E0 x / Z := hx
    rw [this]
    exact div_pos (cavTheta_pos V hlam E0 n x) hZpos
  have hp1 : ∫ x, p x ∂(withDensityReal ρ) = 1 := by
    have := Measure.integral_toReal_rnDeriv hπac
    simpa using this
  have hg : β * γ₀ ≤ 1 / 16 := by
    rw [hγ₀def, beta_mul_pinGamma hβ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.add_one_le_exp (10 : ℝ)]
  have hsm : 2 * (β * γ₀ * M + Eu * δ) ≤ 1 / 2 := by
    have h1 : β * γ₀ * M ≤ (1 / 16) * (1 / 2) := mul_le_mul hgβ hM1 hM0 (by norm_num)
    linarith
  have hEbu : ∀ x, |β / ((n + 1 : ℕ) : ℝ) * Qp x - (β - β / ((n + 1 : ℕ) : ℝ)) * Rr x - β * Kb x
      + Dd x| ≤ Eu * δ := fun x =>
    (hEb x).trans (mul_le_mul_of_nonneg_right hEβ hδ0)
  exact p_near_one (T := fun x => β * Qb x) (ε := Eu * δ)
    (E := fun x => β / ((n + 1 : ℕ) : ℝ) * Qp x - (β - β / ((n + 1 : ℕ) : ℝ)) * Rr x - β * Kb x + Dd x)
    (c := cN - Real.log Z) hp0 hp1 hpint hlog (Filter.Eventually.of_forall hTb)
    (Filter.Eventually.of_forall hEbu) hsm


end OneStepU

end HRS.ME.NfU

end
