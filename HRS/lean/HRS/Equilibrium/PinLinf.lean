/-
# HRS.Equilibrium.PinLinf -- proof of the sup-norm display of Lemma 4.10 (`reference_marginal_linf`)

Downstream of `PinComparison`.  Route (source lines 4536-4550): exact cavity equation for the
first marginal `π_N`, pole-pressure bound `cavD_torus`, unpinned comparison from the dimension
chain of `PinComparison`, calibration, and absorption.
-/
import HRS.Equilibrium.PinComparison

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace PinAux

open HRS.External HRS.External.RefMarg

section Absorb

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

theorem exp_sub_one_le {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1 / 2) : Real.exp e - 1 ≤ 2 * e := by
  rcases h0.eq_or_lt with h | h
  · rw [← h]; simp
  · have := Real.exp_bound_div_one_sub_of_interval' h (by linarith : e < 1)
    have h2 : 1 / (1 - e) ≤ 1 + 2 * e := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith

/-- If `log p = c - T + E` with bounded `T, E` and `∫ p = 1`, then `p` is close to one. -/
theorem p_near_one {p T E : α → ℝ} {c τ ε : ℝ} (hp0 : ∀ᵐ x ∂μ, 0 < p x)
    (hp1 : ∫ x, p x ∂μ = 1) (hpi : Integrable p μ)
    (hlog : ∀ᵐ x ∂μ, Real.log (p x) = c - T x + E x) (hT : ∀ᵐ x ∂μ, |T x| ≤ τ)
    (hE : ∀ᵐ x ∂μ, |E x| ≤ ε) (hsmall : 2 * (τ + ε) ≤ 1 / 2) :
    ∀ᵐ x ∂μ, |p x - 1| ≤ 4 * (τ + ε) := by
  have hτε : 0 ≤ τ + ε := by
    have : ∀ᵐ x ∂μ, 0 ≤ τ + ε := by
      filter_upwards [hT, hE] with x h1 h2
      linarith [abs_nonneg (T x), abs_nonneg (E x)]
    obtain ⟨x, hx⟩ := this.exists
    exact hx
  -- bounds on `p`
  have hup : ∀ᵐ x ∂μ, p x ≤ Real.exp (c + (τ + ε)) := by
    filter_upwards [hp0, hlog, hT, hE] with x h0 hl hT' hE'
    have : Real.log (p x) ≤ c + (τ + ε) := by
      rw [hl]; linarith [(abs_le.1 hT').1, (abs_le.1 hE').2]
    calc p x = Real.exp (Real.log (p x)) := (Real.exp_log h0).symm
      _ ≤ _ := Real.exp_le_exp.2 this
  have hlo : ∀ᵐ x ∂μ, Real.exp (c - (τ + ε)) ≤ p x := by
    filter_upwards [hp0, hlog, hT, hE] with x h0 hl hT' hE'
    have : c - (τ + ε) ≤ Real.log (p x) := by
      rw [hl]; linarith [(abs_le.1 hT').2, (abs_le.1 hE').1]
    calc Real.exp (c - (τ + ε)) ≤ Real.exp (Real.log (p x)) := Real.exp_le_exp.2 this
      _ = p x := Real.exp_log h0
  have h1 : 1 ≤ Real.exp (c + (τ + ε)) := by
    have := integral_mono_ae hpi (integrable_const _) hup
    simpa [hp1] using this
  have h2 : Real.exp (c - (τ + ε)) ≤ 1 := by
    have := integral_mono_ae (integrable_const _) hpi hlo
    simpa [hp1] using this
  have hc1 : 0 ≤ c + (τ + ε) := Real.one_le_exp_iff.1 h1
  have hc2 : c - (τ + ε) ≤ 0 := Real.exp_le_one_iff.1 h2
  filter_upwards [hp0, hlog, hT, hE] with x h0 hl hT' hE'
  have hlg : |Real.log (p x)| ≤ 2 * (τ + ε) := by
    rw [hl, abs_le]
    constructor <;> linarith [(abs_le.1 hT').1, (abs_le.1 hT').2, (abs_le.1 hE').1, (abs_le.1 hE').2]
  have := abs_sub_one_le_of_abs_log_le h0 hlg
  have h3 := exp_sub_one_le (by linarith : 0 ≤ 2 * (τ + ε)) hsmall
  linarith

end Absorb


section QInt

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q : Torus d → ℝ}

theorem integrable_q_row (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) {γ₀ : ℝ} (hγ₀ : 0 ≤ γ₀)
    (hrow : ∀ z, ∫⁻ y, ENNReal.ofReal (q (z - y)) ∂μ ≤ ENNReal.ofReal γ₀) (x : Torus d) :
    Integrable (fun y => q (x - y)) μ ∧ ∫ y, q (x - y) ∂μ ≤ γ₀ := by
  have hm : Measurable (fun y => q (x - y)) := hqm.comp (measurable_const.sub measurable_id)
  have hint : Integrable (fun y => q (x - y)) μ := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ y, ‖q (x - y)‖ₑ = ENNReal.ofReal (q (x - y)) := fun y => by
      rw [Real.enorm_eq_ofReal (hq0 _)]
    simp_rw [this]
    exact (hrow x).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hq0 _) hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hγ₀ (hrow x)

end QInt


section QInt2

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q : Torus d → ℝ}

theorem abs_integral_q_mul_le (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) {γ₀ : ℝ} (hγ₀ : 0 ≤ γ₀)
    (hrow : ∀ z, ∫⁻ y, ENNReal.ofReal (q (z - y)) ∂μ ≤ ENNReal.ofReal γ₀)
    {f : Torus d → ℝ} (hfm : Measurable f) {F : ℝ} (hF : 0 ≤ F) (hf : ∀ᵐ y ∂μ, |f y| ≤ F) (x : Torus d) :
    Integrable (fun y => q (x - y) * f y) μ ∧ |∫ y, q (x - y) * f y ∂μ| ≤ F * γ₀ := by
  obtain ⟨hint, hle⟩ := integrable_q_row hqm hq0 hγ₀ hrow x
  have hm : Measurable (fun y => q (x - y)) := hqm.comp (measurable_const.sub measurable_id)
  have hb : ∀ᵐ y ∂μ, ‖q (x - y) * f y‖ ≤ F * q (x - y) := by
    filter_upwards [hf] with y hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 _)]
    calc q (x - y) * |f y| ≤ q (x - y) * F := mul_le_mul_of_nonneg_left hy (hq0 _)
      _ = _ := mul_comm _ _
  have hI : Integrable (fun y => q (x - y) * f y) μ :=
    Integrable.mono' (hint.const_mul F) (hm.mul hfm).aestronglyMeasurable hb
  refine ⟨hI, ?_⟩
  have := norm_integral_le_of_norm_le (hint.const_mul F) hb
  rw [Real.norm_eq_abs, integral_const_mul] at this
  exact this.trans (mul_le_mul_of_nonneg_left hle hF)

end QInt2

section Cavity

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

theorem rnDeriv_marginal_ae (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ)
    (i : Fin (n + 1)) :
    ∀ᵐ x ∂μ, (((pinnedLaw V lam (n + 1) (fun e : Empty => e.elim)).map (fun y => y i)).rnDeriv μ x).toReal
      = cavTheta V lam n (fun e : Empty => e.elim) x
          / ∫ x', cavTheta V lam n (fun e : Empty => e.elim) x' ∂μ := by
  rw [marginal_eq_normalized V hlam (fun e : Empty => e.elim) i]
  have hZ := integral_cavTheta_pos V hlam (fun e : Empty => e.elim) n
  have hm : Measurable (fun x => ENNReal.ofReal (cavTheta V lam n (fun e : Empty => e.elim) x
      / ∫ x', cavTheta V lam n (fun e : Empty => e.elim) x' ∂μ)) :=
    ENNReal.measurable_ofReal.comp ((measurable_cavTheta V hlam _ n).div_const _)
  filter_upwards [Measure.rnDeriv_withDensity μ hm] with x hx
  rw [hx, ENNReal.toReal_ofReal (div_nonneg (cavTheta_pos V hlam _ n x).le hZ.le)]

end Cavity


section CavConst

variable {d : ℕ}

theorem cavD_const {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z)
    (hqm : Measurable q) (hqe : ∀ z, q (-z) = q z) (Cq : ℝ)
    (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c) :
    ∃ (CD : ℝ) (N₁ : ℕ), 0 ≤ CD ∧
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
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  obtain ⟨C0, C1, C2, cl, Cw, A', hE⟩ := exists_env hd hcrit q hq0 Cq hqenv hdec γ₀ hγ₀.le
  obtain ⟨Λ0, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  -- weak-L^p bound
  obtain ⟨K0, hK0, hw⟩ := weakLp_of_envelope (d := d) (s := s) hd hs0.le hsd (B := max Cq 0)
    (le_max_right _ _) (q := q) (fun x hx => by
      refine (hqenv x hx).trans ?_
      have hsing : singEnvelope s (Torus.eucDist x 0) = 1 + Torus.eucDist x 0 ^ (-s) := by
        unfold singEnvelope; rw [if_neg hs0.ne']
      rw [hsing]
      refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
      have : 0 ≤ Torus.eucDist x 0 ^ (-s) := Real.rpow_nonneg (PairCorrAux.eucDist_nonneg' _ _) _
      linarith)
  -- integrability of q w.r.t. volume
  have hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal (Cw * C0) := by
    calc ∫⁻ z, ENNReal.ofReal (q z) ≤ ∫⁻ z, ENNReal.ofReal Cw * ENNReal.ofReal (wEnv s 0 z) := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_mul hE.Cw_nn]
          refine ENNReal.ofReal_le_ofReal ?_
          have := hE.kern z 0
          have h2 : wEnv s z 0 = wEnv s 0 z := PairCorrAux.wEnv_symm s z 0
          rw [sub_zero, h2] at this
          linarith [hγ₀.le]
      _ = ENNReal.ofReal Cw * ∫⁻ z, ENNReal.ofReal (wEnv s 0 z) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Cw * ENNReal.ofReal C0 := by gcongr; exact hE.int_w 0
      _ = _ := (ENNReal.ofReal_mul hE.Cw_nn).symm
  have hCν : (1 : ℝ) ≤ Real.exp ((β * γ₀ + 1) + 1 + β * γ₀) := Real.one_le_exp (by
    have := mul_nonneg hβ.le hγ₀.le; linarith)
  obtain ⟨CD, N₁, hCD0, hCD⟩ := cavD_torus hd hs0.le hsd (Λ := max Λ0 1) (le_max_right _ _) hqm hq0 hqe
    (c := Cw * C0) (mul_nonneg hE.Cw_nn hE.C0_nn) hqc hK0 hw hβ hCν
  refine ⟨CD, N₁, hCD0, ?_⟩
  intro V hVq hVγ hVM hVM' N n _ hN1 hnN x
  refine hCD (withDensityReal ρ |> fun _ => ρ) hρ.density (fun y => (hΛ y).trans (le_max_left _ _)) V hVq ?_ ?_ N n hN1 hnN x
  · rw [hVM, hVM', hVγ]
  · have hg : β * γ₀ = 1 / (16 * Real.exp 10) := beta_mul_pinGamma hβ
    have hg1 : β * γ₀ ≤ 1 := by
      rw [hg, div_le_one (by positivity)]
      nlinarith [Real.exp_pos 10, Real.add_one_le_exp (10 : ℝ)]
    unfold weakKappa
    rw [hVM, hVM', hVγ]
    have hex : Real.exp ((β * γ₀ + 1) + 1 + β * γ₀) ≤ Real.exp 10 :=
      Real.exp_le_exp.2 (by linarith)
    calc 4 * Real.exp ((β * γ₀ + 1) + 1 + β * γ₀) * (β * γ₀)
        ≤ 4 * Real.exp 10 * (β * γ₀) := by gcongr
      _ = 1 / 4 := by rw [hg]; field_simp; ring
      _ ≤ 1 / 2 := by norm_num

end CavConst


section L1

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

theorem integral_abs_le_of_eLpNorm_two {f : α → ℝ} (hfm : Measurable f) {c : ℝ} (hc : 0 ≤ c)
    (h : eLpNorm f 2 μ ≤ ENNReal.ofReal c) : ∫ x, |f x| ∂μ ≤ c := by
  have h1 : eLpNorm f 1 μ ≤ eLpNorm f 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have h2 : eLpNorm f 1 μ ≤ ENNReal.ofReal c := h1.trans h
  have e : ∫ x, |f x| ∂μ = (eLpNorm f 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hfm.aestronglyMeasurable]
    have := integral_norm_eq_lintegral_enorm (μ := μ) hfm.aestronglyMeasurable
    simpa [Real.norm_eq_abs] using this
  rw [e]
  exact ENNReal.toReal_le_of_le_ofReal hc h2

end L1


section OneStep

variable {d : ℕ}

theorem deltaN_ge_inv {s : ℝ} (hcrit : s = (d : ℝ) / 2) {N : ℕ} (hN : 1 ≤ N) :
    1 / (N : ℝ) ≤ deltaN d s N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : ¬ s < (d : ℝ) / 2 := by rw [hcrit]; exact lt_irrefl _
  unfold deltaN
  rw [if_neg hs, if_pos hcrit]
  have hlog : (1 : ℝ) ≤ Real.log (Real.exp 1 * N) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    have := Real.log_nonneg hNr
    linarith
  rw [one_div]
  calc (N : ℝ)⁻¹ = (N : ℝ)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (N : ℝ)⁻¹ * Real.log (Real.exp 1 * N) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)

theorem deltaN_nonneg {s : ℝ} (hcrit : s = (d : ℝ) / 2) {N : ℕ} (hN : 1 ≤ N) : 0 ≤ deltaN d s N :=
  (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)).trans (deltaN_ge_inv hcrit hN)

end OneStep


section OneStep2

variable {d : ℕ}

theorem linf_one_step {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z)
    (hqm : Measurable q) (hqe : ∀ z, q (-z) = q z) (Cq : ℝ)
    (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c)
    (hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (pinGamma β))
    (k : Torus d → ℝ) (Ck : ℝ) (hkm : Measurable k) (hkb : ∀ z, |k z| ≤ Ck) (C₁ : ℝ) :
    ∃ (Eδ : ℝ) (N₁ : ℕ), 0 ≤ Eδ ∧ ∀ (h : Torus d → ℝ), Measurable h → (∀ x, |h x| ≤ 1) →
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
  have hprob : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  obtain ⟨CD, N₁c, hCD0, hCD⟩ := cavD_const hd hcrit β hβ ρ hρ q hq0 hqm hqe Cq hqenv hdec
  obtain ⟨C3, hC3, hchain⟩ := chain_unpinned hd hcrit β hβ ρ hρ q hq0 hqm Cq hqenv hdec 0
  set Kd : ℝ := Real.exp ((β * γ₀ + 1) + 1 + β * (1 + 0) * γ₀) with hKd
  have hKd0 : 0 < Kd := Real.exp_pos _
  have hCk : 0 ≤ Ck := (abs_nonneg _).trans (hkb 0)
  set C₁' : ℝ := max C₁ 0 with hC₁'
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  refine ⟨β * Kd * γ₀ + β * β * C3 * γ₀ + β * Ck * C₁' + CD, N₁c, by positivity, ?_⟩
  intro h hhm hh1 N hN1 hN2 cN hcal hL2 hsmall M hM0 hM1 hMae
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
      have hch := hchain V hVq hVγ hVM hVM' hrow (n + 1) n 1 (by omega) hn1 (by omega) B hB
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
  have hcavD := hCD V hVq hVγ hVM hVM' (n + 1) n hN1 (by omega)
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
  have hsm : 2 * (β * γ₀ * M + (β * Kd * γ₀ + β * β * C3 * γ₀ + β * Ck * C₁' + CD) * δ) ≤ 1 / 2 := by
    have h1 : β * γ₀ * M ≤ (1 / 16) * (1 / 2) := mul_le_mul hg hM1 hM0 (by norm_num)
    linarith
  exact p_near_one (T := fun x => β * Qb x)
    (E := fun x => β / ((n + 1 : ℕ) : ℝ) * Qp x - (β - β / ((n + 1 : ℕ) : ℝ)) * Rr x - β * Kb x + Dd x)
    (c := cN - Real.log Z) hp0 hp1 hpint hlog (Filter.Eventually.of_forall hTb)
    (Filter.Eventually.of_forall hEb) hsm

end OneStep2

end PinAux


section DensLe

open PinAux HRS.External HRS.External.RefMarg

variable {d : ℕ}

theorem weakRef_density_le (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q)
    (hqe : ∀ z, q (-z) = q z)
    (hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (pinGamma β))
    (h : Torus d → ℝ) (hhm : Measurable h) (hh1 : ∀ x, |h x| ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂(withDensityReal ρ), ((weakRefMarginal q h (withDensityReal ρ) β N).rnDeriv
      (withDensityReal ρ) x).toReal ≤ Real.exp ((β * pinGamma β + 1) + 1 + β * (1 + 0) * pinGamma β) := by
  have hprob : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  obtain ⟨V, hVq, hVφ, hVγ, hVM, hVM'⟩ := exists_weakPotential (withDensityReal ρ) β γ₀ hγ₀ q h
    hqm hq0 hqe hrow hhm hh1 hβ
  have hNpos : 0 < N := hN
  have hlam : 0 ≤ β / (N : ℝ) := by positivity
  set E0 : Empty → Torus d := fun e => e.elim with hE0
  have hid2 : weakRefMarginal q h (withDensityReal ρ) β N
      = (pinnedLaw V (β / N) N E0).map (fun y => y ⟨0, hNpos⟩) := by
    unfold weakRefMarginal firstMarginal
    rw [dif_pos hNpos, pinnedReference_eq_pinnedLaw (withDensityReal ρ) V q _ hVq hVφ N hlam,
      pinnedLaw_isEmpty V (β / N) N (Fin.elim0 : Fin 0 → Torus d), pinnedLaw_isEmpty V (β / N) N E0]
  have hP := isProb_pinnedLaw V hlam N E0
  have hK := pinned_marginal_le (μ := withDensityReal ρ) V hβ.le hNpos (le_refl N) E0 ⟨0, hNpos⟩
  have e : V.M + V.M' + β * (1 + (Fintype.card Empty : ℝ)) * V.γ
      = (β * γ₀ + 1) + 1 + β * (1 + 0) * γ₀ := by rw [hVM, hVM', hVγ]; simp
  rw [e] at hK
  rw [hid2]
  exact ae_rnDeriv_le_of_le (Measure.absolutelyContinuous_of_le_smul hK) (Real.exp_pos _).le hK

end DensLe

section Final

variable {d : ℕ} {s : ℝ}

open PinAux HRS.External HRS.External.RefMarg in
/-- Lemma 4.10, display `Q:eq:reference-linf` (restatement of `HRS.reference_marginal_linf`, proved
downstream of `PairCorrection`). -/
theorem reference_marginal_linf_proof (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ (q : Torus d → ℝ) (Cq : ℝ), Measurable q → (∀ z, 0 ≤ q z) →
      (∀ z, q (-z) = q z) →
      (∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 → periodicRiesz d s z = q z + k z + c) →
      (∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s))) →
      (∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₀) →
      ∀ (k : Torus d → ℝ) (Ck : ℝ), Measurable k → (∀ z, |k z| ≤ Ck) →
      ∀ hN : ℕ → Torus d → ℝ, (∀ N, Measurable (hN N) ∧ ∀ x, |hN N x| ≤ 1) →
      (∀ N, 2 ≤ N → weakRefMarginal q (hN N) (withDensityReal ρ) β N ≪ withDensityReal ρ) →
      (∀ N, 2 ≤ N → ∃ cN : ℝ, ∀ x, hN N x = -β * ∫ y, k (x - y) *
          (((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1) ∂(withDensityReal ρ) + cN) →
      (∃ C₁ : ℝ, ∀ N, 2 ≤ N →
        eLpNorm (fun y => ((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C₁ * deltaN d s N)) →
      (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ᵐ y ∂(withDensityReal ρ),
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ ε) →
      ∃ C : ℝ, ∀ N, 2 ≤ N → ∀ᵐ y ∂(withDensityReal ρ),
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * deltaN d s N := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hprob : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  refine ⟨pinGamma β, pinGamma_pos hβ, ?_⟩
  intro q Cq hqm hq0 hqe hdec hqenv hrow k Ck hkm hkb hN hNb hac hcal hL2 hunif
  obtain ⟨C₁, hC₁⟩ := hL2
  obtain ⟨Eδ, N₁, hEδ, hstep⟩ := linf_one_step hd hcrit β hβ ρ hρ q hq0 hqm hqe Cq hqenv hdec hrow
    k Ck hkm hkb C₁
  obtain ⟨N₀, hN₀⟩ := hunif (1 / 2) (by norm_num)
  have htend := (tendsto_deltaN (d := d) hd hs0 hsd).const_mul Eδ
  have hev := htend.eventually (gt_mem_nhds (by norm_num : Eδ * 0 < 1 / 32))
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 hev
  set N₂ : ℕ := max (max N₀ N₁) (max N₃ 2) with hN₂
  set Kd : ℝ := Real.exp ((β * pinGamma β + 1) + 1 + β * (1 + 0) * pinGamma β) with hKd
  have hKd0 : 0 < Kd := Real.exp_pos _
  refine ⟨max (8 * Eδ) (max 1 Kd * N₂), ?_⟩
  intro N hN2
  have hδ0 : 0 ≤ deltaN d s N := deltaN_nonneg hcrit (by omega)
  have hδ1 : 1 / (N : ℝ) ≤ deltaN d s N := deltaN_ge_inv hcrit (by omega)
  by_cases hbig : N₂ ≤ N
  · -- large N: iterate the one-step estimate
    have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hbig
    have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hbig
    have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hbig
    have hε : Eδ * deltaN d s N < 1 / 32 := by
      have := hN₃ N hN3
      simpa using this
    obtain ⟨cN, hcN⟩ := hcal N hN2
    set θ : ℝ := 4 * (β * pinGamma β) with hθ
    have hg : β * pinGamma β ≤ 1 / 16 := by
      rw [beta_mul_pinGamma hβ, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.add_one_le_exp (10 : ℝ)]
    have hg0 : 0 ≤ β * pinGamma β := mul_nonneg hβ.le (pinGamma_pos hβ).le
    have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
    have hθ1 : θ ≤ 1 / 4 := by rw [hθ]; linarith
    have hind : ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ M ≤ 1 / 2 ∧ M ≤ θ ^ m / 2 + 8 * (Eδ * deltaN d s N) ∧
        ∀ᵐ y ∂(withDensityReal ρ), |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
          (withDensityReal ρ) y).toReal - 1| ≤ M := by
      intro m
      induction m with
      | zero =>
        refine ⟨1 / 2, by norm_num, le_rfl, ?_, hN₀ N hN0⟩
        have : 0 ≤ Eδ * deltaN d s N := mul_nonneg hEδ hδ0
        simp only [pow_zero]; linarith
      | succ m ih =>
        obtain ⟨M, hM0, hM1, hMθ, hMae⟩ := ih
        have hstp := hstep (hN N) (hNb N).1 (hNb N).2 N hN1 hN2 cN hcN (hC₁ N hN2) (by linarith) M hM0 hM1 hMae
        have hε0 : 0 ≤ Eδ * deltaN d s N := mul_nonneg hEδ hδ0
        refine ⟨4 * (β * pinGamma β * M + Eδ * deltaN d s N), by positivity, ?_, ?_, hstp⟩
        · nlinarith
        · have : θ ^ (m + 1) = θ * θ ^ m := by ring
          rw [this]
          rw [hθ] at hθ0 hθ1 ⊢
          nlinarith [mul_nonneg hθ0 hε0, mul_le_mul_of_nonneg_left hMθ hθ0]
    have hall : ∀ᵐ y ∂(withDensityReal ρ), ∀ m : ℕ,
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv (withDensityReal ρ) y).toReal - 1|
          ≤ θ ^ m / 2 + 8 * (Eδ * deltaN d s N) := by
      rw [ae_all_iff]
      intro m
      obtain ⟨M, -, -, hM, hae⟩ := hind m
      filter_upwards [hae] with y hy
      exact hy.trans hM
    filter_upwards [hall] with y hy
    have hlim : Filter.Tendsto (fun m : ℕ => θ ^ m / 2 + 8 * (Eδ * deltaN d s N)) Filter.atTop
        (nhds (0 / 2 + 8 * (Eδ * deltaN d s N))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 (by linarith)).div_const 2).add_const _
    have := ge_of_tendsto hlim (Filter.Eventually.of_forall hy)
    refine this.trans ?_
    rw [zero_div, zero_add]
    calc 8 * (Eδ * deltaN d s N) = (8 * Eδ) * deltaN d s N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
  · -- small N
    push Not at hbig
    have hK := weakRef_density_le β hβ ρ hρ q hq0 hqm hqe hrow (hN N) (hNb N).1 (hNb N).2 N (by omega)
    filter_upwards [hK] with y hy
    have hnn : 0 ≤ ((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
        (withDensityReal ρ) y).toReal := ENNReal.toReal_nonneg
    have h1 : |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv (withDensityReal ρ) y).toReal - 1|
        ≤ max 1 Kd := by
      rw [abs_le]
      constructor
      · linarith [le_max_left 1 Kd]
      · linarith [le_max_right 1 Kd, le_max_left 1 Kd]
    refine h1.trans ?_
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hN2r : (N : ℝ) ≤ N₂ := by exact_mod_cast hbig.le
    have hmax : 1 ≤ max 1 Kd := le_max_left _ _
    have h2 : max 1 Kd ≤ (max 1 Kd * N₂) * (1 / (N : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ (by linarith)]
      nlinarith
    calc max 1 Kd ≤ (max 1 Kd * N₂) * (1 / (N : ℝ)) := h2
      _ ≤ (max 1 Kd * N₂) * deltaN d s N :=
          mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0

end Final

end HRS
