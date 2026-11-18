import HRS.ME.UnifP5C

/-!
# Uniform Lemma 4.6 (cavity response), part D (packet P5)

Uniform versions of `pole_marg_le`, `gplus_abs_conv_small`, `l1_q0_rate` and `pole_marginal_l1`
(`HRS/Equilibrium/CavityPrefactor.lean`), with constants chosen after `d, s, βm, βp, Λ, c` and before
`β ∈ [βm, βp]` and the smooth density `ρ ≤ Λ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

variable {d : ℕ} {s c : ℝ}

/-- Uniform `pole_marg_le`: every one-coordinate marginal of every pole law has density bounded by `M₁`. -/
theorem pole_marg_le_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ M1 : ℝ, 0 < M1 ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≪
          withDensityReal ρ ∧
        ∀ j : Fin (N - 1),
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
              (fun Y : Config d (N - 1) => Y j) ≤ ENNReal.ofReal M1 • withDensityReal ρ := by
  obtain ⟨C1, hC1, h1U⟩ := pole_density_clauses_unif hd hs0 hsd βm βp hβm Λ
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨C1 * Real.exp (βp * max B 0), by positivity, fun β hβI ρ hρ hΛ N hN x t ht => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have h1 := h1U β hβI ρ hρ hΛ
  have hbp : β * max B 0 ≤ βp * max B 0 := mul_le_mul_of_nonneg_right hβI.2 hB0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  obtain ⟨⟨hac, hle⟩, -⟩ := h1 N hN x t ht
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  haveI hνp := isProb_firstMarginal hn1 (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)
  refine ⟨hac, fun j => ?_⟩
  have hexch := MarginalAux.poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t
  have hfm : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
        (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
    unfold firstMarginal; rw [dif_pos hn1]
  rw [hexch.marginal_eq j ⟨0, hn1⟩, ← hfm]
  refine Measure.le_iff'.2 fun A => ?_
  have hlam1 : β / N ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hbd : ∀ᵐ y ∂(withDensityReal ρ),
      (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
        (withDensityReal ρ) y ≤ ENNReal.ofReal (C1 * Real.exp (βp * max B 0)) := by
    filter_upwards [hle] with y hy
    refine hy.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC1.le))
    have h4 := hB (x - y)
    have h5 : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
    have h6 : t * (β / N) ≤ β := by nlinarith [ht.2]
    have h7 : -B ≤ periodicRiesz d s (x - y) := by linarith
    nlinarith [le_max_left B 0, hbp]
  have hA : (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) A =
      ∫⁻ y in A, (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
        (withDensityReal ρ) y ∂(withDensityReal ρ) := by
    rw [Measure.setLIntegral_rnDeriv hac]
  rw [hA]
  calc _ ≤ ∫⁻ y in A, ENNReal.ofReal (C1 * Real.exp (βp * max B 0)) ∂(withDensityReal ρ) :=
        lintegral_mono_ae (ae_restrict_of_ae hbd)
    _ = _ := by simp [Measure.smul_apply]

/-- Uniform `gplus_abs_conv_small` (does not involve `β`). -/
theorem gplus_abs_conv_small_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) (M : ℝ) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ h : Torus d → ℝ, Measurable h → (∀ y, |h y| ≤ M) →
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 → ∫ y, |h y| ∂(withDensityReal ρ) ≤ e → ∀ x : Torus d,
        ∫ y, gPlus d s c (x - y) * |h y| ∂(withDensityReal ρ) ≤ CM * Real.sqrt e := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cc, -, -, h4⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ1
  have hΛ0 : 0 < Λ := by linarith
  have hgpm := measurable_gPlus hd hs0 hsd c
  obtain ⟨CM, hCM⟩ := h4 (Λ * M)
  refine ⟨|CM|, abs_nonneg _, fun ρ hρ hΛ h hm hb e he0 he1 hl x => ?_⟩
  have hμ := isProbabilityMeasure_mu hρ
  have hρm : Measurable ρ := hρ.density.measurable
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb (Classical.arbitrary _))
  set w : Torus d → ℝ := fun y => ρ y * |h y| with hw
  have hwm : Measurable w := hρm.mul hm.abs
  have hwb : ∀ y, |w y| ≤ Λ * M := by
    intro y
    have h2 : |ρ y| ≤ Λ := by rw [abs_of_pos (hρ.pos y)]; exact hΛ y
    rw [hw]; simp only [abs_mul, abs_abs]
    exact mul_le_mul h2 (hb y) (abs_nonneg _) hΛ0.le
  have hhi : Integrable (fun y => |h y|) (withDensityReal ρ) :=
    Integrable.of_bound (C := M) hm.abs.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_abs]; exact hb y)
  have hl1 : ∫⁻ y, ‖w y‖ₑ ≤ ENNReal.ofReal e := by
    have e1 : ∀ y, ‖w y‖ₑ = ENNReal.ofReal (ρ y) * ENNReal.ofReal |h y| := by
      intro y
      simp only [hw, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y), Real.enorm_eq_ofReal_abs,
        abs_abs]
    simp_rw [e1]
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    have e2 : ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal |h y| =
        ∫⁻ y, ENNReal.ofReal |h y| ∂(withDensityReal ρ) := by
      show _ = ∫⁻ y, ENNReal.ofReal |h y| ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x))
      rw [lintegral_withDensity_eq_lintegral_mul _ hmρ
        (show Measurable fun y => ENNReal.ofReal |h y| from ENNReal.measurable_ofReal.comp hm.abs)]
      rfl
    rw [e2, ← ofReal_integral_eq_lintegral_ofReal hhi (Eventually.of_forall fun y => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hl
  have h1 := hCM w e hwm hwb he1 hl1 x
  have hmeasF : Measurable fun y => gPlus d s c (x - y) * |h y| :=
    (hgpm.comp (measurable_const.sub measurable_id)).mul hm.abs
  have hF0 : ∀ y, 0 ≤ gPlus d s c (x - y) * |h y| := fun y => mul_nonneg (hc _) (abs_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hmeasF.aestronglyMeasurable]
  have h2 : ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) * |h y|) ∂(withDensityReal ρ) =
      ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ := by
    show _ = _
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    unfold withDensityReal
    rw [lintegral_withDensity_eq_lintegral_mul _ hmρ
      (show Measurable fun y => ENNReal.ofReal (gPlus d s c (x - y) * |h y|) from
        ENNReal.measurable_ofReal.comp hmeasF)]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply, hw, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y),
      Real.enorm_eq_ofReal_abs, abs_abs]
    have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
    rw [ENNReal.ofReal_mul hg0]
    ring
  rw [h2]
  have h3 : (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ).toReal ≤ |CM| * Real.sqrt e :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (h1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))))
  exact h3

/-- Uniform `l1_q0_rate`. -/
theorem l1_q0_rate_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      ∫ y, |1 - qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y| ∂(withDensityReal ρ) ≤
        Ce * deltaN d s (n + 1) := by
  obtain ⟨Mp, hMp1, hMpU⟩ := pDens_bounds_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Mq, hMq0, hMqU⟩ := qDens_bound_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨C2, hC20, hC2U⟩ := L2_all_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨CL, hCL0, hCLU⟩ := cavity_L2_unif hd hs0 hsd βm βp hβm hββ Λ
  refine ⟨C2 + CL, by positivity, fun β hβI ρ hρ hΛ n hn lam hlamdef => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hMp := hMpU β hβI ρ hρ hΛ
  have hMq := hMqU β hβI ρ hρ hΛ
  have hC2 := hC2U β hβI ρ hρ hΛ
  have hCL := hCLU β hβI ρ hρ hΛ
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ deltaN d s (n + 1) := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
  have hsδ : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ deltaN d s (n + 1) := by
    rw [Real.sqrt_le_left hδ0]
    have : deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ deltaN d s (n + 1) ^ 2 := by
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_left hδinv hδ0
    exact this
  have hacq := hMq (n + 1) hN
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hp0 : ∀ y, 0 < pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y :=
    pDens_pos hd hs0 hsd hρ hlam hln
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  have hp2 : Real.sqrt (∫ y, (p y - 1) ^ 2 ∂μ) ≤ C2 * deltaN d s (n + 1) :=
    Real.sqrt_le_iff.2 ⟨by positivity, hC2 n hn lam hlamdef⟩
  have hpq2 : Real.sqrt (∫ y, (p y - q y) ^ 2 ∂μ) ≤ CL * deltaN d s (n + 1) :=
    (hCL n hn lam hlamdef).trans (mul_le_mul_of_nonneg_left hsδ hCL0)
  have hpb' : ∀ y, |p y - 1| ≤ Mp + 1 := fun y => by
    rw [abs_le]; constructor <;> linarith [hp0 y, hpb y]
  have hpqb : ∀ y, |p y - qb y| ≤ Mp + Mq := fun y => by
    rw [abs_le]; constructor <;> linarith [hp0 y, hpb y, hqb0 y, hqbM y]
  have hl1a : ∫ y, |p y - 1| ∂μ ≤ C2 * deltaN d s (n + 1) :=
    (l1_le_sqrt (h := fun y => p y - 1) (hpm.sub measurable_const) hpb').trans hp2
  have hl1b : ∫ y, |p y - qb y| ∂μ ≤ CL * deltaN d s (n + 1) := by
    have e : ∫ y, (p y - qb y) ^ 2 ∂μ = ∫ y, (p y - q y) ^ 2 ∂μ :=
      integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
    refine (l1_le_sqrt (h := fun y => p y - qb y) (hpm.sub hqbm) hpqb).trans ?_
    rw [e]; exact hpq2
  have hpi : Integrable p μ := Integrable.of_bound (C := Mp) hpm.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (hp0 y)]; exact hpb y)
  have hqbi : Integrable qb μ := Integrable.of_bound (C := Mq) hqbm.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hqb0 y)]; exact hqbM y)
  have h1 : Integrable (fun y => |p y - 1|) μ := (hpi.sub (integrable_const _)).abs
  have h2 : Integrable (fun y => |p y - qb y|) μ := (hpi.sub hqbi).abs
  have h3 : Integrable (fun y => |1 - qb y|) μ := ((integrable_const (1 : ℝ)).sub hqbi).abs
  have hle : ∫ y, |1 - qb y| ∂μ ≤ ∫ y, (|p y - 1| + |p y - qb y|) ∂μ := by
    refine integral_mono h3 (h1.add h2) fun y => ?_
    have := abs_add_le (1 - p y) (p y - qb y)
    rw [show (1 - p y) + (p y - qb y) = 1 - qb y by ring, abs_sub_comm 1 (p y)] at this
    exact this
  rw [integral_add h1 h2] at hle
  have e : ∫ y, |1 - q y| ∂μ = ∫ y, |1 - qb y| ∂μ :=
    integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
  rw [e]
  nlinarith

/-- Uniform `pole_marginal_l1`. -/
theorem pole_marginal_l1_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫ y, |((firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
          (withDensityReal ρ) y).toReal - 1| ∂(withDensityReal ρ) ≤ Ce * deltaN d s N := by
  obtain ⟨Ce0, hCe0, hCeU⟩ := l1_q0_rate_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Cd, hCd0, hCdU⟩ := pole_dual_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨M1, hM1, hMargU⟩ := pole_marg_le_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Mq, hMq0, hMqU⟩ := qDens_bound_unif hd hs0 hsd βm βp hβm hββ Λ
  refine ⟨Ce0 + 2 * Cd, by positivity, fun β hβI ρ hρ hΛ N hN x t ht => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hCe := hCeU β hβI ρ hρ hΛ
  have hCd := hCdU β hβI ρ hρ hΛ
  have hMarg := hMargU β hβI ρ hρ hΛ
  have hMq := hMqU β hβI ρ hρ hΛ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlamdef
  have hlamdef' : lam = β / ((n + 1 : ℕ) : ℝ) := rfl
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam : 0 ≤ lam := by positivity
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ deltaN d s (n + 1) := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
  have hsδ : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ deltaN d s (n + 1) := by
    rw [Real.sqrt_le_left hδ0]
    have : deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ deltaN d s (n + 1) ^ 2 := by
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_left hδinv hδ0
    exact this
  haveI hPt := pole_isProb hd hs0 hsd β hρ n lam hlam x t ht.1
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ n lam hlam
  haveI hνt := isProb_firstMarginal hn (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)
  haveI hν0 := isProb_firstMarginal hn (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)
  have hact : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t) ≪
      withDensityReal ρ := (hMarg (n + 1) (by omega) x t ht).1
  have hac0 : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := (hMq (n + 1) (by omega)).1
  obtain ⟨hqti, hqt1, hqteq⟩ := dens_facts hact
  obtain ⟨hq0i, hq01, hq0eq⟩ := dens_facts hac0
  set μ := withDensityReal ρ with hμdef
  set qt : Torus d → ℝ := fun y => ((firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x t)).rnDeriv μ y).toReal
    with hqt
  set q0 : Torus d → ℝ := fun y => ((firstMarginal (cavityLaw (periodicRiesz d s) μ n lam β)).rnDeriv μ y).toReal
    with hq0
  have hqtm : Measurable qt := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hq0m : Measurable q0 := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hqt0 : ∀ y, 0 ≤ qt y := fun y => ENNReal.toReal_nonneg
  have hq00 : ∀ y, 0 ≤ q0 y := fun y => ENNReal.toReal_nonneg
  -- the total variation bound
  have hTV : ∀ A : Set (Torus d), MeasurableSet A →
      |(∫ y in A, qt y ∂μ) - ∫ y in A, q0 y ∂μ| ≤ Cd * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro A hA
    have e1 : ∫ y in A, qt y ∂μ =
        (firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x t) A).toReal := by
      conv_rhs => rw [hqteq]
      rw [toReal_withDensity_apply (fun y => ENNReal.toReal_nonneg) hqti hA]
    have e2 : ∫ y in A, q0 y ∂μ =
        (firstMarginal (cavityLaw (periodicRiesz d s) μ n lam β) A).toReal := by
      conv_rhs => rw [hq0eq]
      rw [toReal_withDensity_apply (fun y => ENNReal.toReal_nonneg) hq0i hA]
    rw [e1, e2]
    have hf : Measurable (A.indicator fun _ : Torus d => (1 : ℝ)) := measurable_const.indicator hA
    have hfb : ∀ y, |A.indicator (fun _ : Torus d => (1 : ℝ)) y| ≤ 1 := fun y => by
      by_cases h : y ∈ A <;> simp [Set.indicator, h]
    have h1 := hCd (n + 1) (by omega) x t ht _ hf 1 hfb
    have e3 : ∀ m : Measure (Torus d), IsProbabilityMeasure m →
        ∫ y, A.indicator (fun _ : Torus d => (1 : ℝ)) y ∂m = (m A).toReal := by
      intro m _
      rw [integral_indicator_const _ hA]
      simp [Measure.real]
    have e4 := e3 (firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x t)) hνt
    have e5 := e3 (firstMarginal (cavityLaw (periodicRiesz d s) μ n lam β)) hν0
    have h2 : Real.sqrt (∫ y, A.indicator (fun _ : Torus d => (1 : ℝ)) y ^ 2 ∂μ) ≤ 1 := by
      rw [Real.sqrt_le_one]
      have : ∫ y, A.indicator (fun _ : Torus d => (1 : ℝ)) y ^ 2 ∂μ ≤ ∫ _y, (1 : ℝ) ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) (integrable_const _)
          (Eventually.of_forall fun y => ?_)
        have := hfb y
        nlinarith [abs_nonneg (A.indicator (fun _ : Torus d => (1 : ℝ)) y),
          sq_abs (A.indicator (fun _ : Torus d => (1 : ℝ)) y)]
      simpa using this
    rw [← e4, ← e5]
    have hlamE : β / ((n + 1 : ℕ) : ℝ) = lam := rfl
    refine h1.trans ?_
    have hs0' : 0 ≤ Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hCd0 hs0']
  have hl1 := l1_of_sets (μ := μ) hqtm hq0m hqti hq0i hqt1 hq01 hTV
  -- compare with `1`
  have hq0m' : Measurable fun y => 1 - q0 y := measurable_const.sub hq0m
  have h2 : Integrable (fun y => |qt y - q0 y|) μ := (hqti.sub hq0i).abs
  have h3 : Integrable (fun y => |1 - q0 y|) μ := ((integrable_const (1 : ℝ)).sub hq0i).abs
  have h4 : Integrable (fun y => |qt y - 1|) μ := (hqti.sub (integrable_const _)).abs
  have hle : ∫ y, |qt y - 1| ∂μ ≤ ∫ y, (|qt y - q0 y| + |1 - q0 y|) ∂μ := by
    refine integral_mono h4 (h2.add h3) fun y => ?_
    have := abs_add_le (qt y - q0 y) (q0 y - 1)
    rw [show (qt y - q0 y) + (q0 y - 1) = qt y - 1 by ring, abs_sub_comm (q0 y) 1] at this
    exact this
  rw [integral_add h2 h3] at hle
  have hl0 := hCe n hn lam hlamdef'
  have e6 : ∫ y, |1 - q0 y| ∂μ = ∫ y, |1 - qDens (periodicRiesz d s) μ n lam β y| ∂μ := rfl
  have hCdδ : Cd * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ Cd * deltaN d s (n + 1) :=
    mul_le_mul_of_nonneg_left hsδ hCd0
  have hl0' : ∫ y, |1 - q0 y| ∂μ ≤ Ce0 * deltaN d s (n + 1) := by
    rw [e6]; exact hl0
  have hl1' : ∫ y, |qt y - q0 y| ∂μ ≤ 2 * (Cd * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ))) := hl1
  have hfin : ∫ y, |qt y - 1| ∂μ ≤ Ce0 * deltaN d s (n + 1) + 2 * (Cd * deltaN d s (n + 1)) := by
    linarith [hle, hl0', hl1', hCdδ]
  calc ∫ y, |qt y - 1| ∂μ ≤ _ := hfin
    _ = (Ce0 + 2 * Cd) * deltaN d s (n + 1) := by ring

end HRS.ME.Unif

end
