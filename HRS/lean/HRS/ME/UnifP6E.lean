import HRS.ME.UnifP6D

/-!
# Uniform Proposition 4.8, part E (packet P6): marginal estimates

Uniform forms of `l48_cavity_marg_L2`, `l48_mean_shift`, `l48_var_S`, `l48_Phi_i`, `l48_marg_dom`
(`HRS/Equilibrium/L48Aux{2,3}.lean`), using `CavRespUnif` (clauses 2 and 4 of the uniform Lemma 4.6).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.L48

variable {d : ℕ} {s : ℝ}

/-- Uniform `l48_cavity_marg_L2`: the cavity first marginal is `δ_N`-close to `μ` in `L²(μ)`. -/
theorem l48_cavity_marg_L2_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) (hCR : CavRespUnif d s c βm βp c₀ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N →
      firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ ∧
      eLpNorm (fun y => ((firstMarginal (critCavity d s c β ρ N)).rnDeriv
          (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
        ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C2, hC2, h2_all⟩ := hCR
  obtain ⟨C1, hC10, h1_all⟩ := firstMarginal_density_L2_unif hd hs0 hsd βm βp hβm hββ Λ
  refine ⟨|C1| + C2, by positivity, fun β hβI ρ hF N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := isProbabilityMeasure_mu hρ
  have h2 := h2_all β hβI ρ hF
  have h1 := h1_all β hβI ρ hρ hF.up
  obtain ⟨hm1, ha1, hb1⟩ := (h2 N hN).1
  obtain ⟨-, hc1⟩ := h1 N hN
  refine ⟨ha1, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ0 : 0 ≤ deltaN d s N := by
    have := l48_sqrt_log_le hd hcrit hβ hρ hc hN
    exact (div_nonneg (Real.sqrt_nonneg _) hN0.le).trans this
  set pm : Torus d → ℝ := fun y => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
    (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal with hpm
  set pν : Torus d → ℝ := fun y => ((firstMarginal (critCavity d s c β ρ N)).rnDeriv
    (withDensityReal ρ) y).toReal with hpν
  have hpmm : Measurable pm := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpνm : Measurable pν := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have e1 : (fun y => pν y - 1) = (fun y => pν y - pm y) + (fun y => pm y - 1) := by
    funext y; simp
  have e2 : eLpNorm (fun y => pν y - pm y) 2 (withDensityReal ρ) =
      eLpNorm (fun y => pm y - pν y) 2 (withDensityReal ρ) := by
    have := eLpNorm_sub_comm (f := fun y => pm y) (g := fun y => pν y) (p := 2) (μ := withDensityReal ρ)
    exact this.symm ▸ rfl
  have h3 : eLpNorm (fun y => pν y - 1) 2 (withDensityReal ρ) ≤
      eLpNorm (fun y => pν y - pm y) 2 (withDensityReal ρ) +
        eLpNorm (fun y => pm y - 1) 2 (withDensityReal ρ) := by
    rw [e1]
    exact eLpNorm_add_le (by norm_num)
  refine h3.trans ?_
  rw [e2]
  have hb2 : eLpNorm (fun y => pm y - pν y) 2 (withDensityReal ρ) ≤ ENNReal.ofReal (C2 * deltaN d s N) :=
    hb1.trans (ENNReal.ofReal_le_ofReal (by
      have := l48_sqrt_log_le hd hcrit hβ hρ hc hN
      calc C2 * Real.sqrt (Real.log N) / N = C2 * (Real.sqrt (Real.log N) / N) := by ring
        _ ≤ C2 * deltaN d s N := mul_le_mul_of_nonneg_left this hC2))
  have hc2 : eLpNorm (fun y => pm y - 1) 2 (withDensityReal ρ) ≤ ENNReal.ofReal (|C1| * deltaN d s N) :=
    hc1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0))
  calc _ ≤ ENNReal.ofReal (C2 * deltaN d s N) + ENNReal.ofReal (|C1| * deltaN d s N) := add_le_add hb2 hc2
    _ = ENNReal.ofReal ((|C1| + C2) * deltaN d s N) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hC2 hδ0) (mul_nonneg (abs_nonneg _) hδ0)]
        congr 1; ring


/-- Uniform `l48_mean_shift`. -/
theorem l48_mean_shift_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) (hCR : CavRespUnif d s c βm βp c₀ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j : Fin (N - 1),
      ∀ Φ : Torus d → ℝ, Measurable Φ → ∀ K : ℝ, 0 < K →
        ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal K →
        |∫ Y, Φ (Y j) ∂(critPole d s c β ρ N x t) - ∫ y, Φ y ∂(withDensityReal ρ)| ≤
          C * Real.sqrt K * deltaN d s N := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cd, hCd0, hCd_all⟩ := pole_dual_unif_fam hd hs0 hsd βm βp hβm hββ c₀ Λ
  obtain ⟨M1, hM1, hM_all⟩ := pole_marg_le_unif_fam hd hs0 hsd βm βp hβm c₀ Λ
  obtain ⟨Mc, hMc, hMcav_all⟩ := cavity_marginal_le_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Cm, hCm0, hCm_all⟩ := l48_cavity_marg_L2_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hΛ hCR
  refine ⟨Cd + Cm + 1, by positivity, fun β hβI ρ hF N hN x t ht j Φ hΦ K hK hKint => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := isProbabilityMeasure_mu hρ
  have hCd := hCd_all β hβI ρ hF
  have hM := hM_all β hβI ρ hF
  have hMcav := hMcav_all β hβI ρ hρ hF.up
  have hCm := hCm_all β hβI ρ hF
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  have hδinv : (N : ℝ)⁻¹ ≤ deltaN d s N := inv_le_deltaN (d := d) hs0 N (by omega)
  have hδ0 : 0 < deltaN d s N := lt_of_lt_of_le (inv_pos.2 hN0) hδinv
  have hsδ : Real.sqrt (deltaN d s N / (N : ℝ)) ≤ deltaN d s N := by
    rw [Real.sqrt_le_left hδ0.le]
    have : deltaN d s N / (N : ℝ) ≤ deltaN d s N ^ 2 := by
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_left hδinv hδ0.le
    exact this
  have hPeq : critPole d s c β ρ N x t =
      poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t :=
    critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t
  haveI hPprob := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  have hexch := MarginalAux.poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t
  have hνt : (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
      (fun Y : Config d (N - 1) => Y j) =
      firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) := by
    have : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
          (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
      unfold firstMarginal; rw [dif_pos hn1]
    rw [this]
    exact hexch.marginal_eq j ⟨0, hn1⟩
  have hstep1 : ∫ Y, Φ (Y j) ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
      ∫ y, Φ y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) := by
    rw [← hνt, integral_map (measurable_pi_apply j).aemeasurable hΦ.aestronglyMeasurable]
  rw [hPeq, hstep1]
  have hνt_le : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
      ENNReal.ofReal M1 • withDensityReal ρ := by
    rw [← hνt]; exact ((hM N hN x t ht).2 j)
  have hν0_le : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) ≤
      ENNReal.ofReal Mc • withDensityReal ρ := by
    have : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) =
        (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
          (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
      unfold firstMarginal; rw [dif_pos hn1]
    rw [this]
    exact hMcav N hN ⟨0, hn1⟩
  -- integrability of `Φ`, `Φ²`
  have hΦ2i : Integrable (fun y => Φ y ^ 2) (withDensityReal ρ) := by
    refine ⟨(hΦ.pow_const 2).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hKint ENNReal.ofReal_lt_top)
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  have hΦ1i : Integrable Φ (withDensityReal ρ) := by
    have hmem : MemLp Φ 2 (withDensityReal ρ) :=
      (memLp_two_iff_integrable_sq hΦ.aestronglyMeasurable).2 hΦ2i
    exact hmem.integrable (by norm_num)
  have hΦK : ∫ y, Φ y ^ 2 ∂(withDensityReal ρ) ≤ K := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKint
    rwa [← ofReal_integral_eq_lintegral_ofReal hΦ2i (Eventually.of_forall fun y => sq_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun y => sq_nonneg _),
      ENNReal.toReal_ofReal hK.le] at this
  -- Step 2: pole versus cavity
  have hdual : ∀ f : Torus d → ℝ, Measurable f → ∀ K' : ℝ, (∀ y, |f y| ≤ K') →
      |∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
        ∫ y, f y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β))| ≤
        (Cd * Real.sqrt (deltaN d s N / N)) * Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) := by
    intro f hf K' hfb
    have := hCd N hN x t ht f hf K' hfb
    calc _ ≤ Cd * Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) * Real.sqrt (deltaN d s N / N) := this
      _ = _ := by ring
  have h2 := l48_dual_extend hνt_le hν0_le (by positivity) hdual hΦ hΦ1i hΦ2i
  have h2' : |∫ y, Φ y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
      ∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β))| ≤
      Cd * deltaN d s N * Real.sqrt K := by
    refine h2.trans ?_
    have h5 : Real.sqrt (∫ y, Φ y ^ 2 ∂(withDensityReal ρ)) ≤ Real.sqrt K := Real.sqrt_le_sqrt hΦK
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsδ hCd0) h5 (Real.sqrt_nonneg _) (by positivity)
  -- Step 3: cavity versus `μ`
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam
  haveI hν0 := isProb_firstMarginal hn1
    (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)
  obtain ⟨hac0, hL2⟩ := hCm N hN
  rw [critCavity_eq hd hs0 hsd c β hρ N] at hac0 hL2
  set q0 : Torus d → ℝ := fun y => ((firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ)
    (N - 1) (β / N) β)).rnDeriv (withDensityReal ρ) y).toReal with hq0
  have hq0m : Measurable q0 := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hΦν0 : Integrable Φ (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) :=
    (hΦ1i.smul_measure ENNReal.ofReal_ne_top).mono_measure hν0_le
  have hq0Φ : Integrable (fun y => q0 y * Φ y) (withDensityReal ρ) :=
    (integrable_rnDeriv_smul_iff hac0).2 hΦν0
  have e1 : ∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) =
      ∫ y, q0 y * Φ y ∂(withDensityReal ρ) := by
    have := (integral_rnDeriv_smul (f := Φ) hac0).symm
    simpa [hq0, smul_eq_mul] using this
  have hdiff : ∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) -
      ∫ y, Φ y ∂(withDensityReal ρ) = ∫ y, (q0 y - 1) * Φ y ∂(withDensityReal ρ) := by
    rw [e1, ← integral_sub hq0Φ hΦ1i]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [sub_mul, one_mul]
  have hfm : Measurable (fun y => q0 y - 1) := hq0m.sub measurable_const
  have hδd : 0 ≤ Cm * deltaN d s N := mul_nonneg hCm0 hδ0.le
  have hL2' : ∫⁻ y, ENNReal.ofReal ((q0 y - 1) ^ 2) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (((Cm + 1) * deltaN d s N) ^ 2) := by
    refine ((l48_eLpNorm_le_iff hfm hδd).1 hL2).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_nonneg hCm0 hδ0.le, hδ0]
  have hgK : ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Real.sqrt K ^ 2) := by
    rw [Real.sq_sqrt hK.le]; exact hKint
  have hcs := l48_cs hfm hΦ (a := (Cm + 1) * deltaN d s N) (b := Real.sqrt K)
    (by positivity) (Real.sqrt_pos.2 hK) hL2' hgK
  have hsplit : ∫ y, Φ y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
      ∫ y, Φ y ∂(withDensityReal ρ) =
      (∫ y, Φ y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
        ∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β))) +
      (∫ y, Φ y ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) -
        ∫ y, Φ y ∂(withDensityReal ρ)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [hdiff]
  have hK0 := Real.sqrt_nonneg K
  calc _ ≤ Cd * deltaN d s N * Real.sqrt K + (Cm + 1) * deltaN d s N * Real.sqrt K := add_le_add h2' hcs
    _ = (Cd + Cm + 1) * Real.sqrt K * deltaN d s N := by ring


/-- Uniform `l48_var_S`: pole variance of the empirical sum of `Φ(y_j)`. -/
theorem l48_var_S_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (c₀ Λ : ℝ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ Φ : Torus d → ℝ, Measurable Φ → ∀ K : ℝ, 0 < K →
        ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal K →
        ∫⁻ Y, ENNReal.ofReal ((∑ j, Φ (Y j) - ∫ Y', ∑ j, Φ (Y' j) ∂(critPole d s c β ρ N x t)) ^ 2)
          ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal (Cv * K * N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C₁, hC₁, hvar_all⟩ := pole_variance_clause_unif hd hs0 hsd βm βp hβm Λ
  refine ⟨C₁ * Real.exp (βp * |c|), by positivity, fun β hβI ρ hF N hN x t ht Φ hΦ K hK hKint => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hvar := hvar_all β hβI ρ hρ hF.up
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
  have h1 := hvar N hN x t ht Φ hΦ
  have hE : ∫⁻ y, ‖Φ y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Real.exp (β * |c|)) * ENNReal.ofReal K := by
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (β * |c|)) * ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          have e2 : ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y))) ≤
              ENNReal.ofReal (Real.exp (β * |c|)) := by
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
            have h4 := hc (x - y)
            have h5 : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
            have h6 : t * (β / N) ≤ β := by
              have : β / N ≤ β := by
                rw [div_le_iff₀ hN0]
                have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
                nlinarith
              nlinarith [ht.2]
            have h7 : -(t * (β / N)) * periodicRiesz d s (x - y) ≤ (t * (β / N)) * c := by nlinarith
            have h8 : (t * (β / N)) * c ≤ (t * (β / N)) * |c| :=
              mul_le_mul_of_nonneg_left (le_abs_self c) h5
            have h9 : (t * (β / N)) * |c| ≤ β * |c| := mul_le_mul_of_nonneg_right h6 (abs_nonneg _)
            linarith
          have e3 : ‖Φ y‖ₑ ^ 2 = ENNReal.ofReal (Φ y ^ 2) := by
            rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
          rw [e3, mul_comm]
          exact mul_le_mul' e2 le_rfl
      _ = ENNReal.ofReal (Real.exp (β * |c|)) * ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl hKint
  have h2 := h1.trans (mul_le_mul' le_rfl hE)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)] at h2
  unfold evariance at h2
  refine le_trans (le_of_eq ?_) (h2.trans (ENNReal.ofReal_le_ofReal ?_))
  · refine lintegral_congr fun Y => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  · have hn : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N - 1 ≤ N)
    have hKp := hK.le
    have : C₁ * ((N - 1 : ℕ) : ℝ) * (Real.exp (β * |c|) * K) ≤ C₁ * Real.exp (β * |c|) * K * N := by
      have h0 : 0 ≤ C₁ * (Real.exp (β * |c|) * K) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hn h0]
    refine this.trans ?_
    have hexp : Real.exp (β * |c|) ≤ Real.exp (βp * |c|) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hβI.2 (abs_nonneg c))
    have h0 : 0 ≤ C₁ * K * N := by positivity
    calc C₁ * Real.exp (β * |c|) * K * N = (C₁ * K * N) * Real.exp (β * |c|) := by ring
      _ ≤ (C₁ * K * N) * Real.exp (βp * |c|) := mul_le_mul_of_nonneg_left hexp h0
      _ = _ := by ring


/-- Uniform `l48_Phi_i`: the `i`-th coordinate of `Φ` in `L²(P)`. -/
theorem l48_Phi_i_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (c₀ Λ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      ∀ Φ : Torus d → ℝ, Measurable Φ → ∀ K : ℝ, 0 < K →
        ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal K →
        ∫⁻ Y, ENNReal.ofReal (Φ (Y i) ^ 2) ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal (M * K) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨M1, hM1, hM_all⟩ := pole_marg_le_unif_fam hd hs0 hsd βm βp hβm c₀ Λ
  refine ⟨M1, hM1.le, fun β hβI ρ hF N hN x t ht i Φ hΦ K hK hKint => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hM := hM_all β hβI ρ hF
  have hmap := (hM N hN x t ht).2 i
  rw [← critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t] at hmap
  calc ∫⁻ Y, ENNReal.ofReal (Φ (Y i) ^ 2) ∂(critPole d s c β ρ N x t)
      = ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂((critPole d s c β ρ N x t).map
          (fun Y : Config d (N - 1) => Y i)) :=
        (lintegral_map (ENNReal.measurable_ofReal.comp (hΦ.pow_const 2)) (measurable_pi_apply i)).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(ENNReal.ofReal M1 • withDensityReal ρ) :=
        lintegral_mono' hmap le_rfl
    _ = ENNReal.ofReal M1 * ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) :=
        lintegral_smul_measure _ _
    _ ≤ ENNReal.ofReal M1 * ENNReal.ofReal K := mul_le_mul' le_rfl hKint
    _ = ENNReal.ofReal (M1 * K) := (ENNReal.ofReal_mul hM1.le).symm


/-- Uniform `l48_marg_dom`. -/
theorem l48_marg_dom_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (c₀ Λ : ℝ) :
    ∃ M1 : ℝ, 0 < M1 ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j : Fin (N - 1),
      (critPole d s c β ρ N x t).map (fun Y : Config d (N - 1) => Y j) ≤
        ENNReal.ofReal M1 • withDensityReal ρ := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨M1, hM1, hM_all⟩ := pole_marg_le_unif_fam hd hs0 hsd βm βp hβm c₀ Λ
  refine ⟨M1, hM1, fun β hβI ρ hF N hN x t ht j => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hF.smooth hN x t]
  exact ((hM_all β hβI ρ hF N hN x t ht).2 j)

end HRS.ME.Unif

end
