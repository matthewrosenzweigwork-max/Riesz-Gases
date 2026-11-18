import HRS.ME.UnifP6E

/-!
# Uniform Proposition 4.8, part F (packet P6): the linear term

Uniform form of `l48_linear` (`HRS/Equilibrium/L48Aux3.lean`, TeX `R:eq:L-linear-bound`).  `β` is replaced by `βp`
in the explicit constant.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.L48

variable {d : ℕ} {s : ℝ}

set_option maxHeartbeats 1600000 in
/-- Uniform `l48_linear`: the linear term `∫ ψ v_Y dμ` in `L²(P)`. -/
theorem l48_linear_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) (hCR : CavRespUnif d s c βm βp c₀ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      ∀ ψ : Torus d → ℝ, Measurable ψ → Integrable ψ (withDensityReal ρ) → ∀ A K : ℝ, 0 < K → 0 ≤ A →
        ∫ y, |ψ y| ∂(withDensityReal ρ) ≤ A →
        ∫⁻ z, l48_Phiabs d s c ρ ψ z ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal K →
        eLpNorm (fun Y : Config d (N - 1) =>
            ∫ y, ψ y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)) 2
          (critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C * (Real.sqrt K + A) / Real.sqrt N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cg, hCg0, hCg_all⟩ := conv_gPlus_unif_fam hd hs0 hsd c hc c₀ Λ
  obtain ⟨Cv, hCv0, hvarS_all⟩ := l48_var_S_unif hd hcrit c hc βm βp hβm c₀ Λ
  obtain ⟨M, hM0, hMi_all⟩ := l48_Phi_i_unif hd hcrit c hc βm βp hβm c₀ Λ
  obtain ⟨Cms, hCms0, hms_all⟩ := l48_mean_shift_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hΛ hCR
  obtain ⟨M1, hM1, hdom_all⟩ := l48_marg_dom_unif hd hcrit c hc βm βp hβm c₀ Λ
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  refine ⟨βp * (Real.sqrt Cv + Real.sqrt M + 2 * Cms + Cg), by positivity,
    fun β hβI ρ hF N hN x t ht i ψ hψ hψ1 A K hK hA hAint hKint => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := isProbabilityMeasure_mu hρ
  have hCg := hCg_all ρ hF
  have hvarS := hvarS_all β hβI ρ hF
  have hMi := hMi_all β hβI ρ hF
  have hms := hms_all β hβI ρ hF
  have hdom := hdom_all β hβI ρ hF

  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hr1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast (by omega : 1 ≤ N))
  have hrr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hlam : 0 ≤ β / N := by positivity
  have hPprob : IsProbabilityMeasure (critPole d s c β ρ N x t) := by
    rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
    exact pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  set Φ := l48_Phi d s c ρ ψ with hΦdef
  have hΦm : Measurable Φ := l48_meas_Phi hd hcrit hβ hρ hc hψ
  have hΦK := l48_Phi_sq_le hd hcrit hβ hρ hc hψ hKint
  obtain ⟨hΦ2i, hΦ1i⟩ := l48_sq_integrable hd hcrit hβ hρ hc hΦm hΦK
  have hae := l48_ell_ae hd hcrit hβ hρ hc hN x ht i hψ hψ1 hKint
  set S : Config d (N - 1) → ℝ := fun Y => ∑ j, Φ (Y j) with hS
  have hSm : Measurable S := Finset.measurable_sum _ fun j _ => hΦm.comp (measurable_pi_apply j)
  set m : ℝ := ∫ Y, S Y ∂(critPole d s c β ρ N x t) with hm
  set μΦ : ℝ := ∫ z, Φ z ∂(withDensityReal ρ) with hμΦ
  set c0 : ℝ := (β / N) * m - β * μΦ with hc0
  have hℓ : (fun Y : Config d (N - 1) =>
        ∫ y, ψ y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)) =ᵐ[critPole d s c β ρ N x t]
      (fun Y => (β / N) * (S Y - m) - (β / N) * Φ (Y i) + c0) := by
    filter_upwards [hae] with Y hY
    rw [hY]
    have h := l48_split_erase i (fun j => Φ (Y j))
    simp only [hS, hc0]
    rw [h]
    ring
  rw [eLpNorm_congr_ae hℓ]
  have hsplit : (fun Y : Config d (N - 1) => (β / N) * (S Y - m) - (β / N) * Φ (Y i) + c0) =
      ((fun Y => (β / N) * (S Y - m)) - (fun Y => (β / N) * Φ (Y i))) + (fun _ => c0) := rfl
  rw [hsplit]
  -- the three pieces
  have hb1 : eLpNorm (fun Y : Config d (N - 1) => (β / N) * (S Y - m)) 2 (critPole d s c β ρ N x t) ≤
      ENNReal.ofReal ((β / N) * Real.sqrt (Cv * K * N)) := by
    have hS2 : eLpNorm (fun Y => S Y - m) 2 (critPole d s c β ρ N x t) ≤
        ENNReal.ofReal (Real.sqrt (Cv * K * N)) := by
      refine (l48_eLpNorm_le_iff (f := fun Y : Config d (N - 1) => S Y - m)
        (hSm.sub measurable_const) (Real.sqrt_nonneg _)).2 ?_
      rw [Real.sq_sqrt (by positivity)]
      exact hvarS N hN x t ht Φ hΦm K hK hΦK
    calc eLpNorm (fun Y : Config d (N - 1) => (β / N) * (S Y - m)) 2 (critPole d s c β ρ N x t)
        = eLpNorm ((β / N) • fun Y => S Y - m) 2 (critPole d s c β ρ N x t) := rfl
      _ ≤ ‖β / N‖ₑ * eLpNorm (fun Y => S Y - m) 2 (critPole d s c β ρ N x t) := eLpNorm_const_smul_le
      _ ≤ ENNReal.ofReal (β / N) * ENNReal.ofReal (Real.sqrt (Cv * K * N)) := by
          rw [Real.enorm_eq_ofReal hlam]; exact mul_le_mul' le_rfl hS2
      _ = _ := (ENNReal.ofReal_mul hlam).symm
  have hb2 : eLpNorm (fun Y : Config d (N - 1) => (β / N) * Φ (Y i)) 2 (critPole d s c β ρ N x t) ≤
      ENNReal.ofReal ((β / N) * Real.sqrt (M * K)) := by
    have hΦ2 : eLpNorm (fun Y : Config d (N - 1) => Φ (Y i)) 2 (critPole d s c β ρ N x t) ≤
        ENNReal.ofReal (Real.sqrt (M * K)) := by
      refine (l48_eLpNorm_le_iff (f := fun Y : Config d (N - 1) => Φ (Y i))
        (hΦm.comp (measurable_pi_apply i)) (Real.sqrt_nonneg _)).2 ?_
      rw [Real.sq_sqrt (by positivity)]
      exact hMi N hN x t ht i Φ hΦm K hK hΦK
    calc eLpNorm (fun Y : Config d (N - 1) => (β / N) * Φ (Y i)) 2 (critPole d s c β ρ N x t)
        = eLpNorm ((β / N) • fun Y : Config d (N - 1) => Φ (Y i)) 2 (critPole d s c β ρ N x t) := rfl
      _ ≤ ‖β / N‖ₑ * eLpNorm (fun Y : Config d (N - 1) => Φ (Y i)) 2 (critPole d s c β ρ N x t) :=
          eLpNorm_const_smul_le
      _ ≤ ENNReal.ofReal (β / N) * ENNReal.ofReal (Real.sqrt (M * K)) := by
          rw [Real.enorm_eq_ofReal hlam]; exact mul_le_mul' le_rfl hΦ2
      _ = _ := (ENNReal.ofReal_mul hlam).symm
  have hb3 : eLpNorm (fun _ : Config d (N - 1) => c0) 2 (critPole d s c β ρ N x t) =
      ENNReal.ofReal |c0| := by
    rw [eLpNorm_const c0 (by norm_num) (IsProbabilityMeasure.ne_zero _)]
    simp [Real.enorm_eq_ofReal_abs]
  -- the constant
  have hδ0 : 0 ≤ deltaN d s N := by
    have := inv_le_deltaN (d := d) hs0 N (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδ := l48_delta_le hd hcrit hβ hρ hc hN
  have hmj : ∀ j : Fin (N - 1), |∫ Y, Φ (Y j) ∂(critPole d s c β ρ N x t) - μΦ| ≤
      Cms * Real.sqrt K * deltaN d s N := fun j => hms N hN x t ht j Φ hΦm K hK hΦK
  have hint_j : ∀ j : Fin (N - 1), Integrable (fun Y : Config d (N - 1) => Φ (Y j))
      (critPole d s c β ρ N x t) := by
    intro j
    have h1 : Integrable Φ ((critPole d s c β ρ N x t).map (fun Y : Config d (N - 1) => Y j)) :=
      (hΦ1i.smul_measure ENNReal.ofReal_ne_top).mono_measure (hdom N hN x t ht j)
    exact (integrable_map_measure hΦm.aestronglyMeasurable (measurable_pi_apply j).aemeasurable).1 h1
  have hmsum : m = ∑ j : Fin (N - 1), ∫ Y, Φ (Y j) ∂(critPole d s c β ρ N x t) := by
    simp only [hm, hS]
    exact integral_finsetSum _ fun j _ => hint_j j
  have hn : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hmn : |m - ((N - 1 : ℕ) : ℝ) * μΦ| ≤ ((N - 1 : ℕ) : ℝ) * (Cms * Real.sqrt K * deltaN d s N) := by
    have e : m - ((N - 1 : ℕ) : ℝ) * μΦ =
        ∑ j : Fin (N - 1), (∫ Y, Φ (Y j) ∂(critPole d s c β ρ N x t) - μΦ) := by
      rw [hmsum, Finset.sum_sub_distrib]
      simp
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hmj j).trans (le_of_eq ?_)
    simp
  have hμΦ_le : |μΦ| ≤ Cg * A := by
    have e1 : μΦ = ∫ y, ψ y * convMeasure (gPlus d s c) (withDensityReal ρ) y ∂(withDensityReal ρ) :=
      (l48_int_psi_h hd hcrit hβ hρ hc hψ hψ1).symm
    rw [e1]
    exact (l48_abs_int_psi_h_le hd hcrit hβ hρ hc hψ hψ1 hCg).trans
      (mul_le_mul_of_nonneg_left hAint hCg0)
  have hc0e : c0 = (β / N) * (m - ((N - 1 : ℕ) : ℝ) * μΦ) - (β / N) * μΦ := by
    simp only [hc0]
    rw [hn]
    field_simp
    ring
  have hc0b : |c0| ≤ β * (Cms * Real.sqrt K * deltaN d s N) + β * Cg * A / N := by
    rw [hc0e]
    have e1 : |(β / N) * (m - ((N - 1 : ℕ) : ℝ) * μΦ)| ≤ β * (Cms * Real.sqrt K * deltaN d s N) := by
      rw [abs_mul, abs_of_nonneg hlam]
      have h2 : (β / N) * ((N - 1 : ℕ) : ℝ) ≤ β := by
        rw [hn]
        have : (β / N) * ((N : ℝ) - 1) = β - β / N := by field_simp
        rw [this]; linarith
      calc (β / N) * |m - ((N - 1 : ℕ) : ℝ) * μΦ|
          ≤ (β / N) * (((N - 1 : ℕ) : ℝ) * (Cms * Real.sqrt K * deltaN d s N)) :=
            mul_le_mul_of_nonneg_left hmn hlam
        _ = ((β / N) * ((N - 1 : ℕ) : ℝ)) * (Cms * Real.sqrt K * deltaN d s N) := by ring
        _ ≤ β * (Cms * Real.sqrt K * deltaN d s N) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
    have e2 : |(β / N) * μΦ| ≤ β * Cg * A / N := by
      rw [abs_mul, abs_of_nonneg hlam]
      calc (β / N) * |μΦ| ≤ (β / N) * (Cg * A) := mul_le_mul_of_nonneg_left hμΦ_le hlam
        _ = β * Cg * A / N := by ring
    calc |(β / N) * (m - ((N - 1 : ℕ) : ℝ) * μΦ) - (β / N) * μΦ|
        ≤ |(β / N) * (m - ((N - 1 : ℕ) : ℝ) * μΦ)| + |(β / N) * μΦ| := abs_sub _ _
      _ ≤ _ := add_le_add e1 e2
  -- assemble
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  refine (add_le_add ((eLpNorm_sub_le (by norm_num)).trans (add_le_add hb1 hb2)) (le_of_eq hb3)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- real inequality
  set r := Real.sqrt N with hr
  have hsK := Real.sqrt_nonneg K
  have e1 : (β / N) * Real.sqrt (Cv * K * N) = β * Real.sqrt Cv * Real.sqrt K / r := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCv0]
    rw [← hr, ← hrr]
    field_simp
  have e2 : (β / N) * Real.sqrt (M * K) = β * Real.sqrt M * Real.sqrt K / (r * r) := by
    rw [Real.sqrt_mul hM0, ← hrr]
    field_simp
  have e2' : β * Real.sqrt M * Real.sqrt K / (r * r) ≤ β * Real.sqrt M * Real.sqrt K / r := by
    refine div_le_div_of_nonneg_left (by positivity) hr0 ?_
    nlinarith
  have e3 : β * (Cms * Real.sqrt K * deltaN d s N) ≤ β * (Cms * Real.sqrt K * (2 / r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ (by positivity)) hβ.le
  have e4 : β * Cg * A / N ≤ β * Cg * A / r := by
    rw [← hrr]
    refine div_le_div_of_nonneg_left (by positivity) hr0 ?_
    nlinarith
  have hfin : β * Real.sqrt Cv * Real.sqrt K / r + β * Real.sqrt M * Real.sqrt K / r +
      β * Cms * Real.sqrt K * (2 / r) + β * Cg * A / r =
      (β * (Real.sqrt Cv + Real.sqrt M + 2 * Cms + Cg) * (Real.sqrt K + A) / r) -
        (β * Cg * Real.sqrt K / r + β * (Real.sqrt Cv + Real.sqrt M + 2 * Cms) * A / r) := by
    field_simp
    ring
  have hrest : 0 ≤ β * Cg * Real.sqrt K / r + β * (Real.sqrt Cv + Real.sqrt M + 2 * Cms) * A / r := by
    positivity
  have hmain : (β / N) * Real.sqrt (Cv * K * N) + (β / N) * Real.sqrt (M * K) + |c0| ≤
      β * Real.sqrt Cv * Real.sqrt K / r + β * Real.sqrt M * Real.sqrt K / r +
        β * Cms * Real.sqrt K * (2 / r) + β * Cg * A / r := by
    rw [e1, e2]
    linarith [e2', e3, e4, hc0b]
  calc _ ≤ _ := hmain
    _ = _ := hfin
    _ ≤ β * (Real.sqrt Cv + Real.sqrt M + 2 * Cms + Cg) * (Real.sqrt K + A) / r :=
        sub_le_self _ hrest
    _ ≤ _ := by
        have h0 : 0 ≤ (Real.sqrt Cv + Real.sqrt M + 2 * Cms + Cg) * (Real.sqrt K + A) / r := by positivity
        calc β * (Real.sqrt Cv + Real.sqrt M + 2 * Cms + Cg) * (Real.sqrt K + A) / r
            = β * ((Real.sqrt Cv + Real.sqrt M + 2 * Cms + Cg) * (Real.sqrt K + A) / r) := by ring
          _ ≤ βp * ((Real.sqrt Cv + Real.sqrt M + 2 * Cms + Cg) * (Real.sqrt K + A) / r) :=
              mul_le_mul_of_nonneg_right hβI.2 h0
          _ = _ := by ring

end HRS.ME.Unif

end
