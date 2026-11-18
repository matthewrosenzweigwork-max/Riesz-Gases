import HRS.ME.UnifP6B

/-!
# Uniform Lemma 4.7 (`integrated_taylor_remainder`), part C (packet P6)

Uniform forms of `taylor_field_lower`, `taylor_B1_bound`, `taylor_Lp_total` (`TaylorAux6`, `TaylorAux7`) and
`integrated_taylor_remainder_proof` (`TaylorAux8`, Lemma 4.7).  `β` is replaced by `βp` in the explicit
constants; the constants of Lemma 4.4 come from `product_moment_transfer_unif`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.TaylorAux
  HRS.KernelAux HRS.KernelAux2

variable {d : ℕ} {s : ℝ}

/-- Uniform `taylor_field_lower`. -/
theorem taylor_field_lower_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ (N : ℕ) (n : ℕ) (i : Fin n) (H : ℝ), 0 ≤ H →
      ∀ (Y : Config d n) (y : Torus d), -K ≤ taylorFieldH d s c β ρ N i H Y y := by
  obtain ⟨Ch, hCh0, hCh_all⟩ := taylor_h_bound_unif hd hcrit c hc c₀ Λ (by linarith)
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  refine ⟨βp * Ch, by positivity, fun β hβI ρ hF N n i H hH Y y => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hCh := hCh_all ρ hF
  unfold taylorFieldH
  have h1 : 0 ≤ (β / N) * ∑ j ∈ Finset.univ.erase i, gTrunc d s c H (y - Y j) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => le_min (hc _) hH)
  have h2 : β * convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ β * Ch :=
    mul_le_mul_of_nonneg_left (hCh y).2.2 hβ.le
  have h3 : β * Ch ≤ βp * Ch := mul_le_mul_of_nonneg_right hβI.2 hCh0
  linarith

/-- Uniform `taylor_B1_bound`. -/
theorem taylor_B1_bound_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) (q : ℕ) (hq : 1 ≤ q) {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ H : ℝ, 2 ≤ H → ∀ i : Fin (N - 1), ∀ x : Torus d,
      ∀ φ ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)),
        taylorLp (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ) ((2 * q : ℕ) : ℝ)
          (fun Y => ∫⁻ y, ENNReal.ofReal (φ y) *
              ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2)
            ∂(withDensityReal ρ)) ≤
        ENNReal.ofReal (Cb * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 +
          1 / (N : ℝ) ^ 2)) := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨Cf, hCf0, hCf_all⟩ := taylor_field_moment_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hΛ q hq
  obtain ⟨Cp, hCp0, hCp_all⟩ := taylor_tail_bounds_unif hd hcrit c hc c₀ Λ hΛ 2 le_rfl
  refine ⟨Cp * Real.exp K * max Cf 1, by positivity, fun β hβI ρ hF N hN H hH i x φ hφ => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hCf := hCf_all β hβI ρ hF
  have hCp := hCp_all ρ hF

  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hH0 : 0 < H := by linarith
  have hp0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
  set μ : Measure (Torus d) := withDensityReal ρ with hμdef
  set Pm : Measure (Config d (N - 1)) := Measure.pi fun _ : Fin (N - 1) => μ with hPm
  set Θ : ℝ := Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2 with hΘ
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hΘ0 : 0 ≤ Θ := by positivity
  have hφm : Measurable φ := by
    rcases hφ with rfl | rfl
    · exact measurable_const
    · exact (PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)).comp
        (measurable_const.sub measurable_id)
  have hmass : ∫⁻ y, ENNReal.ofReal (φ y) ∂μ ≤ ENNReal.ofReal Cp := (hCp H hH x φ hφ).1
  set Fm : Torus d → ℝ≥0∞ := fun y => ENNReal.ofReal (φ y) with hFm
  have hFmm : Measurable Fm := hφm.ennreal_ofReal
  have hvm := taylor_measurable_fieldH hd hcrit β ρ c (N := N) (N - 1) i H
  set Gf : Config d (N - 1) → Torus d → ℝ≥0∞ :=
    fun Y y => ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) with hGf
  have hGfm : Measurable (Function.uncurry Gf) := by
    refine Measurable.ennreal_ofReal ?_
    exact measurable_const.mul (hvm.pow_const 2)
  have hGfy : ∀ Y, Measurable (Gf Y) := fun Y =>
    (hGfm.comp (measurable_const.prodMk measurable_id) : Measurable fun y => Function.uncurry Gf (Y, y))
  have hGfY : ∀ y, Measurable (fun Y => Gf Y y) := fun y =>
    (hGfm.comp (measurable_id.prodMk measurable_const) : Measurable fun Y => Function.uncurry Gf (Y, y))
  -- Jensen in `y`
  have hjen : ∀ Y, (∫⁻ y, Fm y * Gf Y y ∂μ) ^ (2 * q) ≤
      (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ :=
    fun Y => taylor_jensen hFmm (hGfy Y) (2 * q) (by omega)
  -- the `L^{4q}` moment of the field, as a bound on `∫⁻ (G)^{2q}`
  set bd : ℝ := Real.exp K ^ (2 * q) * (Cf * Θ ^ (2 * q)) with hbd
  have hbd0 : 0 ≤ bd := by positivity
  have hY : ∀ y : Torus d, ∫⁻ Y, Gf Y y ^ (2 * q) ∂Pm ≤ ENNReal.ofReal bd := by
    intro y
    obtain ⟨B, hB⟩ := taylor_field_bdd hd hcrit β hβ ρ hρ c hc N (N - 1) i H hH0.le y
    set vv : Config d (N - 1) → ℝ := fun Y => taylorFieldH d s c β ρ N i H Y y with hvv
    have hvvm : Measurable vv :=
      Measurable.of_uncurry_right (f := fun (Y : Config d (N - 1)) (y : Torus d) =>
        taylorFieldH d s c β ρ N i H Y y) hvm
    have hev : Even (4 * q) := ⟨2 * q, by ring⟩
    have e0 : ∀ Y, (Real.exp K * vv Y ^ 2) ^ (2 * q) = Real.exp K ^ (2 * q) * vv Y ^ (4 * q) := by
      intro Y; ring
    have e1 : ∀ Y, Gf Y y ^ (2 * q) = ENNReal.ofReal (Real.exp K ^ (2 * q) * vv Y ^ (4 * q)) := by
      intro Y
      have : Gf Y y = ENNReal.ofReal (Real.exp K * vv Y ^ 2) := rfl
      rw [this, ← ENNReal.ofReal_pow (by positivity), e0]
    simp_rw [e1]
    have hgint : Integrable (fun Y => Real.exp K ^ (2 * q) * vv Y ^ (4 * q)) Pm :=
      taylor_integrable_of_bdd ((hvvm.pow_const _).const_mul _)
        (B := Real.exp K ^ (2 * q) * B ^ (4 * q)) fun Y => by
          rw [abs_mul, abs_pow, abs_pow, abs_of_pos (Real.exp_pos K)]
          gcongr
          exact hB Y
    rw [← ofReal_integral_eq_lintegral_ofReal hgint (Filter.Eventually.of_forall fun Y => by
      have := hev.pow_nonneg (vv Y); positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hCf N hN H hH i y) (by positivity)
  -- integrate the Jensen bound over `Y`
  have hswap : ∫⁻ Y, ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ ∂Pm =
      ∫⁻ y, ∫⁻ Y, Fm y * Gf Y y ^ (2 * q) ∂Pm ∂μ := by
    refine lintegral_lintegral_swap ?_
    exact ((hFmm.comp measurable_snd).mul (hGfm.pow_const (2 * q))).aemeasurable
  have hFmfin : (∫⁻ y, Fm y ∂μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hmid : ∫⁻ Y, (∫⁻ y, Fm y * Gf Y y ∂μ) ^ (2 * q) ∂Pm ≤
      ENNReal.ofReal Cp ^ (2 * q) * ENNReal.ofReal bd := by
    calc ∫⁻ Y, (∫⁻ y, Fm y * Gf Y y ∂μ) ^ (2 * q) ∂Pm
        ≤ ∫⁻ Y, (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ ∂Pm :=
          lintegral_mono hjen
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ Y, ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ ∂Pm :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top hFmfin)
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, ∫⁻ Y, Fm y * Gf Y y ^ (2 * q) ∂Pm ∂μ := by
          rw [hswap]
      _ ≤ (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, Fm y * ENNReal.ofReal bd ∂μ := by
          refine mul_le_mul' le_rfl (lintegral_mono fun y => ?_)
          rw [lintegral_const_mul _ ((hGfY y).pow_const _)]
          exact mul_le_mul' le_rfl (hY y)
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ((∫⁻ y, Fm y ∂μ) * ENNReal.ofReal bd) := by
          rw [lintegral_mul_const _ hFmm]
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q) * ENNReal.ofReal bd := by
          rw [← mul_assoc, ← pow_succ]
          congr 2; omega
      _ ≤ ENNReal.ofReal Cp ^ (2 * q) * ENNReal.ofReal bd := by gcongr
  refine taylorLp_le_of_lintegral_le hp0 _ ?_
  simp_rw [ENNReal.rpow_natCast]
  refine hmid.trans ?_
  rw [← ENNReal.ofReal_pow hCp0, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmx : Cf ≤ max Cf 1 ^ (2 * q) := by
    calc Cf ≤ max Cf 1 := le_max_left _ _
      _ = max Cf 1 ^ 1 := (pow_one _).symm
      _ ≤ max Cf 1 ^ (2 * q) := pow_le_pow_right₀ (le_max_right _ _) (by omega)
  calc Cp ^ (2 * q) * bd = Cp ^ (2 * q) * Real.exp K ^ (2 * q) * (Cf * Θ ^ (2 * q)) := by
        rw [hbd]; ring
    _ ≤ Cp ^ (2 * q) * Real.exp K ^ (2 * q) * (max Cf 1 ^ (2 * q) * Θ ^ (2 * q)) := by
        gcongr
    _ = (Cp * Real.exp K * max Cf 1 * Θ) ^ (2 * q) := by
        rw [mul_pow, mul_pow, mul_pow]; ring


/-- Uniform `taylor_Lp_total`. -/
theorem taylor_Lp_total_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) (q : ℕ) (hq : 1 ≤ q) {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ i : Fin (N - 1), ∀ x : Torus d,
      ∀ φ ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)),
        taylorLp (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ) ((2 * q : ℕ) : ℝ)
          (fun Y => (∫⁻ y, ENNReal.ofReal (φ y) *
              ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i (2 * taylorNu N ^ 5) Y y ^ 2)
                ∂(withDensityReal ρ)) +
            ENNReal.ofReal (β / N) * ∑ j ∈ Finset.univ.erase i,
              taylorT (withDensityReal ρ) φ (taylorG d s c (2 * taylorNu N ^ 5)) (Y j)) ≤
          ENNReal.ofReal (Cb * (taylorNu N ^ 5)⁻¹) := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨CB1, hCB10, hCB1_all⟩ := taylor_B1_bound_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hΛ q hq hK
  obtain ⟨Ct, hCt0, hCt_all⟩ := taylor_tail_bounds_unif hd hcrit c hc c₀ Λ hΛ (6 * q) (by omega)
  have hkb := taylor_kb_one_le q
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  refine ⟨12 * CB1 + (βp * Ct / 2 + βp * taylor_kb q * Real.sqrt (Ct / 2 + 1) + βp * max Ct 1),
    by positivity, fun β hβI ρ hF N hN i x φ hφ => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hCB1 := hCB1_all β hβI ρ hF
  have hCt := hCt_all ρ hF
  set ν : ℝ := taylorNu N with hν
  have hν1 : 1 ≤ ν := one_le_taylorNu N (by omega)
  have hν8 : ν ^ 8 = N := taylorNu_pow8 N
  have hν0 : 0 < ν := by linarith
  set H : ℝ := 2 * ν ^ 5 with hHdef
  have hH : 2 ≤ H := by
    have : 1 ≤ ν ^ 5 := one_le_pow₀ hν1
    rw [hHdef]; linarith
  have hH0 : 0 < H := by linarith
  have hφm : Measurable φ := by
    rcases hφ with rfl | rfl
    · exact measurable_const
    · exact (PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)).comp
        (measurable_const.sub measurable_id)
  set μ : Measure (Torus d) := withDensityReal ρ with hμdef
  set Pm : Measure (Config d (N - 1)) := Measure.pi fun _ : Fin (N - 1) => μ with hPm
  have hGm := measurable_taylorG hd hs0 hsd c H (s := s)
  have hTm : Measurable (taylorT μ φ (taylorG d s c H)) := taylor_measurable_T hφm hGm
  have hp1 : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * q)
  -- the two pieces
  have hB1 := hCB1 N hN H hH i x φ hφ
  have hB1' : taylorLp Pm ((2 * q : ℕ) : ℝ) (fun Y => ∫⁻ y, ENNReal.ofReal (φ y) *
      ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) ∂μ) ≤
      ENNReal.ofReal (CB1 * (12 * (ν ^ 5)⁻¹)) := by
    refine hB1.trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left ?_ hCB10
    have := taylor_theta_le hν1
    rw [hν8] at this
    simpa [hHdef] using this
  obtain ⟨hmass, hL1, hLp⟩ := hCt H hH x φ hφ
  have hB2 := taylor_sum_bound (μ := μ) (Finset.univ.erase i) (taylorT μ φ (taylorG d s c H)) hTm q hq
    (m1 := Ct / H) (CT := Ct) (M := ν ^ 3) (lam := β / N) (by positivity) hL1 hLp
    (by positivity) (by positivity)
  have hB2' : taylorLp Pm ((2 * q : ℕ) : ℝ) (fun Y => ENNReal.ofReal (β / N) * ∑ j ∈ Finset.univ.erase i,
      taylorT μ φ (taylorG d s c H) (Y j)) ≤
      ENNReal.ofReal ((β * Ct / 2 + β * taylor_kb q * Real.sqrt (Ct / 2 + 1) + β * max Ct 1) * (ν ^ 5)⁻¹) := by
    refine hB2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcard : ((Finset.univ.erase i).card : ℝ) ≤ ν ^ 8 := by
      rw [hν8, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      have : N - 1 - 1 ≤ N := by omega
      exact_mod_cast this
    have := taylor_real_est (ν := ν) (β := β) (Ct := Ct) (kb := taylor_kb q)
      (ℓ := ((Finset.univ.erase i).card : ℝ)) hν1 hβ hCt0 (by linarith) (Nat.cast_nonneg _) hcard
    rw [hν8] at this
    simpa [hHdef] using this
  -- Minkowski
  have hB1m : Measurable fun Y : Config d (N - 1) => ∫⁻ y, ENNReal.ofReal (φ y) *
      ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) ∂μ := by
    refine Measurable.lintegral_prod_right' (f := fun p : Config d (N - 1) × Torus d =>
      ENNReal.ofReal (φ p.2) * ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H p.1 p.2 ^ 2)) ?_
    exact (hφm.comp measurable_snd).ennreal_ofReal.mul
      ((measurable_const.mul
        ((taylor_measurable_fieldH hd hcrit β ρ c (N := N) (N - 1) i H).pow_const 2)).ennreal_ofReal)
  have hB2m : Measurable fun Y : Config d (N - 1) => ENNReal.ofReal (β / N) *
      ∑ j ∈ Finset.univ.erase i, taylorT μ φ (taylorG d s c H) (Y j) :=
    (Finset.measurable_sum _ fun j _ => hTm.comp (measurable_pi_apply j)).const_mul _
  refine (taylorLp_add hp1 hB1m.aemeasurable hB2m.aemeasurable).trans ?_
  refine (add_le_add hB1' hB2').trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 : 0 ≤ Ct / 2 + taylor_kb q * Real.sqrt (Ct / 2 + 1) + max Ct 1 := by positivity
  have hmono : β * Ct / 2 + β * taylor_kb q * Real.sqrt (Ct / 2 + 1) + β * max Ct 1 ≤
      βp * Ct / 2 + βp * taylor_kb q * Real.sqrt (Ct / 2 + 1) + βp * max Ct 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hβI.2 h0]
  have hinv : 0 ≤ (ν ^ 5)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hmono hinv]


/-- **Lemma 4.7 (`integrated_taylor_remainder`), uniform form.**  `C` is chosen after
`d, s, c, βm, βp, c₀, Λ` and before `β ∈ [βm, βp]` and `ρ ∈ UFam d c₀ Λ`. -/
theorem integrated_taylor_remainder_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ t' ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      ∀ f ∈ ({fun _ => 1,
          fun y => Real.exp (-(t * (β / N)) * gPlus d s c (x - y)),
          fun y => gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))} :
            Set (Torus d → ℝ)),
        ∫⁻ Y, (∫⁻ y, ENNReal.ofReal (f y * taylorH (cavityField d s c β ρ N i Y y))
              ∂(withDensityReal ρ)) ^ 2 ∂(critPole d s c β ρ N x t') ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(9 / 8 : ℝ))) := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨q, hq2, C0, hC0_all⟩ := product_moment_transfer_unif hd hcrit βm βp hβm hββ c₀ Λ hc₀ c hc
    (1 / 16) (by norm_num)
  obtain ⟨K, hK0, hKl_all⟩ := taylor_field_lower_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hΛ
  obtain ⟨Cb, hCb0, hCb_all⟩ := taylor_Lp_total_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hΛ q (by omega) hK0
  refine ⟨(max C0 0 * Cb) ^ 2, fun β hβI ρ hF N hN x t ht t' ht' i f hf => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hC0 := hC0_all β hβI ρ hρ hF.low hF.up
  have hKl := hKl_all β hβI ρ hF
  have hCb := hCb_all β hβI ρ hF
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set ν : ℝ := taylorNu N with hν
  have hν1 : 1 ≤ ν := one_le_taylorNu N (by omega)
  have hν0 : 0 < ν := by linarith
  set H : ℝ := 2 * ν ^ 5 with hHdef
  have hH : 2 ≤ H := by
    have : 1 ≤ ν ^ 5 := one_le_pow₀ hν1
    rw [hHdef]; linarith
  have hp0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
  set P : Measure (Config d (N - 1)) := critPole d s c β ρ N x t' with hP
  set Pm : Measure (Config d (N - 1)) := Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ with hPm
  -- general claim for a dominating test `φ`
  have key : ∀ φ ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)),
      ∀ g : Torus d → ℝ, (∀ y, g y ≤ φ y) →
      ∫⁻ Y, (∫⁻ y, ENNReal.ofReal (g y * taylorH (cavityField d s c β ρ N i Y y))
              ∂(withDensityReal ρ)) ^ 2 ∂P ≤
        ENNReal.ofReal ((max C0 0 * Cb) ^ 2 * (N : ℝ) ^ (-(9 / 8 : ℝ))) := by
    intro φ hφ g hgφ
    have hφm : Measurable φ := by
      rcases hφ with rfl | rfl
      · exact measurable_const
      · exact (PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)).comp
          (measurable_const.sub measurable_id)
    have hφ0 : ∀ y, 0 ≤ φ y := by
      rcases hφ with rfl | rfl
      · intro y; exact zero_le_one
      · intro y; exact hc _
    set B : (Config d (N - 1)) → ℝ≥0∞ := fun Y => (∫⁻ y, ENNReal.ofReal (φ y) *
        ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) ∂(withDensityReal ρ)) +
        ENNReal.ofReal (β / N) * ∑ j ∈ Finset.univ.erase i,
          taylorT (withDensityReal ρ) φ (taylorG d s c H) (Y j) with hB
    have hBm : Measurable B := by
      refine Measurable.add ?_ ?_
      · refine Measurable.lintegral_prod_right' (f := fun p : Config d (N - 1) × Torus d =>
          ENNReal.ofReal (φ p.2) * ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H p.1 p.2 ^ 2)) ?_
        exact (hφm.comp measurable_snd).ennreal_ofReal.mul
          ((measurable_const.mul
            ((taylor_measurable_fieldH hd hcrit β ρ c (N := N) (N - 1) i H).pow_const 2)).ennreal_ofReal)
      · exact (Finset.measurable_sum _ fun j _ =>
          (taylor_measurable_T hφm (measurable_taylorG hd hs0 hsd c H (s := s))).comp
            (measurable_pi_apply j)).const_mul _
    have hpt : ∀ Y, ∫⁻ y, ENNReal.ofReal (g y * taylorH (cavityField d s c β ρ N i Y y))
        ∂(withDensityReal ρ) ≤ B Y := fun Y =>
      taylor_pointwise hd hcrit β hβ ρ hρ c hc hK0 hKl N H hH i φ g hφm hφ0 hgφ Y
    have hLp := hCb N hN i x φ hφ
    -- the `L^{2q}(Pm)` bound on `B`
    have hb : ∫⁻ a, B a ^ (2 * q) ∂Pm ≤ (ENNReal.ofReal (Cb * (ν ^ 5)⁻¹)) ^ (2 * q) := by
      have h1 := taylorLp_rpow hp0 B (P := Pm)
      have h2 : taylorLp Pm ((2 * q : ℕ) : ℝ) B ≤ ENNReal.ofReal (Cb * (ν ^ 5)⁻¹) := hLp
      have h3 := ENNReal.rpow_le_rpow h2 hp0.le
      rw [h1] at h3
      simp only [ENNReal.rpow_natCast] at h3
      exact h3
    have hwrap := taylor_transfer_wrap P Pm q (by omega) (ENNReal.ofReal (C0 * (N : ℝ) ^ ((1 : ℝ) / 16)))
      (fun Y hY => (hC0 N hN).2 x t' ht' Y hY) B hBm _ hb
    calc ∫⁻ Y, (∫⁻ y, ENNReal.ofReal (g y * taylorH (cavityField d s c β ρ N i Y y))
              ∂(withDensityReal ρ)) ^ 2 ∂P ≤ ∫⁻ Y, B Y ^ 2 ∂P :=
          lintegral_mono fun Y => pow_le_pow_left' (hpt Y) 2
      _ ≤ (ENNReal.ofReal (C0 * (N : ℝ) ^ ((1 : ℝ) / 16)) * ENNReal.ofReal (Cb * (ν ^ 5)⁻¹)) ^ 2 := hwrap
      _ ≤ (ENNReal.ofReal (max C0 0 * (N : ℝ) ^ ((1 : ℝ) / 16)) * ENNReal.ofReal (Cb * (ν ^ 5)⁻¹)) ^ 2 := by
          refine pow_le_pow_left' (mul_le_mul' ?_ le_rfl) 2
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hN0.le _))
      _ = ENNReal.ofReal ((max C0 0 * (N : ℝ) ^ ((1 : ℝ) / 16) * (Cb * (ν ^ 5)⁻¹)) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
      _ = ENNReal.ofReal ((max C0 0 * Cb) ^ 2 * (N : ℝ) ^ (-(9 / 8 : ℝ))) := by
          congr 1
          rw [← taylor_rpow_ids N (by omega)]
          ring
  have hmem1 : (fun _ => (1 : ℝ)) ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)) := by
    simp
  have hmem2 : (fun y => gPlus d s c (x - y)) ∈
      ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)) := by simp
  have hE : ∀ y, Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ≤ 1 := by
    intro y
    rw [Real.exp_le_one_iff]
    have : 0 ≤ t * (β / N) := mul_nonneg ht.1 (by positivity)
    have := hc (x - y)
    have : 0 ≤ gPlus d s c (x - y) := this
    nlinarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl
  · exact key _ hmem1 _ fun y => le_rfl
  · exact key _ hmem1 _ fun y => hE y
  · refine key _ hmem2 _ fun y => ?_
    have h0 : 0 ≤ gPlus d s c (x - y) := hc _
    have := Real.exp_pos (-(t * (β / N)) * gPlus d s c (x - y))
    calc gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
        ≤ gPlus d s c (x - y) * 1 := mul_le_mul_of_nonneg_left (hE y) h0
      _ = _ := mul_one _

end HRS.ME.Unif

end
