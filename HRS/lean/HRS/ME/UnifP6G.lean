import HRS.ME.UnifP6F

/-!
# Uniform Proposition 4.8, part G (packet P6): bounds on `ψ`

Uniform form of `l48_psi_K` (`HRS/Equilibrium/L48Aux5.lean`, `R:eq:double-convolution`): the constants `K`, `A` are
chosen before `β ∈ [βm, βp]` and `ρ ∈ UFam d c₀ Λ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.L48

variable {d : ℕ} {s : ℝ}

/-- Uniform `l48_psi_K`. -/
theorem l48_psi_K_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Measurable (l48_psi d s c β ρ N x t) ∧
      Integrable (l48_psi d s c β ρ N x t) (withDensityReal ρ) ∧
      ∫ y, |l48_psi d s c β ρ N x t y| ∂(withDensityReal ρ) ≤ A ∧
      ∫⁻ z, l48_Phiabs d s c ρ (l48_psi d s c β ρ N x t) z ^ 2 ∂(withDensityReal ρ) ≤
        ENNReal.ofReal K := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hgm := measurable_gPlus hd hs0 hsd c
  obtain ⟨Cg, hCg0, hCg_all⟩ := conv_gPlus_unif_fam hd hs0 hsd c hc c₀ Λ
  obtain ⟨C6, hmain, -⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ
  refine ⟨2 * (Cg * Cg) ^ 2 + 2 * |C6| + 1, 2 * Cg, by positivity, by positivity,
    fun β hβI ρ hF N hN x t ht => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := isProbabilityMeasure_mu hρ
  have hCg := hCg_all ρ hF
  have h6 := (hmain ρ hρ hF.up).2.2.2 β hβ.le

  obtain ⟨hB1, hB2, hF1, hF2⟩ := l48_BF_bounds hd hcrit hβ hρ hc hCg hN x ht
  have hBpos : 0 < l48_B d s c β ρ N x t := lt_of_lt_of_le (Real.exp_pos _) hB1
  have ha0m := l48_meas_a0 hd hcrit hβ hρ hc (β := β) N x t
  have hGm : Measurable fun y => gPlus d s c (x - y) := hgm.comp (measurable_const.sub measurable_id)
  have hf0i := l48_int_a0 hd hcrit hβ hρ hc (ρ := ρ) hN x ht
  have hf1i := l48_int_f1 hd hcrit hβ hρ hc (ρ := ρ) hN x ht
  have ha0p := l48_a0_pos hd hcrit hβ hρ hc (β := β) N x t
  have hG0 : ∀ y, 0 ≤ gPlus d s c (x - y) := fun y => hc _
  set B := l48_B d s c β ρ N x t with hBdef
  set F := l48_F d s c β ρ N x t with hFdef
  set a0 := l48_a0 d s c β N x t with ha0def
  set ψ := l48_psi d s c β ρ N x t with hψdef
  have hψy : ∀ y, ψ y = F * a0 y - B * (gPlus d s c (x - y) * a0 y) := fun y => rfl
  have hψeq : ψ = fun y => F * a0 y - B * (gPlus d s c (x - y) * a0 y) := funext hψy
  have hψm : Measurable ψ := by
    rw [hψeq]; exact (ha0m.const_mul _).sub ((hGm.mul ha0m).const_mul _)
  have hψi : Integrable ψ (withDensityReal ρ) := by
    rw [hψeq]; exact (hf0i.const_mul _).sub (hf1i.const_mul _)
  have hψabs : ∀ y, |ψ y| ≤ F * a0 y + B * (gPlus d s c (x - y) * a0 y) := fun y => by
    rw [hψy]
    have h1 : 0 ≤ F * a0 y := mul_nonneg hF1 (ha0p y).le
    have h2 : 0 ≤ B * (gPlus d s c (x - y) * a0 y) :=
      mul_nonneg hBpos.le (mul_nonneg (hG0 y) (ha0p y).le)
    rw [abs_le]; constructor <;> linarith
  refine ⟨hψm, hψi, ?_, ?_⟩
  · -- `‖ψ‖₁ ≤ 2 F B ≤ 2 Cg`
    calc ∫ y, |ψ y| ∂(withDensityReal ρ)
        ≤ ∫ y, (F * a0 y + B * (gPlus d s c (x - y) * a0 y)) ∂(withDensityReal ρ) :=
          integral_mono hψi.abs ((hf0i.const_mul _).add (hf1i.const_mul _)) hψabs
      _ = F * B + B * F := by
          rw [integral_add (hf0i.const_mul _) (hf1i.const_mul _), integral_const_mul,
            integral_const_mul]
          rfl
      _ ≤ 2 * Cg := by nlinarith [mul_le_mul hF2 hB2 (by linarith) hCg0]
  · -- the `L²` bound
    have hP1 : ∀ z, Measurable fun y => ENNReal.ofReal (a0 y * gPlus d s c (y - z)) := fun z =>
      ENNReal.measurable_ofReal.comp (ha0m.mul (hgm.comp (measurable_id.sub measurable_const)))
    have hP2 : ∀ z, Measurable fun y =>
        ENNReal.ofReal ((gPlus d s c (x - y) * a0 y) * gPlus d s c (y - z)) := fun z =>
      ENNReal.measurable_ofReal.comp ((hGm.mul ha0m).mul (hgm.comp (measurable_id.sub measurable_const)))
    have hΦ : ∀ z, l48_Phiabs d s c ρ ψ z ≤
        ENNReal.ofReal (Cg * Cg) +
          ∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) *
            gPlus d s c (y - z)) ∂(withDensityReal ρ) := by
      intro z
      have hp0 : ∀ y, 0 ≤ gPlus d s c (y - z) := fun y => hc _
      unfold l48_Phiabs
      have step1 : ∫⁻ y, ENNReal.ofReal (|ψ y| * gPlus d s c (y - z)) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal F * ∫⁻ y, ENNReal.ofReal (a0 y * gPlus d s c (y - z)) ∂(withDensityReal ρ) +
            ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * a0 y) * gPlus d s c (y - z))
              ∂(withDensityReal ρ) := by
        rw [← lintegral_const_mul _ (hP1 z), ← lintegral_const_mul _ (hP2 z),
          ← lintegral_add_left ((hP1 z).const_mul _)]
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul hF1, ← ENNReal.ofReal_mul hBpos.le,
          ← ENNReal.ofReal_add (mul_nonneg hF1 (mul_nonneg (ha0p y).le (hp0 y)))
            (mul_nonneg hBpos.le (mul_nonneg (mul_nonneg (hG0 y) (ha0p y).le) (hp0 y)))]
        refine ENNReal.ofReal_le_ofReal ?_
        calc |ψ y| * gPlus d s c (y - z)
            ≤ (F * a0 y + B * (gPlus d s c (x - y) * a0 y)) * gPlus d s c (y - z) :=
              mul_le_mul_of_nonneg_right (hψabs y) (hp0 y)
          _ = _ := by ring
      have step2 : ∫⁻ y, ENNReal.ofReal (a0 y * gPlus d s c (y - z)) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal Cg := by
        obtain ⟨hGi, hGe⟩ := G_shift_int hd hcrit hβ hρ hc z
        calc ∫⁻ y, ENNReal.ofReal (a0 y * gPlus d s c (y - z)) ∂(withDensityReal ρ)
            ≤ ∫⁻ y, ENNReal.ofReal (gPlus d s c (y - z)) ∂(withDensityReal ρ) := by
              refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
              calc a0 y * gPlus d s c (y - z) ≤ 1 * gPlus d s c (y - z) :=
                    mul_le_mul_of_nonneg_right (l48_a0_le_one hd hcrit hβ hρ hc hN x ht y) (hp0 y)
                _ = _ := one_mul _
          _ = ENNReal.ofReal (∫ y, gPlus d s c (y - z) ∂(withDensityReal ρ)) :=
              (ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hp0)).symm
          _ = ENNReal.ofReal (convMeasure (gPlus d s c) (withDensityReal ρ) z) := by rw [hGe]
          _ ≤ ENNReal.ofReal Cg := ENNReal.ofReal_le_ofReal (hCg z).2
      refine step1.trans (add_le_add ?_ ?_)
      · calc ENNReal.ofReal F * ∫⁻ y, ENNReal.ofReal (a0 y * gPlus d s c (y - z)) ∂(withDensityReal ρ)
            ≤ ENNReal.ofReal Cg * ENNReal.ofReal Cg :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hF2) step2
          _ = ENNReal.ofReal (Cg * Cg) := (ENNReal.ofReal_mul hCg0).symm
      · calc ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * a0 y) * gPlus d s c (y - z))
              ∂(withDensityReal ρ)
            ≤ 1 * ∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * a0 y) * gPlus d s c (y - z))
              ∂(withDensityReal ρ) := by
              refine mul_le_mul' ?_ le_rfl
              rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hB2
          _ = _ := one_mul _
    have hC6 := h6 N hN x t ht
    calc ∫⁻ z, l48_Phiabs d s c ρ ψ z ^ 2 ∂(withDensityReal ρ)
        ≤ ∫⁻ z, 2 * (ENNReal.ofReal (Cg * Cg) ^ 2 +
            (∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) *
              gPlus d s c (y - z)) ∂(withDensityReal ρ)) ^ 2) ∂(withDensityReal ρ) := by
          refine lintegral_mono fun z => ?_
          exact (pow_le_pow_left' (hΦ z) 2).trans (l48_add_sq_le _ _)
      _ = 2 * (ENNReal.ofReal (Cg * Cg) ^ 2 +
            ∫⁻ z, (∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) *
              gPlus d s c (y - z)) ∂(withDensityReal ρ)) ^ 2 ∂(withDensityReal ρ)) := by
          have hmeas : Measurable fun z => (∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) *
              Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) * gPlus d s c (y - z))
              ∂(withDensityReal ρ)) ^ 2 := by
            have h : Measurable fun q : Torus d × Torus d => ENNReal.ofReal
                ((gPlus d s c (x - q.2) * Real.exp (-(t * (β / N)) * gPlus d s c (x - q.2))) *
                  gPlus d s c (q.2 - q.1)) :=
              ENNReal.measurable_ofReal.comp (((hgm.comp (measurable_const.sub measurable_snd)).mul
                (Real.measurable_exp.comp ((measurable_const.mul
                  (hgm.comp (measurable_const.sub measurable_snd)))))).mul
                (hgm.comp (measurable_snd.sub measurable_fst)))
            exact (h.lintegral_prod_right' (ν := withDensityReal ρ)).pow_const 2
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left (by measurability)]
          simp
      _ ≤ 2 * (ENNReal.ofReal ((Cg * Cg) ^ 2) + ENNReal.ofReal |C6|) := by
          refine mul_le_mul' le_rfl (add_le_add (le_of_eq ?_) (hC6.trans (ENNReal.ofReal_le_ofReal (le_abs_self _))))
          rw [ENNReal.ofReal_pow (mul_nonneg hCg0 hCg0)]
      _ = ENNReal.ofReal (2 * ((Cg * Cg) ^ 2 + |C6|)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
          simp
      _ ≤ ENNReal.ofReal (2 * (Cg * Cg) ^ 2 + 2 * |C6| + 1) :=
          ENNReal.ofReal_le_ofReal (by linarith)

set_option maxHeartbeats 3200000 in
/-- Uniform `l48_T_L2` (step 5 of the chain of Proposition 4.8): `‖T₁ - F_t/B_t‖_{L²(P)} ≤ C N^{-1/2}`. -/
theorem l48_T_L2_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ) (hCR : CavRespUnif d s c βm βp c₀ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      eLpNorm (fun Y : Config d (N - 1) => l48_T d s c β ρ N x t i Y -
          l48_F d s c β ρ N x t / l48_B d s c β ρ N x t) 2 (critPole d s c β ρ N x t) ≤
        ENNReal.ofReal (C / Real.sqrt N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cg, hCg0, hCg_all⟩ := conv_gPlus_unif_fam hd hs0 hsd c hc c₀ Λ
  obtain ⟨K, A, hK0, hA0, hψ_all⟩ := l48_psi_K_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hΛ
  obtain ⟨Clin, hClin0, hlin_all⟩ := l48_linear_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hΛ hCR
  obtain ⟨C47, h47_all⟩ := integrated_taylor_remainder_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hc₀ hΛ
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  set Q' : ℝ := 1 / (Real.exp (-(βp * Cg)) * Real.exp (-(3 * (βp * Cg)))) with hQ'
  have hQ'0 : 0 < Q' := by positivity
  set b0 : ℝ := Real.sqrt |C47| with hb0
  refine ⟨Q' * (Clin * (Real.sqrt K + A) + Cg * b0 + b0), by positivity,
    fun β hβI ρ hF N hN x t ht i => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := isProbabilityMeasure_mu hρ
  have hCg := hCg_all ρ hF
  have hψ := hψ_all β hβI ρ hF
  have hlin := hlin_all β hβI ρ hF
  have h47 := h47_all β hβI ρ hF
  set Q : ℝ := 1 / (Real.exp (-(β * Cg)) * Real.exp (-(3 * (β * Cg)))) with hQ
  have hQ0 : 0 < Q := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hr1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast (by omega : 1 ≤ N))
  have hlam : 0 ≤ β / N := by positivity
  have hPprob : IsProbabilityMeasure (critPole d s c β ρ N x t) := by
    rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
    exact pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  obtain ⟨hψm, hψi, hψA, hψK⟩ := hψ N hN x t ht
  have hℓ := hlin N hN x t ht i _ hψm hψi A K hK0 hA0 hψA hψK
  obtain ⟨hB1, hB2, hF1, hF2⟩ := l48_BF_bounds hd hcrit hβ hρ hc hCg hN x ht
  have hBpos : 0 < l48_B d s c β ρ N x t := lt_of_lt_of_le (Real.exp_pos _) hB1
  -- the Taylor remainders
  have h47a := h47 N hN x t ht t ht i (fun y => Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) (by simp)
  have h47b := h47 N hN x t ht t ht i
    (fun y => gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) (by simp)
  set R0 : Config d (N - 1) → ℝ≥0∞ := fun Y =>
    ∫⁻ y, ENNReal.ofReal (l48_a0 d s c β N x t y * taylorH (cavityField d s c β ρ N i Y y))
      ∂(withDensityReal ρ) with hR0
  set R1 : Config d (N - 1) → ℝ≥0∞ := fun Y =>
    ∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * l48_a0 d s c β N x t y) *
      taylorH (cavityField d s c β ρ N i Y y)) ∂(withDensityReal ρ) with hR1
  have hgm := measurable_gPlus hd hs0 hsd c
  have hjoint := measurable_field_joint' hd hcrit hβ hρ hc (s := s) (c := c) (β := β) (ρ := ρ) N i
  have hTm : Measurable fun v : ℝ => taylorH v := by
    unfold taylorH; exact ((Real.measurable_exp.comp measurable_neg).sub measurable_const).add measurable_id
  have ha0m := l48_meas_a0 hd hcrit hβ hρ hc (β := β) N x t
  have hGm : Measurable fun y => gPlus d s c (x - y) := hgm.comp (measurable_const.sub measurable_id)
  have hR0m : Measurable R0 := by
    have h : Measurable fun q : Config d (N - 1) × Torus d =>
        ENNReal.ofReal (l48_a0 d s c β N x t q.2 * taylorH (cavityField d s c β ρ N i q.1 q.2)) :=
      ENNReal.measurable_ofReal.comp ((ha0m.comp measurable_snd).mul (hTm.comp hjoint))
    exact h.lintegral_prod_right' (ν := withDensityReal ρ)
  have hR1m : Measurable R1 := by
    have h : Measurable fun q : Config d (N - 1) × Torus d =>
        ENNReal.ofReal ((gPlus d s c (x - q.2) * l48_a0 d s c β N x t q.2) *
          taylorH (cavityField d s c β ρ N i q.1 q.2)) :=
      ENNReal.measurable_ofReal.comp (((hGm.comp measurable_snd).mul (ha0m.comp measurable_snd)).mul
        (hTm.comp hjoint))
    exact h.lintegral_prod_right' (ν := withDensityReal ρ)
  have hR0sq : ∫⁻ Y, R0 Y ^ 2 ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C47 * (N : ℝ) ^ (-(9 / 8 : ℝ))) :=
    h47a
  have hR1sq : ∫⁻ Y, R1 Y ^ 2 ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C47 * (N : ℝ) ^ (-(9 / 8 : ℝ))) :=
    h47b
  have hfin : ∀ (R : Config d (N - 1) → ℝ≥0∞), Measurable R →
      ∫⁻ Y, R Y ^ 2 ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C47 * (N : ℝ) ^ (-(9 / 8 : ℝ))) →
      ∀ᵐ Y ∂(critPole d s c β ρ N x t), R Y < ⊤ := by
    intro R hRm hRsq
    have h2 : ∀ᵐ Y ∂(critPole d s c β ρ N x t), R Y ^ 2 < ⊤ :=
      ae_lt_top (hRm.pow_const 2) (lt_of_le_of_lt hRsq ENNReal.ofReal_lt_top).ne
    filter_upwards [h2] with Y hY
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h] at hY
    simp at hY
  have hae0 := hfin R0 hR0m hR0sq
  have hae1 := hfin R1 hR1m hR1sq
  -- the `L²` norms of the remainders
  have hrem : ∀ (R : Config d (N - 1) → ℝ≥0∞), Measurable R →
      ∫⁻ Y, R Y ^ 2 ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C47 * (N : ℝ) ^ (-(9 / 8 : ℝ))) →
      eLpNorm (fun Y => (R Y).toReal) 2 (critPole d s c β ρ N x t) ≤ ENNReal.ofReal (b0 / Real.sqrt N) := by
    intro R hRm hRsq
    refine (l48_eLpNorm_le_iff (hRm.ennreal_toReal) (by positivity)).2 ?_
    calc ∫⁻ Y, ENNReal.ofReal ((R Y).toReal ^ 2) ∂(critPole d s c β ρ N x t)
        ≤ ∫⁻ Y, R Y ^ 2 ∂(critPole d s c β ρ N x t) := by
          refine lintegral_mono fun Y => ?_
          rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
          exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2
      _ ≤ ENNReal.ofReal (C47 * (N : ℝ) ^ (-(9 / 8 : ℝ))) := hRsq
      _ ≤ ENNReal.ofReal ((b0 / Real.sqrt N) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_pow, hb0, Real.sq_sqrt (abs_nonneg _), Real.sq_sqrt hN0.le]
          have h1 : (N : ℝ) ^ (-(9 / 8 : ℝ)) ≤ (N : ℝ)⁻¹ := by
            rw [← Real.rpow_neg_one]
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
          calc C47 * (N : ℝ) ^ (-(9 / 8 : ℝ)) ≤ |C47| * (N : ℝ) ^ (-(9 / 8 : ℝ)) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hN0.le _)
            _ ≤ |C47| * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
            _ = |C47| / N := by rw [div_eq_mul_inv]
  have hr0' := hrem R0 hR0m hR0sq
  have hr1' := hrem R1 hR1m hR1sq
  -- pointwise bound
  have hpt : ∀ᵐ Y ∂(critPole d s c β ρ N x t),
      ‖l48_T d s c β ρ N x t i Y - l48_F d s c β ρ N x t / l48_B d s c β ρ N x t‖ ≤
        ‖Q * (|∫ y, l48_psi d s c β ρ N x t y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)| +
          Cg * (R0 Y).toReal + (R1 Y).toReal)‖ := by
    filter_upwards [hae0, hae1] with Y h0 h1
    have hq := l48_quotient hd hcrit hβ hρ hc hCg hN x ht i Y h0 h1
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hr0pos : 0 ≤ (R0 Y).toReal := ENNReal.toReal_nonneg
    have hr1pos : 0 ≤ (R1 Y).toReal := ENNReal.toReal_nonneg
    have hnn : 0 ≤ Q * (|∫ y, l48_psi d s c β ρ N x t y * cavityField d s c β ρ N i Y y
        ∂(withDensityReal ρ)| + Cg * (R0 Y).toReal + (R1 Y).toReal) := by positivity
    rw [abs_of_nonneg hnn]
    refine hq.trans ?_
    set L := |∫ y, l48_psi d s c β ρ N x t y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)|
      with hL
    have hL0 : 0 ≤ L := abs_nonneg _
    have hnum : L + l48_F d s c β ρ N x t * (R0 Y).toReal + l48_B d s c β ρ N x t * (R1 Y).toReal ≤
        L + Cg * (R0 Y).toReal + (R1 Y).toReal := by
      have e1 : l48_F d s c β ρ N x t * (R0 Y).toReal ≤ Cg * (R0 Y).toReal :=
        mul_le_mul_of_nonneg_right hF2 hr0pos
      have e2 : l48_B d s c β ρ N x t * (R1 Y).toReal ≤ 1 * (R1 Y).toReal :=
        mul_le_mul_of_nonneg_right hB2 hr1pos
      linarith
    have hnn' : 0 ≤ L + l48_F d s c β ρ N x t * (R0 Y).toReal + l48_B d s c β ρ N x t * (R1 Y).toReal := by
      positivity
    calc _ ≤ (L + Cg * (R0 Y).toReal + (R1 Y).toReal) /
          (l48_B d s c β ρ N x t * Real.exp (-(3 * (β * Cg)))) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (L + Cg * (R0 Y).toReal + (R1 Y).toReal) /
          (Real.exp (-(β * Cg)) * Real.exp (-(3 * (β * Cg)))) := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          exact mul_le_mul_of_nonneg_right hB1 (Real.exp_pos _).le
      _ = Q * (L + Cg * (R0 Y).toReal + (R1 Y).toReal) := by rw [hQ]; ring
  have hTmeas := l48_meas_T hd hcrit hβ hρ hc (N := N) x t i
  refine (eLpNorm_mono_ae (hTmeas.sub measurable_const).aestronglyMeasurable hpt).trans ?_
  have hsplit : (fun Y : Config d (N - 1) => Q * (|∫ y, l48_psi d s c β ρ N x t y *
        cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)| + Cg * (R0 Y).toReal + (R1 Y).toReal)) =
      Q • (((fun Y => |∫ y, l48_psi d s c β ρ N x t y * cavityField d s c β ρ N i Y y
          ∂(withDensityReal ρ)|) + Cg • (fun Y => (R0 Y).toReal)) + (fun Y => (R1 Y).toReal)) := by
    funext Y; simp [smul_eq_mul]
  rw [hsplit]
  refine eLpNorm_const_smul_le.trans ?_
  have hlabs : eLpNorm (fun Y : Config d (N - 1) => |∫ y, l48_psi d s c β ρ N x t y *
      cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)|) 2 (critPole d s c β ρ N x t) ≤
      ENNReal.ofReal (Clin * (Real.sqrt K + A) / Real.sqrt N) := by
    refine le_trans (le_of_eq ?_) hℓ
    exact eLpNorm_congr_norm_ae (l48_meas_ell hd hcrit hβ hρ hc hψm i).abs.aestronglyMeasurable
      (l48_meas_ell hd hcrit hβ hρ hc hψm i).aestronglyMeasurable
      (Eventually.of_forall fun Y => by simp)
  have hcr0 : eLpNorm (Cg • fun Y : Config d (N - 1) => (R0 Y).toReal) 2 (critPole d s c β ρ N x t) ≤
      ENNReal.ofReal Cg * ENNReal.ofReal (b0 / Real.sqrt N) := by
    refine eLpNorm_const_smul_le.trans ?_
    rw [Real.enorm_eq_ofReal hCg0]
    exact mul_le_mul' le_rfl hr0'
  have hsum := (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) (f := (fun Y : Config d (N - 1) => |∫ y,
      l48_psi d s c β ρ N x t y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)|) +
        Cg • (fun Y : Config d (N - 1) => (R0 Y).toReal)) (g := fun Y => (R1 Y).toReal)
      (μ := critPole d s c β ρ N x t))
  have hsum2 := (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) (f := fun Y : Config d (N - 1) => |∫ y,
      l48_psi d s c β ρ N x t y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)|)
      (g := Cg • (fun Y : Config d (N - 1) => (R0 Y).toReal)) (μ := critPole d s c β ρ N x t))
  rw [Real.enorm_eq_ofReal hQ0.le]
  have hbl : 0 ≤ Clin * (Real.sqrt K + A) / Real.sqrt N := by positivity
  have hbb : 0 ≤ b0 / Real.sqrt N := by positivity
  calc ENNReal.ofReal Q * eLpNorm (((fun Y : Config d (N - 1) => |∫ y, l48_psi d s c β ρ N x t y *
          cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)|) + Cg • (fun Y => (R0 Y).toReal)) +
          (fun Y => (R1 Y).toReal)) 2 (critPole d s c β ρ N x t)
      ≤ ENNReal.ofReal Q * (ENNReal.ofReal (Clin * (Real.sqrt K + A) / Real.sqrt N) +
          ENNReal.ofReal Cg * ENNReal.ofReal (b0 / Real.sqrt N) + ENNReal.ofReal (b0 / Real.sqrt N)) :=
        mul_le_mul' le_rfl (hsum.trans (add_le_add (hsum2.trans (add_le_add hlabs hcr0)) hr1'))
    _ = ENNReal.ofReal (Q * (Clin * (Real.sqrt K + A) / Real.sqrt N + Cg * (b0 / Real.sqrt N) +
          b0 / Real.sqrt N)) := by
        rw [← ENNReal.ofReal_mul hCg0, ← ENNReal.ofReal_add hbl (mul_nonneg hCg0 hbb),
          ← ENNReal.ofReal_add (by positivity) hbb, ← ENNReal.ofReal_mul hQ0.le]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hexp : Real.exp (-(βp * Cg)) * Real.exp (-(3 * (βp * Cg))) ≤
            Real.exp (-(β * Cg)) * Real.exp (-(3 * (β * Cg))) := by
          refine mul_le_mul (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
            (Real.exp_pos _).le
          · nlinarith [mul_le_mul_of_nonneg_right hβI.2 hCg0]
          · nlinarith [mul_le_mul_of_nonneg_right hβI.2 hCg0]
        have hQQ : Q ≤ Q' := by
          rw [hQ, hQ']
          exact one_div_le_one_div_of_le (by positivity) hexp
        have hE : Q * (Clin * (Real.sqrt K + A) / Real.sqrt N + Cg * (b0 / Real.sqrt N) +
            b0 / Real.sqrt N) = Q * (Clin * (Real.sqrt K + A) + Cg * b0 + b0) / Real.sqrt N := by
          field_simp
        rw [hE]
        refine div_le_div_of_nonneg_right ?_ hr0.le
        exact mul_le_mul_of_nonneg_right hQQ (by positivity)

end HRS.ME.Unif

end
