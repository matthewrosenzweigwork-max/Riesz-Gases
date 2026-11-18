import HRS.MS.FldRemCen2

/-!
# S5.3 (`field_remainder_centered`), part 3: second moments along the stationary process and the Duhamel formula for `ℓ`

* `s53_second_moment`: `N E|D f(X_r) - ℓ f|² ≤ C_A δ_N (sup‖D²f‖)²` for `r ∈ [0,T]` (stationarity);
* `s53_L1_bound`: `E|D f(X_r)| ≤ 1 + C_A⁺ δ L² + C_m L` for `cbNorm 2 f ≤ L`;
* `s53_mean_ftc`: `ℓ(G τ) = ℓ(G 0) + ∫_0^τ ℓ(G' σ) dσ` (Fubini; the pathwise Duhamel formula `s53_ftc` integrated).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole

variable {d N : ℕ} {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X' : ℝ≥0 → Ω → EucConfig d N} {T CA δ : ℝ}

lemma s53_second_moment [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (H : S53Var s ρ P X' T CA δ)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {f : Euc d → ℝ} (hf : MemCb 2 f) :
    (N : ℝ≥0∞) * ∫⁻ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (CA * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2) := by
  have hm : Measurable fun Y : EucConfig d N => ‖s53_Dk s ρ f Y - s53_ell s ρ P X' f‖ₑ ^ 2 :=
    ((s53_Dk_meas_config ctx.hρ (hf.1.of_le (by norm_num))).sub_const _).enorm.pow_const 2
  rw [s53_stat_lintegral H hr hm]
  exact H.var f hf

lemma s53_L1_bound [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) (hδ : 0 ≤ δ)
    (H : S53Var s ρ P X' T CA δ) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : ∀ f : Euc d → ℝ, MemCb 2 f → |s53_ell s ρ P X' f| ≤ Cm * cbNorm 2 f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {f : Euc d → ℝ} (hf : MemCb 2 f) {L : ℝ}
    (hL : cbNorm 2 f ≤ L) :
    ∫⁻ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ)‖ₑ ∂P ≤
      1 + ENNReal.ofReal (max CA 0 * δ * L ^ 2) + ENNReal.ofReal (Cm * L) := by
  have hmY : Measurable fun Y : EucConfig d N => s53_Dk s ρ f Y :=
    s53_Dk_meas_config ctx.hρ (hf.1.of_le (by norm_num))
  have hmr : Measurable fun ζ => s53_Dk s ρ f (X' (Real.toNNReal r) ζ) := hmY.comp (H.meas _)
  have h1 : ∀ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ)‖ₑ ≤
      ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f‖ₑ + ‖s53_ell s ρ P X' f‖ₑ := fun ζ => by
    have := enorm_add_le (s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f) (s53_ell s ρ P X' f)
    simpa using this
  have h2 : ∫⁻ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f‖ₑ ∂P ≤
      1 + ENNReal.ofReal (max CA 0 * δ * L ^ 2) := by
    have hmd : Measurable fun ζ => ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f‖ₑ :=
      (hmr.sub_const _).enorm
    have h3 : ∫⁻ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f‖ₑ ∂P ≤
        ∫⁻ ζ, (1 + ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f‖ₑ ^ 2) ∂P :=
      lintegral_mono fun ζ => s53_enorm_le_one_add_sq _
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one] at h3
    refine h3.trans (add_le_add le_rfl ?_)
    have hN1 : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
    refine le_trans (le_mul_of_one_le_left' hN1) ((s53_second_moment ctx H hr hf).trans
      (ENNReal.ofReal_le_ofReal ?_))
    have hp : (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ≤ L := (s53_p_le_cb hf).trans hL
    have hp0 := s53_cbSup_nonneg f
    have hp2 : (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hp0 hp 2
    have h0 : 0 ≤ max CA 0 * δ := mul_nonneg (le_max_right _ _) hδ
    calc CA * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2 ≤
          max CA 0 * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2 := by
          gcongr; exact le_max_left _ _
      _ ≤ max CA 0 * δ * L ^ 2 := by gcongr
  have h4 : ‖s53_ell s ρ P X' f‖ₑ ≤ ENNReal.ofReal (Cm * L) := by
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal ((hCm f hf).trans (mul_le_mul_of_nonneg_left hL hCm0))
  calc ∫⁻ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ)‖ₑ ∂P ≤
        ∫⁻ ζ, (‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f‖ₑ +
          ENNReal.ofReal (Cm * L)) ∂P :=
        lintegral_mono fun ζ => (h1 ζ).trans (add_le_add le_rfl h4)
    _ = ∫⁻ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f‖ₑ ∂P +
          ENNReal.ofReal (Cm * L) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
        rw [add_assoc]
        exact add_le_add h2 le_rfl |>.trans (le_of_eq (by ring))


lemma s53_mean_ftc [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (H : S53Var s ρ P X' T CA δ) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : ∀ f : Euc d → ℝ, MemCb 2 f → |s53_ell s ρ P X' f| ≤ Cm * cbNorm 2 f)
    {G G' : ℝ → Euc d → ℝ} (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ))
    (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ)) (hdiff : S53Diff T G G') (hc' : S53Cont T G')
    {L : ℝ} (hL : ∀ σ ∈ Set.Icc (0 : ℝ) T, cbNorm 2 (G' σ) ≤ L) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    s53_ell s ρ P X' (G τ) = s53_ell s ρ P X' (G 0) +
      ∫ σ in Set.Ioc 0 τ, s53_ell s ρ P X' (G' σ) := by
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hG1m := s53_grad_measurable hT hG' hc'
  have m1 : Measurable fun p : ℝ × EucConfig d N => s53_Dk s ρ (G' (s53_clamp T p.1)) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun τ => G' (s53_clamp T τ)) hG1m
  have hjm : Measurable fun q : Ω × ℝ => s53_Dk s ρ (G' (s53_clamp T q.2)) (X' 0 q.1) := by
    have hpr : Measurable fun q : Ω × ℝ => (q.2, X' 0 q.1) := measurable_snd.prodMk ((H.meas 0).comp measurable_fst)
    have := m1.comp hpr
    exact this
  -- pathwise Duhamel formula
  have hpath : ∀ ζ, s53_Dk s ρ (G τ) (X' 0 ζ) = s53_Dk s ρ (G 0) (X' 0 ζ) +
      ∫ σ in Set.Ioc 0 τ, s53_Dk s ρ (G' (s53_clamp T σ)) (X' 0 ζ) := fun ζ => by
    rw [s53_ftc ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN hG hG' hdiff hc' (X' 0 ζ) hτ]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
    simp only [s53_clamp_of_mem (⟨hσ.1.le, hσ.2.trans hτ.2⟩ : σ ∈ Set.Icc (0 : ℝ) T)]
  have hI0 : Integrable (fun ζ => s53_Dk s ρ (G 0) (X' 0 ζ)) P :=
    (s53_memLp ctx.hρ hN H (hG 0 h0T)).integrable one_le_two
  have hIτ : Integrable (fun ζ => s53_Dk s ρ (G τ) (X' 0 ζ)) P :=
    (s53_memLp ctx.hρ hN H (hG τ hτ)).integrable one_le_two
  have hIB : Integrable (fun ζ => ∫ σ in Set.Ioc 0 τ, s53_Dk s ρ (G' (s53_clamp T σ)) (X' 0 ζ)) P := by
    refine (hIτ.sub hI0).congr (Filter.Eventually.of_forall fun ζ => ?_)
    show _ = _
    simp only [Pi.sub_apply]
    rw [hpath ζ]; ring
  -- Fubini
  have hint : Integrable (Function.uncurry fun ζ σ => s53_Dk s ρ (G' (s53_clamp T σ)) (X' 0 ζ))
      (P.prod (volume.restrict (Set.Ioc 0 τ))) := by
    refine ⟨hjm.aestronglyMeasurable, ?_⟩
    show ∫⁻ z, ‖s53_Dk s ρ (G' (s53_clamp T z.2)) (X' 0 z.1)‖ₑ ∂(P.prod (volume.restrict (Set.Ioc 0 τ))) < ⊤
    rw [lintegral_prod _ hjm.enorm.aemeasurable,
      lintegral_lintegral_swap (f := fun ζ σ => ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' 0 ζ)‖ₑ) hjm.enorm.aemeasurable]
    have hb : ∀ σ ∈ Set.Ioc (0 : ℝ) τ, ∫⁻ ζ, ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' 0 ζ)‖ₑ ∂P ≤
        1 + ENNReal.ofReal (max CA 0 * δ * L ^ 2) + ENNReal.ofReal (Cm * L) := fun σ hσ => by
      have hσT : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσ.1.le, hσ.2.trans hτ.2⟩
      rw [s53_clamp_of_mem hσT]
      have := s53_L1_bound ctx hN hδ H hCm0 hCm h0T (hG' σ hσT) (hL σ hσT)
      simpa using this
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc hb |>.trans (le_of_eq (setLIntegral_const _ _))) ?_
    refine ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩,
      ENNReal.ofReal_lt_top⟩) ?_
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hswap := integral_integral_swap (μ := P) (ν := volume.restrict (Set.Ioc 0 τ))
    (f := fun ζ σ => s53_Dk s ρ (G' (s53_clamp T σ)) (X' 0 ζ)) hint
  have hell : s53_ell s ρ P X' (G τ) = ∫ ζ, (s53_Dk s ρ (G 0) (X' 0 ζ) +
      ∫ σ in Set.Ioc 0 τ, s53_Dk s ρ (G' (s53_clamp T σ)) (X' 0 ζ)) ∂P := by
    unfold s53_ell
    exact integral_congr_ae (Filter.Eventually.of_forall hpath)
  rw [hell, integral_add hI0 hIB, hswap]
  unfold s53_ell
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
  simp only [s53_clamp_of_mem (⟨hσ.1.le, hσ.2.trans hτ.2⟩ : σ ∈ Set.Icc (0 : ℝ) T)]

end HRS.MS.S53
