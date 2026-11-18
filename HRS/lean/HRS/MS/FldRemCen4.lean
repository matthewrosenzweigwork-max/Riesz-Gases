import HRS.MS.FldRemCen3

/-!
# S5.3 (`field_remainder_centered`), part 4: one Hermite coordinate, centered

The centered dominating function `Hc(Y) = |D(G_0)(Y) - ℓ G_0| + ∫_0^T |D(G_1(σ))(Y) - ℓ G_1(σ)| dσ` of a configuration,
its measurability, the pathwise bound `|F(t,r) - E F(t,r)| ≤ Hc(X_r)` (pathwise Duhamel formula `s53_ftc` for `D` and
`s53_mean_ftc` for `ℓ`), and the second moment of `g = ∫_0^T Hc(X_r) dr` (Cauchy–Schwarz in `r` and `σ`).
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

/-- The centered dominating function. -/
def s53_Hc (s : ℝ) (ρ : Euc d → ℝ) (T : ℝ) (G G' : ℝ → Euc d → ℝ) (ℓ0 : ℝ) (ℓ1 : ℝ → ℝ)
    (Y : EucConfig d N) : ℝ≥0∞ :=
  ‖s53_Dk s ρ (G 0) Y - ℓ0‖ₑ +
    ∫⁻ σ in Set.Icc (0 : ℝ) T, ‖s53_Dk s ρ (G' (s53_clamp T σ)) Y - ℓ1 σ‖ₑ

lemma s53_Hc_measurable (ctx : S53Ctx s ρ Mρ) (T : ℝ) {G G' : ℝ → Euc d → ℝ} {ℓ0 : ℝ} {ℓ1 : ℝ → ℝ}
    (hG0 : Measurable fun x : Euc d => gradient (G 0) x)
    (hG1 : Measurable fun p : ℝ × Euc d => gradient (G' (s53_clamp T p.1)) p.2) (hℓ1 : Measurable ℓ1) :
    Measurable (s53_Hc (N := N) s ρ T G G' ℓ0 ℓ1) := by
  have m1 : Measurable fun p : ℝ × EucConfig d N =>
      s53_Dk s ρ ((fun τ : ℝ => G' (s53_clamp T τ)) p.1) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun τ => G' (s53_clamp T τ)) hG1
  have m0 : Measurable fun p : ℝ × EucConfig d N => s53_Dk s ρ ((fun _ : ℝ => G 0) p.1) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun _ => G 0) (hG0.comp measurable_snd)
  have h0 : Measurable fun Y : EucConfig d N => ‖s53_Dk s ρ (G 0) Y - ℓ0‖ₑ := by
    have hpr : Measurable fun Y : EucConfig d N => ((0 : ℝ), Y) :=
      measurable_const.prodMk measurable_id
    exact ((m0.comp hpr).sub_const _).enorm
  have h1 : Measurable fun q : EucConfig d N × ℝ =>
      ‖s53_Dk s ρ (G' (s53_clamp T q.2)) q.1 - ℓ1 q.2‖ₑ :=
    ((m1.comp measurable_swap).sub (hℓ1.comp measurable_snd)).enorm
  exact h0.add (h1.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T)))

/-- the mean `σ ↦ ℓ (G' (clamp σ))` is measurable -/
lemma s53_ell_clamp_measurable [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (H : S53Var s ρ P X' T CA δ) (T' : ℝ) {G' : ℝ → Euc d → ℝ}
    (hG1 : Measurable fun p : ℝ × Euc d => gradient (G' (s53_clamp T' p.1)) p.2) :
    Measurable fun σ => s53_ell s ρ P X' (G' (s53_clamp T' σ)) := by
  have m1 : Measurable fun p : ℝ × EucConfig d N =>
      s53_Dk s ρ ((fun τ : ℝ => G' (s53_clamp T' τ)) p.1) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun τ => G' (s53_clamp T' τ)) hG1
  have hjm : Measurable fun q : Ω × ℝ => s53_Dk s ρ (G' (s53_clamp T' q.2)) (X' 0 q.1) := by
    have hpr : Measurable fun q : Ω × ℝ => (q.2, X' 0 q.1) :=
      measurable_snd.prodMk ((H.meas 0).comp measurable_fst)
    have := m1.comp hpr
    exact this
  exact (StronglyMeasurable.integral_prod_left (μ := P)
    (f := fun ζ σ => s53_Dk s ρ (G' (s53_clamp T' σ)) (X' 0 ζ)) hjm.stronglyMeasurable).measurable


lemma s53_path_bound_c [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (H : S53Var s ρ P X' T CA δ) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : ∀ f : Euc d → ℝ, MemCb 2 f → |s53_ell s ρ P X' f| ≤ Cm * cbNorm 2 f)
    {G G' : ℝ → Euc d → ℝ} (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ))
    (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ)) (hdiff : S53Diff T G G') (hc' : S53Cont T G')
    {L : ℝ} (hL : ∀ σ ∈ Set.Icc (0 : ℝ) T, cbNorm 2 (G' σ) ≤ L)
    (Y : EucConfig d N) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    ‖s53_Dk s ρ (G τ) Y - s53_ell s ρ P X' (G τ)‖ₑ ≤
      s53_Hc s ρ T G G' (s53_ell s ρ P X' (G 0)) (fun σ => s53_ell s ρ P X' (G' (s53_clamp T σ))) Y := by
  have hG1m := s53_grad_measurable hT hG' hc'
  have hℓm := s53_ell_clamp_measurable ctx H T hG1m
  have hsubT : ∀ σ ∈ Set.Ioc (0 : ℝ) τ, σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ => ⟨hσ.1.le, hσ.2.trans hτ.2⟩
  have hf := s53_ftc ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN hG hG' hdiff hc' Y hτ
  have hmf := s53_mean_ftc ctx hN hδ hT H hCm0 hCm hG hG' hdiff hc' hL hτ
  have hf' : s53_Dk s ρ (G τ) Y = s53_Dk s ρ (G 0) Y +
      ∫ σ in Set.Ioc 0 τ, s53_Dk s ρ (G' (s53_clamp T σ)) Y := by
    rw [hf]; congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
    simp only [s53_clamp_of_mem (hsubT σ hσ)]
  have hmf' : s53_ell s ρ P X' (G τ) = s53_ell s ρ P X' (G 0) +
      ∫ σ in Set.Ioc 0 τ, s53_ell s ρ P X' (G' (s53_clamp T σ)) := by
    rw [hmf]; congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
    simp only [s53_clamp_of_mem (hsubT σ hσ)]
  have hi1 : IntegrableOn (fun σ => s53_Dk s ρ (G' (s53_clamp T σ)) Y) (Set.Ioc 0 τ) := by
    have hc := (s53_Dk_continuousOn ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN hG' hc' Y)
    have h1 : IntegrableOn (fun σ => s53_Dk s ρ (G' σ) Y) (Set.Ioc 0 τ) :=
      (hc.mono (Set.Icc_subset_Icc_right hτ.2)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    exact h1.congr_fun (fun σ hσ => by simp only [s53_clamp_of_mem (hsubT σ hσ)]) measurableSet_Ioc
  have hi2 : IntegrableOn (fun σ => s53_ell s ρ P X' (G' (s53_clamp T σ))) (Set.Ioc 0 τ) := by
    refine Measure.integrableOn_of_bounded (M := Cm * L) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      hℓm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_eq_abs, s53_clamp_of_mem (hsubT σ hσ)]
    exact (hCm _ (hG' σ (hsubT σ hσ))).trans (mul_le_mul_of_nonneg_left (hL σ (hsubT σ hσ)) hCm0)
  have hdiffeq : s53_Dk s ρ (G τ) Y - s53_ell s ρ P X' (G τ) =
      (s53_Dk s ρ (G 0) Y - s53_ell s ρ P X' (G 0)) +
        ∫ σ in Set.Ioc 0 τ, (s53_Dk s ρ (G' (s53_clamp T σ)) Y -
          s53_ell s ρ P X' (G' (s53_clamp T σ))) := by
    rw [integral_sub hi1 hi2, hf', hmf']; ring
  rw [hdiffeq]
  unfold s53_Hc
  refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  exact lintegral_mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right hτ.2))


lemma s53_cs_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) {h : α → ℝ≥0∞} (hm : AEMeasurable h μ) :
    (∫⁻ a, h a ∂μ) ^ 2 ≤ μ Set.univ * ∫⁻ a, h a ^ 2 ∂μ := by
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := h) aemeasurable_const hm
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const] at H
  have e1 : ∀ a, h a ^ (2 : ℝ) = h a ^ 2 := fun a => by rw [ENNReal.rpow_two]
  simp only [e1] at H
  have h2 : (∫⁻ a, h a ∂μ) ^ 2 ≤ ((μ Set.univ) ^ (1 / 2 : ℝ) * (∫⁻ a, h a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left' H 2
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

lemma s53_add_sq (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at h
  have e : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rw [e] at h
  calc (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := h
    _ = _ := by ring

/-- pointwise square bound of the centered dominating function -/
lemma s53_Hc_sq_le (T : ℝ) (hT : 0 ≤ T) (G G' : ℝ → Euc d → ℝ) (ℓ0 : ℝ) (ℓ1 : ℝ → ℝ)
    (hm : ∀ Y : EucConfig d N, Measurable fun σ : ℝ => ‖s53_Dk s ρ (G' (s53_clamp T σ)) Y - ℓ1 σ‖ₑ)
    (Y : EucConfig d N) :
    s53_Hc s ρ T G G' ℓ0 ℓ1 Y ^ 2 ≤ 2 * ‖s53_Dk s ρ (G 0) Y - ℓ0‖ₑ ^ 2 +
      2 * (ENNReal.ofReal T * ∫⁻ σ in Set.Icc (0 : ℝ) T, ‖s53_Dk s ρ (G' (s53_clamp T σ)) Y - ℓ1 σ‖ₑ ^ 2) := by
  unfold s53_Hc
  refine (s53_add_sq _ _).trans (add_le_add le_rfl (mul_le_mul_right ?_ _))
  have := s53_cs_sq (volume.restrict (Set.Icc (0 : ℝ) T)) (hm Y).aemeasurable
  rwa [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero] at this


lemma s53_sm_V [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (hδ : 0 ≤ δ) (H : S53Var s ρ P X' T CA δ)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {f : Euc d → ℝ} (hf : MemCb 2 f) {L : ℝ}
    (hL : cbNorm 2 f ≤ L) :
    (N : ℝ≥0∞) * ∫⁻ ζ, ‖s53_Dk s ρ f (X' (Real.toNNReal r) ζ) - s53_ell s ρ P X' f‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (max CA 0 * δ * L ^ 2) := by
  refine (s53_second_moment ctx H hr hf).trans (ENNReal.ofReal_le_ofReal ?_)
  have hp : (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ≤ L := (s53_p_le_cb hf).trans hL
  have hp0 := s53_cbSup_nonneg f
  have hp2 : (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hp0 hp 2
  have h0 : 0 ≤ max CA 0 * δ := mul_nonneg (le_max_right _ _) hδ
  calc CA * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2 ≤
        max CA 0 * δ * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2 := by
        gcongr; exact le_max_left _ _
    _ ≤ max CA 0 * δ * L ^ 2 := by gcongr

/-- the second moment of the centered dominating function along the process -/
lemma s53_exp_Hc_sq [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (H : S53Var s ρ P X' T CA δ) {G G' : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ))
    (hG0m : Measurable fun x : Euc d => gradient (G 0) x)
    (hG1m : Measurable fun p : ℝ × Euc d => gradient (G' (s53_clamp T p.1)) p.2)
    {L : ℝ} (hL0 : cbNorm 2 (G 0) ≤ L) (hL1 : ∀ σ ∈ Set.Icc (0 : ℝ) T, cbNorm 2 (G' σ) ≤ L)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    (N : ℝ≥0∞) * ∫⁻ ζ, s53_Hc s ρ T G G' (s53_ell s ρ P X' (G 0))
        (fun σ => s53_ell s ρ P X' (G' (s53_clamp T σ))) (X' (Real.toNNReal r) ζ) ^ 2 ∂P ≤
      2 * ENNReal.ofReal (max CA 0 * δ * L ^ 2) +
        2 * (ENNReal.ofReal T * (ENNReal.ofReal T * ENNReal.ofReal (max CA 0 * δ * L ^ 2))) := by
  set V := ENNReal.ofReal (max CA 0 * δ * L ^ 2) with hV
  set ℓ0 := s53_ell s ρ P X' (G 0) with hℓ0
  set ℓ1 : ℝ → ℝ := fun σ => s53_ell s ρ P X' (G' (s53_clamp T σ)) with hℓ1
  have hℓm : Measurable ℓ1 := s53_ell_clamp_measurable ctx H T hG1m
  have m1 : Measurable fun p : ℝ × EucConfig d N =>
      s53_Dk s ρ ((fun τ : ℝ => G' (s53_clamp T τ)) p.1) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun τ => G' (s53_clamp T τ)) hG1m
  have hXr := H.meas (Real.toNNReal r)
  have hmeasσ : ∀ Y : EucConfig d N, Measurable fun σ : ℝ => ‖s53_Dk s ρ (G' (s53_clamp T σ)) Y - ℓ1 σ‖ₑ :=
    fun Y => by
      have hpr : Measurable fun σ : ℝ => (σ, Y) := measurable_id.prodMk measurable_const
      exact ((m1.comp hpr).sub hℓm).enorm
  have hjσ : Measurable fun q : Ω × ℝ =>
      ‖s53_Dk s ρ (G' (s53_clamp T q.2)) (X' (Real.toNNReal r) q.1) - ℓ1 q.2‖ₑ ^ 2 := by
    have hpr : Measurable fun q : Ω × ℝ => (q.2, X' (Real.toNNReal r) q.1) :=
      measurable_snd.prodMk (hXr.comp measurable_fst)
    exact (((m1.comp hpr).sub (hℓm.comp measurable_snd)).enorm).pow_const 2
  have m0 : Measurable fun p : ℝ × EucConfig d N => s53_Dk s ρ ((fun _ : ℝ => G 0) p.1) p.2 :=
    s53_Dk_measurable ctx.hρ (F := fun _ => G 0) (hG0m.comp measurable_snd)
  have hA : Measurable fun ζ => ‖s53_Dk s ρ (G 0) (X' (Real.toNNReal r) ζ) - ℓ0‖ₑ ^ 2 := by
    have hpr : Measurable fun ζ => ((0 : ℝ), X' (Real.toNNReal r) ζ) :=
      measurable_const.prodMk hXr
    exact (((m0.comp hpr).sub_const _).enorm).pow_const 2
  have hpt : ∀ ζ, s53_Hc s ρ T G G' ℓ0 ℓ1 (X' (Real.toNNReal r) ζ) ^ 2 ≤
      2 * ‖s53_Dk s ρ (G 0) (X' (Real.toNNReal r) ζ) - ℓ0‖ₑ ^ 2 +
        2 * (ENNReal.ofReal T * ∫⁻ σ in Set.Icc (0 : ℝ) T,
          ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ) - ℓ1 σ‖ₑ ^ 2) :=
    fun ζ => s53_Hc_sq_le T hT G G' ℓ0 ℓ1 hmeasσ _
  have hswap : ∫⁻ ζ, (∫⁻ σ in Set.Icc (0 : ℝ) T,
      ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ) - ℓ1 σ‖ₑ ^ 2) ∂P =
      ∫⁻ σ in Set.Icc (0 : ℝ) T, ∫⁻ ζ,
        ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ) - ℓ1 σ‖ₑ ^ 2 ∂P :=
    lintegral_lintegral_swap hjσ.aemeasurable
  have hA' : (N : ℝ≥0∞) * ∫⁻ ζ, ‖s53_Dk s ρ (G 0) (X' (Real.toNNReal r) ζ) - ℓ0‖ₑ ^ 2 ∂P ≤ V :=
    s53_sm_V ctx hδ H hr (hG 0 ⟨le_rfl, hT⟩) hL0
  have hB' : (N : ℝ≥0∞) * ∫⁻ σ in Set.Icc (0 : ℝ) T, ∫⁻ ζ,
      ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ) - ℓ1 σ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal T * V := by
    rw [← lintegral_const_mul' _ _ (by exact_mod_cast ENNReal.natCast_ne_top N)]
    calc ∫⁻ σ in Set.Icc (0 : ℝ) T, (N : ℝ≥0∞) * ∫⁻ ζ,
          ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ) - ℓ1 σ‖ₑ ^ 2 ∂P
        ≤ ∫⁻ σ in Set.Icc (0 : ℝ) T, V := by
          refine setLIntegral_mono' measurableSet_Icc fun σ hσ => ?_
          have := s53_sm_V ctx hδ H hr (hG' σ hσ) (hL1 σ hσ)
          simp only [hℓ1, s53_clamp_of_mem hσ] at this ⊢
          exact this
      _ = ENNReal.ofReal T * V := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
  calc (N : ℝ≥0∞) * ∫⁻ ζ, s53_Hc s ρ T G G' ℓ0 ℓ1 (X' (Real.toNNReal r) ζ) ^ 2 ∂P
      ≤ (N : ℝ≥0∞) * ∫⁻ ζ, (2 * ‖s53_Dk s ρ (G 0) (X' (Real.toNNReal r) ζ) - ℓ0‖ₑ ^ 2 +
          2 * (ENNReal.ofReal T * ∫⁻ σ in Set.Icc (0 : ℝ) T,
            ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ) - ℓ1 σ‖ₑ ^ 2)) ∂P :=
        mul_le_mul_right (lintegral_mono hpt) _
    _ = 2 * ((N : ℝ≥0∞) * ∫⁻ ζ, ‖s53_Dk s ρ (G 0) (X' (Real.toNNReal r) ζ) - ℓ0‖ₑ ^ 2 ∂P) +
        2 * (ENNReal.ofReal T * ((N : ℝ≥0∞) * ∫⁻ σ in Set.Icc (0 : ℝ) T, ∫⁻ ζ,
          ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ) - ℓ1 σ‖ₑ ^ 2 ∂P)) := by
        have hBm : Measurable fun ζ => ∫⁻ σ in Set.Icc (0 : ℝ) T,
            ‖s53_Dk s ρ (G' (s53_clamp T σ)) (X' (Real.toNNReal r) ζ) - ℓ1 σ‖ₑ ^ 2 :=
          hjσ.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))
        rw [lintegral_add_left (hA.const_mul 2), lintegral_const_mul 2 hA,
          lintegral_const_mul 2 (hBm.const_mul _), lintegral_const_mul _ hBm, hswap]
        ring
    _ ≤ 2 * V + 2 * (ENNReal.ofReal T * (ENNReal.ofReal T * V)) :=
        add_le_add (mul_le_mul_right hA' _) (mul_le_mul_right (mul_le_mul_right hB' _) _)


/-- abstract second moment of a time integral (Cauchy–Schwarz in time, Tonelli) -/
lemma s53_g_second [IsProbabilityMeasure P] {h : Ω → ℝ → ℝ≥0∞} (hm : Measurable fun q : Ω × ℝ => h q.1 q.2)
    (T : ℝ) {W : ℝ≥0∞}
    (hW : ∀ r ∈ Set.Icc (0 : ℝ) T, (N : ℝ≥0∞) * ∫⁻ ζ, h ζ r ^ 2 ∂P ≤ W) :
    (N : ℝ≥0∞) * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, h ζ r) ^ 2 ∂P ≤
      ENNReal.ofReal T * (ENNReal.ofReal T * W) := by
  have hcs : ∀ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, h ζ r) ^ 2 ≤
      ENNReal.ofReal T * ∫⁻ r in Set.Icc (0 : ℝ) T, h ζ r ^ 2 := fun ζ => by
    have hmr : Measurable fun r : ℝ => h ζ r := hm.comp (measurable_const.prodMk measurable_id)
    have := s53_cs_sq (volume.restrict (Set.Icc (0 : ℝ) T)) hmr.aemeasurable
    rwa [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero] at this
  have hsq : Measurable fun q : Ω × ℝ => h q.1 q.2 ^ 2 := hm.pow_const 2
  have hN : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  calc (N : ℝ≥0∞) * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, h ζ r) ^ 2 ∂P
      ≤ (N : ℝ≥0∞) * ∫⁻ ζ, (ENNReal.ofReal T * ∫⁻ r in Set.Icc (0 : ℝ) T, h ζ r ^ 2) ∂P :=
        mul_le_mul_right (lintegral_mono hcs) _
    _ = ENNReal.ofReal T * ∫⁻ r in Set.Icc (0 : ℝ) T, (N : ℝ≥0∞) * ∫⁻ ζ, h ζ r ^ 2 ∂P := by
        rw [lintegral_const_mul _ (hsq.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))),
          lintegral_lintegral_swap hsq.aemeasurable, lintegral_const_mul' _ _ hN]
        ring
    _ ≤ ENNReal.ofReal T * ∫⁻ r in Set.Icc (0 : ℝ) T, W :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Icc hW) _
    _ = _ := by rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm W]


/-- the pathwise facts for one coordinate and one `ζ` in the good set -/
lemma s53_alpha_c_path [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hT : 0 ≤ T) (H : S53Var s ρ P X' T CA δ) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : ∀ f : Euc d → ℝ, MemCb 2 f → |s53_ell s ρ P X' f| ≤ Cm * cbNorm 2 f)
    {C : WholeCoeff d} {m : ℝ} {α : MultiIndex d} {G G' G'' : ℝ → Euc d → ℝ}
    (hom : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → propagatorW C r t (oscTestFun m α) = G (t - r))
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ))
    (hG'' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G'' τ))
    (hd0 : S53Diff T G G') (hd1 : S53Diff T G' G'') {L : ℝ}
    (hL0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, cbNorm 2 (G τ) ≤ L) (hL1 : ∀ σ ∈ Set.Icc (0 : ℝ) T, cbNorm 2 (G' σ) ≤ L)
    {X : ℝ≥0 → Ω → EucConfig d N} {Gs : Set Ω}
    (hX'j : Measurable fun p : ℝ × Ω => X' (Real.toNNReal p.1) p.2)
    (hGs : ∀ ζ ∈ Gs, ∀ t, X' t ζ = X t ζ) (hae : ∀ t, ∀ᵐ ζ ∂P, X' t ζ = X t ζ)
    {ζ : Ω} (hζ : ζ ∈ Gs) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫⁻ r in Set.Icc (0 : ℝ) t, ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
        ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P‖ₑ ≤
      ∫⁻ r in Set.Icc (0 : ℝ) T, s53_Hc s ρ T G G' (s53_ell s ρ P X' (G 0))
        (fun σ => s53_ell s ρ P X' (G' (s53_clamp T σ))) (X' (Real.toNNReal r) ζ)) ∧
    (∫⁻ r in Set.Icc (0 : ℝ) t, ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ‖ₑ ≤
      (∫⁻ r in Set.Icc (0 : ℝ) t, ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
        ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P‖ₑ) +
        ENNReal.ofReal T * ENNReal.ofReal (Cm * L)) ∧
    AEStronglyMeasurable (fun r => commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := by
  have hc0 : S53Cont T G := s53_cont_of_diff hG hG' hd0
  have hc1 : S53Cont T G' := s53_cont_of_diff hG' hG'' hd1
  have hF0m := s53_grad_measurable hT hG hc0
  have hmean : ∀ r ∈ Set.Icc (0 : ℝ) t,
      ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P =
        s53_ell s ρ P X' (G (t - r)) := by
    intro r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    have hτ : t - r ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩
    have hmY : Measurable fun Y : EucConfig d N => s53_Dk s ρ (G (t - r)) Y :=
      s53_Dk_meas_config ctx.hρ ((hG _ hτ).1.of_le (by norm_num))
    calc ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P
        = ∫ ζ', s53_Dk s ρ (G (t - r)) (X' (Real.toNNReal r) ζ') ∂P := by
          refine integral_congr_ae ((hae (Real.toNNReal r)).mono fun ζ' hζ' => ?_)
          beta_reduce
          rw [s53_comm_eq, hom r t hr.1 hr.2 ht.2, hζ']
      _ = ∫ ζ', s53_Dk s ρ (G (t - r)) (X' 0 ζ') ∂P := s53_mean_eq H hrT hmY
      _ = _ := rfl
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t,
      ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
        ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P‖ₑ ≤
      s53_Hc s ρ T G G' (s53_ell s ρ P X' (G 0))
        (fun σ => s53_ell s ρ P X' (G' (s53_clamp T σ))) (X' (Real.toNNReal r) ζ) := by
    intro r hr
    have hτ : t - r ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩
    rw [hmean r hr, s53_comm_eq, hom r t hr.1 hr.2 ht.2, ← hGs ζ hζ]
    exact s53_path_bound_c ctx hN hδ hT H hCm0 hCm hG hG' hd0 hc1 hL1 _ hτ
  refine ⟨(setLIntegral_mono' measurableSet_Icc hpt).trans
    (lintegral_mono_set (Set.Icc_subset_Icc_right ht.2)), ?_, ?_⟩
  · have hpt2 : ∀ r ∈ Set.Icc (0 : ℝ) t,
        ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ‖ₑ ≤
          ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
            ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P‖ₑ +
            ENNReal.ofReal (Cm * L) := by
      intro r hr
      have hτ : t - r ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩
      have h4 : ‖∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P‖ₑ ≤
          ENNReal.ofReal (Cm * L) := by
        rw [hmean r hr, ← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal ((hCm _ (hG _ hτ)).trans
          (mul_le_mul_of_nonneg_left (hL0 _ hτ) hCm0))
      have := enorm_add_le (commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
        ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P)
        (∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P)
      rw [sub_add_cancel] at this
      exact this.trans (add_le_add le_rfl h4)
    refine (setLIntegral_mono' measurableSet_Icc hpt2).trans ?_
    rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Icc, sub_zero]
    refine add_le_add le_rfl ?_
    rw [mul_comm]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal ht.2) _
  · have m0 : Measurable fun p : ℝ × EucConfig d N =>
        s53_Dk s ρ (G (s53_clamp T p.1)) p.2 :=
      s53_Dk_measurable ctx.hρ (F := fun τ => G (s53_clamp T τ)) hF0m
    have hpr : Measurable fun r : ℝ => (t - r, X' (Real.toNNReal r) ζ) :=
      (measurable_const.sub measurable_id).prodMk
        (hX'j.comp (measurable_id.prodMk measurable_const))
    have hm : Measurable fun r : ℝ =>
        s53_Dk s ρ (G (s53_clamp T (t - r))) (X' (Real.toNNReal r) ζ) :=
      Measurable.comp (f := fun r : ℝ => (t - r, X' (Real.toNNReal r) ζ)) m0 hpr
    refine hm.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    beta_reduce
    rw [s53_comm_eq, hom r t hr.1 hr.2 ht.2, hGs ζ hζ,
      s53_clamp_of_mem (show t - r ∈ Set.Icc (0 : ℝ) T from
        ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩)]

end HRS.MS.S53
