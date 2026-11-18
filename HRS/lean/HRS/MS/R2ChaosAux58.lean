import HRS.MS.R2ChaosAux57

/-!
# HRS.MS.R2ChaosAux58 -- S9.6 (P3, part 3): a jointly measurable limit `F` of a family of chaos versions

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_limit_F`: if `Φ_j` are jointly measurable and `2Φ_j(t,·)` is the Wick chaos of `cen(k_j(t))` for every ONB and `t ∈ [0,T]`, with
`k_j(t) → k₀(t)` in `L²(μ⊗μ)` and `sup ‖k_j(t)‖₂ < ∞`, then there is a jointly measurable `F` with `F(·,ζ) ∈ L²(dt)` for every `ζ`,
`2F(t,·)` the Wick chaos of `cen(k₀(t))` for every ONB, and `Φ_j → F` in `L²(dt ⊗ P')` (with an explicit null sequence).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section LimitF

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_limit_F (hd : 2 ≤ d) (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 < T)
    {kk : ℕ → ℝ → Euc d → Euc d → ℝ} {k0 : ℝ → Euc d → Euc d → ℝ}
    (hkok : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, S94KOK (Whole.withDensityReal ρ) (kk j t))
    (hk0ok : ∀ t ∈ Set.Icc (0 : ℝ) T, S94KOK (Whole.withDensityReal ρ) (k0 t))
    (hconv : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun j => eLpNorm
      (fun q : Euc d × Euc d => kk j t q.1 q.2 - k0 t q.1 q.2) 2
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))) atTop (𝓝 0))
    (hκ : ∃ κ : ℝ, ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, eLpNorm (fun q : Euc d × Euc d => kk j t q.1 q.2) 2
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) ≤ ENNReal.ofReal κ)
    {Φ : ℕ → ℝ → Ω' → ℝ} (hΦm : ∀ j, Measurable fun q : ℝ × Ω' => Φ j q.1 q.2)
    (hΦW : ∀ j, ∀ a : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (Whole.withDensityReal ρ) a → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsR2WickChaos P' (Whole.withDensityReal ρ) a (fun i ζ => r2PathEval T (ξ (a i) ζ) t)
        (r2CenterKernel (Whole.withDensityReal ρ) (kk j t)) (fun ζ => 2 * Φ j t ζ)) :
    ∃ F : ℝ → Ω' → ℝ, (Measurable fun q : ℝ × Ω' => F q.1 q.2) ∧
      (∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
      (∀ a : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (Whole.withDensityReal ρ) a → ∀ t ∈ Set.Icc (0 : ℝ) T,
        IsR2WickChaos P' (Whole.withDensityReal ρ) a (fun i ζ => r2PathEval T (ξ (a i) ζ) t)
          (r2CenterKernel (Whole.withDensityReal ρ) (k0 t)) (fun ζ => 2 * F t ζ)) ∧
      ∃ η : ℕ → ℝ, (∀ j, 0 ≤ η j) ∧ Tendsto η atTop (𝓝 0) ∧ ∀ j,
        ∫⁻ ζ', ∫⁻ t in Set.Icc (0 : ℝ) T, ‖Φ j t ζ' - F t ζ'‖ₑ ^ 2 ∂volume ∂P' ≤ ENNReal.ofReal (η j) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  set μ := Whole.withDensityReal ρ with hμ
  obtain ⟨Λ0, hcov0⟩ := hset.cov
  set Λ : ℝ := max Λ0 0 with hΛ
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean μ a x) ^ 2 ∂μ :=
    fun t ht a ha => (hcov0 t ht a ha).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg fun x => sq_nonneg _))
  have hzs : ∀ (a : ℕ → Euc d → ℝ), IsR2ZeroMeanONB μ a → ∀ t ∈ Set.Icc (0 : ℝ) T,
      S94GSeq P' (fun i ζ => r2PathEval T (ξ (a i) ζ) t) Λ := fun a ha t ht =>
    s94_gseq_of_setting hset hcov hΛ0 ha.1 ha.2.1 ht
  obtain ⟨κ, hκb⟩ := hκ
  -- chaos convergence for each ONB
  have hchaos : ∀ a : ℕ → Euc d → ℝ, IsR2ZeroMeanONB μ a → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ Q0 : Ω' → ℝ, s94WickL2 P' μ a (fun i ζ => r2PathEval T (ξ (a i) ζ) t) (r2CenterKernel μ (k0 t)) Q0 ∧
        Tendsto (fun j => eLpNorm (fun ζ => 2 * Φ j t ζ - Q0 ζ) 2 P') atTop (𝓝 0) := by
    intro a ha t ht
    exact s94_chaos_conv (hzs a ha t ht) hΛ0 ha.1 ha.2.1 (kk := fun j => kk j t) (k0 := k0 t)
      (fun j => hkok j t ht) (hk0ok t ht)
      (Q := fun j ζ => 2 * Φ j t ζ) (fun j => s94_isWick_to_L2 (hzs a ha t ht) (hΦW j a ha t ht)) (hconv t ht)
  obtain ⟨a0, ha0⟩ := s94_exists_onb hd hρ
  -- uniform bound
  set Cb : ℝ := Real.sqrt 2 * Λ * 4 * |κ| with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  have hbd2 : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, eLpNorm (fun ζ => 2 * Φ j t ζ) 2 P' ≤ ENNReal.ofReal Cb := by
    intro j t ht
    have h1 := s94_chaos_bound (hzs a0 ha0 t ht) hΛ0 ha0.1 ha0.2.1 (hkok j t ht)
      (s94_isWick_to_L2 (hzs a0 ha0 t ht) (hΦW j a0 ha0 t ht))
    refine h1.trans ?_
    calc ENNReal.ofReal (Real.sqrt 2 * Λ * 4) * eLpNorm (fun q : Euc d × Euc d => kk j t q.1 q.2) 2 (μ.prod μ)
        ≤ ENNReal.ofReal (Real.sqrt 2 * Λ * 4) * ENNReal.ofReal κ := mul_le_mul_right (hκb j t ht) _
      _ = ENNReal.ofReal (Real.sqrt 2 * Λ * 4 * κ) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal Cb := ENNReal.ofReal_le_ofReal (by
          rw [hCb]; exact mul_le_mul_of_nonneg_left (le_abs_self κ) (by positivity))
  have hbd1 : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, eLpNorm (fun ζ => Φ j t ζ) 2 P' ≤ ENNReal.ofReal Cb := by
    intro j t ht
    have e : (fun ζ => Φ j t ζ) = (1 / 2 : ℝ) • (fun ζ => 2 * Φ j t ζ) := by
      funext ζ; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e, eLpNorm_const_smul]
    calc ‖(1 / 2 : ℝ)‖ₑ * eLpNorm (fun ζ => 2 * Φ j t ζ) 2 P' ≤ 1 * ENNReal.ofReal Cb := by
          gcongr
          · rw [← ofReal_norm_eq_enorm]
            norm_num
          · exact hbd2 j t ht
      _ = ENNReal.ofReal Cb := one_mul _
  have hΦ2 : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (fun ζ => Φ j t ζ) 2 P' := by
    intro j t ht
    have := (s94_isWick_to_L2 (hzs a0 ha0 t ht) (hΦW j a0 ha0 t ht)).1.const_mul (1 / 2 : ℝ)
    refine (memLp_congr_ae (Filter.EventuallyEq.of_eq ?_)).1 this
    funext ζ; ring
  -- Cauchy property
  have hcau : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℕ, ∀ m, M ≤ m → ∀ m', M ≤ m' →
      eLpNorm (fun ζ => Φ m t ζ - Φ m' t ζ) 2 P' < ε := by
    intro t ht ε hε
    obtain ⟨Q0, -, hQ0⟩ := hchaos a0 ha0 t ht
    have hev := hQ0.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne'))
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
    refine ⟨M, fun m hm m' hm' => ?_⟩
    have e : (fun ζ => Φ m t ζ - Φ m' t ζ) = (1 / 2 : ℝ) • ((fun ζ => 2 * Φ m t ζ - Q0 ζ) - (fun ζ => 2 * Φ m' t ζ - Q0 ζ)) := by
      funext ζ; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [e, eLpNorm_const_smul]
    have h1 : ‖(1 / 2 : ℝ)‖ₑ ≤ 1 := by rw [← ofReal_norm_eq_enorm]; norm_num
    calc ‖(1 / 2 : ℝ)‖ₑ * eLpNorm ((fun ζ => 2 * Φ m t ζ - Q0 ζ) - (fun ζ => 2 * Φ m' t ζ - Q0 ζ)) 2 P'
        ≤ 1 * (eLpNorm (fun ζ => 2 * Φ m t ζ - Q0 ζ) 2 P' + eLpNorm (fun ζ => 2 * Φ m' t ζ - Q0 ζ) 2 P') := by
          gcongr
          exact eLpNorm_sub_le (by norm_num)
      _ < ε / 2 + ε / 2 := by
          rw [one_mul]; exact ENNReal.add_lt_add (hM m hm) (hM m' hm')
      _ = ε := ENNReal.add_halves ε
  obtain ⟨F0, hF0m, hF0⟩ := s94_measurable_L2_limit (Φ := fun j q => Φ j q.1 q.2) measurableSet_Icc hΦm
    hΦ2 hcau
  have hF0b : ∀ t ∈ Set.Icc (0 : ℝ) T, eLpNorm (fun ζ => F0 (t, ζ)) 2 P' ≤ ENNReal.ofReal Cb := by
    intro t ht
    have h1 : ∀ j, eLpNorm (fun ζ => F0 (t, ζ)) 2 P' ≤
        eLpNorm (fun ζ => Φ j t ζ - F0 (t, ζ)) 2 P' + ENNReal.ofReal Cb := by
      intro j
      have e : (fun ζ => F0 (t, ζ)) = (fun ζ => Φ j t ζ) - (fun ζ => Φ j t ζ - F0 (t, ζ)) := by
        funext ζ; simp
      rw [e]
      refine (eLpNorm_sub_le (by norm_num)).trans ?_
      rw [add_comm]
      gcongr
      exact hbd1 j t ht
    have hlim : Tendsto (fun j => eLpNorm (fun ζ => Φ j t ζ - F0 (t, ζ)) 2 P' + ENNReal.ofReal Cb) atTop
        (𝓝 (0 + ENNReal.ofReal Cb)) := (hF0 t ht).2.add_const _
    rw [zero_add] at hlim
    exact ge_of_tendsto' hlim h1
  let e : ℕ → ℝ → ℝ≥0∞ := fun j t => ∫⁻ ζ, ‖Φ j t ζ - F0 (t, ζ)‖ₑ ^ 2 ∂P'
  have hem : ∀ j, Measurable (e j) := fun j =>
    (((hΦm j).sub hF0m).enorm.pow_const 2).lintegral_prod_right' (ν := P')
  have hmeas_t : ∀ j t, AEStronglyMeasurable (fun ζ => Φ j t ζ - F0 (t, ζ)) P' := fun j t =>
    (((hΦm j).sub hF0m).comp (measurable_prodMk_left (x := t))).aestronglyMeasurable
  have he_eq : ∀ j t, e j t = eLpNorm (fun ζ => Φ j t ζ - F0 (t, ζ)) 2 P' ^ 2 :=
    fun j t => s94_lintegral_sq_eq (hmeas_t j t)
  have he_bd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j, e j t ≤ ENNReal.ofReal (2 * Cb) ^ 2 := by
    intro t ht j
    rw [he_eq]
    refine pow_le_pow_left' ?_ 2
    have e1 : (fun ζ => Φ j t ζ - F0 (t, ζ)) = (fun ζ => Φ j t ζ) - (fun ζ => F0 (t, ζ)) := rfl
    rw [e1]
    refine (eLpNorm_sub_le (by norm_num)).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    have : ENNReal.ofReal 2 = 2 := by norm_num
    rw [this]
    calc _ ≤ ENNReal.ofReal Cb + ENNReal.ofReal Cb := add_le_add (hbd1 j t ht) (hF0b t ht)
      _ = 2 * ENNReal.ofReal Cb := by rw [two_mul]
  have he_lim : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun j => e j t) atTop (𝓝 0) := by
    intro t ht
    have h1 := ((ENNReal.continuous_pow 2).tendsto 0).comp (hF0 t ht).2
    simp only [Function.comp_def, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    exact (tendsto_congr fun j => he_eq j t).2 h1
  have hfin : ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (2 * Cb) ^ 2 ≠ ⊤ := by
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by simp)
  have hDCT : Tendsto (fun j => ∫⁻ t in Set.Icc (0 : ℝ) T, e j t) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := e) (f := fun _ => 0) (fun _ => ENNReal.ofReal (2 * Cb) ^ 2) hem
      (fun j => (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => he_bd t ht j)) hfin
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ he_lim))
    simpa using this
  have hIfin : ∀ j, ∫⁻ t in Set.Icc (0 : ℝ) T, e j t ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top hfin (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2
      (ae_of_all _ fun t ht => he_bd t ht j)))
  let I : Ω' → ℝ≥0∞ := fun ζ => ∫⁻ t in Set.Icc (0 : ℝ) T, ‖F0 (t, ζ)‖ₑ ^ 2 ∂volume
  have hIm : Measurable I := ((hF0m.enorm.pow_const 2).comp measurable_swap).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) T))
  have hIswap : ∫⁻ ζ, I ζ ∂P' = ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ, ‖F0 (t, ζ)‖ₑ ^ 2 ∂P' :=
    lintegral_lintegral_swap ((hF0m.enorm.pow_const 2).comp measurable_swap).aemeasurable
  have hIbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ‖F0 (t, ζ)‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal Cb ^ 2 := by
    intro t ht
    have hsm_t : AEStronglyMeasurable (fun ζ => F0 (t, ζ)) P' :=
      (hF0m.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable
    rw [s94_lintegral_sq_eq hsm_t]
    exact pow_le_pow_left' (hF0b t ht) 2
  have hIlt : ∫⁻ ζ, I ζ ∂P' < ⊤ := by
    rw [hIswap]
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Icc hIbd) ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (by simp)
  have hIae : ∀ᵐ ζ ∂P', I ζ < ⊤ := ae_lt_top hIm hIlt.ne
  let F : ℝ → Ω' → ℝ := fun t ζ => if I ζ < ⊤ then F0 (t, ζ) else 0
  have hFm : Measurable fun q : ℝ × Ω' => F q.1 q.2 :=
    Measurable.ite ((hIm.comp measurable_snd) measurableSet_Iio) hF0m measurable_const
  have hFeq : ∀ t, (fun ζ => F t ζ) =ᵐ[P'] fun ζ => F0 (t, ζ) := fun t => by
    filter_upwards [hIae] with ζ hζ
    simp [F, hζ]
  have hF2 : ∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    intro ζ
    by_cases hζ : I ζ < ⊤
    · have e1 : (fun t => F t ζ) = fun t => F0 (t, ζ) := by funext t; simp [F, hζ]
      rw [e1]
      have hsm : AEStronglyMeasurable (fun t => F0 (t, ζ)) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
        (hF0m.comp (measurable_prodMk_right (y := ζ))).aestronglyMeasurable
      have h2 : eLpNorm (fun t => F0 (t, ζ)) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) ^ 2 < ⊤ := by
        rw [← s94_lintegral_sq_eq hsm]; exact hζ
      by_contra hne
      have htop : eLpNorm (fun t => F0 (t, ζ)) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) = ⊤ := by
        by_contra h'; exact hne (lt_top_iff_ne_top.2 h')
      rw [htop] at h2
      simp at h2
    · have e1 : (fun t => F t ζ) = fun _ => 0 := by funext t; simp [F, hζ]
      rw [e1]
      exact MemLp.zero
  have hFt2 : ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (fun ζ => F t ζ) 2 P' := fun t ht =>
    (memLp_congr_ae (hFeq t)).2 (hF0 t ht).1
  have hFlim : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun j => eLpNorm (fun ζ => Φ j t ζ - F t ζ) 2 P') atTop (𝓝 0) := by
    intro t ht
    refine (tendsto_congr fun j => ?_).2 (hF0 t ht).2
    exact (eLpNorm_congr_ae (by filter_upwards [hFeq t] with ζ hζ; simp [hζ])).symm
  refine ⟨F, hFm, hF2, fun a ha t ht => ?_, fun j => (∫⁻ t in Set.Icc (0 : ℝ) T, e j t).toReal,
    fun j => ENNReal.toReal_nonneg, ?_, ?_⟩
  · -- Wick clause for the ONB `a`
    obtain ⟨Q0, hQ0, hlimQ⟩ := hchaos a ha t ht
    have hFm2 : MemLp (fun ζ => 2 * F t ζ) 2 P' := (hFt2 t ht).const_mul 2
    have h2F : ∀ j, eLpNorm (fun ζ => 2 * F t ζ - 2 * Φ j t ζ) 2 P' =
        2 * eLpNorm (fun ζ => Φ j t ζ - F t ζ) 2 P' := by
      intro j
      have e1 : (fun ζ => 2 * F t ζ - 2 * Φ j t ζ) = (-2 : ℝ) • (fun ζ => Φ j t ζ - F t ζ) := by
        funext ζ; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [e1, eLpNorm_const_smul]
      congr 1
      rw [← ofReal_norm_eq_enorm]
      norm_num
    have hbound : ∀ j, eLpNorm (fun ζ => 2 * F t ζ - Q0 ζ) 2 P' ≤
        2 * eLpNorm (fun ζ => Φ j t ζ - F t ζ) 2 P' + eLpNorm (fun ζ => 2 * Φ j t ζ - Q0 ζ) 2 P' := by
      intro j
      have e1 : (fun ζ => 2 * F t ζ - Q0 ζ) = (fun ζ => 2 * F t ζ - 2 * Φ j t ζ) +
          (fun ζ => 2 * Φ j t ζ - Q0 ζ) := by funext ζ; simp only [Pi.add_apply]; ring
      rw [e1]
      refine (eLpNorm_add_le (by norm_num)).trans ?_
      rw [h2F j]
    have hz0 : eLpNorm (fun ζ => 2 * F t ζ - Q0 ζ) 2 P' = 0 := by
      refine le_antisymm ?_ bot_le
      have hlim : Tendsto (fun j => 2 * eLpNorm (fun ζ => Φ j t ζ - F t ζ) 2 P' +
          eLpNorm (fun ζ => 2 * Φ j t ζ - Q0 ζ) 2 P') atTop (𝓝 0) := by
        have h1 : Tendsto (fun j => 2 * eLpNorm (fun ζ => Φ j t ζ - F t ζ) 2 P') atTop (𝓝 (2 * 0)) :=
          ENNReal.Tendsto.const_mul (hFlim t ht) (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
        simpa using h1.add hlimQ
      exact ge_of_tendsto' hlim hbound
    have hae : (fun ζ => 2 * F t ζ) =ᵐ[P'] Q0 := by
      have := (eLpNorm_eq_zero_iff (by norm_num)).1 hz0
      filter_upwards [this] with ζ hζ
      simpa [sub_eq_zero] using hζ
    have hW : s94WickL2 P' μ a (fun i ζ => r2PathEval T (ξ (a i) ζ) t) (r2CenterKernel μ (k0 t))
        (fun ζ => 2 * F t ζ) := by
      refine ⟨hFm2, ?_⟩
      refine hQ0.2.congr fun n => ?_
      refine integral_congr_ae ?_
      filter_upwards [hae] with ζ hζ
      rw [hζ]
    exact hW.isWick (hzs a ha t ht)
  · have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDCT
    rw [ENNReal.toReal_zero] at this
    exact this
  · intro j
    have hDm : Measurable fun q : ℝ × Ω' => ‖Φ j q.1 q.2 - F q.1 q.2‖ₑ ^ 2 :=
      (((hΦm j).sub hFm).enorm.pow_const 2)
    have hswap : ∫⁻ ζ', ∫⁻ t in Set.Icc (0 : ℝ) T, ‖Φ j t ζ' - F t ζ'‖ₑ ^ 2 ∂volume ∂P' =
        ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ', ‖Φ j t ζ' - F t ζ'‖ₑ ^ 2 ∂P' :=
      lintegral_lintegral_swap (hDm.comp measurable_swap).aemeasurable
    have hcongr : ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ', ‖Φ j t ζ' - F t ζ'‖ₑ ^ 2 ∂P' =
        ∫⁻ t in Set.Icc (0 : ℝ) T, e j t :=
      setLIntegral_congr_fun measurableSet_Icc fun t ht => lintegral_congr_ae (by
        filter_upwards [hFeq t] with ζ hζ
        simp [hζ])
    beta_reduce
    rw [hswap, hcongr, ENNReal.ofReal_toReal (hIfin j)]

end LimitF

end HRS.MS.R2Chaos
