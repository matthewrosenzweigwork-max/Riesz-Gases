import HRS.MS.R2ChaosAux44

/-!
# HRS.MS.R2ChaosAux45 -- (b), (c): the jointly measurable version `F` with all properties

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_exists_F_full`: there is `F : ℝ → Ω' → ℝ`, jointly measurable, with `F(·,ζ) ∈ L²(dt)` for EVERY `ζ`, `2 F(t,·)` the Wick chaos of
`cen(h_t)` for every orthonormal basis and every `t ∈ [0,T]`, and `Φ_m → F` in `L²(dt ⊗ P')` with an explicit null sequence `ηF`.
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

section FullF

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_exists_F_full (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 < T) {B C₁ : ℝ}
    {h : ℝ → Euc d → Euc d → ℝ} (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t))
    {n : ℕ → ℕ} {u : ∀ m, Fin (n m) → Euc d → ℝ} {Cm : ∀ m, ℝ → Fin (n m) → Fin (n m) → ℝ}
    (hu : ∀ m a, IsR2Test (u m a)) (hCm : ∀ m a b, Measurable fun t => Cm m t a b)
    (hCs : ∀ m t a b, Cm m t a b = Cm m t b a)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T, IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h t)
      (fun m => r2FiniteRankKernel (Cm m t) (u m))) :
    ∃ F : ℝ → Ω' → ℝ, (Measurable fun q : ℝ × Ω' => F q.1 q.2) ∧
      (∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
      (∀ a : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (Whole.withDensityReal ρ) a → ∀ t ∈ Set.Icc (0 : ℝ) T,
        IsR2WickChaos P' (Whole.withDensityReal ρ) a (fun i ζ => r2PathEval T (ξ (a i) ζ) t)
          (r2CenterKernel (Whole.withDensityReal ρ) (h t)) (fun ζ => 2 * F t ζ)) ∧
      ∃ ηF : ℕ → ℝ, (∀ m, 0 ≤ ηF m) ∧ Tendsto ηF atTop (𝓝 0) ∧ ∀ m,
        ∫⁻ ζ', ∫⁻ t in Set.Icc (0 : ℝ) T, ‖s94Flim ξ P' (Cm m) (u m) t ζ' - F t ζ'‖ₑ ^ 2 ∂volume ∂P'
          ≤ ENNReal.ofReal (ηF m) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨Λ0, hcov0⟩ := hset.cov
  set Λ : ℝ := max Λ0 0 with hΛ
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean (Whole.withDensityReal ρ) a x) ^ 2 ∂(Whole.withDensityReal ρ) :=
    fun t ht a ha => (hcov0 t ht a ha).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg fun x => sq_nonneg _))
  obtain ⟨a0, ha0⟩ := s94_exists_onb hd hρ
  obtain ⟨F0, hF0m, hF0⟩ := s94_exists_F hd hs0 hs hρ hset hcov hΛ0 ha0 hker hu hCm hCs hA
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hB' : 0 ≤ C₁ * B := s94_B_nonneg hd (s94_approx_bounded (hA 0 hT0) 0)
  obtain ⟨C, hC0, hC⟩ := s94_flim_bound hd hs0 hs hρ hset hcov hΛ0 ha0 hB' hu hCs
    (fun m t ht => s94_approx_bounded (hA t ht) m)
  have hΦ : ∀ m, Measurable fun q : ℝ × Ω' => s94Flim ξ P' (Cm m) (u m) q.1 q.2 := fun m =>
    s94Flim_measurable hset.measξ P' (hCm m) (u m)
  have hF0b : ∀ t ∈ Set.Icc (0 : ℝ) T, eLpNorm (fun ζ => F0 (t, ζ)) 2 P' ≤ ENNReal.ofReal C := by
    intro t ht
    have h1 : ∀ m, eLpNorm (fun ζ => F0 (t, ζ)) 2 P' ≤
        eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F0 (t, ζ)) 2 P' + ENNReal.ofReal C := by
      intro m
      have e : (fun ζ => F0 (t, ζ)) = (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ) -
          (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F0 (t, ζ)) := by funext ζ; simp
      rw [e]
      refine (eLpNorm_sub_le (by norm_num)).trans ?_
      rw [add_comm]
      gcongr
      exact hC t ht m
    have hlim : Tendsto (fun m => eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F0 (t, ζ)) 2 P' +
        ENNReal.ofReal C) atTop (𝓝 (0 + ENNReal.ofReal C)) := (hF0 t ht).2.add_const _
    rw [zero_add] at hlim
    exact ge_of_tendsto' hlim h1
  -- the L²(P') distance as a function of t
  let e : ℕ → ℝ → ℝ≥0∞ := fun m t => ∫⁻ ζ, ‖s94Flim ξ P' (Cm m) (u m) t ζ - F0 (t, ζ)‖ₑ ^ 2 ∂P'
  have hem : ∀ m, Measurable (e m) := fun m =>
    (((hΦ m).sub hF0m).enorm.pow_const 2).lintegral_prod_right' (ν := P')
  have hmeas_t : ∀ m t, AEStronglyMeasurable (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F0 (t, ζ)) P' := fun m t =>
    (((hΦ m).sub hF0m).comp (measurable_prodMk_left (x := t))).aestronglyMeasurable
  have he_eq : ∀ m t, e m t = eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F0 (t, ζ)) 2 P' ^ 2 :=
    fun m t => s94_lintegral_sq_eq (hmeas_t m t)
  have he_bd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ m, e m t ≤ ENNReal.ofReal (2 * C) ^ 2 := by
    intro t ht m
    rw [he_eq]
    refine pow_le_pow_left' ?_ 2
    have e1 : (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F0 (t, ζ)) =
        (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ) - (fun ζ => F0 (t, ζ)) := rfl
    rw [e1]
    refine (eLpNorm_sub_le (by norm_num)).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    have : ENNReal.ofReal 2 = 2 := by norm_num
    rw [this, two_mul, ← two_mul]
    calc _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add (hC t ht m) (hF0b t ht)
      _ = 2 * ENNReal.ofReal C := by rw [two_mul]
  have he_lim : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun m => e m t) atTop (𝓝 0) := by
    intro t ht
    have h1 := ((ENNReal.continuous_pow 2).tendsto 0).comp (hF0 t ht).2
    simp only [Function.comp_def, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    exact (tendsto_congr fun m => he_eq m t).2 h1
  have hfin : ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (2 * C) ^ 2 ≠ ⊤ := by
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by simp)
  have hDCT : Tendsto (fun m => ∫⁻ t in Set.Icc (0 : ℝ) T, e m t) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := e) (f := fun _ => 0) (fun _ => ENNReal.ofReal (2 * C) ^ 2) hem
      (fun m => (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => he_bd t ht m)) hfin
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ he_lim))
    simpa using this
  have hIfin : ∀ m, ∫⁻ t in Set.Icc (0 : ℝ) T, e m t ≠ ⊤ := fun m =>
    ne_top_of_le_ne_top hfin (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2
      (ae_of_all _ fun t ht => he_bd t ht m)))
  -- the modification of F0 on the null set where `∫ F0² dt = ∞`
  let I : Ω' → ℝ≥0∞ := fun ζ => ∫⁻ t in Set.Icc (0 : ℝ) T, ‖F0 (t, ζ)‖ₑ ^ 2 ∂volume
  have hIm : Measurable I := ((hF0m.enorm.pow_const 2).comp measurable_swap).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) T))
  have hIswap : ∫⁻ ζ, I ζ ∂P' = ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ, ‖F0 (t, ζ)‖ₑ ^ 2 ∂P' :=
    lintegral_lintegral_swap ((hF0m.enorm.pow_const 2).comp measurable_swap).aemeasurable
  have hIbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ‖F0 (t, ζ)‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal C ^ 2 := by
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
  have hFlim : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun m => eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F t ζ) 2 P')
      atTop (𝓝 0) := by
    intro t ht
    refine (tendsto_congr fun m => ?_).2 (hF0 t ht).2
    exact (eLpNorm_congr_ae (by filter_upwards [hFeq t] with ζ hζ; simp [hζ])).symm
  refine ⟨F, hFm, hF2, fun a ha t ht => ?_, fun m => (∫⁻ t in Set.Icc (0 : ℝ) T, e m t).toReal, fun m => ENNReal.toReal_nonneg,
    ?_, ?_⟩
  · exact s94_wick_clause hd hs0 hs hρ hset hcov hΛ0 ha hker hu hCs hA ht (hFt2 t ht) (hFlim t ht)
  · have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDCT
    rw [ENNReal.toReal_zero] at this
    exact this
  · intro m
    have hDm : Measurable fun q : ℝ × Ω' => ‖s94Flim ξ P' (Cm m) (u m) q.1 q.2 - F q.1 q.2‖ₑ ^ 2 :=
      (((hΦ m).sub hFm).enorm.pow_const 2)
    have hswap : ∫⁻ ζ', ∫⁻ t in Set.Icc (0 : ℝ) T, ‖s94Flim ξ P' (Cm m) (u m) t ζ' - F t ζ'‖ₑ ^ 2 ∂volume ∂P' =
        ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ', ‖s94Flim ξ P' (Cm m) (u m) t ζ' - F t ζ'‖ₑ ^ 2 ∂P' :=
      lintegral_lintegral_swap (hDm.comp measurable_swap).aemeasurable
    beta_reduce
    have hcongr : ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ', ‖s94Flim ξ P' (Cm m) (u m) t ζ' - F t ζ'‖ₑ ^ 2 ∂P' =
        ∫⁻ t in Set.Icc (0 : ℝ) T, e m t :=
      setLIntegral_congr_fun measurableSet_Icc fun t ht => lintegral_congr_ae (by
        filter_upwards [hFeq t] with ζ hζ
        simp [hζ])
    rw [hswap, hcongr, ENNReal.ofReal_toReal (hIfin m)]

end FullF

end HRS.MS.R2Chaos
