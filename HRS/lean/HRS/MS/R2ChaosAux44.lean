import HRS.MS.R2ChaosAux43

/-!
# HRS.MS.R2ChaosAux44 -- (d): the Wick-chaos clause for every orthonormal basis

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_wick_clause`: if `F(t,·) ∈ L²(P')` is the `L²(P')`-limit of the finite-rank Gaussian integrands `Φ_m(t,·)`, then `2F(t,·)` is the
Wick chaos of `cen(h_t)` for EVERY orthonormal basis `a` (chaos of `cen FR_m` is `2Φ_m` for `a`, the chaos is `Λ`-Lipschitz in the kernel,
`cen` is `4`-bounded, and `L²` limits are unique).
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

section WickClause

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_wick_clause (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean (Whole.withDensityReal ρ) a x) ^ 2 ∂(Whole.withDensityReal ρ))
    (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : IsR2ZeroMeanONB (Whole.withDensityReal ρ) a) {B C₁ : ℝ}
    {h : ℝ → Euc d → Euc d → ℝ} (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t))
    {n : ℕ → ℕ} {u : ∀ m, Fin (n m) → Euc d → ℝ} {Cm : ∀ m, ℝ → Fin (n m) → Fin (n m) → ℝ}
    (hu : ∀ m a, IsR2Test (u m a)) (hCs : ∀ m t a b, Cm m t a b = Cm m t b a)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T, IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h t)
      (fun m => r2FiniteRankKernel (Cm m t) (u m)))
    {F : ℝ → Ω' → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (hFm : MemLp (fun ζ => F t ζ) 2 P')
    (hFl : Tendsto (fun m => eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F t ζ) 2 P') atTop (𝓝 0)) :
    IsR2WickChaos P' (Whole.withDensityReal ρ) a (fun i ζ => r2PathEval T (ξ (a i) ζ) t)
      (r2CenterKernel (Whole.withDensityReal ρ) (h t)) (fun ζ => 2 * F t ζ) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  set μ := Whole.withDensityReal ρ with hμ
  set ν := μ.prod μ with hν
  obtain ⟨ha0, hon, hcomplete⟩ := ha
  have hz := s94_gseq_of_setting hset hcov hΛ0 ha0 hon ht
  obtain ⟨Qs, hQs⟩ := s94_wick_env_exists hd hs0 hs hρ hset hcov hΛ0 ha0 hon (hker t ht) ht
  let Qm : ∀ m, Ω' → ℝ := fun m ζ => ∑ α, ∑ β, Cm m t α β * (r2PathEval T (ξ (u m α) ζ) t *
    r2PathEval T (ξ (u m β) ζ) t - ∫ ζ', r2PathEval T (ξ (u m α) ζ') t * r2PathEval T (ξ (u m β) ζ') t ∂P')
  have hch : ∀ m, s94WickL2 P' μ a (fun i ζ => r2PathEval T (ξ (a i) ζ) t)
      (r2CenterKernel μ (r2FiniteRankKernel (Cm m t) (u m))) (Qm m) := fun m =>
    s94_wick_finiteRank hset hcov hΛ0 ha0 hon hcomplete (Cm m t) (hu m) ht
  have hF : ∀ m ζ, s94Flim ξ P' (Cm m) (u m) t ζ = (1 / 2) * Qm m ζ := by
    intro m ζ
    unfold s94Flim
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  have hbd : ∀ m, IsBoundedPairKernel s (C₁ * B) (r2FiniteRankKernel (Cm m t) (u m)) := fun m =>
    s94_approx_bounded (hA t ht) m
  let D : ℕ → ℝ≥0∞ := fun m => eLpNorm (fun q : Euc d × Euc d => h t q.1 q.2 -
    r2FiniteRankKernel (Cm m t) (u m) q.1 q.2) 2 ν
  have hDlim : Tendsto D atTop (𝓝 0) := by
    have := (hA t ht).converges 2 (by norm_num) (by linarith [(by exact_mod_cast hd : (2 : ℝ) ≤ d)])
    have e : ∀ m, D m = eLpNorm (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m t) (u m) q.1 q.2 -
        h t q.1 q.2) (ENNReal.ofReal 2) ν := by
      intro m
      have e2 : ENNReal.ofReal 2 = 2 := by norm_num
      rw [e2]
      exact eLpNorm_sub_comm (fun q : Euc d × Euc d => h t q.1 q.2) _ 2 ν
    exact (tendsto_congr e).2 this
  -- Lipschitz estimate: ‖Qs - Qm‖ ≤ c0 * D m
  set c0 : ℝ := Real.sqrt 2 * Λ * 4 with hc0
  have hkey : ∀ m, eLpNorm (fun ζ => Qs ζ - Qm m ζ) 2 P' ≤ ENNReal.ofReal c0 * D m := by
    intro m
    have hmh := (hker t ht).measurable
    have hm1 := s94_finiteRank_measurable (c := Cm m t) (u := u m) (hu m)
    have hlD : MemLp (fun q : Euc d × Euc d => h t q.1 q.2 - r2FiniteRankKernel (Cm m t) (u m) q.1 q.2) 2 ν :=
      (s94_env_memLp hd hs0 hs hρ (hker t ht)).sub (s94_finiteRank_memLp (hu m))
    have hDfin : D m ≠ ⊤ := hlD.eLpNorm_ne_top
    have hlip := s94_wick_lipschitz hz hΛ0 ha0 hon
      (s94_center_measurable (μ := μ) hmh) (s94_center_symm (hker t ht).symm)
      (s94_center_memLp hd hs0 hs hρ (hker t ht))
      (s94_center_measurable (μ := μ) hm1) (s94_center_symm (s94_finiteRank_symm (hCs m t)))
      (s94_center_memLp hd hs0 hs hρ (hbd m)) hQs (hch m)
    have hcd : eLpNorm (fun q : Euc d × Euc d => r2CenterKernel μ (h t) q.1 q.2 -
        r2CenterKernel μ (r2FiniteRankKernel (Cm m t) (u m)) q.1 q.2) 2 ν ≤ ENNReal.ofReal (4 * (D m).toReal) := by
      refine (s94_center_diff_le hd hs0 hs hρ (hker t ht) (hu m)).trans ?_
      have e4 : ENNReal.ofReal 4 = 4 := by norm_num
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hDfin, e4]
    have hsq := s94_integral_sq_le_of_eLpNorm
      ((((s94_center_measurable (μ := μ) hmh).sub (s94_center_measurable (μ := μ) hm1))).aestronglyMeasurable)
      (by positivity) hcd
    have hQQ : eLpNorm (fun ζ => Qs ζ - Qm m ζ) 2 P' ≤ ENNReal.ofReal (Real.sqrt 2 * Λ * (4 * (D m).toReal)) := by
      refine s94_eLpNorm_le_of_sq (hQs.1.sub (hch m).1) (by positivity) ?_
      calc _ ≤ 2 * Λ ^ 2 * ∫ q, (r2CenterKernel μ (h t) q.1 q.2 -
            r2CenterKernel μ (r2FiniteRankKernel (Cm m t) (u m)) q.1 q.2) ^ 2 ∂ν := hlip
        _ ≤ 2 * Λ ^ 2 * (4 * (D m).toReal) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (Real.sqrt 2 * Λ * (4 * (D m).toReal)) ^ 2 := by
          rw [show (Real.sqrt 2 * Λ * (4 * (D m).toReal)) ^ 2 = Real.sqrt 2 ^ 2 * Λ ^ 2 * (4 * (D m).toReal) ^ 2 by ring,
            Real.sq_sqrt (by norm_num)]
    refine hQQ.trans (le_of_eq ?_)
    rw [show Real.sqrt 2 * Λ * (4 * (D m).toReal) = c0 * (D m).toReal by rw [hc0]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hDfin]
  have hu0 : Tendsto (fun m => ENNReal.ofReal c0 * D m) atTop (𝓝 0) := by
    have : Tendsto (fun m => ENNReal.ofReal c0 * D m) atTop (𝓝 (ENNReal.ofReal c0 * 0)) :=
      ENNReal.Tendsto.const_mul hDlim (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  -- 2F is the L² limit of 2 Φ_m, hence equals Qs a.e.
  have hFm2 : MemLp (fun ζ => 2 * F t ζ) 2 P' := hFm.const_mul 2
  have h2F : ∀ m, eLpNorm (fun ζ => 2 * F t ζ - Qm m ζ) 2 P' =
      2 * eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F t ζ) 2 P' := by
    intro m
    have e : (fun ζ => 2 * F t ζ - Qm m ζ) = (-2 : ℝ) • (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F t ζ) := by
      funext ζ
      simp only [hF, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, eLpNorm_const_smul]
    congr 1
    rw [← ofReal_norm_eq_enorm]
    norm_num
  have hbound : ∀ m, eLpNorm (fun ζ => 2 * F t ζ - Qs ζ) 2 P' ≤
      2 * eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F t ζ) 2 P' + ENNReal.ofReal c0 * D m := by
    intro m
    have e : (fun ζ => 2 * F t ζ - Qs ζ) = (fun ζ => 2 * F t ζ - Qm m ζ) - (fun ζ => Qs ζ - Qm m ζ) := by
      funext ζ; simp only [Pi.sub_apply]; ring
    rw [e]
    refine (eLpNorm_sub_le (by norm_num)).trans ?_
    rw [h2F m]
    gcongr
    exact hkey m
  have hz0 : eLpNorm (fun ζ => 2 * F t ζ - Qs ζ) 2 P' = 0 := by
    refine le_antisymm ?_ bot_le
    have hlim : Tendsto (fun m => 2 * eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F t ζ) 2 P' +
        ENNReal.ofReal c0 * D m) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m => 2 * eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F t ζ) 2 P') atTop
          (𝓝 (2 * 0)) := ENNReal.Tendsto.const_mul hFl (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      simpa using h1.add hu0
    exact ge_of_tendsto' hlim hbound
  have hae : (fun ζ => 2 * F t ζ) =ᵐ[P'] Qs := by
    have := (eLpNorm_eq_zero_iff (by norm_num)).1 hz0
    filter_upwards [this] with ζ hζ
    simpa [sub_eq_zero] using hζ
  have hW : s94WickL2 P' μ a (fun i ζ => r2PathEval T (ξ (a i) ζ) t) (r2CenterKernel μ (h t)) (fun ζ => 2 * F t ζ) := by
    refine ⟨hFm2, ?_⟩
    have := hQs.2
    refine this.congr fun n => ?_
    refine integral_congr_ae ?_
    filter_upwards [hae] with ζ hζ
    rw [hζ]
  exact hW.isWick hz

end WickClause

end HRS.MS.R2Chaos
