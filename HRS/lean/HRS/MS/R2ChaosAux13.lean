import HRS.MS.R2ChaosAux12

/-!
# HRS.MS.R2ChaosAux13 -- fixed-time Wick chaos of `(h_t)_c`: existence for every basis, basis independence

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
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

section Fixed

variable {s T b p K M L B : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_wick_env_exists (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean (Whole.withDensityReal ρ) a x) ^ 2 ∂(Whole.withDensityReal ρ))
    (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean (Whole.withDensityReal ρ) (a i) x * Whole.projMean (Whole.withDensityReal ρ) (a j) x
      ∂(Whole.withDensityReal ρ) = if i = j then 1 else 0)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ Q, s94WickL2 P' (Whole.withDensityReal ρ) a (fun i ζ => r2PathEval T (ξ (a i) ζ) t)
      (r2CenterKernel (Whole.withDensityReal ρ) h) Q := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hz := s94_gseq_of_setting hset hcov hΛ0 ha hon ht
  obtain ⟨Q, hQ, -⟩ := s94_wick_exists hz hΛ0 ha hon (k := r2CenterKernel (Whole.withDensityReal ρ) h)
    (s94_center_measurable hh.measurable) (s94_center_symm hh.symm) (s94_center_memLp hd hs0 hs hρ hh)
  exact ⟨Q, hQ⟩

/-- Basis independence of the fixed-time Wick chaos (any two bases give the same limit a.s.). -/
theorem s94_wick_env_unique (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean (Whole.withDensityReal ρ) a x) ^ 2 ∂(Whole.withDensityReal ρ))
    (hΛ0 : 0 ≤ Λ) {a a' : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) (ha' : ∀ i, IsR2Test (a' i))
    (hon : ∀ i j, ∫ x, Whole.projMean (Whole.withDensityReal ρ) (a i) x * Whole.projMean (Whole.withDensityReal ρ) (a j) x
      ∂(Whole.withDensityReal ρ) = if i = j then 1 else 0)
    (hon' : ∀ i j, ∫ x, Whole.projMean (Whole.withDensityReal ρ) (a' i) x * Whole.projMean (Whole.withDensityReal ρ) (a' j) x
      ∂(Whole.withDensityReal ρ) = if i = j then 1 else 0)
    (hcomplete : ∀ f : Euc d → ℝ, MemLp f 2 (Whole.withDensityReal ρ) → ∫ x, f x ∂(Whole.withDensityReal ρ) = 0 →
      (∀ i, ∫ x, f x * a i x ∂(Whole.withDensityReal ρ) = 0) → f =ᵐ[Whole.withDensityReal ρ] 0)
    (hcomplete' : ∀ f : Euc d → ℝ, MemLp f 2 (Whole.withDensityReal ρ) → ∫ x, f x ∂(Whole.withDensityReal ρ) = 0 →
      (∀ i, ∫ x, f x * a' i x ∂(Whole.withDensityReal ρ) = 0) → f =ᵐ[Whole.withDensityReal ρ] 0)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {Q Q' : Ω' → ℝ}
    (hQ : s94WickL2 P' (Whole.withDensityReal ρ) a (fun i ζ => r2PathEval T (ξ (a i) ζ) t)
      (r2CenterKernel (Whole.withDensityReal ρ) h) Q)
    (hQ' : s94WickL2 P' (Whole.withDensityReal ρ) a' (fun i ζ => r2PathEval T (ξ (a' i) ζ) t)
      (r2CenterKernel (Whole.withDensityReal ρ) h) Q') :
    Q =ᵐ[P'] Q' := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  set μ := Whole.withDensityReal ρ with hμ
  have hz := s94_gseq_of_setting hset hcov hΛ0 ha hon ht
  have hz' := s94_gseq_of_setting hset hcov hΛ0 ha' hon' ht
  obtain ⟨C, hC⟩ := HRS.Whole.U1.round2_approximation_proof hd s hs0 hs
  obtain ⟨hj, hA⟩ := hC M L ρ hρ B h hh
  choose m c u hdata hjeq using hA.finiteRank
  have hu : ∀ j α, IsR2Test (u j α) := fun j α => ⟨(hdata j).smooth α, (hdata j).compactSupport α⟩
  set e : ℕ → ℝ≥0∞ := fun j => eLpNorm (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2) (ENNReal.ofReal 2)
    (μ.prod μ) with he
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have he0 : Tendsto e atTop (𝓝 0) := hA.converges 2 (by norm_num) (by linarith)
  have hetop : ∀ᶠ j in atTop, e j < ⊤ := he0.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  set r : ℕ → ℝ := fun j => (e j).toReal with hr
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he0
    rw [ENNReal.toReal_zero] at this
    exact this
  -- key per-index estimate
  have key : ∀ j, e j < ⊤ → ∀ {a₁ : ℕ → Euc d → ℝ} (ha₁ : ∀ i, IsR2Test (a₁ i))
      (hon₁ : ∀ i j, ∫ x, Whole.projMean μ (a₁ i) x * Whole.projMean μ (a₁ j) x ∂μ = if i = j then 1 else 0)
      (hcomplete₁ : ∀ f : Euc d → ℝ, MemLp f 2 μ → ∫ x, f x ∂μ = 0 → (∀ i, ∫ x, f x * a₁ i x ∂μ = 0) → f =ᵐ[μ] 0)
      {Q₁ : Ω' → ℝ}, s94WickL2 P' μ a₁ (fun i ζ => r2PathEval T (ξ (a₁ i) ζ) t) (r2CenterKernel μ h) Q₁ →
      ∫ ζ, (Q₁ ζ - (∑ α, ∑ β, c j α β * (r2PathEval T (ξ (u j α) ζ) t * r2PathEval T (ξ (u j β) ζ) t -
        ∫ ζ', r2PathEval T (ξ (u j α) ζ') t * r2PathEval T (ξ (u j β) ζ') t ∂P'))) ^ 2 ∂P' ≤
        2 * Λ ^ 2 * (4 * r j) ^ 2 := by
    intro j hj1 a₁ ha₁ hon₁ hcomplete₁ Q₁ hQ₁
    have hz₁ := s94_gseq_of_setting hset hcov hΛ0 ha₁ hon₁ ht
    have hQj := s94_wick_finiteRank hset hcov hΛ0 ha₁ hon₁ hcomplete₁ (c j) (hu j) ht
    have hlip := s94_wick_lipschitz hz₁ hΛ0 ha₁ hon₁ (s94_center_measurable hh.measurable)
      (s94_center_symm hh.symm) (s94_center_memLp hd hs0 hs hρ hh)
      (s94_center_finiteRank_measurable (hu j)) (fun x y => s94_center_finiteRank_symm (hu j) ((hdata j).symm) x y)
      (s94_center_finiteRank_memLp (hu j)) hQ₁ hQj
    refine hlip.trans ?_
    have hdiff := s94_center_diff_le hd hs0 hs hρ hh (c := c j) (u := u j) (hu j)
    have hen : eLpNorm (fun q : Euc d × Euc d => h q.1 q.2 - r2FiniteRankKernel (c j) (u j) q.1 q.2) 2 (μ.prod μ) =
        e j := by
      rw [he, ← hjeq j]
      have : ENNReal.ofReal 2 = 2 := by norm_num
      rw [this]
      exact eLpNorm_sub_comm (fun q : Euc d × Euc d => h q.1 q.2)
        (fun q : Euc d × Euc d => hj j q.1 q.2) 2 (μ.prod μ)
    rw [hen] at hdiff
    have hej : e j = ENNReal.ofReal (r j) := by
      rw [hr]; exact (ENNReal.ofReal_toReal hj1.ne).symm
    have hr0' : 0 ≤ r j := ENNReal.toReal_nonneg
    have hle : eLpNorm (fun q : Euc d × Euc d => r2CenterKernel μ h q.1 q.2 -
        r2CenterKernel μ (r2FiniteRankKernel (c j) (u j)) q.1 q.2) 2 (μ.prod μ) ≤ ENNReal.ofReal (4 * r j) := by
      refine hdiff.trans ?_
      rw [hej, ENNReal.ofReal_mul (by norm_num)]
      simp
    have hmeasd : Measurable fun q : Euc d × Euc d => r2CenterKernel μ h q.1 q.2 -
        r2CenterKernel μ (r2FiniteRankKernel (c j) (u j)) q.1 q.2 :=
      (s94_center_measurable hh.measurable).sub (s94_center_finiteRank_measurable (hu j))
    have := s94_integral_sq_le_of_eLpNorm hmeasd.aestronglyMeasurable (by positivity) hle
    exact mul_le_mul_of_nonneg_left this (by positivity)
  -- conclusion
  have hQj : ∀ j, MemLp (fun ζ => ∑ α, ∑ β, c j α β * (r2PathEval T (ξ (u j α) ζ) t * r2PathEval T (ξ (u j β) ζ) t -
        ∫ ζ', r2PathEval T (ξ (u j α) ζ') t * r2PathEval T (ξ (u j β) ζ') t ∂P')) 2 P' := fun j =>
    (s94_wick_finiteRank hset hcov hΛ0 ha hon hcomplete (c j) (hu j) ht).1
  have hbd : ∀ᶠ j in atTop, ∫ ζ, (Q ζ - Q' ζ) ^ 2 ∂P' ≤ 4 * (2 * Λ ^ 2 * (4 * r j) ^ 2) := by
    filter_upwards [hetop] with j hj1
    have k1 := key j hj1 ha hon hcomplete hQ
    have k2 := key j hj1 ha' hon' hcomplete' hQ'
    set Qj := fun ζ => ∑ α, ∑ β, c j α β * (r2PathEval T (ξ (u j α) ζ) t * r2PathEval T (ξ (u j β) ζ) t -
        ∫ ζ', r2PathEval T (ξ (u j α) ζ') t * r2PathEval T (ξ (u j β) ζ') t ∂P') with hQjdef
    have i1 : Integrable (fun ζ => (Q ζ - Qj ζ) ^ 2) P' := (hQ.1.sub (hQj j)).integrable_sq
    have i2 : Integrable (fun ζ => (Q' ζ - Qj ζ) ^ 2) P' := (hQ'.1.sub (hQj j)).integrable_sq
    have i3 : Integrable (fun ζ => (Q ζ - Q' ζ) ^ 2) P' := (hQ.1.sub hQ'.1).integrable_sq
    calc ∫ ζ, (Q ζ - Q' ζ) ^ 2 ∂P' ≤ ∫ ζ, (2 * (Q ζ - Qj ζ) ^ 2 + 2 * (Q' ζ - Qj ζ) ^ 2) ∂P' := by
          refine integral_mono i3 ((i1.const_mul 2).add (i2.const_mul 2)) fun ζ => ?_
          nlinarith [sq_nonneg (Q ζ - Qj ζ + (Q' ζ - Qj ζ))]
      _ = 2 * ∫ ζ, (Q ζ - Qj ζ) ^ 2 ∂P' + 2 * ∫ ζ, (Q' ζ - Qj ζ) ^ 2 ∂P' := by
          rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
      _ ≤ 4 * (2 * Λ ^ 2 * (4 * r j) ^ 2) := by linarith
  have hlim : Tendsto (fun j => 4 * (2 * Λ ^ 2 * (4 * r j) ^ 2)) atTop (𝓝 (4 * (2 * Λ ^ 2 * (4 * 0) ^ 2))) :=
    (((hr0.const_mul 4).pow 2).const_mul (2 * Λ ^ 2)).const_mul 4
  have hz0 : ∫ ζ, (Q ζ - Q' ζ) ^ 2 ∂P' ≤ 0 := by
    have := ge_of_tendsto hlim hbd
    simpa using this
  have hnn : 0 ≤ ∫ ζ, (Q ζ - Q' ζ) ^ 2 ∂P' := integral_nonneg fun ζ => sq_nonneg _
  have hi0 : ∫ ζ, (Q ζ - Q' ζ) ^ 2 ∂P' = 0 := le_antisymm hz0 hnn
  have hi3 : Integrable (fun ζ => (Q ζ - Q' ζ) ^ 2) P' := (hQ.1.sub hQ'.1).integrable_sq
  have := (integral_eq_zero_iff_of_nonneg (fun ζ => sq_nonneg _) hi3).1 hi0
  filter_upwards [this] with ζ hζ
  have : (Q ζ - Q' ζ) ^ 2 = 0 := hζ
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

end Fixed

end HRS.MS.R2Chaos
