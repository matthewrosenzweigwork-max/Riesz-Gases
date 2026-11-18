import HRS.MS.R2ChaosAux19

/-!
# HRS.MS.R2ChaosAux20 -- the deterministic centering `m_N → m` in `L²([0,T])`

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

section PathJoint

variable {T : ℝ}

theorem s94_pathEval_joint_measurable :
    Measurable fun q : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ => r2PathEval T q.1 q.2 := by
  by_cases hT : 0 ≤ T
  · have : (fun q : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ => r2PathEval T q.1 q.2) =
        fun q => Set.indicator {q : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) T}
          (fun q => q.1 (Set.projIcc 0 T hT q.2)) q := by
      funext q
      by_cases ht : q.2 ∈ Set.Icc (0 : ℝ) T
      · rw [Set.indicator_of_mem (show q ∈ {q : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) T} from ht),
          s94_pathEval_eq ht]
        simp [Set.projIcc_of_mem hT ht]
      · rw [Set.indicator_of_notMem (show q ∉ {q : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) T} from ht)]
        unfold r2PathEval; simp [ht]
    rw [this]
    refine Measurable.indicator ?_ (measurableSet_Icc.preimage measurable_snd)
    have hc : Continuous fun q : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ => q.1 (Set.projIcc 0 T hT q.2) :=
      continuous_eval.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp continuous_snd))
    exact hc.measurable
  · have : (fun q : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ => r2PathEval T q.1 q.2) = fun _ => 0 := by
      funext q
      have ht : q.2 ∉ Set.Icc (0 : ℝ) T := fun h => hT (h.1.trans h.2)
      unfold r2PathEval; simp [ht]
    rw [this]
    exact measurable_const

theorem s94_Lp2_norm_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} (g : Lp ℝ 2 ν) :
    ‖g‖ ^ 2 = ∫ x, (g x) ^ 2 ∂ν := by
  have h := real_inner_self_eq_norm_sq g
  rw [← h, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp [sq]

theorem s94_dist_sq_r2L2Path {f f' : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hf' : MemLp f' 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    dist (r2L2Path T f) (r2L2Path T f') ^ 2 = ∫ t, (f t - f' t) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) T)) := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  rw [s94_r2L2Path_eq hf, s94_r2L2Path_eq hf']
  have hd : dist (hf.toLp f : Lp ℝ 2 μT) (hf'.toLp f') = ‖(hf.sub hf').toLp (f - f')‖ := by
    rw [dist_eq_norm, ← MemLp.toLp_sub]
  show dist (hf.toLp f : Lp ℝ 2 μT) (hf'.toLp f') ^ 2 = _
  rw [hd, s94_Lp2_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [(hf.sub hf').coeFn_toLp] with t ht
  rw [ht]
  rfl

theorem s94_dist_tendsto_of_dct (hT : 0 ≤ T) {fN : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hfN : ∀ N, Measurable (fN N))
    (hf : Measurable f) {K : ℝ} (hb : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, |fN N t| ≤ K)
    (hbf : ∀ t ∈ Set.Icc (0 : ℝ) T, |f t| ≤ K)
    (hconv : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun N => fN N t) atTop (𝓝 (f t))) :
    Tendsto (fun N => dist (r2L2Path T (fN N)) (r2L2Path T f)) atTop (𝓝 0) := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  haveI : IsFiniteMeasure μT := by constructor; simp [hμT]
  have hmem : ∀ N, MemLp (fN N) 2 μT := fun N =>
    MemLp.of_bound (hfN N).aestronglyMeasurable K
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => by simpa using hb N t ht))
  have hmemf : MemLp f 2 μT :=
    MemLp.of_bound hf.aestronglyMeasurable K
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => by simpa using hbf t ht))
  have hK : 0 ≤ K := by
    by_cases hT0 : 0 ≤ T
    · exact (abs_nonneg _).trans (hbf 0 ⟨le_rfl, hT0⟩)
    · exact absurd hT hT0
  have hint : Tendsto (fun N => ∫ t, (fN N t - f t) ^ 2 ∂μT) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μT) (F := fun N t => (fN N t - f t) ^ 2)
      (f := fun _ => (0 : ℝ)) (fun _ => (2 * K) ^ 2)
      (fun N => (((hfN N).sub hf).pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun N => (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => by
        rw [Real.norm_eq_abs, abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        calc |fN N t - f t| ≤ |fN N t| + |f t| := abs_sub _ _
          _ ≤ 2 * K := by linarith [hb N t ht, hbf t ht]))
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => by
        have := ((hconv t ht).sub_const (f t)).pow 2
        simpa using this))
    simpa using this
  have hsq : ∀ N, dist (r2L2Path T (fN N)) (r2L2Path T f) = Real.sqrt (∫ t, (fN N t - f t) ^ 2 ∂μT) := fun N => by
    rw [← s94_dist_sq_r2L2Path (hmem N) hmemf, Real.sqrt_sq dist_nonneg]
  simp_rw [hsq]
  have := (Real.continuous_sqrt.tendsto 0).comp hint
  rw [Real.sqrt_zero] at this
  exact this

end PathJoint

section MN

/-- The deterministic centering `m_N(t) = ∑_s coef_s(t) E[ξ_N^t(a_s) ξ_N^t(b_s)]`. -/
def s94mN {Ω0 : Type*} [MeasurableSpace Ω0] {N : ℕ} {S : Type*} [Fintype S] (μ : Measure (Euc d))
    (X0 : ℝ≥0 → Ω0 → EucConfig d N) (P0 : Measure Ω0) (coef : S → ℝ → ℝ) (ua ub : S → Euc d → ℝ) (t : ℝ) : ℝ :=
  ∑ s, coef s t * ∫ ζ, r2EmpFluct μ (ua s) X0 ζ t * r2EmpFluct μ (ub s) X0 ζ t ∂P0

/-- The limit `m(t) = ∑_s coef_s(t) E[ξ^t(a_s) ξ^t(b_s)]`. -/
def s94mL {T : ℝ} {Ω0 : Type*} [MeasurableSpace Ω0] {S : Type*} [Fintype S] (ξ0 : (Euc d → ℝ) → Ω0 → C(Set.Icc (0 : ℝ) T, ℝ))
    (P0 : Measure Ω0) (coef : S → ℝ → ℝ) (ua ub : S → Euc d → ℝ) (t : ℝ) : ℝ :=
  ∑ s, coef s t * ∫ ζ, r2PathEval T (ξ0 (ua s) ζ) t * r2PathEval T (ξ0 (ub s) ζ) t ∂P0

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94mN_measurable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {N : ℕ} {Ω0 : Type*} [MeasurableSpace Ω0]
    (X0 : ℝ≥0 → Ω0 → EucConfig d N) (hX : Measurable fun q : ℝ≥0 × Ω0 => X0 q.1 q.2) (P0 : Measure Ω0)
    [IsProbabilityMeasure P0] {S : Type*} [Fintype S] {coef : S → ℝ → ℝ} (hm : ∀ s, Measurable (coef s))
    {ua ub : S → Euc d → ℝ} (hua : ∀ s, IsR2Test (ua s)) (hub : ∀ s, IsR2Test (ub s)) :
    Measurable (s94mN μ X0 P0 coef ua ub) := by
  unfold s94mN
  refine Finset.measurable_sum _ fun s _ => (hm s).mul ?_
  have h1 := s94_empFluct_measurable (μ := μ) (N := N) (hua s) X0 hX
  have h2 := s94_empFluct_measurable (μ := μ) (N := N) (hub s) X0 hX
  have h3 : Measurable fun q : ℝ × Ω0 => r2EmpFluct μ (ua s) X0 q.2 q.1 * r2EmpFluct μ (ub s) X0 q.2 q.1 := h1.mul h2
  exact (h3.stronglyMeasurable.integral_prod_right' (ν := P0)).measurable

theorem s94mL_measurable {Ω0 : Type*} [MeasurableSpace Ω0] (ξ0 : (Euc d → ℝ) → Ω0 → C(Set.Icc (0 : ℝ) T, ℝ))
    (hξ : ∀ a, Measurable (ξ0 a)) (P0 : Measure Ω0) [IsProbabilityMeasure P0] {S : Type*} [Fintype S]
    {coef : S → ℝ → ℝ} (hm : ∀ s, Measurable (coef s)) (ua ub : S → Euc d → ℝ) :
    Measurable (s94mL ξ0 P0 coef ua ub) := by
  unfold s94mL
  refine Finset.measurable_sum _ fun s _ => (hm s).mul ?_
  have hj : ∀ a, Measurable fun q : ℝ × Ω0 => r2PathEval T (ξ0 a q.2) q.1 := fun a =>
    Measurable.comp (g := fun q : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ => r2PathEval T q.1 q.2)
      (f := fun q : ℝ × Ω0 => (ξ0 a q.2, q.1)) s94_pathEval_joint_measurable
      (((hξ a).comp measurable_snd).prodMk measurable_fst)
  have h3 : Measurable fun q : ℝ × Ω0 => r2PathEval T (ξ0 (ua s) q.2) q.1 * r2PathEval T (ξ0 (ub s) q.2) q.1 :=
    (hj _).mul (hj _)
  exact (h3.stronglyMeasurable.integral_prod_right' (ν := P0)).measurable

theorem s94_abs_integral_mul_le {Ω0 : Type*} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {f g : Ω0 → ℝ} (hf : Measurable f) (hg : Measurable g) {B1 B2 : ℝ} (hbf : ∀ ζ, |f ζ| ≤ B1)
    (hbg : ∀ ζ, |g ζ| ≤ B2) {D1 D2 : ℝ} (h1 : ∫ ζ, f ζ ^ 2 ∂P0 ≤ D1) (h2 : ∫ ζ, g ζ ^ 2 ∂P0 ≤ D2) :
    |∫ ζ, f ζ * g ζ ∂P0| ≤ (D1 + D2) / 2 := by
  have i1 : Integrable (fun ζ => f ζ ^ 2) P0 := Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (B1 ^ 2)
    (ae_of_all _ fun ζ => by rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hbf ζ) 2)
  have i2 : Integrable (fun ζ => g ζ ^ 2) P0 := Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable (B2 ^ 2)
    (ae_of_all _ fun ζ => by rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hbg ζ) 2)
  have i3 : Integrable (fun ζ => f ζ * g ζ) P0 := Integrable.of_bound (hf.mul hg).aestronglyMeasurable (B1 * B2)
    (ae_of_all _ fun ζ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hbf ζ) (hbg ζ) (abs_nonneg _) ((abs_nonneg _).trans (hbf ζ)))
  have h3 : ∫ ζ, f ζ * g ζ ∂P0 ≤ (D1 + D2) / 2 := by
    calc ∫ ζ, f ζ * g ζ ∂P0 ≤ ∫ ζ, ((1 / 2) * (f ζ ^ 2 + g ζ ^ 2)) ∂P0 :=
          integral_mono i3 ((i1.add i2).const_mul _) fun ζ => by nlinarith [sq_nonneg (f ζ - g ζ)]
      _ = (1 / 2) * (∫ ζ, f ζ ^ 2 ∂P0 + ∫ ζ, g ζ ^ 2 ∂P0) := by
          rw [integral_const_mul, integral_add i1 i2]
      _ ≤ (D1 + D2) / 2 := by linarith
  have h4 : -(∫ ζ, f ζ * g ζ ∂P0) ≤ (D1 + D2) / 2 := by
    rw [← integral_neg]
    calc ∫ ζ, -(f ζ * g ζ) ∂P0 ≤ ∫ ζ, ((1 / 2) * (f ζ ^ 2 + g ζ ^ 2)) ∂P0 :=
          integral_mono i3.neg ((i1.add i2).const_mul _) fun ζ => by nlinarith [sq_nonneg (f ζ + g ζ)]
      _ = (1 / 2) * (∫ ζ, f ζ ^ 2 ∂P0 + ∫ ζ, g ζ ^ 2 ∂P0) := by
          rw [integral_const_mul, integral_add i1 i2]
      _ ≤ (D1 + D2) / 2 := by linarith
  exact abs_le.2 ⟨by linarith, h3⟩

/-- The deterministic centering of a weighted sum of products of empirical fluctuations converges in `L²([0,T])`. -/
theorem s94_mN_tendsto (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 ≤ T)
    {S : Type*} [Fintype S] {coef : S → ℝ → ℝ} (hm : ∀ s, Measurable (coef s)) {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hbc : ∀ s t, |coef s t| ≤ K0) {ua ub : S → Euc d → ℝ} (hua : ∀ s, IsR2Test (ua s))
    (hub : ∀ s, IsR2Test (ub s)) :
    Tendsto (fun N => dist (r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) coef ua ub))
      (r2L2Path T (s94mL ξ P' coef ua ub))) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := s94_linear_moment hd hs0 hs hb hp hρ hset (r := 2) (by norm_num)
  choose Aa hAa using fun s => s94_test_bounded (hua s)
  choose Ab hAb using fun s => s94_test_bounded (hub s)
  set K1 : ℝ := ∑ s, K0 * (((|C * Aa s|) ^ 2 + (|C * Ab s|) ^ 2) / 2) with hK1
  have hK1' : 0 ≤ K1 := Finset.sum_nonneg fun s _ => by positivity
  have hbN : ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      |s94mN (Whole.withDensityReal ρ) (X N) (P N) coef ua ub t| ≤ K1 := by
    intro N hN t ht
    have hN0 : 0 < N := by omega
    unfold s94mN
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [abs_mul]
    have hE : |∫ ζ, r2EmpFluct (Whole.withDensityReal ρ) (ua s) (X N) ζ t *
        r2EmpFluct (Whole.withDensityReal ρ) (ub s) (X N) ζ t ∂(P N)| ≤ ((|C * Aa s|) ^ 2 + (|C * Ab s|) ^ 2) / 2 := by
      have hsq : ∀ (a : Euc d → ℝ) (A : ℝ) (ha : IsR2Test a), (∀ x, |a x| ≤ A) →
          ∫ ζ, (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t) ^ 2 ∂(P N) ≤ (|C * A|) ^ 2 := by
        intro a A ha hA
        have h1 := hC N hN t ht a A (s94_test_continuous ha).measurable hA
        have h2 : ENNReal.ofReal 2 = 2 := by norm_num
        rw [h2] at h1
        exact s94_integral_sq_le_of_eLpNorm
          (s94_empFluct_section_measurable ha (X N) (hset.measX N) t).aestronglyMeasurable (abs_nonneg _)
          (h1.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
      exact s94_abs_integral_mul_le (s94_empFluct_section_measurable (hua s) (X N) (hset.measX N) t)
        (s94_empFluct_section_measurable (hub s) (X N) (hset.measX N) t)
        (fun ζ => s94_abs_empFluct_le hN0 (X N) (hAa s) ζ t) (fun ζ => s94_abs_empFluct_le hN0 (X N) (hAb s) ζ t)
        (hsq _ _ (hua s) (hAa s)) (hsq _ _ (hub s) (hAb s))
    exact mul_le_mul (hbc s t) hE (abs_nonneg _) hK0
  have hconv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Tendsto (fun N => s94mN (Whole.withDensityReal ρ) (X N) (P N) coef ua ub t) atTop
        (𝓝 (s94mL ξ P' coef ua ub t)) := by
    intro t ht
    unfold s94mN s94mL
    exact tendsto_finset_sum _ fun s _ =>
      (s94_expect_tendsto hd hs0 hs hb hp hρ hset (hua s) (hub s) ht).const_mul (coef s t)
  have hbL : ∀ t ∈ Set.Icc (0 : ℝ) T, |s94mL ξ P' coef ua ub t| ≤ K1 := by
    intro t ht
    have h1 := (continuous_abs.tendsto _).comp (hconv t ht)
    exact le_of_tendsto h1 ((eventually_ge_atTop 2).mono fun N hN => hbN N hN t ht)
  have hm1 : ∀ N, Measurable (s94mN (Whole.withDensityReal ρ) (X N) (P N) coef ua ub) := fun N =>
    s94mN_measurable (X N) (hset.measX N) (P N) hm hua hub
  have hm2 : Measurable (s94mL ξ P' coef ua ub) := s94mL_measurable ξ hset.measξ P' hm ua ub
  have hshift := s94_dist_tendsto_of_dct hT (fN := fun N => s94mN (Whole.withDensityReal ρ) (X (N + 2)) (P (N + 2)) coef ua ub)
    (f := s94mL ξ P' coef ua ub) (fun N => hm1 (N + 2)) hm2 (K := K1) (fun N t ht => hbN (N + 2) (by omega) t ht)
    hbL (fun t ht => (hconv t ht).comp (tendsto_add_atTop_nat 2))
  exact (tendsto_add_atTop_iff_nat 2).1 hshift

/-- Uniform bounds for the deterministic centering. -/
theorem s94mN_bdd (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ)
    {S : Type*} [Fintype S] {coef : S → ℝ → ℝ} {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hbc : ∀ s t, |coef s t| ≤ K0) {ua ub : S → Euc d → ℝ} (hua : ∀ s, IsR2Test (ua s))
    (hub : ∀ s, IsR2Test (ub s)) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ (∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      |s94mN (Whole.withDensityReal ρ) (X N) (P N) coef ua ub t| ≤ K1) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, |s94mL ξ P' coef ua ub t| ≤ K1 := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := s94_linear_moment hd hs0 hs hb hp hρ hset (r := 2) (by norm_num)
  choose Aa hAa using fun s => s94_test_bounded (hua s)
  choose Ab hAb using fun s => s94_test_bounded (hub s)
  set K1 : ℝ := ∑ s, K0 * (((|C * Aa s|) ^ 2 + (|C * Ab s|) ^ 2) / 2) with hK1
  have hK1' : 0 ≤ K1 := Finset.sum_nonneg fun s _ => by positivity
  have hbN : ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      |s94mN (Whole.withDensityReal ρ) (X N) (P N) coef ua ub t| ≤ K1 := by
    intro N hN t ht
    have hN0 : 0 < N := by omega
    unfold s94mN
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [abs_mul]
    have hE : |∫ ζ, r2EmpFluct (Whole.withDensityReal ρ) (ua s) (X N) ζ t *
        r2EmpFluct (Whole.withDensityReal ρ) (ub s) (X N) ζ t ∂(P N)| ≤ ((|C * Aa s|) ^ 2 + (|C * Ab s|) ^ 2) / 2 := by
      have hsq : ∀ (a : Euc d → ℝ) (A : ℝ) (ha : IsR2Test a), (∀ x, |a x| ≤ A) →
          ∫ ζ, (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t) ^ 2 ∂(P N) ≤ (|C * A|) ^ 2 := by
        intro a A ha hA
        have h1 := hC N hN t ht a A (s94_test_continuous ha).measurable hA
        have h2 : ENNReal.ofReal 2 = 2 := by norm_num
        rw [h2] at h1
        exact s94_integral_sq_le_of_eLpNorm
          (s94_empFluct_section_measurable ha (X N) (hset.measX N) t).aestronglyMeasurable (abs_nonneg _)
          (h1.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
      exact s94_abs_integral_mul_le (s94_empFluct_section_measurable (hua s) (X N) (hset.measX N) t)
        (s94_empFluct_section_measurable (hub s) (X N) (hset.measX N) t)
        (fun ζ => s94_abs_empFluct_le hN0 (X N) (hAa s) ζ t) (fun ζ => s94_abs_empFluct_le hN0 (X N) (hAb s) ζ t)
        (hsq _ _ (hua s) (hAa s)) (hsq _ _ (hub s) (hAb s))
    exact mul_le_mul (hbc s t) hE (abs_nonneg _) hK0
  have hconv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Tendsto (fun N => s94mN (Whole.withDensityReal ρ) (X N) (P N) coef ua ub t) atTop
        (𝓝 (s94mL ξ P' coef ua ub t)) := by
    intro t ht
    unfold s94mN s94mL
    exact tendsto_finset_sum _ fun s _ =>
      (s94_expect_tendsto hd hs0 hs hb hp hρ hset (hua s) (hub s) ht).const_mul (coef s t)
  have hbL : ∀ t ∈ Set.Icc (0 : ℝ) T, |s94mL ξ P' coef ua ub t| ≤ K1 := by
    intro t ht
    have h1 := (continuous_abs.tendsto _).comp (hconv t ht)
    exact le_of_tendsto h1 ((eventually_ge_atTop 2).mono fun N hN => hbN N hN t ht)
  exact ⟨K1, hK1', hbN, hbL⟩

end MN

end HRS.MS.R2Chaos
