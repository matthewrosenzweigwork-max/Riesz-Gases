import HRS.MS.R2ChaosAux3

/-!
# HRS.MS.R2ChaosAux4 -- consequences of `IsRound2PathSetting`: a.s. linearity of `ξ`, Gaussian families, covariance form

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

/-! ### Test functions -/

theorem s94_test_continuous {a : Euc d → ℝ} (ha : IsR2Test a) : Continuous a := ha.1.continuous

theorem s94_test_bounded {a : Euc d → ℝ} (ha : IsR2Test a) : ∃ C : ℝ, ∀ x, |a x| ≤ C := by
  obtain ⟨C, hC⟩ := ha.2.exists_bound_of_continuous (s94_test_continuous ha)
  exact ⟨C, fun x => by simpa using hC x⟩

theorem s94_test_integrable {a : Euc d → ℝ} (ha : IsR2Test a) (μ : Measure (Euc d)) [IsFiniteMeasure μ] :
    Integrable a μ := by
  obtain ⟨C, hC⟩ := s94_test_bounded ha
  exact Integrable.of_bound (s94_test_continuous ha).aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa using hC x)

theorem s94_hasCompactSupport_sum {n : ℕ} {f : Fin n → Euc d → ℝ} (hf : ∀ i, HasCompactSupport (f i))
    (s : Finset (Fin n)) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert j s hj ih =>
    simp_rw [Finset.sum_insert hj]
    exact (hf j).add ih

theorem s94_test_lincomb {n : ℕ} {a : Fin n → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) (c : Fin n → ℝ) :
    IsR2Test (fun x => ∑ i, c i * a i x) := by
  constructor
  · exact ContDiff.sum fun i _ => contDiff_const.mul (ha i).1
  · exact s94_hasCompactSupport_sum (fun i => (ha i).2.mul_left (f := fun _ => c i)) Finset.univ

/-! ### Linearity of the empirical fluctuations -/

theorem s94_pair_lincomb (μ : Measure (Euc d)) [IsFiniteMeasure μ] {n : ℕ} {a : Fin n → Euc d → ℝ}
    (ha : ∀ i, IsR2Test (a i)) (c : Fin n → ℝ) :
    Whole.pair μ (fun x => ∑ i, c i * a i x) = ∑ i, c i * Whole.pair μ (a i) := by
  unfold Whole.pair
  rw [integral_finset_sum _ fun i _ => (s94_test_integrable (ha i) μ).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem s94_empFluct_lincomb (μ : Measure (Euc d)) [IsFiniteMeasure μ] {Ω : Type*} {N : ℕ}
    (X : ℝ≥0 → Ω → EucConfig d N) {n : ℕ} {a : Fin n → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (c : Fin n → ℝ) (ζ : Ω) (t : ℝ) :
    r2EmpFluct μ (fun x => ∑ i, c i * a i x) X ζ t = ∑ i, c i * r2EmpFluct μ (a i) X ζ t := by
  unfold r2EmpFluct
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · simp_rw [Whole.pair_empirical hN]
    rw [s94_pair_lincomb μ ha]
    have e : ∑ j, ∑ i, c i * a i (X t.toNNReal ζ j) = ∑ i, c i * ∑ j, a i (X t.toNNReal ζ j) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [e]
    have e2 : ∀ i, c i * (Real.sqrt N * ((N : ℝ)⁻¹ * ∑ j, a i (X t.toNNReal ζ j) - Whole.pair μ (a i))) =
        Real.sqrt N * ((N : ℝ)⁻¹ * (c i * ∑ j, a i (X t.toNNReal ζ j))) - Real.sqrt N * (c i * Whole.pair μ (a i)) :=
      fun i => by ring
    simp_rw [e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring

theorem s94_empFluct_continuous (μ : Measure (Euc d)) {Ω : Type*} {N : ℕ} (X : ℝ≥0 → Ω → EucConfig d N)
    {a : Euc d → ℝ} (ha : IsR2Test a) (ζ : Ω) (hX : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) :
    Continuous fun t : ℝ => r2EmpFluct μ a X ζ t := by
  unfold r2EmpFluct
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul]
    exact continuous_const
  · simp_rw [Whole.pair_empirical hN]
    have hac := s94_test_continuous ha
    refine continuous_const.mul ((continuous_const.mul (continuous_finset_sum _ fun i _ => ?_)).sub
      continuous_const)
    exact hac.comp ((hX i).comp continuous_real_toNNReal)

theorem s94_contPath_lincomb {T : ℝ} {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : ∀ i, Continuous (f i))
    (c : Fin n → ℝ) :
    r2ContPath T (fun t => ∑ i, c i * f i t) = ∑ i, c i • r2ContPath T (f i) := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => ∑ i, c i * f i t :=
    (continuous_finset_sum _ fun i _ => continuous_const.mul ((hf i).comp continuous_subtype_val))
  rw [s94_r2ContPath_eq hc]
  ext t
  show (∑ i, c i * f i t) = (∑ i, c i • r2ContPath T (f i)) t
  rw [ContinuousMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousMap.smul_apply, s94_r2ContPath_eq ((hf i).comp continuous_subtype_val)]
  rfl

/-! ### A.s. linearity of the limit field -/

section Setting

variable {s T b p K : ℝ} {μ : Measure (Euc d)} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_xi_lincomb (hset : IsRound2PathSetting d s T b p K μ P X P' ξ) [IsFiniteMeasure μ] {n : ℕ}
    {a : Fin n → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) (c : Fin n → ℝ) :
    ∀ᵐ ζ ∂P', ξ (fun x => ∑ i, c i * a i x) ζ = ∑ i, c i • ξ (a i) ζ := by
  set aa : Fin (n + 1) → Euc d → ℝ :=
    Fin.snoc (α := fun _ => Euc d → ℝ) a (fun x => ∑ i, c i * a i x) with haa
  have haa_last : aa (Fin.last n) = fun x => ∑ i, c i * a i x := by simp [haa]
  have haa_cast : ∀ i, aa (Fin.castSucc i) = a i := fun i => by simp [haa]
  have haa_test : ∀ j, IsR2Test (aa j) := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [haa_last]; exact s94_test_lincomb ha c
    · rw [haa_cast]; exact ha i
  have hconv := hset.conv (n + 1) aa haa_test
  set S : Set (Fin (n + 1) → C(Set.Icc (0 : ℝ) T, ℝ)) :=
    {w | w (Fin.last n) = ∑ i, c i • w (Fin.castSucc i)} with hS
  have hSc : IsClosed S :=
    isClosed_eq (continuous_apply _) (continuous_finset_sum _ fun i _ => (continuous_apply (Fin.castSucc i)).const_smul (c i))
  have hSm : MeasurableSet S := hSc.measurableSet
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv.tendsto hSc
  have hpre : ∀ N, (((⟨(P N).map (fun ζ i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ)),
      inferInstance⟩ : ProbabilityMeasure _) : Measure _) S) = 1 := by
    intro N
    show ((P N).map (fun ζ i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ))) S = 1
    rw [Measure.map_apply_of_aemeasurable (hconv.forall_aemeasurable N) hSm]
    have hae : ∀ᵐ ζ ∂(P N), ζ ∈ (fun ζ i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ)) ⁻¹' S := by
      filter_upwards [hset.contX N] with ζ hζ
      show r2ContPath T (r2EmpFluct μ (aa (Fin.last n)) (X N) ζ) =
        ∑ i, c i • r2ContPath T (r2EmpFluct μ (aa (Fin.castSucc i)) (X N) ζ)
      simp_rw [haa_last, haa_cast]
      have hf : ∀ i, Continuous fun t : ℝ => r2EmpFluct μ (a i) (X N) ζ t := fun i =>
        s94_empFluct_continuous μ (X N) (ha i) ζ hζ
      have e : r2EmpFluct μ (fun x => ∑ i, c i * a i x) (X N) ζ =
          fun t => ∑ i, c i * r2EmpFluct μ (a i) (X N) ζ t := funext fun t =>
        s94_empFluct_lincomb μ (X N) ha c ζ t
      have := s94_contPath_lincomb (T := T) (fun i t => r2EmpFluct μ (a i) (X N) ζ t) hf c
      rw [e]
      exact this
    refine le_antisymm prob_le_one ?_
    have := measure_univ_le_add_compl (μ := P N) ((fun ζ i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ)) ⁻¹' S)
    have hc0 : (P N) ((fun ζ i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ)) ⁻¹' S)ᶜ = 0 := ae_iff.1 hae
    rw [hc0, add_zero, measure_univ] at this
    exact this
  replace hlim : (1 : ℝ≥0∞) ≤ _ :=
    (le_of_eq ((congrArg (fun f => limsup f atTop) (funext hpre)).trans (limsup_const 1)).symm).trans hlim
  have hmeas : Measurable fun ζ i => ξ (aa i) ζ := measurable_pi_iff.2 fun i => hset.measξ _
  have hS1 : P' ((fun ζ i => ξ (aa i) ζ) ⁻¹' S) = 1 := by
    have h1 : (((⟨P'.map fun ζ i => ξ (aa i) ζ, inferInstance⟩ : ProbabilityMeasure _) : Measure _) S) =
        P' ((fun ζ i => ξ (aa i) ζ) ⁻¹' S) := Measure.map_apply hmeas hSm
    exact le_antisymm prob_le_one (le_of_le_of_eq hlim h1)
  have := (prob_compl_eq_zero_iff (hmeas hSm)).2 hS1
  have hae : ∀ᵐ ζ ∂P', ζ ∈ (fun ζ i => ξ (aa i) ζ) ⁻¹' S := ae_iff.2 this
  filter_upwards [hae] with ζ hζ
  have h2 : ξ (aa (Fin.last n)) ζ = ∑ i, c i • ξ (aa (Fin.castSucc i)) ζ := hζ
  simpa [haa_last, haa_cast] using h2

theorem s94_pathEval_eq {w : C(Set.Icc (0 : ℝ) T, ℝ)} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    r2PathEval T w t = w ⟨t, ht⟩ := by
  unfold r2PathEval
  exact dif_pos ht

theorem s94_pathEval_lincomb {n : ℕ} (w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ)) (c : Fin n → ℝ) (t : ℝ) :
    r2PathEval T (∑ i, c i • w i) t = ∑ i, c i * r2PathEval T (w i) t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) T
  · simp only [s94_pathEval_eq ht, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  · unfold r2PathEval
    simp [ht]

/-- The Gaussian family `ξ(a_i)(t)` at a fixed time. -/
theorem s94_gfam_of_setting (hset : IsRound2PathSetting d s T b p K μ P X P' ξ) {n : ℕ}
    {a : Fin n → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    S94GFam P' (fun i ζ => r2PathEval T (ξ (a i) ζ) t) := by
  have hmeasEval : ∀ x, Measurable fun ζ => r2PathEval T (ξ x ζ) t := fun x => by
    have : (fun ζ => r2PathEval T (ξ x ζ) t) = fun ζ => (ContinuousMap.evalCLM ℝ (⟨t, ht⟩ : Set.Icc (0 : ℝ) T)) (ξ x ζ) := by
      funext ζ
      rw [s94_pathEval_eq ht]
      rfl
    rw [this]
    exact (ContinuousMap.evalCLM ℝ (⟨t, ht⟩ : Set.Icc (0 : ℝ) T)).continuous.measurable.comp (hset.measξ x)
  refine ⟨fun i => (hmeasEval (a i)).aemeasurable, fun α => ?_⟩
  have hG := hset.gaussian n a ha
  set L : (Fin n → C(Set.Icc (0 : ℝ) T, ℝ)) →L[ℝ] ℝ :=
    ∑ i, α i • ((ContinuousMap.evalCLM ℝ (⟨t, ht⟩ : Set.Icc (0 : ℝ) T)).comp
      (ContinuousLinearMap.proj i)) with hL
  have hLapp : ∀ w, L w = ∑ i, α i * w i ⟨t, ht⟩ := fun w => by
    simp [hL]
  have hvec : Measurable fun ζ i => ξ (a i) ζ := measurable_pi_iff.2 fun i => hset.measξ _
  have hmap : P'.map (fun ζ => ∑ i, α i * r2PathEval T (ξ (a i) ζ) t) =
      (P'.map fun ζ i => ξ (a i) ζ).map L := by
    rw [Measure.map_map L.continuous.measurable hvec]
    congr 1
    funext ζ
    simp only [Function.comp, hLapp, s94_pathEval_eq ht]
  have hmean : ∫ z, L z ∂(P'.map fun ζ i => ξ (a i) ζ) = 0 := hG.2 L
  haveI : IsGaussian (P'.map fun ζ i => ξ (a i) ζ) := hG.1
  have hg := IsGaussian.map_eq_gaussianReal (μ := P'.map fun ζ i => ξ (a i) ζ) L
  refine ⟨(ProbabilityTheory.variance L (P'.map fun ζ i => ξ (a i) ζ)).toNNReal, ?_⟩
  rw [hmap, hg, hmean]

end Setting

theorem s94_projMean_lincomb (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {n : ℕ} {a : Fin n → Euc d → ℝ}
    (ha : ∀ i, IsR2Test (a i)) (c : Fin n → ℝ) (x : Euc d) :
    Whole.projMean μ (fun x => ∑ i, c i * a i x) x = ∑ i, c i * Whole.projMean μ (a i) x := by
  unfold Whole.projMean
  rw [s94_pair_lincomb μ ha]
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem s94_integrable_projMean_mul (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {a b : Euc d → ℝ}
    (ha : IsR2Test a) (hb : IsR2Test b) :
    Integrable (fun x => Whole.projMean μ a x * Whole.projMean μ b x) μ := by
  obtain ⟨Ca, hCa⟩ := s94_test_bounded ha
  obtain ⟨Cb, hCb⟩ := s94_test_bounded hb
  have hma : Continuous (Whole.projMean μ a) := (s94_test_continuous ha).sub continuous_const
  have hmb : Continuous (Whole.projMean μ b) := (s94_test_continuous hb).sub continuous_const
  refine Integrable.of_bound (hma.mul hmb).aestronglyMeasurable ((Ca + |Whole.pair μ a|) * (Cb + |Whole.pair μ b|))
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |Whole.projMean μ a x| ≤ Ca + |Whole.pair μ a| := by
    unfold Whole.projMean; exact (abs_sub _ _).trans (by linarith [hCa x])
  have h2 : |Whole.projMean μ b x| ≤ Cb + |Whole.pair μ b| := by
    unfold Whole.projMean; exact (abs_sub _ _).trans (by linarith [hCb x])
  exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith [(abs_nonneg (a x)).trans (hCa x), abs_nonneg (Whole.pair μ a)])

theorem s94_projMean_sq_lincomb (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {n : ℕ} {a : Fin n → Euc d → ℝ}
    (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    (α : Fin n → ℝ) :
    ∫ x, (Whole.projMean μ (fun x => ∑ i, α i * a i x) x) ^ 2 ∂μ = ∑ i, α i ^ 2 := by
  have e : ∀ x, (Whole.projMean μ (fun x => ∑ i, α i * a i x) x) ^ 2 =
      ∑ i, ∑ j, (α i * α j) * (Whole.projMean μ (a i) x * Whole.projMean μ (a j) x) := fun x => by
    rw [s94_projMean_lincomb μ ha, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (s94_integrable_projMean_mul μ (ha i) (ha j)).const_mul (α i * α j)]
  have : ∀ i, ∫ x, ∑ j, (α i * α j) * (Whole.projMean μ (a i) x * Whole.projMean μ (a j) x) ∂μ = α i ^ 2 := by
    intro i
    rw [integral_finset_sum _ fun j _ => (s94_integrable_projMean_mul μ (ha i) (ha j)).const_mul (α i * α j)]
    simp_rw [integral_const_mul, hon]
    simp [sq]
  simp_rw [this]

section Setting2

variable {s T b p K : ℝ} {μ : Measure (Euc d)} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

/-- The covariance bound of the setting, transported to the coordinates of an orthonormal family. -/
theorem s94_q_le (hset : IsRound2PathSetting d s T b p K μ P X P' ξ) [IsProbabilityMeasure μ] {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean μ a x) ^ 2 ∂μ)
    (hΛ0 : 0 ≤ Λ) {n : ℕ} {a : Fin n → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (α : Fin n → ℝ) :
    s94q P' (fun i ζ => r2PathEval T (ξ (a i) ζ) t) α ≤ Λ * ∑ i, α i ^ 2 := by
  have hlin := s94_xi_lincomb hset ha α
  have h1 : s94q P' (fun i ζ => r2PathEval T (ξ (a i) ζ) t) α =
      ∫ ζ, (r2PathEval T (ξ (fun x => ∑ i, α i * a i x) ζ) t) ^ 2 ∂P' := by
    unfold s94q
    refine integral_congr_ae ?_
    filter_upwards [hlin] with ζ hζ
    rw [hζ, s94_pathEval_lincomb]
    rfl
  rw [h1]
  refine (hcov t ht _ (s94_test_lincomb ha α)).trans ?_
  rw [s94_projMean_sq_lincomb μ ha hon]

end Setting2

end HRS.MS.R2Chaos
