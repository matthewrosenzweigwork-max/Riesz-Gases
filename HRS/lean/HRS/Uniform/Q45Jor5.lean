import HRS.Uniform.Q45Jor4

/-!
# Q45 (Lemma 3.20): measurable Jordan decomposition of a trace density
-/

noncomputable section

open MeasureTheory Filter Topology HRS.HilbertCLTAux HRS.Uniform.Q07c
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Dens

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem jordan_density (T : ℝ) (D : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (hD : IsTraceDensityL1 T D) :
    ∃ Dp Dm : ℝ → H →L[ℝ] H →L[ℝ] ℝ, IsDetCovDensity T Dp ∧ IsDetCovDensity T Dm ∧
      (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x y, D r x y = Dp r x y - Dm r x y) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) T, traceNormForm (Dp r) + traceNormForm (Dm r) ≤ traceNormForm (D r)) := by
  classical
  obtain ⟨hsymm, hbdd, hmeas, hint⟩ := hD
  obtain ⟨ι₀, hι₀, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι₀
  set I : Set ℝ := Set.Icc (0 : ℝ) T with hI
  have hIm : MeasurableSet I := measurableSet_Icc
  set A : ℝ → H →L[ℝ] H := fun r => if r ∈ I then formOp (D r) else 0 with hA
  have hAI : ∀ r ∈ I, A r = formOp (D r) := fun r hr => by simp [hA, hr]
  have hA0 : ∀ r ∉ I, A r = 0 := fun r hr => by simp [hA, hr]
  have hAs : ∀ r x y, inner ℝ (A r x) y = inner ℝ x (A r y) := by
    intro r x y
    by_cases hr : r ∈ I
    · rw [hAI r hr, inner_formOp, real_inner_comm, inner_formOp, hsymm r]
    · rw [hA0 r hr]; simp
  have hAm : OpMeas A := by
    intro x
    refine measurable_of_inner_basis e (fun i => ?_)
    have : (fun r => inner ℝ (e i) (A r x)) = fun r => if r ∈ I then D r x (e i) else 0 := by
      funext r
      by_cases hr : r ∈ I
      · simp only [hr, if_true]; rw [hAI r hr, real_inner_comm, inner_formOp]
      · rw [if_neg hr, hA0 r hr]; simp
    rw [this]
    exact Measurable.ite hIm (hmeas _ _) measurable_const
  set tn : ℝ → ℝ := fun r => if r ∈ I then traceNormForm (D r) else 0 with htn
  have htnm : Measurable tn :=
    Measurable.ite hIm (measurable_traceNormForm (α := ℝ) D hmeas) measurable_const
  set c : ℝ → ℝ := fun r => tn r ^ 2 + 1 with hc
  have hcm : Measurable c := (htnm.pow_const 2).add_const 1
  have hcpos : ∀ r, 0 < c r := fun r => by simp only [hc]; positivity
  set AA : ℝ → H →L[ℝ] H := fun r => A r * A r with hAA
  have hAAp : ∀ r, IsPSDOp (AA r) := by
    intro r
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [hAA, ContinuousLinearMap.mul_apply]
      rw [hAs r (A r x) y, ← hAs r x (A r y)]
    · simp only [hAA, ContinuousLinearMap.mul_apply]
      rw [hAs r (A r x) x, real_inner_self_eq_norm_sq]
      positivity
  have hAAc : ∀ r x, inner ℝ (AA r x) x ≤ c r * ‖x‖ ^ 2 := by
    intro r x
    simp only [hAA, ContinuousLinearMap.mul_apply]
    rw [hAs r (A r x) x, real_inner_self_eq_norm_sq]
    have hnorm : ‖A r x‖ ≤ tn r * ‖x‖ := by
      by_cases hr : r ∈ I
      · rw [hAI r hr]; simp only [htn, hr, if_true]
        exact opNorm_formOp_le (hbdd r hr) x
      · rw [hA0 r hr]; simp only [htn, hr, if_false]; simp
    have h0 : 0 ≤ tn r := by
      by_cases hr : r ∈ I
      · simp only [htn, hr, if_true]; exact traceNormForm_nonneg _
      · simp [htn, hr]
    have : ‖A r x‖ ^ 2 ≤ (tn r * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    calc ‖A r x‖ ^ 2 ≤ (tn r * ‖x‖) ^ 2 := this
      _ = tn r ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ c r * ‖x‖ ^ 2 := by simp only [hc]; nlinarith [sq_nonneg ‖x‖]
  have hAAm : OpMeas AA := hAm.mul hAm
  set Sb : ℝ → H →L[ℝ] H := fun r => sqrtOp (c r) (AA r) with hSb
  have hSbm : OpMeas Sb := OpMeas.sqrtOp hAAm hcm hAAp hcpos hAAc
  have hspec : ∀ r, IsPSDOp (Sb r) ∧ Sb r * Sb r = AA r := fun r => sqrtOp_spec (hAAp r) (hcpos r) (hAAc r)
  set Dp : ℝ → H →L[ℝ] H →L[ℝ] ℝ := fun r =>
    if r ∈ I then (1 / 2 : ℝ) • (formOfOp (Sb r) + D r) else 0 with hDp
  set Dm : ℝ → H →L[ℝ] H →L[ℝ] ℝ := fun r =>
    if r ∈ I then (1 / 2 : ℝ) • (formOfOp (Sb r) - D r) else 0 with hDm
  -- pointwise structure on `I`
  have hpt : ∀ r ∈ I, IsTraceClassCov (Dp r) ∧ IsTraceClassCov (Dm r) ∧
      traceNormForm (Dp r) + traceNormForm (Dm r) ≤ traceNormForm (D r) := by
    intro r hr
    set S := Sb r with hS
    set Aop := formOp (D r) with hAop
    have hAsym : ∀ x y, inner ℝ (Aop x) y = inner ℝ x (Aop y) := by
      have := hAs r
      rwa [hAI r hr] at this
    have hSS : S * S = Aop * Aop := by
      have h0 : Sb r * Sb r = A r * A r := (hspec r).2
      rwa [hAI r hr] at h0
    have hSA : S * Aop = Aop * S := by
      have hcomm := sqrtOp_comm (hAAp r) (hcpos r) (hAAc r) (X := Aop) (by
        show Aop * (A r * A r) = (A r * A r) * Aop
        rw [hAI r hr]; exact (mul_assoc _ _ _).symm)
      exact hcomm.symm
    obtain ⟨hP, hN⟩ := isPSD_pn (hspec r).1 hAsym hSS hSA
    have hPN := pn_zero hSS hSA
    have hNP := np_zero hSS hSA
    have hDe : ∀ x y, D r x y = inner ℝ (((1 / 2 : ℝ) • (S + Aop) - (1 / 2 : ℝ) • (S - Aop)) x) y := by
      intro x y
      have : (1 / 2 : ℝ) • (S + Aop) - (1 / 2 : ℝ) • (S - Aop) = Aop := by
        ext z; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.add_apply]; module
      rw [this, hAop, inner_formOp]
    obtain ⟨h1, h2, h3⟩ := jordan_trace hP hN hPN hNP hDe (hbdd r hr)
    have e1 : Dp r = formOfOp ((1 / 2 : ℝ) • (S + Aop)) := by
      simp only [hDp, hr, if_true]
      refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, formOfOp_apply,
        inner_smul_left, inner_add_left, conj_trivial, hAop, inner_formOp, smul_eq_mul]
      rfl
    have e2 : Dm r = formOfOp ((1 / 2 : ℝ) • (S - Aop)) := by
      simp only [hDm, hr, if_true]
      refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, formOfOp_apply,
        inner_smul_left, inner_sub_left, conj_trivial, hAop, inner_formOp, smul_eq_mul]
      rfl
    rw [e1, e2]
    exact ⟨h1, h2, h3⟩
  have hDpm : ∀ x y, Measurable fun r => Dp r x y := by
    intro x y
    have : (fun r => Dp r x y) = fun r => if r ∈ I then (1 / 2) * (inner ℝ (Sb r x) y + D r x y) else 0 := by
      funext r
      by_cases hr : r ∈ I
      · simp [hDp, hr, formOfOp_apply] <;> ring
      · simp [hDp, hr]
    rw [this]
    exact Measurable.ite hIm (((hSbm x).inner measurable_const).add (hmeas _ _) |>.const_mul _)
      measurable_const
  have hDmm : ∀ x y, Measurable fun r => Dm r x y := by
    intro x y
    have : (fun r => Dm r x y) = fun r => if r ∈ I then (1 / 2) * (inner ℝ (Sb r x) y - D r x y) else 0 := by
      funext r
      by_cases hr : r ∈ I
      · simp [hDm, hr, formOfOp_apply] <;> ring
      · simp [hDm, hr]
    rw [this]
    exact Measurable.ite hIm (((hSbm x).inner measurable_const).sub (hmeas _ _) |>.const_mul _)
      measurable_const
  have hint_of : ∀ Q : ℝ → H →L[ℝ] H →L[ℝ] ℝ, (∀ x y, Measurable fun r => Q r x y) →
      (∀ r ∈ I, traceNormForm (Q r) ≤ traceNormForm (D r)) →
      IntegrableOn (fun r => traceNormForm (Q r)) I := by
    intro Q hQm hQle
    refine Integrable.mono' hint ((measurable_traceNormForm (α := ℝ) Q hQm).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' hIm).2 (Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
    exact hQle r hr
  refine ⟨Dp, Dm, ⟨hDpm, fun r hr => (hpt r hr).1, ?_⟩, ⟨hDmm, fun r hr => (hpt r hr).2.1, ?_⟩, ?_, ?_⟩
  · exact hint_of Dp hDpm fun r hr => by
      have := (hpt r hr).2.2
      linarith [traceNormForm_nonneg (Dm r)]
  · exact hint_of Dm hDmm fun r hr => by
      have := (hpt r hr).2.2
      linarith [traceNormForm_nonneg (Dp r)]
  · intro r hr x y
    simp only [hDp, hDm, hr, if_true, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul]
    ring
  · intro r hr
    exact (hpt r hr).2.2

end Dens

end HRS.Uniform.Q45
