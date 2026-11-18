import HRS.Uniform.Q45Obs1

/-!
# Q45 (Lemma 3.20): the class of trace densities is closed under linear combinations and indicators
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

section Class

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma traceNormForm_zero : traceNormForm (0 : H →L[ℝ] H →L[ℝ] ℝ) = 0 := by
  unfold traceNormForm
  simp

lemma isTraceClassCov_zero : IsTraceClassCov (0 : H →L[ℝ] H →L[ℝ] ℝ) := by
  obtain ⟨ι, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  exact ⟨fun x y => by simp, fun x => by simp, ⟨ι, b, by simpa using summable_zero⟩⟩

lemma isDetCov_ind {T : ℝ} {Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ} (hDb : IsDetCovDensity T Db) {I : Set ℝ}
    (hI : MeasurableSet I) : IsDetCovDensity T (fun r => if r ∈ I then Db r else 0) := by
  have hent : ∀ (σ : ℝ) (x y : H), (if σ ∈ I then Db σ else 0) x y = if σ ∈ I then Db σ x y else 0 := by
    intro σ x y; by_cases h : σ ∈ I <;> simp [h]
  refine ⟨fun x y => ?_, fun σ hσ => ?_, ?_⟩
  · simp_rw [hent]
    exact Measurable.ite hI (hDb.meas x y) measurable_const
  · by_cases h : σ ∈ I
    · simp only [h, if_true]; exact hDb.traceClass σ hσ
    · simp only [h, if_false]; exact isTraceClassCov_zero
  · have hm : Measurable fun σ => traceNormForm (if σ ∈ I then Db σ else (0 : H →L[ℝ] H →L[ℝ] ℝ)) :=
      measurable_traceNormForm (α := ℝ) _ (fun x y => by
        simp_rw [hent]; exact Measurable.ite hI (hDb.meas x y) measurable_const)
    refine Integrable.mono' hDb.int hm.aestronglyMeasurable ?_
    refine Eventually.of_forall fun σ => ?_
    by_cases h : σ ∈ I
    · simp only [h, if_true]
      rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
    · simp only [h, if_false, traceNormForm_zero, norm_zero]
      exact traceNormForm_nonneg _

lemma traceNormForm_lin_le {C C' : H →L[ℝ] H →L[ℝ] ℝ}
    (hb : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)|))
    (hb' : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |C' (p.1.2.1 i) (p.1.2.2 i)|))
    (a b : ℝ) :
    traceNormForm (a • C + b • C') ≤ |a| * traceNormForm C + |b| * traceNormForm C' := by
  refine Real.iSup_le (fun p => ?_) (by positivity [traceNormForm_nonneg C, traceNormForm_nonneg C'])
  have e1 := pairSum_le_traceNormForm hb p
  have e2 := pairSum_le_traceNormForm hb' p
  calc ∑ i, |(a • C + b • C') (p.1.2.1 i) (p.1.2.2 i)|
      ≤ ∑ i, (|a| * |C (p.1.2.1 i) (p.1.2.2 i)| + |b| * |C' (p.1.2.1 i) (p.1.2.2 i)|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        calc |a * C (p.1.2.1 i) (p.1.2.2 i) + b * C' (p.1.2.1 i) (p.1.2.2 i)|
            ≤ |a * C (p.1.2.1 i) (p.1.2.2 i)| + |b * C' (p.1.2.1 i) (p.1.2.2 i)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
    _ = |a| * ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)| + |b| * ∑ i, |C' (p.1.2.1 i) (p.1.2.2 i)| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ |a| * traceNormForm C + |b| * traceNormForm C' := by gcongr

lemma bddAbove_lin {C C' : H →L[ℝ] H →L[ℝ] ℝ}
    (hb : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)|))
    (hb' : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |C' (p.1.2.1 i) (p.1.2.2 i)|))
    (a b : ℝ) :
    BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |(a • C + b • C') (p.1.2.1 i) (p.1.2.2 i)|) := by
  refine ⟨|a| * traceNormForm C + |b| * traceNormForm C', ?_⟩
  rintro _ ⟨p, rfl⟩
  have e1 := pairSum_le_traceNormForm hb p
  have e2 := pairSum_le_traceNormForm hb' p
  calc ∑ i, |(a • C + b • C') (p.1.2.1 i) (p.1.2.2 i)|
      ≤ ∑ i, (|a| * |C (p.1.2.1 i) (p.1.2.2 i)| + |b| * |C' (p.1.2.1 i) (p.1.2.2 i)|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        calc |a * C (p.1.2.1 i) (p.1.2.2 i) + b * C' (p.1.2.1 i) (p.1.2.2 i)|
            ≤ |a * C (p.1.2.1 i) (p.1.2.2 i)| + |b * C' (p.1.2.1 i) (p.1.2.2 i)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
    _ = |a| * ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)| + |b| * ∑ i, |C' (p.1.2.1 i) (p.1.2.2 i)| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ |a| * traceNormForm C + |b| * traceNormForm C' := by gcongr

lemma isTraceDensityL1_lin {T : ℝ} {D D' : ℝ → H →L[ℝ] H →L[ℝ] ℝ} (hD : IsTraceDensityL1 T D)
    (hD' : IsTraceDensityL1 T D') (a b : ℝ) :
    IsTraceDensityL1 T (fun r => a • D r + b • D' r) := by
  obtain ⟨s1, b1, m1, i1⟩ := hD
  obtain ⟨s2, b2, m2, i2⟩ := hD'
  refine ⟨fun r x y => ?_, fun r hr => bddAbove_lin (b1 r hr) (b2 r hr) a b, fun x y => ?_, ?_⟩
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, s1 r x y, s2 r x y]
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact ((m1 x y).const_mul a).add ((m2 x y).const_mul b)
  · have hm : Measurable fun r => traceNormForm (a • D r + b • D' r) :=
      measurable_traceNormForm (α := ℝ) _ (fun x y => by
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        exact ((m1 x y).const_mul a).add ((m2 x y).const_mul b))
    refine Integrable.mono' ((i1.const_mul |a|).add (i2.const_mul |b|)) hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
    exact traceNormForm_lin_le (b1 r hr) (b2 r hr) a b

end Class

end HRS.Uniform.Q45
