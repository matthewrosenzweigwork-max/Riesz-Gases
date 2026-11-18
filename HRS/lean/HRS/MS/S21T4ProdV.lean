import HRS.MS.S21T4ProdU

/-! The finite-rank joint CLT using the original Gaussian probability measure itself. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_rank_joint_one_space
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) :
    TendstoInDistribution
      (fun N (X : EucConfig d N) =>
        ((fun i => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))),
         (N : ℝ) * pairEnergy (r2FiniteRankKernel c u) X μ)) atTop
      (fun ω : I.Ω => ((fun i => I.η (f i) ω),
        (1 / 2) * ∑ i, ∑ j, c i j *
          (I.η (u i) ω * I.η (u j) ω - HRS.Whole.pair μ (fun x => u i x * u j x))))
      (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  letI := I.mΩ
  letI := I.prob
  let F : I.Ω → (Fin n → ℝ) × (Fin m → ℝ) := fun ω =>
    ((fun i => I.η (f i) ω), (fun j => I.η (u j) ω))
  let Q : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ) × ℝ := fun z =>
    (z.1, (1 / 2) * ∑ i, ∑ j, c i j *
      (z.2 i * z.2 j - HRS.Whole.pair μ (fun x => u i x * u j x)))
  have hu2 : ∀ j, MemLp (u j) 2 μ := fun j =>
    (hu.smooth j).continuous.memLp_of_hasCompactSupport (hu.compactSupport j)
  have hη : S21LEta μ I.P I.η 1 := s21t4_product_eta_bundle I
  have hF : AEMeasurable F I.P := by
    have hfη : AEMeasurable (fun ω : I.Ω => fun i : Fin n => I.η (f i) ω) I.P :=
      aemeasurable_pi_iff.mpr (fun i => (hη.memLp (f i) (hf i)).aemeasurable)
    have huη : AEMeasurable (fun ω : I.Ω => fun j : Fin m => I.η (u j) ω) I.P :=
      aemeasurable_pi_iff.mpr (fun j => (hη.memLp (u j) (hu2 j)).aemeasurable)
    exact hfη.prodMk huη
  have hclt := s21t4_finite_rank_joint_common I f hf c u hu
  have hm : (I.P.map F).map Q = I.P.map (Q ∘ F) :=
    AEMeasurable.map_map_of_aemeasurable hclt.aemeasurable_limit hF
  refine ⟨hclt.forall_aemeasurable, hclt.aemeasurable_limit.comp_aemeasurable hF, ?_⟩
  have hmeq : (I.P.map F).map Q = I.P.map
      (fun ω : I.Ω => ((fun i => I.η (f i) ω),
        (1 / 2) * ∑ i, ∑ j, c i j *
          (I.η (u i) ω * I.η (u j) ω - HRS.Whole.pair μ (fun x => u i x * u j x)))) := by
    rw [hm]
    rfl
  have heqprob :
      (⟨(I.P.map F).map Q, inferInstance⟩ :
        ProbabilityMeasure ((Fin n → ℝ) × ℝ)) =
      (⟨I.P.map (fun ω : I.Ω => ((fun i => I.η (f i) ω),
        (1 / 2) * ∑ i, ∑ j, c i j *
          (I.η (u i) ω * I.η (u j) ω - HRS.Whole.pair μ (fun x => u i x * u j x)))),
        inferInstance⟩ : ProbabilityMeasure ((Fin n → ℝ) × ℝ)) := by
    apply Subtype.ext
    exact hmeq
  rw [← heqprob]
  exact hclt.tendsto

end HRS.MS.R26T3
