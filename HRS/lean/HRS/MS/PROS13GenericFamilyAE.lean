import HRS.MS.PROS13GenericTransferE
import HRS.MS.S21T4ProdBN

/-!
# S13: measurability of an arbitrary finite family of product-L² pair energies

No everywhere-measurable kernel representative or density condition is assumed.
Every finite-N pair energy is a genuine L² random variable under iid sampling.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_family_source_ae
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, MemLp
      (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (N : ℕ) :
    AEMeasurable
      (fun X : EucConfig d N =>
        (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => r2EmpDistr μ X (f i))
          (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X μ)) :
          EuclideanSpace ℝ (Fin (n + m))))
      (Measure.pi fun _ : Fin N => μ) := by
  letI := I.mΩ
  letI := I.prob
  let u : Fin 0 → Euc d → ℝ := fun i => Fin.elim0 i
  have hz : IsR2FiniteRankData (fun (_ _ : Fin 0) => (0 : ℝ)) u := by
    refine ⟨?_, ?_, ?_⟩
    · intros
      rfl
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  have hbase := s21t4_finite_rank_joint_one_space I f hf
    (fun (_ _ : Fin 0) => (0 : ℝ)) u hz
  have hfirst : AEMeasurable
      (fun X : EucConfig d N => fun i : Fin n => r2EmpDistr μ X (f i))
      (Measure.pi fun _ : Fin N => μ) := by
    simpa only [r2EmpDistr] using (hbase.forall_aemeasurable N).fst
  have hsecond : ∀ k : Fin m, AEMeasurable
      (fun X : EucConfig d N => (N : ℝ) * pairEnergy (h k) X μ)
      (Measure.pi fun _ : Fin N => μ) := by
    intro k
    exact ((pro_s13_generic_pairEnergy_memLp (h k) (hh k)).const_mul
      (N : ℝ)).aestronglyMeasurable.aemeasurable
  have hfamily : AEMeasurable
      (fun X : EucConfig d N =>
        Fin.append (fun i : Fin n => r2EmpDistr μ X (f i))
          (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X μ))
      (Measure.pi fun _ : Fin N => μ) := by
    refine aemeasurable_pi_iff.mpr fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using (aemeasurable_pi_iff.mp hfirst) j
    · simpa only [Fin.append_right] using hsecond k
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + m) => ℝ)).aemeasurable.comp_aemeasurable hfamily


theorem pro_s13_generic_family_centered_source_ae
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, MemLp
      (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (N : ℕ) :
    AEMeasurable
      (fun X : EucConfig d N =>
        (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => r2EmpDistr μ X (f i))
          (fun k : Fin m =>
            (N : ℝ) * pairEnergy (h k) X μ +
              (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ)) :
          EuclideanSpace ℝ (Fin (n + m))))
      (Measure.pi fun _ : Fin N => μ) := by
  letI := I.mΩ
  letI := I.prob
  let b : Fin m → ℝ := fun k =>
    (1 / 2 : ℝ) * ∫ x, ∫ y, h k x y ∂μ ∂μ
  let B : EuclideanSpace ℝ (Fin (n + m)) :=
    WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ)) b)
  let F : EuclideanSpace ℝ (Fin (n + m)) →
      EuclideanSpace ℝ (Fin (n + m)) := fun z => z + B
  have hF : Continuous F := continuous_id.add continuous_const
  have heq : ∀ X : EucConfig d N,
      (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => r2EmpDistr μ X (f i))
        (fun k : Fin m =>
          (N : ℝ) * pairEnergy (h k) X μ + b k)) :
          EuclideanSpace ℝ (Fin (n + m))) =
        F (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => r2EmpDistr μ X (f i))
          (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X μ))) := by
    intro X
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [F, B]
    · simp [F, B]
  change AEMeasurable
    (fun X : EucConfig d N =>
      (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => r2EmpDistr μ X (f i))
        (fun k : Fin m => (N : ℝ) * pairEnergy (h k) X μ + b k)) :
          EuclideanSpace ℝ (Fin (n + m))))
      (Measure.pi fun _ : Fin N => μ)
  simp_rw [heq]
  exact hF.aemeasurable.comp_aemeasurable
    (pro_s13_generic_family_source_ae I f hf h hh N)

end HRS.MS.R26T3
