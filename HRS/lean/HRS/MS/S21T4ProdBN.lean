import HRS.MS.S21T4ProdBM
import HRS.MS.S21T4ProdBC

/-!
# R26-T3.S13: measurable finite families of physical singular statistics

Measurability of the genuine particle pair energies, and of a prescribed
common-space Gaussian limit family. No approximation-sequence hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_singular_family_source_ae
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, S94KOK μ (h k)) (N : ℕ) :
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
    exact ((HRS.MS.Wr.wr9_measurable_pairEnergy (hh k).meas).const_mul _).aemeasurable
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

theorem s21t4_singular_family_limit_ae
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (Q : Fin m → I.Ω → ℝ)
    (hQ : ∀ k, MemLp (Q k) 2 I.P) :
    AEMeasurable
      (fun ω : I.Ω =>
        (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => I.η (f i) ω)
          (fun k : Fin m => Q k ω)) :
          EuclideanSpace ℝ (Fin (n + m)))) I.P := by
  letI := I.mΩ
  letI := I.prob
  have hfirst : AEMeasurable
      (fun ω : I.Ω => fun i : Fin n => I.η (f i) ω) I.P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    exact (s21t4_eta_memLp I (f i) (hf i)).aestronglyMeasurable.aemeasurable
  have hfamily : AEMeasurable
      (fun ω : I.Ω => Fin.append
        (fun i : Fin n => I.η (f i) ω)
        (fun k : Fin m => Q k ω)) I.P := by
    refine aemeasurable_pi_iff.mpr fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using (aemeasurable_pi_iff.mp hfirst) j
    · simpa only [Fin.append_right] using (hQ k).aestronglyMeasurable.aemeasurable
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + m) => ℝ)).aemeasurable.comp_aemeasurable hfamily

end HRS.MS.R26T3
