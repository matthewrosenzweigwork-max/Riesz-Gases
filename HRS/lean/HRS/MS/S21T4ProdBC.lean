import HRS.MS.S21T4ProdBB
import HRS.MS.S21T4ProdV

/-!
# R26-T3.S13: measurability of finite-family statistics and limits

Measurability for each coordinate is inherited from the already proved
one-kernel finite-rank joint CLT, including for arbitrary L² linear tests.
The family may contain zero quadratic coordinates.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS HRS.Whole

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_family_source_ae
    (I : ProductGaussian μ) {n r m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : Fin m → Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (hu : ∀ i, IsR2Test (u i))
    (hc : ∀ k i j, c k i j = c k j i)
    (N : ℕ) :
    AEMeasurable (fun X : EucConfig d N =>
      (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => r2EmpDistr μ X (f i))
        (fun k : Fin m => (N : ℝ) * pairEnergy (r2FiniteRankKernel (c k) u) X μ)) :
        EuclideanSpace ℝ (Fin (n + m))))
      (Measure.pi fun _ : Fin N => μ) := by
  letI := I.mΩ
  letI := I.prob
  have hd : ∀ k, IsR2FiniteRankData (c k) u :=
    fun k => ⟨hc k, (fun i => (hu i).1), (fun i => (hu i).2)⟩
  have hz : IsR2FiniteRankData (fun _ _ : Fin r => (0 : ℝ)) u :=
    ⟨by intros; rfl, (fun i => (hu i).1), (fun i => (hu i).2)⟩
  have hbase := s21t4_finite_rank_joint_one_space I f hf
    (fun _ _ : Fin r => (0 : ℝ)) u hz
  have hfst : AEMeasurable (fun X : EucConfig d N =>
      fun i : Fin n => r2EmpDistr μ X (f i))
      (Measure.pi fun _ : Fin N => μ) := by
    simpa only [r2EmpDistr] using (hbase.forall_aemeasurable N).fst
  have hsnd : ∀ k : Fin m, AEMeasurable
      (fun X : EucConfig d N =>
        (N : ℝ) * pairEnergy (r2FiniteRankKernel (c k) u) X μ)
      (Measure.pi fun _ : Fin N => μ) :=
    fun k => (s21t4_finite_rank_joint_one_space I f hf (c k) u (hd k)).forall_aemeasurable N |>.snd
  have hfam : AEMeasurable (fun X : EucConfig d N =>
      Fin.append (fun i : Fin n => r2EmpDistr μ X (f i))
        (fun k : Fin m => (N : ℝ) * pairEnergy (r2FiniteRankKernel (c k) u) X μ))
      (Measure.pi fun _ : Fin N => μ) := by
    refine aemeasurable_pi_iff.mpr fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using (aemeasurable_pi_iff.mp hfst) j
    · simpa only [Fin.append_right] using hsnd k
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + m) => ℝ)).aemeasurable.comp_aemeasurable hfam

theorem s21t4_finite_family_limit_ae
    (I : ProductGaussian μ) {n r m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : Fin m → Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (hu : ∀ i, IsR2Test (u i))
    (hc : ∀ k i j, c k i j = c k j i) :
    AEMeasurable (fun ω : I.Ω =>
      (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => I.η (f i) ω)
        (fun k : Fin m => (1 / 2 : ℝ) *
          ∑ a : Fin r, ∑ b : Fin r, c k a b *
            (I.η (u a) ω * I.η (u b) ω -
              HRS.Whole.pair μ (fun x => u a x * u b x)))) :
        EuclideanSpace ℝ (Fin (n + m)))) I.P := by
  letI := I.mΩ
  letI := I.prob
  have hd : ∀ k, IsR2FiniteRankData (c k) u :=
    fun k => ⟨hc k, (fun i => (hu i).1), (fun i => (hu i).2)⟩
  have hz : IsR2FiniteRankData (fun _ _ : Fin r => (0 : ℝ)) u :=
    ⟨by intros; rfl, (fun i => (hu i).1), (fun i => (hu i).2)⟩
  have hbase := s21t4_finite_rank_joint_one_space I f hf
    (fun _ _ : Fin r => (0 : ℝ)) u hz
  have hfst : AEMeasurable (fun ω : I.Ω =>
      fun i : Fin n => I.η (f i) ω) I.P := hbase.aemeasurable_limit.fst
  have hsnd : ∀ k : Fin m, AEMeasurable
      (fun ω : I.Ω => (1 / 2 : ℝ) *
        ∑ a : Fin r, ∑ b : Fin r, c k a b *
          (I.η (u a) ω * I.η (u b) ω -
            HRS.Whole.pair μ (fun x => u a x * u b x))) I.P :=
    fun k => (s21t4_finite_rank_joint_one_space I f hf (c k) u (hd k)).aemeasurable_limit.snd
  have hfam : AEMeasurable (fun ω : I.Ω =>
      Fin.append (fun i : Fin n => I.η (f i) ω)
        (fun k : Fin m => (1 / 2 : ℝ) *
          ∑ a : Fin r, ∑ b : Fin r, c k a b *
            (I.η (u a) ω * I.η (u b) ω -
              HRS.Whole.pair μ (fun x => u a x * u b x)))) I.P := by
    refine aemeasurable_pi_iff.mpr fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using (aemeasurable_pi_iff.mp hfst) j
    · simpa only [Fin.append_right] using hsnd k
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + m) => ℝ)).aemeasurable.comp_aemeasurable hfam

end HRS.MS.R26T3
