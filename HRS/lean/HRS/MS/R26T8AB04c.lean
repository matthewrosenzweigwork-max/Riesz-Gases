import HRS.MS.R26T8AB04b
import HRS.MS.R26T8AB02a

/-!
# S8.2 T8A B04c: a.e. path continuity and slice measurability of the two endpoint terms
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

set_option maxHeartbeats 6400000 in
theorem r26t8a_b04_cont (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d)
    {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d) (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) (a0 T : ℝ) (ha0 : 0 ≤ a0) (hT : 0 < T) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (fun w =>
      -r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0 + t).toNNReal w) +
        r26t8a_QAge a beta m rho Psi alpha 0 t (X a0.toNNReal w)) P) ∧
    ∀ᵐ w ∂P, ContinuousOn (fun t : ℝ =>
      -r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0 + t).toNNReal w) +
        r26t8a_QAge a beta m rho Psi alpha 0 t (X a0.toNNReal w)) (Set.Icc 0 T) := by
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t => (hX.solution (t : ℝ)).adapted t
  have hTB : ∀ v : ℝ, 0 ≤ v → ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha 0 v) :=
    fun v hv => ⟨_, horb.bound alpha v hv 0 (by norm_num)⟩
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨A1, hA1⟩ := hTB 0 le_rfl
    obtain ⟨A2, hA2⟩ := hTB t ht.1
    have h1 := r26t8a_b04_Qmeas d N a beta M C hk rho Psi hPsi hA1
    have h2 := r26t8a_b04_Qmeas d N a beta M C hk rho Psi hPsi hA2
    exact ((h1.comp (hXm _)).neg.add (h2.comp (hXm _))).aemeasurable
  · obtain ⟨A1, hA1⟩ := hTB 0 le_rfl
    have hF2 := r26t8a_o03b_Q_contDiffOn N hd a beta M C hC rho Psi hPsi hA1
    have hQc := r26t8a_b02_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 0
      (by norm_num)
    filter_upwards [(hX.solution (a0 + T)).cont, (hX.solution (a0 + T)).no_collision] with w hw hnc
    have hnc0 : X a0.toNNReal w ∉ eucCollisionSet d N :=
      hnc _ (by rw [Real.coe_toNNReal _ ha0]; linarith)
    have hpath : Continuous fun t : ℝ => X (a0 + t).toNNReal w :=
      (continuous_pi hw).comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))
    have hmaps : MapsTo (fun t : ℝ => X (a0 + t).toNNReal w) (Set.Icc 0 T) (eucCollisionSet d N)ᶜ := fun t ht => by
      show X (a0 + t).toNNReal w ∉ eucCollisionSet d N
      refine hnc _ ?_
      rw [Real.coe_toNNReal _ (by linarith [ht.1])]; linarith [ht.2]
    have hc1 : ContinuousOn (fun t : ℝ => r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0 + t).toNNReal w))
        (Set.Icc 0 T) := (hF2.continuousOn).comp hpath.continuousOn hmaps
    have hc2 : ContinuousOn (fun t : ℝ => r26t8a_QAge a beta m rho Psi alpha 0 t (X a0.toNNReal w))
        (Set.Icc 0 T) := by
      have hp : ContinuousOn (fun t : ℝ => (t, X a0.toNNReal w)) (Set.Icc 0 T) :=
        (continuous_id.prodMk continuous_const).continuousOn
      have hm2 : MapsTo (fun t : ℝ => (t, X a0.toNNReal w)) (Set.Icc 0 T) (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) :=
        fun t ht => ⟨ht.1, hnc0⟩
      exact ContinuousOn.comp (g := fun p : ℝ × EucConfig d N => r26t8a_QAge a beta m rho Psi alpha 0 p.1 p.2)
        (f := fun t : ℝ => (t, X a0.toNNReal w)) hQc hp hm2
    exact hc1.neg.add hc2

end HRS.MS.R26T8A

end
