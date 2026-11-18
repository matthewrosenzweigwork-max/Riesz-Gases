import HRS.MS.R26T8AO04b

/-!
# S8.2 T8A O04 (part c): the noise profile `G` is jointly Borel measurable
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_o04_G_meas (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (j : ℕ) (hj : j ≤ 1)
    (i : Fin N × Fin d) :
    Measurable (fun q : ℝ × ℝ × EucConfig d N =>
      r26t8a_o04_G d N a beta m rho Psi alpha j q.1 q.2.1 q.2.2 i) := by
  classical
  set U : Set (EucConfig d N) := (eucCollisionSet d N)ᶜ with hU
  have hUo : IsOpen U := r26t8a_o03b_coll_closed.isOpen_compl
  have hUm : MeasurableSet U := hUo.measurableSet
  set Hf : ℝ × EucConfig d N → ℝ := fun q =>
    Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha j q.1) q.2 i.1 i.2 with hHf
  have hHc : ContinuousOn Hf (Set.Ici 0 ×ˢ U) :=
    r26t8a_o04_H_contOn d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha j hj i.1 i.2
  have hSm : MeasurableSet (Set.Ici (0 : ℝ) ×ˢ U) := measurableSet_Ici.prod hUm
  have hpw : Measurable ((Set.Ici (0 : ℝ) ×ˢ U).piecewise Hf (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise hHc continuousOn_const hSm
  have hφ : Measurable (fun q : ℝ × ℝ × EucConfig d N => (q.1 - q.2.1, q.2.2)) :=
    (measurable_fst.sub (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)
  have hS : MeasurableSet {q : ℝ × ℝ × EucConfig d N | 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.2.2 ∉ eucCollisionSet d N} :=
    (measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).inter
      ((measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst).inter
        (hUm.preimage (measurable_snd.comp measurable_snd)))
  have heq : (fun q : ℝ × ℝ × EucConfig d N => r26t8a_o04_G d N a beta m rho Psi alpha j q.1 q.2.1 q.2.2 i) =
      fun q => if (0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.2.2 ∉ eucCollisionSet d N) then
        Real.sqrt (2 / beta) * (Set.Ici (0 : ℝ) ×ˢ U).piecewise Hf (fun _ => 0) (q.1 - q.2.1, q.2.2) else 0 := by
    funext q
    unfold r26t8a_o04_G
    by_cases h : 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.2.2 ∉ eucCollisionSet d N
    · have hmem : (q.1 - q.2.1, q.2.2) ∈ Set.Ici (0 : ℝ) ×ˢ U := ⟨sub_nonneg.2 h.2.1, h.2.2⟩
      simp only [h, and_self, if_true]
      rw [Set.piecewise_eq_of_mem _ _ _ hmem]
    · simp only [h, if_false]
  rw [heq]
  exact Measurable.ite hS (measurable_const.mul (hpw.comp hφ)) measurable_const

end HRS.MS.R26T8A

end
