import HRS.MS.Fp81S21EmbedField6

/-! The finite nets on the primal unit ball imply compactness of the completed
inclusion operator. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq

/-- The primal inclusion between the completed chart spaces is a compact
operator: its image of the closed unit ball is totally bounded. -/
theorem fp81s21_embedField_primal_isCompactOperator
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (Es : r26t6_WeightedChart d q (Pw + 2)) :
    IsCompactOperator (fp81s21_embedField_primal hP hPs E Es) := by
  classical
  let K := fp81s21_embedField_primal hP hPs E Es
  have htb : TotallyBounded (K '' Metric.closedBall (0 : r26t6_Coeff) 1) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨t, hnet⟩ := fp81s21_embedField_primal_image_finiteNet
      hP hPs E Es ε hε
    refine ⟨(t : Set r26t6_Coeff), t.finite_toSet, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using hx
    obtain ⟨z, hz, hxz⟩ := hnet x hxnorm
    simp only [Set.mem_iUnion, Metric.mem_ball]
    exact ⟨z, hz, by simpa [dist_comm] using hxz⟩
  have hc : IsCompact (closure (K '' Metric.closedBall (0 : r26t6_Coeff) 1)) :=
    htb.closure.isCompact_of_isClosed isClosed_closure
  have hsubset :
      (K : r26t6_Coeff →ₗ[ℝ] r26t6_Coeff) '' Metric.closedBall 0 1 ⊆
        closure (K '' Metric.closedBall (0 : r26t6_Coeff) 1) :=
    subset_closure
  exact (isCompactOperator_iff_image_closedBall_subset_compact
    (K : r26t6_Coeff →ₗ[ℝ] r26t6_Coeff) (r := 1) one_pos).2
      ⟨_, hc, hsubset⟩

#print axioms HRS.Fp81.S21.fp81s21_embedField_primal_isCompactOperator

end HRS.Fp81.S21
