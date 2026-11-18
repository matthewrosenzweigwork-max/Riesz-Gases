import HRS.MS.Fp81S21WickB39

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Inclusion of the finite-rank span into the fixed-point space. -/
def fp81s21_wickB310_inclusion : fp81s21_wickB32_finiteRankSubmodule μ →ₗ[ℝ]
    fp81s21_wickB32_symmetricSubmodule μ where
  toFun x := ⟨x, fp81s21_wickB32_finiteRank_le_symmetric μ x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The finite-rank span is dense in the symmetrizer fixed-point space. -/
theorem fp81s21_wickB310_dense : DenseRange (fp81s21_wickB310_inclusion (μ := μ)) := by
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  have hx : fp81s21_wickB23_symmetrize μ x = x := by
    have h := x.property
    change fp81s21_wickB23_symmetrize μ x - x = 0 at h
    exact sub_eq_zero.mp h
  have hc := fp81s21_wickB33_symmetric_mem_closure μ x hx
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hc ε hε
  refine ⟨⟨y, hy⟩, ?_⟩
  exact hdist

/-- Symmetrization with codomain restricted to its fixed-point space. -/
def fp81s21_wickB310_symmetrize : Lp ℝ 2 (μ.prod μ) →L[ℝ]
    fp81s21_wickB32_symmetricSubmodule μ :=
  (fp81s21_wickB23_symmetrize μ).codRestrict _ (fun x => by
    change fp81s21_wickB23_symmetrize μ (fp81s21_wickB23_symmetrize μ x) -
      fp81s21_wickB23_symmetrize μ x = 0
    rw [fp81s21_wickB23_symmetrize_idempotent, sub_self])

/-- Extension of the finite-rank operator through the symmetrizer. -/
def fp81s21_wickG_operator
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω)) :
    Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 P :=
  ((fp81s21_wickB39_linear L Kstar hL hJoint).extendOfNorm
    (fp81s21_wickB310_inclusion (μ := μ))).comp fp81s21_wickB310_symmetrize

#print axioms fp81s21_wickB310_dense
#print axioms fp81s21_wickG_operator

end HRS.Fp81.S21
end
