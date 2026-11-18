import HRS.MS.Fp81S21WickB314

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def fp81s21_wickB315_inclusion : fp81s21_wickB313_symmetricRepresentable μ →ₗ[ℝ]
    fp81s21_wickB32_symmetricSubmodule μ where
  toFun x := ⟨x, x.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fp81s21_wickB315_dense : DenseRange (fp81s21_wickB315_inclusion (μ := μ)) := by
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp (fp81s21_wickB310_dense (μ := μ)) x ε hε
  refine ⟨⟨y, fp81s21_wickB313_span_le μ y.property⟩, ?_⟩
  exact hy

variable (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))

theorem fp81s21_wickB315_extension_eq
    (x : fp81s21_wickB313_symmetricRepresentable μ) :
    (fp81s21_wickB314_linear L Kstar hL hJoint).extendOfNorm
      (fp81s21_wickB315_inclusion (μ := μ)) (fp81s21_wickB315_inclusion x) =
      fp81s21_wickB314_linear L Kstar hL hJoint x := by
  apply LinearMap.extendOfNorm_eq fp81s21_wickB315_dense
  exact ⟨Kstar ^ 2 / Real.sqrt 2, fp81s21_wickB314_linear_bound L Kstar hL hJoint⟩

def fp81s21_wickB315_operator : Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 P :=
  ((fp81s21_wickB314_linear L Kstar hL hJoint).extendOfNorm
    (fp81s21_wickB315_inclusion (μ := μ))).comp fp81s21_wickB310_symmetrize

theorem fp81s21_wickB315_operator_symm (k : Lp ℝ 2 (μ.prod μ)) :
    fp81s21_wickB315_operator L Kstar hL hJoint k =
      fp81s21_wickB315_operator L Kstar hL hJoint (fp81s21_wickB23_symmetrize μ k) := by
  change (fp81s21_wickB314_linear L Kstar hL hJoint).extendOfNorm
    (fp81s21_wickB315_inclusion (μ := μ)) (fp81s21_wickB310_symmetrize k) =
      (fp81s21_wickB314_linear L Kstar hL hJoint).extendOfNorm
        (fp81s21_wickB315_inclusion (μ := μ))
        (fp81s21_wickB310_symmetrize (fp81s21_wickB23_symmetrize μ k))
  congr 1
  apply Subtype.ext
  exact (fp81s21_wickB23_symmetrize_idempotent μ k).symm

theorem fp81s21_wickB315_operator_finite
    (x : fp81s21_wickB313_symmetricRepresentable μ) :
    fp81s21_wickB315_operator L Kstar hL hJoint x =
      fp81s21_wickB314_linear L Kstar hL hJoint x := by
  have hfixed := x.property.2
  change fp81s21_wickB23_symmetrize μ x - x = 0 at hfixed
  have hsym : fp81s21_wickB310_symmetrize x = fp81s21_wickB315_inclusion x := by
    apply Subtype.ext
    exact sub_eq_zero.mp hfixed
  change (fp81s21_wickB314_linear L Kstar hL hJoint).extendOfNorm
    (fp81s21_wickB315_inclusion (μ := μ)) (fp81s21_wickB310_symmetrize x) = _
  rw [hsym, fp81s21_wickB315_extension_eq]

theorem fp81s21_wickB315_operator_eq :
    fp81s21_wickB315_operator L Kstar hL hJoint = fp81s21_wickG_operator L Kstar hL hJoint := by
  apply fp81s21_wickB312_unique L Kstar hL hJoint
  · exact fp81s21_wickB315_operator_symm L Kstar hL hJoint
  · intro x
    let y : fp81s21_wickB313_symmetricRepresentable μ :=
      ⟨x, fp81s21_wickB313_span_le μ x.property⟩
    let r := fp81s21_wickB38_choose μ x
    change fp81s21_wickB315_operator L Kstar hL hJoint y = _
    rw [fp81s21_wickB315_operator_finite]
    change fp81s21_wickB314_operator L Kstar hL hJoint y =
      fp81s21_wickB22_polynomialLp L Kstar hL hJoint r.u r.hu r.c
    exact fp81s21_wickB314_operator_eq L Kstar hL hJoint y r.u r.hu r.c r.hk r.eq_class

#print axioms fp81s21_wickB315_dense
#print axioms fp81s21_wickB315_extension_eq
#print axioms fp81s21_wickB315_operator_symm
#print axioms fp81s21_wickB315_operator_finite
#print axioms fp81s21_wickB315_operator_eq

end HRS.Fp81.S21
end
