import HRS.MS.Fp81S21WickB311

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))

/-- The expectation of an L² class is continuous for a probability measure. -/
def fp81s21_wickB312_expectation (P : Measure Ω) [IsProbabilityMeasure P] :
    Lp ℝ 2 P →L[ℝ] ℝ :=
  innerSL ℝ ((memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P).toLp _)

theorem fp81s21_wickB312_expectation_eq (f : Lp ℝ 2 P) :
    fp81s21_wickB312_expectation P f = ∫ ω, f ω ∂P := by
  let hone : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
  change inner ℝ (hone.toLp _) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hone.coeFn_toLp] with ω hω
  change f ω * (hone.toLp _ ω) = f ω
  rw [hω]
  ring

/-- The full operator has zero expectation. -/
theorem fp81s21_wickB312_centered (k : Lp ℝ 2 (μ.prod μ)) :
    (∫ ω, fp81s21_wickG_operator L Kstar hL hJoint k ω ∂P) = 0 := by
  let E := (fp81s21_wickB39_linear L Kstar hL hJoint).extendOfNorm
    (fp81s21_wickB310_inclusion (μ := μ))
  have hzero : ∀ y : fp81s21_wickB32_symmetricSubmodule μ,
      fp81s21_wickB312_expectation P (E y) = 0 := by
    apply isClosed_property fp81s21_wickB310_dense
      (isClosed_eq ((fp81s21_wickB312_expectation P).continuous.comp E.continuous) continuous_const)
    intro x
    change fp81s21_wickB312_expectation P (E (fp81s21_wickB310_inclusion x)) = 0
    rw [show E (fp81s21_wickB310_inclusion x) = _ from
      fp81s21_wickB311_extension_eq L Kstar hL hJoint x]
    let r := fp81s21_wickB38_choose μ x
    change fp81s21_wickB312_expectation P
      (fp81s21_wickB22_polynomialLp L Kstar hL hJoint r.u r.hu r.c) = 0
    rw [fp81s21_wickB312_expectation_eq]
    calc
      _ = ∫ ω, fp81s21_wickG_finite_rank_polynomial L r.u r.hu r.c ω ∂P :=
        integral_congr_ae (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint r.u r.hu r.c).2.1.coeFn_toLp
      _ = 0 := (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint r.u r.hu r.c).2.2.1
  rw [← fp81s21_wickB312_expectation_eq]
  exact hzero (fp81s21_wickB310_symmetrize k)

/-- A continuous symmetrization-invariant map with the same finite-rank
values is the constructed operator. -/
theorem fp81s21_wickB312_unique
    (F : Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 P)
    (hFsym : ∀ k, F k = F (fp81s21_wickB23_symmetrize μ k))
    (hFfinite : ∀ x : fp81s21_wickB32_finiteRankSubmodule μ,
      F x = fp81s21_wickB39_linear L Kstar hL hJoint x) :
    F = fp81s21_wickG_operator L Kstar hL hJoint := by
  apply ContinuousLinearMap.ext
  intro k
  rw [hFsym k, fp81s21_wickB311_operator_symmetrize L Kstar hL hJoint k]
  have heq : ∀ y : fp81s21_wickB32_symmetricSubmodule μ,
      F y = fp81s21_wickG_operator L Kstar hL hJoint y := by
    apply isClosed_property fp81s21_wickB310_dense
      (isClosed_eq (F.continuous.comp continuous_subtype_val)
        ((fp81s21_wickG_operator L Kstar hL hJoint).continuous.comp continuous_subtype_val))
    intro x
    change F x = fp81s21_wickG_operator L Kstar hL hJoint x
    rw [hFfinite x, fp81s21_wickB311_operator_finite]
  simpa [fp81s21_wickB310_symmetrize] using heq (fp81s21_wickB310_symmetrize k)

#print axioms fp81s21_wickB312_expectation_eq
#print axioms fp81s21_wickB312_centered
#print axioms fp81s21_wickB312_unique

end HRS.Fp81.S21
end
