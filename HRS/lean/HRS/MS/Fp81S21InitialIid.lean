import HRS.MS.Fp81S21InitialFam
import HRS.MS.S21H2_S30

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc cbNorm)
open HRS.MS.R26T3

/-- At zero preparation strength, the actual initial particle law is the product
of the actual one-particle initial law. -/
theorem fp81s21_initial_iid_Q
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (N : ℕ) :
    r26t3_Q R N = Measure.pi (fun _ : Fin N => r26t3_mu R 0) := by
  have hdens := (r26t3_reference_data p δ hδ hδh R).2.2.1 0 le_rfl
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    s11iid_prob hdens.1.nonneg hdens.1.integral_one
  unfold r26t3_Q
  rw [hγ]
  exact s11iid_gibbs_zero _ N (r26t3_mu R 0)

/-- Every nonempty finite marginal of the zero-strength initial law is the actual
one-particle initial law. -/
theorem fp81s21_initial_iid_marg
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (N : ℕ) (hN : 1 ≤ N) :
    r26t3_marg R N = r26t3_mu R 0 := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) := by
    have hdens := (r26t3_reference_data p δ hδ hδh R).2.2.1 0 le_rfl
    exact s11iid_prob hdens.1.nonneg hdens.1.integral_one
  change HRS.Whole.firstMarginal (r26t3_Q R N) = r26t3_mu R 0
  rw [fp81s21_initial_iid_Q hδ hδh R hγ N]
  exact s21h2_marg_pi N hN (r26t3_mu R 0)

/-- At zero strength, the actual continuous response representative is pointwise
centering under the actual initial law. -/
theorem fp81s21_initial_iid_response
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (hγ : p.γ = 0)
    (f : Euc p.d → ℝ) (x : Euc p.d) :
    r26t3_a R f x = f x - HRS.Whole.pair (r26t3_mu R 0) f := by
  simp [r26t3_a, HRS.Whole.responseRepW, HRS.Whole.projMean, hγ]

/-- At zero strength, susceptibility covariance with a bounded continuous second
observable is its centered integral under the actual initial law. -/
theorem fp81s21_initial_iid_cov
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0)
    {f g : Euc p.d → ℝ} (hg : Continuous g)
    {Cg : ℝ} (hgb : ∀ x, |g x| ≤ Cg) :
    HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ f g =
      ∫ x, (f x - HRS.Whole.pair (r26t3_mu R 0) f) *
        (g x - HRS.Whole.pair (r26t3_mu R 0) g) ∂(r26t3_mu R 0) := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) := by
    have hdens := (r26t3_reference_data p δ hδ hδh R).2.2.1 0 le_rfl
    exact s11iid_prob hdens.1.nonneg hdens.1.integral_one
  have hresp := s11iid_resp_ae (r26t3_mu R 0)
    (HRS.Whole.rieszKernel p.d p.s) hg (C := Cg) hgb
  rw [hγ]
  unfold HRS.Whole.susceptibilityCov HRS.Whole.l2Inner
  refine integral_congr_ae ?_
  filter_upwards [hresp] with x hx
  rw [hx]
  simp [HRS.Whole.projMean, HRS.Whole.pair]

#print axioms fp81s21_initial_iid_Q
#print axioms fp81s21_initial_iid_marg
#print axioms fp81s21_initial_iid_response
#print axioms fp81s21_initial_iid_cov

end HRS.Fp81.S21

end
