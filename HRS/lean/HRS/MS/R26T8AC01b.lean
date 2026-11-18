import HRS.MS.R26T8AC00
import HRS.MS.R26T8AC01a

/-!
# S8.2 observed-time layer, packet T8A.C01b: the fractional exponent
Measurability, upper bound, and the one-coordinate decomposition `E (insertNth y X') = psi X' y + E X'`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

/-- The exponent of `r26t8a_fractionalLaw`. -/
def r26t8a_c01_E {d p : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N n : ℕ) (pins : Fin p → Euc d)
    (weights : Fin p → ℝ) (X : HRS.Whole.EucConfig d n) : ℝ :=
  referenceExponent q h mu beta N (fun i : Fin 0 => Fin.elim0 i) X -
      ∑ i, ∑ j, weights j * q (X i - pins j)

theorem r26t8a_c01_law_eq {d p : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N n : ℕ) (pins : Fin p → Euc d) (weights : Fin p → ℝ) :
    r26t8a_fractionalLaw q h mu beta N n pins weights =
      exponentialTilt (Measure.pi (fun _ : Fin n => mu)) (r26t8a_c01_E q h mu beta N n pins weights) := rfl

theorem r26t8a_c01_E_meas {d p : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SFinite mu] (hq : Measurable q) (beta : ℝ) (N n : ℕ)
    (hh : Measurable (h N)) (pins : Fin p → Euc d) (weights : Fin p → ℝ) :
    Measurable (r26t8a_c01_E q h mu beta N n pins weights) := by
  unfold r26t8a_c01_E
  refine (HRS.MS.S82P2.s82p2_exponent_measurable hq beta N hh _).sub ?_
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (hq.comp ((measurable_pi_apply i).sub measurable_const))

theorem r26t8a_c01_E_le {d p : ℕ} {a beta C0 : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hbeta : 0 < beta) (hcal : WeakReferenceSetup d a beta rho q h C0) (N n : ℕ) (hN : 2 ≤ N)
    (hh1 : ∀ x, |h N x| ≤ 1) (pins : Fin p → Euc d) (weights : Fin p → ℝ)
    (hw : ∀ j, 0 ≤ weights j) (X : HRS.Whole.EucConfig d n) :
    r26t8a_c01_E q h (HRS.Whole.withDensityReal rho) beta N n pins weights X ≤
      (n : ℝ) * (1 + 1 / 1000) := by
  have hqn := hcal.short.nonneg
  unfold r26t8a_c01_E referenceExponent Phase2S82.pairSum
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero, Finset.sum_const_zero]
  have h1 : ∑ i, (beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) (X i) + h N (X i)) ≤
      (n : ℝ) * (1 + 1 / 1000) := by
    calc _ ≤ ∑ _i : Fin n, (1 + 1 / 1000 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hs := hcal.small_row (X i)
          have hh := (abs_le.1 (hh1 (X i))).2
          linarith
      _ = _ := by simp; ring
  have h2 : 0 ≤ (beta / (2 * N)) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i - X j) :=
    mul_nonneg (div_nonneg hbeta.le (by positivity))
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hqn _)
  have h3 : 0 ≤ ∑ i, ∑ j, weights j * q (X i - pins j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hqn _)
  linarith

theorem r26t8a_c01_E_insert {d p m : ℕ} {q : Euc d → ℝ} (hqe : ∀ z, q (-z) = q z)
    (h : ℕ → Euc d → ℝ) (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d)
    (weights : Fin p → ℝ) (i : Fin (m + 1)) (y : Euc d) (X' : Fin m → Euc d) :
    r26t8a_c01_E q h mu beta N (m + 1) pins weights (i.insertNth y X' : HRS.Whole.EucConfig d (m + 1)) =
      (beta * HRS.Whole.convMeasure q mu y + h N y -
        ((beta / N) * ∑ l, q (y - X' l) + ∑ j, weights j * q (y - pins j))) +
      r26t8a_c01_E q h mu beta N m pins weights X' := by
  have hsym : ∀ a b : Euc d, q (a - b) = q (b - a) := fun a b => by
    rw [← hqe (b - a), neg_sub]
  unfold r26t8a_c01_E
  rw [HRS.MS.S82P2.s82p2_exponent_insertNth hqe h mu beta N (fun i : Fin 0 => Fin.elim0 i) i y X',
    HRS.MS.S82P2.s82p2_exponent_cons]
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, HRS.MS.S82P2.s82p2_site,
    Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero, hsym _ y]
  ring

end HRS.MS.R26T8A
