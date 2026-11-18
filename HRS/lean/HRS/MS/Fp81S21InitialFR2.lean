import HRS.MS.Fp81S21InitialFR

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-! The mixed response limit `fp81s21_initial_Mab` and the actual-law moment and
bias estimates listed in `Fp81S21InitialFR` give the same decomposition as thermal
`S99.s99_FR`. The finite-rank coefficient expansion additionally needs absolute
summability of the actual susceptibility coefficients. This file proves that
envelope directly from the compiled `InitialFamData` response bound; it does not
assume a thermal response representative or thermal integration by parts.
-/

/-- Each actual susceptibility coefficient is bounded by the observable norm times
the summable feature norm and the `InitialFamData` response constant. -/
theorem fp81s21_initial_kap_bound
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ} (hφ :
      IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {u : Euc p.d → ℝ}
    (hu : MemCb (fp81s21_J1 p.d) u) (l : ℕ) :
    |fp81s21_initial_kap (R := R) u φ l| ≤
      cbNorm (fp81s21_J1 p.d) u *
        (F.K * cbNorm (fp81s21_J1 p.d) (φ l)) := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let cu : ℝ := cbNorm (fp81s21_J1 p.d) u
  let b : ℝ := cbNorm (fp81s21_J1 p.d) (φ l)
  have hcu0 : 0 ≤ cu := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hb0 : 0 ≤ b := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hK0 : 0 ≤ F.K := F.hK
  have hub : ∀ x, |u x| ≤ cu := by
    intro x
    have h := HRS.MS.Tc5.tc5_cb_sup_le hu x
    simpa [cu, Real.norm_eq_abs] using h
  have hab : ∀ x, |r26t3_a R (φ l) x| ≤ F.K * b := by
    intro x
    calc |r26t3_a R (φ l) x|
        ≤ cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ l)) := by
          have h := HRS.MS.Tc5.tc5_cb_sup_le (F.amem l) x
          simpa [Real.norm_eq_abs] using h
      _ ≤ F.K * b := by simpa [b] using F.anorm l
  have hm : Measurable fun x : Euc p.d => u x * r26t3_a R (φ l) x :=
    (hu.1.continuous.mul (F.amem l).1.continuous).measurable
  have hC0 : 0 ≤ cu * (F.K * b) := mul_nonneg hcu0 (mul_nonneg hK0 hb0)
  have hpoint : ∀ x, |u x * r26t3_a R (φ l) x| ≤ cu * (F.K * b) := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hub x) (hab x) (abs_nonneg _) hcu0
  have hpoint_norm : ∀ x, ‖u x * r26t3_a R (φ l) x‖ ≤ cu * (F.K * b) := by
    intro x
    simpa [Real.norm_eq_abs] using hpoint x
  have hi : Integrable (fun x : Euc p.d => u x * r26t3_a R (φ l) x) μ :=
    Integrable.of_bound hm.aestronglyMeasurable (cu * (F.K * b)) <|
      Filter.Eventually.of_forall hpoint_norm
  have hnorm : ‖∫ x, u x * r26t3_a R (φ l) x ∂μ‖ ≤ cu * (F.K * b) := by
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall hpoint_norm)
    simpa using h
  rw [Real.norm_eq_abs] at hnorm
  simpa [μ, cu, b, fp81s21_initial_kap] using hnorm

/-- The actual susceptibility coefficients are absolutely summable in the feature index. -/
theorem fp81s21_initial_kap_summable
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ} (hφ :
      IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {u : Euc p.d → ℝ}
    (hu : MemCb (fp81s21_J1 p.d) u) :
    Summable (fun l => |fp81s21_initial_kap (R := R) u φ l|) := by
  let b : ℕ → ℝ := fun l => cbNorm (fp81s21_J1 p.d) (φ l)
  have hb0 : ∀ l, 0 ≤ b l := fun l => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  let C : ℝ := cbNorm (fp81s21_J1 p.d) u * F.K
  have hC0 : 0 ≤ C := mul_nonneg
    (HRS.MS.Tc5.tc5_cb_nonneg _ _) F.hK
  refine Summable.of_nonneg_of_le (fun l => abs_nonneg _)
    (fun l => ?_) (hbs.mul_left C)
  have h := fp81s21_initial_kap_bound E hφ F hu l
  simpa [C, b, mul_assoc] using h

#print axioms fp81s21_initial_kap_bound
#print axioms fp81s21_initial_kap_summable

end HRS.Fp81.S21

end
