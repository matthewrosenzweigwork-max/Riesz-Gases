import HRS.MS.Fp81S21WeightedMoments6

/-! Measurability of the physical weighted-dual norm from weak test
measurability, linearity, and the weighted Sobolev bound. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_dual_chartAction_test_coordinate
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (q : r26t6_Coeff) (j : ℕ) :
    fp81s21_chartAction E q (E.test j) = q j := by
  have hcoord : E.encode (E.test j) =
      (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext i
    change E.encode (E.test j) i = _
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  rw [fp81s21_chartAction, hcoord]
  simpa [lp.inner_single_right]

/-- The weighted-dual norm is measurable whenever the functional is linear,
bounded by the weighted Sobolev norm on each time slice, and weakly
measurable on every weighted test. -/
theorem fp81s21_dualNormE_aemeasurable_of_L1F
    {d r : ℕ} {Pw T : ℝ} (hd : 0 < d) (hP : (d : ℝ) < 2 * Pw)
    {z : ℝ → (Euc d → ℝ) → ℝ}
    (hlin : ∀ u ∈ Icc (0 : ℝ) T,
      (∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g →
        z u (f + g) = z u f + z u g) ∧
      (∀ c f, IsR2WeightedTest r Pw f → z u (c • f) = c * z u f) ∧
      ∃ M, ∀ f, IsR2WeightedTest r Pw f →
        |z u f| ≤ M * (weightedSobolevE r Pw f).toReal)
    (hmeas : ∀ f, IsR2WeightedTest r Pw f → Measurable fun u => z u f) :
    AEMeasurable (fun u => dualNormE r Pw (z u))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  let E : r26t6_WeightedChart d r Pw := Classical.choice
    (physical_weighted_chart (d := d) (r := r) (Pw := Pw) hd hP)
  have hRiesz : ∀ u ∈ Icc (0 : ℝ) T,
      ∃ q : r26t6_Coeff,
        (∀ f, IsR2Test f → fp81s21_chartAction E q f = z u f) ∧
        dualNormE r Pw (z u) = ENNReal.ofReal ‖q‖ := by
    intro u hu
    obtain ⟨M, hM⟩ := (hlin u hu).2.2
    let C : ℝ := max M 0
    have hC : 0 ≤ C := by simp [C]
    have hadd : ∀ f g, IsR2Test f → IsR2Test g →
        z u (f + g) = z u f + z u g := by
      intro f g hf hg
      exact (hlin u hu).1 f g
        (weightedTestSubmodule_iff.1
          (weighted_test_of_compact_smooth (r := r) (Pw := Pw) hP hf))
        (weightedTestSubmodule_iff.1
          (weighted_test_of_compact_smooth (r := r) (Pw := Pw) hP hg))
    have hsmul : ∀ c f, IsR2Test f → z u (c • f) = c * z u f := by
      intro c f hf
      exact (hlin u hu).2.1 c f
        (weightedTestSubmodule_iff.1
          (weighted_test_of_compact_smooth (r := r) (Pw := Pw) hP hf))
    have hbound : ∀ f, IsR2Test f →
        |z u f| ≤ C * (weightedSobolevE r Pw f).toReal := by
      intro f hf
      let hw : IsR2WeightedTest r Pw f :=
        weightedTestSubmodule_iff.1
          (weighted_test_of_compact_smooth (r := r) (Pw := Pw) hP hf)
      calc
        |z u f| ≤ M * (weightedSobolevE r Pw f).toReal := hM f hw
        _ ≤ C * (weightedSobolevE r Pw f).toReal :=
          mul_le_mul_of_nonneg_right (le_max_left M 0) ENNReal.toReal_nonneg
    exact fp81s21_chart_riesz_from_tests (d := d) (r := r) (Pw := Pw)
      hP E (z u) hadd hsmul C hC hbound
  let q : ℝ → r26t6_Coeff := fun u =>
    if hu : u ∈ Icc (0 : ℝ) T then Classical.choose (hRiesz u hu) else 0
  have hqcoord : ∀ j, Measurable (fun u => q u j) := by
    intro j
    have htest : IsR2WeightedTest r Pw (E.test j) :=
      weightedTestSubmodule_iff.1
        (weighted_test_of_compact_smooth (r := r) (Pw := Pw) hP
          (E.test_smooth j))
    have hscalar : Measurable (fun u => z u (E.test j)) := hmeas _ htest
    have hEq : (fun u => q u j) = fun u =>
        if hu : u ∈ Icc (0 : ℝ) T then z u (E.test j) else 0 := by
      funext u
      by_cases hu : u ∈ Icc (0 : ℝ) T
      · simp only [q, dif_pos hu]
        obtain ⟨hact, -⟩ := Classical.choose_spec (hRiesz u hu)
        calc
          Classical.choose (hRiesz u hu) j =
              fp81s21_chartAction E (Classical.choose (hRiesz u hu)) (E.test j) :=
                (fp81s21_dual_chartAction_test_coordinate E
                  (Classical.choose (hRiesz u hu)) j).symm
          _ = z u (E.test j) := hact _ (E.test_smooth j)
      · have hq0 : q u = 0 := by
          change (if h : u ∈ Icc (0 : ℝ) T then Classical.choose (hRiesz u h) else 0) = 0
          exact dif_neg hu
        change q u j = (if h : u ∈ Icc (0 : ℝ) T then z u (E.test j) else 0)
        rw [hq0]
        simp [hu]
    rw [hEq]
    exact Measurable.ite isClosed_Icc.measurableSet hscalar measurable_const
  have hqmeas : Measurable q := fp81s21_coeff_measurable q hqcoord
  have hnormEq : (fun u => dualNormE r Pw (z u)) =ᵐ[volume.restrict
      (Icc (0 : ℝ) T)] (fun u => ENNReal.ofReal ‖q u‖) := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with u hu
    obtain ⟨-, hnorm⟩ := Classical.choose_spec (hRiesz u hu)
    change dualNormE r Pw (z u) =
      ENNReal.ofReal ‖if h : u ∈ Icc (0 : ℝ) T then Classical.choose (hRiesz u h) else 0‖
    rw [dif_pos hu]
    exact hnorm
  have hqnorm : Measurable (fun u => ENNReal.ofReal ‖q u‖) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.comp hqmeas)
  exact hqnorm.aemeasurable.restrict.congr hnormEq.symm

#print axioms HRS.Fp81.S21.fp81s21_dualNormE_aemeasurable_of_L1F

end HRS.Fp81.S21
end
