import HRS.MS.Fp81S21InitialConsumer4
import HRS.MS.Fp81S21InitialIid

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open HRS.Whole HRS.MS.R26T3

/-- A pointwise response-vector bound gives a uniform finite-N bound on the
zero-coupling static residual. -/
theorem fp81s21_initial_staticResidual_abs_bound
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (N : ℕ) (hN : 2 ≤ N)
    (a : ℝ) (ha : 0 ≤ a)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (F : SeqL2 → ℝ) (hF : F ∈ CbUnitBall SeqL2 5)
    (D : ℝ) (hD : 0 ≤ D)
    (hell : ∀ x, ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ ≤ D) :
    |fp81s21_staticResidual R N a G F| ≤
      2 * Real.sqrt N + (1 / 6) * D ^ 3 := by
  haveI hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [fp81s21_initial_iid_Q hδ hδh R hγ N]
    infer_instance
  have hFbound : ∀ z, ‖F z‖ ≤ 1 := by
    intro z
    simpa [norm_iteratedFDeriv_zero] using
      HRS.MC.E213U6.u6_norm_iteratedFDeriv_le hF (j := 0) (by norm_num) z
  have htest : ∀ z, |F z| ≤ 1 := by
    intro z
    simpa [Real.norm_eq_abs] using hFbound z
  have hI : |∫ X, F (featureVec (r26t3_qwin R a)
      (r26t3_marg R N) X) ∂(r26t3_Q R N)| ≤ 1 := by
    simpa [Real.norm_eq_abs, Measure.real] using
      norm_integral_le_of_norm_le_const (μ := r26t3_Q R N)
        (Filter.Eventually.of_forall fun X => hFbound
          (featureVec (r26t3_qwin R a) (r26t3_marg R N) X))
  have hG : |∫ z, F z ∂G| ≤ 1 := by
    simpa [Real.norm_eq_abs, Measure.real] using
      norm_integral_le_of_norm_le_const (μ := G)
        (Filter.Eventually.of_forall hFbound)
  have hT : ∀ z x,
      ‖iteratedFDeriv ℝ 3 F z
        ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
          fp81s21_initial_ellv R (r26t3_qwin R a) x,
          fp81s21_initial_ellv R (r26t3_qwin R a) x]‖ ≤ D ^ 3 := by
    intro z x
    have hF3 := HRS.MC.E213U6.u6_norm_iteratedFDeriv_le hF
      (by norm_num : 3 ≤ 5) z
    have hprod : (∏ i : Fin 3, ‖(![fp81s21_initial_ellv R
        (r26t3_qwin R a) x, fp81s21_initial_ellv R (r26t3_qwin R a) x,
        fp81s21_initial_ellv R (r26t3_qwin R a) x] : Fin 3 → SeqL2) i‖) ≤ D ^ 3 := by
      simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      calc
        ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ *
            ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ *
            ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ ≤ D * D * D := by
          gcongr <;> exact hell x
        _ = D ^ 3 := by ring
    calc
      ‖iteratedFDeriv ℝ 3 F z
          ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
            fp81s21_initial_ellv R (r26t3_qwin R a) x,
            fp81s21_initial_ellv R (r26t3_qwin R a) x]‖ ≤
          ‖iteratedFDeriv ℝ 3 F z‖ *
            ∏ i : Fin 3, ‖(![fp81s21_initial_ellv R (r26t3_qwin R a) x,
              fp81s21_initial_ellv R (r26t3_qwin R a) x,
              fp81s21_initial_ellv R (r26t3_qwin R a) x] : Fin 3 → SeqL2) i‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ 1 * D ^ 3 := mul_le_mul hF3 hprod
        (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = D ^ 3 := one_mul _
  have hinner : ∀ z,
      ‖∫ x, iteratedFDeriv ℝ 3 F z
        ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
          fp81s21_initial_ellv R (r26t3_qwin R a) x,
          fp81s21_initial_ellv R (r26t3_qwin R a) x]
        ∂(r26t3_mu R 0)‖ ≤ D ^ 3 := by
    intro z
    simpa [Measure.real] using
      norm_integral_le_of_norm_le_const (μ := r26t3_mu R 0)
        (Filter.Eventually.of_forall (hT z))
  have hthird : |∫ z, ∫ x, iteratedFDeriv ℝ 3 F z
      ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
        fp81s21_initial_ellv R (r26t3_qwin R a) x,
        fp81s21_initial_ellv R (r26t3_qwin R a) x]
      ∂(r26t3_mu R 0) ∂G| ≤ D ^ 3 := by
    simpa [Real.norm_eq_abs, Measure.real] using
      norm_integral_le_of_norm_le_const (μ := G)
        (Filter.Eventually.of_forall hinner)
  have hdiff : |Real.sqrt N *
      ((∫ X, F (featureVec (r26t3_qwin R a)
        (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, F z ∂G)| ≤
        2 * Real.sqrt N := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt N * |(∫ X, F (featureVec (r26t3_qwin R a)
          (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, F z ∂G| ≤
        Real.sqrt N * (|∫ X, F (featureVec (r26t3_qwin R a)
          (r26t3_marg R N) X) ∂(r26t3_Q R N)| + |∫ z, F z ∂G|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add hI hG) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N := by ring
  unfold fp81s21_staticResidual
  have hthirdmul : |(1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 F z
      ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
        fp81s21_initial_ellv R (r26t3_qwin R a) x,
        fp81s21_initial_ellv R (r26t3_qwin R a) x]
      ∂(r26t3_mu R 0) ∂G| ≤ (1 / 6) * D ^ 3 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    exact mul_le_mul_of_nonneg_left hthird (by norm_num : (0 : ℝ) ≤ 1 / 6)
  calc
    |Real.sqrt N *
        ((∫ X, F (featureVec (r26t3_qwin R a)
          (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, F z ∂G) -
        (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 F z
          ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
            fp81s21_initial_ellv R (r26t3_qwin R a) x,
            fp81s21_initial_ellv R (r26t3_qwin R a) x]
          ∂(r26t3_mu R 0) ∂G|
      ≤ |Real.sqrt N *
          ((∫ X, F (featureVec (r26t3_qwin R a)
            (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, F z ∂G)| +
        |(1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 F z
          ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
            fp81s21_initial_ellv R (r26t3_qwin R a) x,
            fp81s21_initial_ellv R (r26t3_qwin R a) x]
          ∂(r26t3_mu R 0) ∂G| := abs_sub _ _
    _ ≤ 2 * Real.sqrt N + (1 / 6) * D ^ 3 := add_le_add hdiff hthirdmul

#print axioms fp81s21_initial_staticResidual_abs_bound
end HRS.Fp81.S21
end
