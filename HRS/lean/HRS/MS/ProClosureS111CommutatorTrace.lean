import HRS.MS.ProClosureS111ChartTrace
import HRS.MS.R2S11Aux1
import HRS.MS.Comm
import HRS.MH.DualityRdB1Aux

/-!
The physical commutator is a bounded linear functional of a compact smooth
test in the exact weighted norm. Its bound follows from the proved Hessian
evaluation estimate and the segment mean-value theorem. Applying the
chart Bessel argument before integration gives the Hilbert--Schmidt trace;
no sum of individually bounded chart norms is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.FixEq HRS.MS.S85

variable {d r : ℕ} {Pw : ℝ}

def compactGradientEvaluation (x : Euc d) :
    compactSmoothSubmodule d →ₗ[ℝ] Euc d where
  toFun f := gradient (f : Euc d → ℝ) x
  map_add' f g := by
    change gradient ((f : Euc d → ℝ) + (g : Euc d → ℝ)) x =
      gradient (f : Euc d → ℝ) x + gradient (g : Euc d → ℝ) x
    unfold gradient
    rw [fderiv_add (f.property.1.differentiable (by norm_num) x)
      (g.property.1.differentiable (by norm_num) x), map_add]
  map_smul' c f := by
    change gradient (fun y => c * (f : Euc d → ℝ) y) x =
      c • gradient (f : Euc d → ℝ) x
    unfold gradient
    rw [fderiv_const_mul (f.property.1.differentiable (by norm_num) x) c,
      map_smul]

def compactCommutatorEvaluation (s : ℝ) (x y : Euc d) :
    compactSmoothSubmodule d →ₗ[ℝ] ℝ :=
  (innerSL ℝ (rieszKernelGrad d s (x - y))).toLinearMap.comp
    (compactGradientEvaluation x - compactGradientEvaluation y)

theorem compactCommutatorEvaluation_apply (s : ℝ) (x y : Euc d)
    (f : compactSmoothSubmodule d) :
    compactCommutatorEvaluation s x y f =
      HRS.Whole.commutatorKernel d s (gradient (f : Euc d → ℝ)) x y := by
  change inner ℝ (rieszKernelGrad d s (x-y))
      (gradient (f : Euc d → ℝ) x - gradient (f : Euc d → ℝ) y) =
    inner ℝ (gradient (f : Euc d → ℝ) x - gradient (f : Euc d → ℝ) y)
      (rieszKernelGrad d s (x-y))
  exact real_inner_comm _ _

/-- The actual polynomial/Riesz envelope, including its logarithmic case. -/
def chartKernelEnvelope (s Pw : ℝ) (x y : Euc d) : ℝ :=
  (jbracket x + jbracket y) ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y))

theorem chartKernelEnvelope_nonneg (s Pw : ℝ) (x y : Euc d) :
    0 ≤ chartKernelEnvelope s Pw x y := by
  unfold chartKernelEnvelope
  exact mul_nonneg (Real.rpow_nonneg
    (add_nonneg (s57p_jbracket_pos x).le (s57p_jbracket_pos y).le) _)
    (by linarith [HRS.MS.R2S11.s11_rieszWeight_nonneg s (x-y)])

/-- One constant controls the commutator functional for every compact
smooth test and every spatial pair. -/
theorem compact_commutator_weighted_bound (d r : ℕ) (Pw s : ℝ)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (hs : 0 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : compactSmoothSubmodule d, ∀ x y,
      |HRS.Whole.commutatorKernel d s (gradient (f : Euc d → ℝ)) x y| ≤
        K * chartKernelEnvelope s Pw x y *
          (weightedSobolevE r Pw (f : Euc d → ℝ)).toReal := by
  obtain ⟨C, hC, hjet⟩ := weighted_test_jet_evaluation d r Pw hr hP
  have hPw : 0 ≤ Pw := by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
  let K : ℝ := (s + 1) * C * (2 : ℝ) ^ Pw
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, fun f x y => ?_⟩
  by_cases hxy : x = y
  · subst y
    simp only [HRS.Whole.commutatorKernel, sub_self, inner_zero_left, abs_zero]
    exact mul_nonneg (mul_nonneg hK (chartKernelEnvelope_nonneg s Pw x x))
      ENNReal.toReal_nonneg
  let R : ℝ := jbracket x + jbracket y
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [s85_jb_one_le x, s85_jb_one_le y]
  have hnorm : ∀ z : Euc d, ‖z‖ ≤ jbracket z := fun z => by
    unfold jbracket
    exact Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg z])
  have hx : x ∈ closedBall (0 : Euc d) R := by
    rw [mem_closedBall, dist_zero_right]
    exact (hnorm x).trans (by dsimp [R]; linarith [s57p_jbracket_pos y])
  have hy : y ∈ closedBall (0 : Euc d) R := by
    rw [mem_closedBall, dist_zero_right]
    exact (hnorm y).trans (by dsimp [R]; linarith [s57p_jbracket_pos x])
  let A : ℝ := C * (2 * R) ^ Pw *
    (weightedSobolevE r Pw (f : Euc d → ℝ)).toReal
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hf2 : ContDiff ℝ 2 (f : Euc d → ℝ) := f.property.1.of_le (by norm_num)
  have hfd : ∀ z ∈ closedBall (0 : Euc d) R,
      ‖fderiv ℝ (gradient (f : Euc d → ℝ)) z‖ ≤ A := by
    intro z hz
    have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hjz : jbracket z ≤ 2 * R := (u2_jb_le z).trans (by linarith)
    have hsecond : ‖fderiv ℝ (fderiv ℝ (f : Euc d → ℝ)) z‖ =
        ‖iteratedFDeriv ℝ 2 (f : Euc d → ℝ) z‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    refine (HRS.MH.DualityRd.db1_fderiv_gradient_le hf2 z).trans ?_
    rw [hsecond]
    refine (hjet (f : Euc d → ℝ) f.property 2 le_rfl z).trans ?_
    dsimp [A]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (s57p_jbracket_pos z).le hjz hPw) hC)
      ENNReal.toReal_nonneg
  have hdiff : ∀ z ∈ closedBall (0 : Euc d) R,
      DifferentiableAt ℝ (gradient (f : Euc d → ℝ)) z :=
    fun z _ => HRS.MH.DualityRd.db1_gradient_differentiable hf2 z
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hfd
    (convex_closedBall (0 : Euc d) R) hy hx
  have hbound := HRS.MS.R2S11.s11_inner_bound hs (sub_ne_zero.2 hxy) hA hmv
  change |HRS.Whole.commutatorKernel d s (gradient (f : Euc d → ℝ)) x y| ≤ _ at hbound
  refine hbound.trans_eq ?_
  dsimp [A, K, chartKernelEnvelope, R]
  rw [Real.mul_rpow (by norm_num)
    (add_nonneg (s57p_jbracket_pos x).le (s57p_jbracket_pos y).le)]
  ring

/-- The actual commutator trace, with a constant before the chart and
the spatial pair. In particular the singularity is squared only after
the whole chart sum has been controlled. -/
theorem physical_chart_commutator_trace (d r : ℕ) (Pw s : ℝ)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (hs : 0 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ E : r26t6_WeightedChart d r Pw, ∀ x y,
      Summable (fun n => HRS.Whole.commutatorKernel d s (gradient (E.test n)) x y ^ 2) ∧
      (∑' n, HRS.Whole.commutatorKernel d s (gradient (E.test n)) x y ^ 2) ≤
        K ^ 2 * chartKernelEnvelope s Pw x y ^ 2 := by
  obtain ⟨K, hK, hb⟩ := compact_commutator_weighted_bound d r Pw s hr hP hs
  refine ⟨K, hK, fun E x y => ?_⟩
  have h := frozen_chart_functional_trace E hP (compactCommutatorEvaluation s x y)
    (K * chartKernelEnvelope s Pw x y)
    (mul_nonneg hK (chartKernelEnvelope_nonneg s Pw x y)) (fun f => by
      rw [compactCommutatorEvaluation_apply, compactFrozenEncode_norm]
      exact hb f x y)
  simpa only [compactCommutatorEvaluation_apply, frozenChartTest,
    mul_pow] using h

#print axioms compact_commutator_weighted_bound
#print axioms physical_chart_commutator_trace

end HRS.MS.ProClosureS111
