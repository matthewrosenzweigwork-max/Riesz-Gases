import HRS.MS.S82UG8
import HRS.MS.S82P2Local
import HRS.MS.S82WP1

/-!
# S8.2 A05 (S82W), part 2: pointwise jets of the pair kernel from `PairCorrector`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

section Qjets
variable {d : ℕ}

lemma w_Q_fderiv_le {Q : Euc d → Euc d → ℝ} {U : Set (Euc d × Euc d)} (hU : IsOpen U)
    (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) U) {x y : Euc d} (hxy : (x, y) ∈ U) :
    ‖fderiv ℝ (Function.uncurry Q) (x, y)‖ ≤ ‖pairGradX Q x y‖ + ‖pairGradY Q x y‖ := by
  have hd : DifferentiableAt ℝ (Function.uncurry Q) (x, y) :=
    (hQ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hxy)
  set D := fderiv ℝ (Function.uncurry Q) (x, y) with hD
  have hx : fderiv ℝ (fun x' => Q x' y) x = D.comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
    have hι : HasFDerivAt (fun z : Euc d => (z, y)) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
    exact (hd.hasFDerivAt.comp x hι).fderiv
  have hy : fderiv ℝ (Q x) y = D.comp (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) := by
    have hι : HasFDerivAt (fun z : Euc d => (x, z)) (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) y :=
      (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)
    exact (hd.hasFDerivAt.comp y hι).fderiv
  have e1 : ‖pairGradX Q x y‖ = ‖D.comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))‖ := by
    unfold pairGradX gradient; rw [LinearIsometryEquiv.norm_map, hx]
  have e2 : ‖pairGradY Q x y‖ = ‖D.comp (ContinuousLinearMap.inr ℝ (Euc d) (Euc d))‖ := by
    unfold pairGradY gradient; rw [LinearIsometryEquiv.norm_map, hy]
  rw [e1, e2]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  have hp : D p = D (ContinuousLinearMap.inl ℝ _ _ p.1) + D (ContinuousLinearMap.inr ℝ _ _ p.2) := by
    rw [← map_add]; congr 1; ext <;> simp
  rw [hp]
  have h1 : ‖D (ContinuousLinearMap.inl ℝ _ _ p.1)‖ ≤ ‖D.comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))‖ * ‖p‖ :=
    (ContinuousLinearMap.le_opNorm (D.comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) p.1).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le p) (norm_nonneg _))
  have h2 : ‖D (ContinuousLinearMap.inr ℝ _ _ p.2)‖ ≤ ‖D.comp (ContinuousLinearMap.inr ℝ (Euc d) (Euc d))‖ * ‖p‖ :=
    (ContinuousLinearMap.le_opNorm (D.comp (ContinuousLinearMap.inr ℝ (Euc d) (Euc d))) p.2).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le p) (norm_nonneg _))
  calc _ ≤ ‖D (ContinuousLinearMap.inl ℝ _ _ p.1)‖ + ‖D (ContinuousLinearMap.inr ℝ _ _ p.2)‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

lemma w_small_pos {x y : Euc d} (hxy : x ≠ y) : 0 < smallRadius x y ∧ smallRadius x y ≤ 1 := by
  unfold smallRadius
  exact ⟨lt_min one_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)), min_le_left _ _⟩

lemma w_pw_nonneg (M : ℝ) (x y : Euc d) : 0 ≤ Phase2S82.pairWeight M x y := by
  unfold Phase2S82.pairWeight
  exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

lemma w_Qjets (hd : 2 ≤ d) {a beta : ℝ} {rho : Euc d → ℝ} {M A : ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (hA : 0 ≤ A) {x y : Euc d} (hxy : x ≠ y) :
    |Q x y| ≤ 2 * (A * Phase2S82.pairWeight M x y * (1 + smallRadius x y ^ (-criticalS d))) ∧
    ‖fderiv ℝ (Function.uncurry Q) (x, y)‖ ≤ 2 * (A * Phase2S82.pairWeight M x y * (1 + smallRadius x y ^ (-criticalS d))) ∧
    ‖fderiv ℝ (fderiv ℝ (Function.uncurry Q)) (x, y)‖ ≤ A * Phase2S82.pairWeight M x y * (1 + smallRadius x y ^ (-criticalS d)) := by
  obtain ⟨hr0, hr1⟩ := w_small_pos hxy
  set r := smallRadius x y with hr
  have hs1 : 1 ≤ criticalS d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hw : 0 ≤ A * Phase2S82.pairWeight M x y := mul_nonneg hA (w_pw_nonneg M x y)
  have hU : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hmem : (x, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := hxy
  have k1 : r ^ (2 - criticalS d) ≤ r ^ (-criticalS d) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  have k2 : r ^ (1 - criticalS d) ≤ r ^ (-criticalS d) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  have k3 : 0 < r ^ (-criticalS d) := Real.rpow_pos_of_pos hr0 _
  have klog : |Real.log r| ≤ r ^ (-criticalS d) := by
    have h1 : |Real.log r| ≤ r⁻¹ := by
      rw [abs_of_nonpos (Real.log_nonpos hr0.le hr1)]
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hr0)
      rw [Real.log_inv] at this
      linarith
    refine h1.trans ?_
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · refine (hQ.value x y hxy).trans ?_
    have : (1 + r ^ (2 - criticalS d) + if d = 4 then |Real.log r| else 0) ≤ 2 * (1 + r ^ (-criticalS d)) := by
      split_ifs <;> nlinarith
    calc _ ≤ A * Phase2S82.pairWeight M x y * (2 * (1 + r ^ (-criticalS d))) := mul_le_mul_of_nonneg_left this hw
      _ = _ := by ring
  · refine (w_Q_fderiv_le hU hQ2 hmem).trans ?_
    refine (hQ.gradient x y hxy).trans ?_
    have : (1 + r ^ (1 - criticalS d)) ≤ 2 * (1 + r ^ (-criticalS d)) := by nlinarith
    calc _ ≤ A * Phase2S82.pairWeight M x y * (2 * (1 + r ^ (-criticalS d))) := mul_le_mul_of_nonneg_left this hw
      _ = _ := by ring
  · have := hQ.hessian x y hxy
    rwa [← w_j2] at *

end Qjets

end HRS.MS.S82W
