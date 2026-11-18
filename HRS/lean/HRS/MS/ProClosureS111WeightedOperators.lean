import HRS.MS.ProClosureS111WeightedAllTests
import HRS.MS.ProClosureS111ThermalTrace

/-!
The value and commutator maps on the entire frozen finite-norm weighted
test domain. These bounds include constants and differences of compact
chart sections from constants. The latter are needed to prove physical
zero mass, without treating the constant function as an oscillator test.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.FixEq HRS.MS.S85

variable {d r : ℕ} {Pw : ℝ}

theorem weighted_commutator_bound_all (d r : ℕ) (Pw s : ℝ)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hPw : 0 ≤ Pw) (hs : 0 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f → ∀ x y,
      |HRS.Whole.commutatorKernel d s (gradient f) x y| ≤
        K * chartKernelEnvelope s Pw x y * (weightedSobolevE r Pw f).toReal := by
  obtain ⟨C, hC, hjet⟩ := weighted_jet_evaluation_all d r Pw hr
  have hr2 : 2 ≤ r := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have hh : (2 : ℝ) ≤ r := by linarith
    exact_mod_cast hh
  let K : ℝ := (s + 1) * C * (2 : ℝ) ^ Pw
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, fun f hf x y => ?_⟩
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
  let A : ℝ := C * (2 * R) ^ Pw * (weightedSobolevE r Pw f).toReal
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (by exact_mod_cast hr2)
  have hfd : ∀ z ∈ closedBall (0 : Euc d) R, ‖fderiv ℝ (gradient f) z‖ ≤ A := by
    intro z hz
    have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hjz : jbracket z ≤ 2 * R := (u2_jb_le z).trans (by linarith)
    have hsecond : ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    refine (HRS.MH.DualityRd.db1_fderiv_gradient_le hf2 z).trans ?_
    rw [hsecond]
    refine (hjet f hf 2 le_rfl z).trans ?_
    dsimp [A]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (s57p_jbracket_pos z).le hjz hPw) hC)
      ENNReal.toReal_nonneg
  have hdiff : ∀ z ∈ closedBall (0 : Euc d) R, DifferentiableAt ℝ (gradient f) z :=
    fun z _ => HRS.MH.DualityRd.db1_gradient_differentiable hf2 z
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hfd
    (convex_closedBall (0 : Euc d) R) hy hx
  have hbound := HRS.MS.R2S11.s11_inner_bound hs (sub_ne_zero.2 hxy) hA hmv
  change |HRS.Whole.commutatorKernel d s (gradient f) x y| ≤ _ at hbound
  refine hbound.trans_eq ?_
  dsimp [A, K, chartKernelEnvelope, R]
  rw [Real.mul_rpow (by norm_num)
    (add_nonneg (s57p_jbracket_pos x).le (s57p_jbracket_pos y).le)]
  ring

/-- Actual bounded spatial value and commutator operators, on the full
finite weighted C^r domain. The thermal L2 kernel estimate uses exactly
the hypothesis `2*s < d`; it includes the logarithmic case `s = 0`. -/
theorem physical_weighted_L2_operators (hd : 2 ≤ d)
    (s a beta Pw : ℝ) (r : ℕ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (rho : Euc d → ℝ) (hrho : HRS.Whole.IsThermalEquilibrium d s a beta rho) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f →
      MemLp f 2 (HRS.Whole.withDensityReal rho) ∧
      (∫ x, f x ^ 2 ∂HRS.Whole.withDensityReal rho) ≤
        B * (weightedSobolevE r Pw f).toReal ^ 2 ∧
      MemLp (fun xy : Euc d × Euc d =>
        HRS.Whole.commutatorKernel d s (gradient f) xy.1 xy.2) 2
        ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho)) ∧
      (∫ xy : Euc d × Euc d,
        HRS.Whole.commutatorKernel d s (gradient f) xy.1 xy.2 ^ 2
        ∂((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho))) ≤
          B * (weightedSobolevE r Pw f).toReal ^ 2 := by
  obtain ⟨M, L, c, hR, hG⟩ := HRS.MS.R2S11.s11_thermal_round2 hd hs0 hs ha hbeta hrho
  have hPw : 0 ≤ Pw := by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
  have hr2 : 2 ≤ r := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have hh : (2 : ℝ) ≤ r := by linarith
    exact_mod_cast hh
  obtain ⟨C, hC, hvalue⟩ := weighted_jet_evaluation_all d r Pw hr
  obtain ⟨K, hK, hkernel⟩ := weighted_commutator_bound_all d r Pw s hr hPw hs0
  let mu := HRS.Whole.withDensityReal rho
  let W : Euc d → ℝ := fun x => jbracket x ^ (2 * Pw)
  let V : Euc d × Euc d → ℝ := fun xy => chartKernelEnvelope s Pw xy.1 xy.2 ^ 2
  have hW : Integrable W mu :=
    thermal_polynomial_weight_integrable hR.prob hG (mul_nonneg (by norm_num) hPw)
  have henv : MemLp (fun xy : Euc d × Euc d => chartKernelEnvelope s Pw xy.1 xy.2)
      2 (mu.prod mu) := by
    simpa only [ENNReal.ofReal_ofNat] using HRS.MS.R2Chaos.s94_poly_memLp
      hd hs0 hs hR hG hPw zero_le_one (chartKernelEnvelope_poly (d := d) s Pw)
      (q := 2) (by norm_num) (by linarith)
  have hV : Integrable V (mu.prod mu) := henv.integrable_sq
  let B : ℝ := C ^ 2 * (∫ x, W x ∂mu) + K ^ 2 * (∫ xy, V xy ∂mu.prod mu)
  have hWI : 0 ≤ ∫ x, W x ∂mu := integral_nonneg fun x =>
    Real.rpow_nonneg (s57p_jbracket_pos x).le _
  have hVI : 0 ≤ ∫ xy, V xy ∂mu.prod mu := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (sq_nonneg _) hWI)
    (mul_nonneg (sq_nonneg _) hVI)
  refine ⟨B, hB, fun f hf => ?_⟩
  let e : ℝ := (weightedSobolevE r Pw f).toReal
  have hvb : ∀ x, f x ^ 2 ≤ (C ^ 2 * e ^ 2) * W x := by
    intro x
    have hh : |f x| ≤ C * jbracket x ^ Pw * e := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hvalue f hf 0 (by omega) x
    have hh2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
    have hw : (jbracket x ^ Pw) ^ 2 = jbracket x ^ (2 * Pw) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (s57p_jbracket_pos x).le]
      congr 1
      ring
    simpa only [sq_abs, mul_pow, hw, W, mul_assoc, mul_left_comm, mul_comm] using hh2
  have hvI : Integrable (fun x => f x ^ 2) mu := by
    refine (hW.const_mul (C ^ 2 * e ^ 2)).mono'
      (hf.1.continuous.measurable.pow_const 2).aestronglyMeasurable ?_
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hvb x
  have hvM : MemLp f 2 mu :=
    (memLp_two_iff_integrable_sq hf.1.continuous.aestronglyMeasurable).2 hvI
  have hkM : Measurable (fun xy : Euc d × Euc d =>
      HRS.Whole.commutatorKernel d s (gradient f) xy.1 xy.2) :=
    HRS.MS.Comm.comm_meas _ (HRS.MH.DualityRd.db1_gradient_continuous
      (hf.1.of_le (by exact_mod_cast hr2))).measurable
  have hkb : ∀ xy : Euc d × Euc d,
      HRS.Whole.commutatorKernel d s (gradient f) xy.1 xy.2 ^ 2 ≤
        (K ^ 2 * e ^ 2) * V xy := by
    intro xy
    have hh := pow_le_pow_left₀ (abs_nonneg _)
      (hkernel f hf xy.1 xy.2) 2
    simpa only [sq_abs, mul_pow, V, mul_assoc, mul_left_comm, mul_comm] using hh
  have hkI : Integrable (fun xy : Euc d × Euc d =>
      HRS.Whole.commutatorKernel d s (gradient f) xy.1 xy.2 ^ 2) (mu.prod mu) := by
    refine (hV.const_mul (K ^ 2 * e ^ 2)).mono'
      (hkM.pow_const 2).aestronglyMeasurable ?_
    exact ae_of_all _ fun xy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hkb xy
  refine ⟨hvM, ?_, (memLp_two_iff_integrable_sq hkM.aestronglyMeasurable).2 hkI, ?_⟩
  · calc
      _ ≤ ∫ x, (C ^ 2 * e ^ 2) * W x ∂mu :=
        integral_mono hvI (hW.const_mul _) hvb
      _ = (C ^ 2 * ∫ x, W x ∂mu) * e ^ 2 := by rw [integral_const_mul]; ring
      _ ≤ B * e ^ 2 := mul_le_mul_of_nonneg_right
        (by dsimp [B]; nlinarith [mul_nonneg (sq_nonneg K) hVI]) (sq_nonneg _)
  · calc
      _ ≤ ∫ xy, (K ^ 2 * e ^ 2) * V xy ∂mu.prod mu :=
        integral_mono hkI (hV.const_mul _) hkb
      _ = (K ^ 2 * ∫ xy, V xy ∂mu.prod mu) * e ^ 2 := by rw [integral_const_mul]; ring
      _ ≤ B * e ^ 2 := mul_le_mul_of_nonneg_right
        (by dsimp [B]; nlinarith [mul_nonneg (sq_nonneg C) hWI]) (sq_nonneg _)

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.weighted_commutator_bound_all
#print axioms HRS.MS.ProClosureS111.physical_weighted_L2_operators
