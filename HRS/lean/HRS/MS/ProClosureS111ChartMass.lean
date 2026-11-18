import HRS.MS.ProClosureS111ChartSections
import HRS.MS.ProClosureS111ChartCoordinates
import HRS.MS.ProClosureS111WickLinear
import HRS.MS.ProClosureS111MassLimit

/-!
The physical constant-test mass identity. It is derived from the actual
centered covariance and commutator formulas, using compact chart sections
converging to the constant in the exact frozen weighted norm. It is not
assumed for the raw coefficient fields. Only after proving the identity
almost everywhere do we apply the verified orthogonal projection to make
it hold at every point without altering any coordinate law or L2 class.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111X1 HRS.MS.R2Chaos

variable {d r : ℕ} {Pw : ℝ}

section FixedTime

variable (hd : 2 ≤ d) (s a beta gamma H : ℝ)
  (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hbeta : 0 < beta)
  (hgamma : 0 ≤ gamma) (hr : (2 : ℝ) + (d : ℝ) / 2 < r)
  (hP : (d : ℝ) < 2 * Pw) (rho : Euc d → ℝ)
  (hrho : HRS.Whole.IsThermalEquilibrium d s a beta rho)
  (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
  (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d))
  (hZ : IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
    (wholeSpaceIndex d) beta⁻¹ H
    (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) Z)
  (E : r26t6_WeightedChart d r Pw) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H)

include hd hs0 hs ha hbeta hgamma hr hP hrho hZ ht in
theorem physical_chart_linear_mass_zero (q : Omega → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, (fun w => q w j) =ᵐ[P]
      (fun w => OscDual.eval (Z t w) (E.test j))) :
    ∀ᵐ w ∂P, inner ℝ (q w) (E.encode (fun _ => 1)) = 0 := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  let c : r26t6_Coeff := E.encode (fun _ => 1)
  let fn : ℕ → compactSmoothSubmodule d := chartSection E c
  let gn : ℕ → Euc d → ℝ := fun n => (fn n : Euc d → ℝ) - (fun _ => 1)
  let en : ℕ → ℝ := fun n => (weightedSobolevE r Pw (gn n)).toReal
  have hg : ∀ n, IsR2WeightedTest r Pw (gn n) :=
    chartSection_error_weighted E hP (fun _ => 1) (constant_isWeightedTest hP 1)
  have he : Tendsto en atTop (𝓝 0) :=
    chartSection_error_tendsto E hP (fun _ => 1) (constant_isWeightedTest hP 1)
  obtain ⟨B, hB, hOp⟩ := physical_weighted_L2_operators hd s a beta Pw r
    hs0 hs ha hbeta hr hP rho hrho
  obtain ⟨L, hL, hCov⟩ := physical_covariance_all_time hd s a beta hs0 hs ha hbeta
  have hsection : ∀ n, (∫ w, OscDual.eval (Z t w) (fn n) ^ 2 ∂P) ≤
      (L * B) * en n ^ 2 := by
    intro n
    let phi : oscSub d (wholeSpaceIndex d) :=
      ⟨fn n, r2Test_isOscTest _ (fn n).property⟩
    have hcv := hCov rho hrho gamma hgamma t ht.1 (fn n) phi.property
    have hsecond := (gaussian_observation_law_and_second hZ ht phi hcv.1).2
    have hfm : MemLp (fn n : Euc d → ℝ) 2 mu :=
      (hOp (fn n) (weightedTestSubmodule_iff.1
        (weighted_test_of_compact_smooth hP (fn n).property))).1
    have hcenter : HRS.Whole.projMean mu (gn n) = HRS.Whole.projMean mu (fn n) := by
      funext x
      dsimp [HRS.Whole.projMean, HRS.Whole.pair, gn]
      rw [integral_sub (hfm.integrable one_le_two) (integrable_const (1 : ℝ))]
      simp only [integral_const, probReal_univ, one_smul]
      ring
    calc
      _ = linearGaussianCov (r26t6_thermalCoeff d s a beta rho) beta⁻¹
          (HRS.Whole.susceptibilityCov (rieszKernel d s) mu gamma) t t (fn n) (fn n) := hsecond
      _ ≤ L * ∫ x, HRS.Whole.projMean mu (fn n) x ^ 2 ∂mu := hcv.2
      _ = L * ∫ x, HRS.Whole.projMean mu (gn n) x ^ 2 ∂mu := by rw [hcenter]
      _ ≤ L * ∫ x, gn n x ^ 2 ∂mu := mul_le_mul_of_nonneg_left
        (centered_square_le_square mu (gn n) (hOp _ (hg n)).1) hL.le
      _ ≤ L * (B * en n ^ 2) := mul_le_mul_of_nonneg_left (hOp _ (hg n)).2.1 hL.le
      _ = _ := by ring
  have hinner : ∀ n, (fun w => inner ℝ (q w) (coeffSection c n)) =ᵐ[P]
      (fun w => OscDual.eval (Z t w) (fn n)) := by
    intro n
    filter_upwards [ae_all_iff.2 hcoord] with w hw
    rw [inner_coeffSection, chartSection_eval]
    exact Finset.sum_congr rfl fun j _ => by rw [hw j]
  have hlimit : Tendsto (fun n => ∫ w, inner ℝ (q w) (coeffSection c n) ^ 2 ∂P)
      atTop (𝓝 0) := by
    have hu : Tendsto (fun n => (L * B) * en n ^ 2) atTop (𝓝 0) := by
      simpa using (he.pow 2).const_mul (L * B)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun n => integral_nonneg fun _ => sq_nonneg _) fun n => ?_
    refine (le_of_eq (integral_congr_ae ((hinner n).fun_comp (fun x : ℝ => x ^ 2)))).trans ?_
    exact hsection n
  exact inner_ae_zero_of_approximants P q hq c (coeffSection c) (coeffSection_tendsto c) hlimit

include hd hs0 hs ha hbeta hgamma hr hP hrho hZ ht in
theorem physical_chart_quadratic_mass_zero (basis : ℕ → Euc d → ℝ)
    (hbasis : IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis)
    (q : Omega → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
      (fun i w => OscDual.eval (Z t w) (basis i))
      (HRS.Whole.commutatorKernel d s (gradient (E.test j))) (fun w => -2 * q w j)) :
    ∀ᵐ w ∂P, inner ℝ (q w) (E.encode (fun _ => 1)) = 0 := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  let c : r26t6_Coeff := E.encode (fun _ => 1)
  let fn : ℕ → compactSmoothSubmodule d := chartSection E c
  let gn : ℕ → Euc d → ℝ := fun n => (fn n : Euc d → ℝ) - (fun _ => 1)
  let en : ℕ → ℝ := fun n => (weightedSobolevE r Pw (gn n)).toReal
  let k : ℕ → Euc d → Euc d → ℝ := fun j =>
    HRS.Whole.commutatorKernel d s (gradient (E.test j))
  let kn : ℕ → Euc d → Euc d → ℝ := fun n =>
    HRS.Whole.commutatorKernel d s (gradient (fn n : Euc d → ℝ))
  let z : ℕ → Omega → ℝ := fun i w => OscDual.eval (Z t w) (basis i)
  have hg : ∀ n, IsR2WeightedTest r Pw (gn n) :=
    chartSection_error_weighted E hP (fun _ => 1) (constant_isWeightedTest hP 1)
  have he : Tendsto en atTop (𝓝 0) :=
    chartSection_error_tendsto E hP (fun _ => 1) (constant_isWeightedTest hP 1)
  obtain ⟨B, hB, hOp⟩ := physical_weighted_L2_operators hd s a beta Pw r
    hs0 hs ha hbeta hr hP rho hrho
  obtain ⟨L, hL, hSeq⟩ := physical_gaussian_sequence_uniform hd s a beta hs0 hs ha hbeta
  have hz : S94GSeq P z L := hSeq rho hrho gamma hgamma Omega P H Z hZ basis hbasis t ht
  have hkm : ∀ j, Measurable (fun xy : Euc d × Euc d => k j xy.1 xy.2) :=
    fun j => HRS.MS.Comm.comm_meas _ (HRS.MH.DualityRd.db1_gradient_continuous
      ((E.test_smooth j).1.of_le (by norm_num))).measurable
  have hk2 : ∀ j, MemLp (fun xy : Euc d × Euc d => k j xy.1 xy.2) 2 (mu.prod mu) :=
    fun j => (hOp (E.test j) (weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth hP (E.test_smooth j)))).2.2.1
  have hkn : ∀ n,
      MemLp (fun xy : Euc d × Euc d => kn n xy.1 xy.2) 2 (mu.prod mu) ∧
      (∫ xy : Euc d × Euc d, kn n xy.1 xy.2 ^ 2 ∂mu.prod mu) ≤ B * en n ^ 2 := by
    intro n
    have hk := (hOp _ (hg n)).2.2
    have heq : HRS.Whole.commutatorKernel d s (gradient (gn n)) = kn n :=
      commutator_gradient_sub_const s 1 (fn n : Euc d → ℝ)
    simpa only [heq] using hk
  have hwick : ∀ n, IsR2WickChaos P mu basis z (kn n)
      (fun w => -2 * inner ℝ (q w) (coeffSection c n)) := by
    intro n
    have hsum := wick_family_linear_L2 P hz basis hbasis.1
      (fun j : Fin n => k j) (fun j => hkm j) (fun j => hk2 j)
      (fun j => c j) (fun j w => -2 * q w j) (fun j => hcoord j)
    have hkSum : (fun x y => ∑ j : Fin n, c j * k j x y) = kn n := by
      funext x y
      change ∑ j : Fin n, (c : r26t6_Coeff) j * k j x y = kn n x y
      rw [Fin.sum_univ_eq_sum_range (fun j => (c : r26t6_Coeff) j * k j x y) n]
      exact (chartSection_commutator E (c : r26t6_Coeff) n s x y).symm
    have hQSum : (fun w => ∑ j : Fin n, c j * (-2 * q w j)) =
        fun w => -2 * inner ℝ (q w) (coeffSection c n) := by
      funext w
      change ∑ j : Fin n, (c : r26t6_Coeff) j *
        (-2 * (q w : r26t6_Coeff) j) =
        -2 * inner ℝ (q w : r26t6_Coeff) (coeffSection (c : r26t6_Coeff) n)
      rw [Fin.sum_univ_eq_sum_range
        (fun j => (c : r26t6_Coeff) j * (-2 * (q w : r26t6_Coeff) j)) n]
      rw [inner_coeffSection (q w : r26t6_Coeff) (c : r26t6_Coeff) n]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hkSum, hQSum] at hsum
    exact hsum
  have hbound : ∀ n, (∫ w, inner ℝ (q w) (coeffSection c n) ^ 2 ∂P) ≤
      (L ^ 2 / 2 * B) * en n ^ 2 := by
    intro n
    have hknm : Measurable (fun xy : Euc d × Euc d => kn n xy.1 xy.2) :=
      HRS.MS.Comm.comm_meas _ (HRS.MH.DualityRd.db1_gradient_continuous
        ((fn n).property.1.of_le (by norm_num))).measurable
    have hh := s94_wick_bound hz hL.le hbasis.1 hbasis.2.1 hknm
      (HRS.MS.Comm.comm_symm _) (hkn n).1 (s94_isWick_to_L2 hz (hwick n))
    simp_rw [mul_pow] at hh
    rw [integral_const_mul] at hh
    have hupper := mul_le_mul_of_nonneg_left (hkn n).2 (show 0 ≤ 2 * L ^ 2 by positivity)
    norm_num only at hh
    nlinarith
  have hlimit : Tendsto (fun n => ∫ w, inner ℝ (q w) (coeffSection c n) ^ 2 ∂P)
      atTop (𝓝 0) := by
    have hu : Tendsto (fun n => (L ^ 2 / 2 * B) * en n ^ 2) atTop (𝓝 0) := by
      simpa using (he.pow 2).const_mul (L ^ 2 / 2 * B)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun n => integral_nonneg fun _ => sq_nonneg _) hbound
  exact inner_ae_zero_of_approximants P q hq c (coeffSection c) (coeffSection_tendsto c) hlimit

end FixedTime

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_chart_linear_mass_zero
#print axioms HRS.MS.ProClosureS111.physical_chart_quadratic_mass_zero
