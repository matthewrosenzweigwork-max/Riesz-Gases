import HRS.MS.ProClosureS111PhysicalChartFields
import HRS.MS.ProClosureS111PairingLimits

/-!
Coherent full weighted-test Wick identification for the actual coefficient
fields. The same almost-everywhere time set works for every weighted test:
the extension is deterministic once all countable basis coordinates and
sectional L2 membership hold. The full-kernel L2 limit is the accepted
Wick construction and Lipschitz theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Chaos

variable {d r : ℕ} {Pw : ℝ}

theorem commutator_gradient_sub (s : ℝ) (f g : Euc d → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    HRS.Whole.commutatorKernel d s (gradient (f - g)) =
      fun x y => HRS.Whole.commutatorKernel d s (gradient f) x y -
        HRS.Whole.commutatorKernel d s (gradient g) x y := by
  have hgrad : ∀ x, gradient (f - g) x = gradient f x - gradient g x := by
    intro x
    unfold gradient
    rw [fderiv_sub (hf x) (hg x), map_sub]
  funext x y
  unfold HRS.Whole.commutatorKernel
  rw [hgrad x, hgrad y]
  have he : (gradient f x - gradient g x) - (gradient f y - gradient g y) =
      (gradient f x - gradient f y) - (gradient g x - gradient g y) := by abel
  rw [he, inner_sub_left]

theorem chart_section_wick {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (basis : ℕ → Euc d → ℝ) (hbasis : IsR2ZeroMeanONB mu basis)
    (z : ℕ → Omega → ℝ) (L : ℝ) (hz : S94GSeq P z L)
    (E : r26t6_WeightedChart d r Pw) (s : ℝ)
    (hk : ∀ j, MemLp (fun xy : Euc d × Euc d =>
      HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2) 2 (mu.prod mu))
    (q : Omega → r26t6_Coeff)
    (hcoord : ∀ j, IsR2WickChaos P mu basis z
      (HRS.Whole.commutatorKernel d s (gradient (E.test j))) (fun w => -2 * q w j))
    (c : r26t6_Coeff) (n : ℕ) :
    IsR2WickChaos P mu basis z
      (HRS.Whole.commutatorKernel d s (gradient (chartSection E c n : Euc d → ℝ)))
      (fun w => -2 * inner ℝ (q w) (coeffSection c n)) := by
  let k : ℕ → Euc d → Euc d → ℝ := fun j =>
    HRS.Whole.commutatorKernel d s (gradient (E.test j))
  have hkm : ∀ j, Measurable (fun xy : Euc d × Euc d => k j xy.1 xy.2) :=
    fun j => HRS.MS.Comm.comm_meas _ (HRS.MH.DualityRd.db1_gradient_continuous
      ((E.test_smooth j).1.of_le (by norm_num))).measurable
  have hsum := wick_family_linear_L2 P hz basis hbasis.1
    (fun j : Fin n => k j) (fun j => hkm j) (fun j => hk j)
    (fun j => c j) (fun j w => -2 * q w j) (fun j => hcoord j)
  have hkSum : (fun x y => ∑ j : Fin n, c j * k j x y) =
      HRS.Whole.commutatorKernel d s (gradient (chartSection E c n : Euc d → ℝ)) := by
    funext x y
    rw [Fin.sum_univ_eq_sum_range (fun j => (c : r26t6_Coeff) j * k j x y) n]
    exact (chartSection_commutator E (c : r26t6_Coeff) n s x y).symm
  have hQSum : (fun w => ∑ j : Fin n, c j * (-2 * q w j)) =
      fun w => -2 * inner ℝ (q w) (coeffSection c n) := by
    funext w
    rw [Fin.sum_univ_eq_sum_range
      (fun j => (c : r26t6_Coeff) j * (-2 * (q w : r26t6_Coeff) j)) n]
    rw [inner_coeffSection (q w : r26t6_Coeff) (c : r26t6_Coeff) n]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hkSum, hQSum] at hsum
  exact hsum

/-- Every weighted finite-norm test has its actual frozen full-kernel Wick
identity. The conclusion is for the given physical coefficient field,
not for a newly chosen test-dependent realization. -/
theorem physical_chart_quadratic_all_tests (hd : 2 ≤ d)
    (s a beta gamma H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho)
    (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d))
    (hZ : IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
      (wholeSpaceIndex d) beta⁻¹ H
      (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) Z)
    (E : r26t6_WeightedChart d r Pw) (basis : ℕ → Euc d → ℝ)
    (hbasis : IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H)
    (q : Omega → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
      (fun i w => OscDual.eval (Z t w) (basis i))
      (HRS.Whole.commutatorKernel d s (gradient (E.test j))) (fun w => -2 * q w j)) :
    ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f →
      IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
        (fun i w => OscDual.eval (Z t w) (basis i))
        (HRS.Whole.commutatorKernel d s (gradient f))
        (fun w => -2 * inner ℝ (q w) (E.encode f)) := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  obtain ⟨B, hB, hOp⟩ := physical_weighted_L2_operators hd s a beta Pw r
    hs0 hs ha hbeta hr hP rho hrho
  obtain ⟨L, hL, hSeq⟩ := physical_gaussian_sequence_uniform hd s a beta hs0 hs ha hbeta
  let z : ℕ → Omega → ℝ := fun i w => OscDual.eval (Z t w) (basis i)
  have hz : S94GSeq P z L := hSeq rho hrho gamma hgamma Omega P H Z hZ basis hbasis t ht
  have hr2 : 2 ≤ r := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have hrr : (2 : ℝ) ≤ r := by linarith
    exact_mod_cast hrr
  have hk : ∀ j, MemLp (fun xy : Euc d × Euc d =>
      HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2) 2 (mu.prod mu) :=
    fun j => (hOp (E.test j) (weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth hP (E.test_smooth j)))).2.2.1
  intro f hf
  let c := E.encode f
  let fn : ℕ → compactSmoothSubmodule d := chartSection E c
  let kn : ℕ → Euc d → Euc d → ℝ := fun n =>
    HRS.Whole.commutatorKernel d s (gradient (fn n : Euc d → ℝ))
  let k := HRS.Whole.commutatorKernel d s (gradient f)
  let Qn : ℕ → Omega → ℝ := fun n w => -2 * inner ℝ (q w) (coeffSection c n)
  let W : Omega → ℝ := fun w => -2 * inner ℝ (q w) c
  have hfn : ∀ n, IsR2WeightedTest r Pw (fn n) := fun n =>
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP
      (show IsR2Test (fn n : Euc d → ℝ) from (fn n).property))
  have hdiff : ∀ n, IsR2WeightedTest r Pw ((fn n : Euc d → ℝ) - f) :=
    chartSection_error_weighted E hP f hf
  have he : Tendsto (fun n => (weightedSobolevE r Pw ((fn n : Euc d → ℝ) - f)).toReal)
      atTop (𝓝 0) := chartSection_error_tendsto E hP f hf
  have hkm : Measurable (fun xy : Euc d × Euc d => k xy.1 xy.2) :=
    HRS.MS.Comm.comm_meas _ (HRS.MH.DualityRd.db1_gradient_continuous
      (hf.1.of_le (by exact_mod_cast hr2))).measurable
  have hknm : ∀ n, Measurable (fun xy : Euc d × Euc d => kn n xy.1 xy.2) :=
    fun n => HRS.MS.Comm.comm_meas _ (HRS.MH.DualityRd.db1_gradient_continuous
      ((fn n).property.1.of_le (by norm_num))).measurable
  have hkn2 : ∀ n, MemLp (fun xy : Euc d × Euc d => kn n xy.1 xy.2) 2 (mu.prod mu) :=
    fun n => (hOp _ (hfn n)).2.2.1
  have hk2 : MemLp (fun xy : Euc d × Euc d => k xy.1 xy.2) 2 (mu.prod mu) :=
    (hOp _ hf).2.2.1
  have hWn : ∀ n, IsR2WickChaos P mu basis z (kn n) (Qn n) :=
    fun n => chart_section_wick P mu basis hbasis z L hz E s hk q hcoord c n
  have hQn : ∀ n, MemLp (Qn n) 2 P :=
    fun n => (hq.inner_const (coeffSection c n)).const_mul (-2)
  have hW : MemLp W 2 P := (hq.inner_const c).const_mul (-2)
  obtain ⟨Q, hQ, hQbound⟩ := s94_wick_exists hz hL.le hbasis.1 hbasis.2.1
    hkm (HRS.MS.Comm.comm_symm _) hk2
  have hkernel : ∀ n, (∫ xy : Euc d × Euc d,
      (kn n xy.1 xy.2 - k xy.1 xy.2) ^ 2 ∂mu.prod mu) ≤
        B * (weightedSobolevE r Pw ((fn n : Euc d → ℝ) - f)).toReal ^ 2 := by
    intro n
    have hsub := commutator_gradient_sub s (fn n) f
      ((fn n).property.1.differentiable (by norm_num))
      (hf.1.differentiable (by
        exact_mod_cast (Nat.ne_of_gt (show 0 < r by omega))))
    simpa only [hsub] using (hOp _ (hdiff n)).2.2.2
  have hToQ : Tendsto (fun n => ∫ w, (Qn n w - Q w) ^ 2 ∂P) atTop (𝓝 0) := by
    have hu : Tendsto (fun n => (2 * L ^ 2 * B) *
        (weightedSobolevE r Pw ((fn n : Euc d → ℝ) - f)).toReal ^ 2)
        atTop (𝓝 0) := by simpa using (he.pow 2).const_mul (2 * L ^ 2 * B)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun n => integral_nonneg fun _ => sq_nonneg _) fun n => ?_
    have hh := s94_wick_lipschitz hz hL.le hbasis.1 hbasis.2.1
      (hknm n) (HRS.MS.Comm.comm_symm _) (hkn2 n)
      hkm (HRS.MS.Comm.comm_symm _) hk2 (s94_isWick_to_L2 hz (hWn n)) hQ
    exact hh.trans ((mul_le_mul_of_nonneg_left (hkernel n) (by positivity)).trans_eq (by ring))
  have hToW : Tendsto (fun n => ∫ w, (Qn n w - W w) ^ 2 ∂P) atTop (𝓝 0) := by
    have hi := inner_pairing_square_tendsto P q hq c (coeffSection c) (coeffSection_tendsto c)
    have heq : ∀ n w, (Qn n w - W w) ^ 2 =
        4 * (inner ℝ (q w) (coeffSection c n) - inner ℝ (q w) c) ^ 2 := by
      intro n w
      dsimp [Qn, W]
      ring
    simp_rw [heq, integral_const_mul]
    simpa using hi.const_mul 4
  have hae : Q =ᵐ[P] W := HRS.TendstoL2.ae_unique
    (fun n => (hQn n).aestronglyMeasurable)
    (HRS.tendstoL2_of_memLp hQ.1 hQn hToQ)
    (HRS.tendstoL2_of_memLp hW hQn hToW)
  exact wick_congr_ae (hQ.isWick hz) hae

/-- The time exceptional set precedes the arbitrary weighted-test
quantifier. No common spatial or probability null set over all tests is
asserted or needed. -/
theorem physical_chart_quadratic_all_tests_ae (hd : 2 ≤ d)
    (s a beta gamma H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho)
    (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d))
    (hZ : IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
      (wholeSpaceIndex d) beta⁻¹ H
      (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) Z)
    (E : r26t6_WeightedChart d r Pw) (basis : ℕ → Euc d → ℝ)
    (hbasis : IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis)
    (qLin qQuad : ℝ × Omega → r26t6_Coeff)
    (hfields : r26t6_PhysicalChartFields P rho s H E basis Z qLin qQuad) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) H), ∀ f : Euc d → ℝ,
      IsR2WeightedTest r Pw f →
      IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
        (fun i w => OscDual.eval (Z t w) (basis i))
        (HRS.Whole.commutatorKernel d s (gradient f))
        (fun w => -2 * inner ℝ (qQuad (t,w)) (E.encode f)) := by
  filter_upwards [coeff_field_sections_memLp (volume.restrict (Icc (0 : ℝ) H)) P qQuad
    hfields.quadratic_measurable hfields.quadratic_moment,
    hfields.wick_coordinates, ae_restrict_mem measurableSet_Icc] with t hq hc ht
  exact physical_chart_quadratic_all_tests hd s a beta gamma H hs0 hs ha hbeta hgamma
    hr hP rho hrho Omega P Z hZ E basis hbasis t ht (fun w => qQuad (t,w)) hq hc

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_chart_quadratic_all_tests
#print axioms HRS.MS.ProClosureS111.physical_chart_quadratic_all_tests_ae
