import HRS.MS.ProClosureS111ChartCoordinates
import HRS.MS.ProClosureS111CoeffMoments
import HRS.MS.S111K4H

/-!
Uniform individual coefficient-field moments from the actual thermal
covariance and commutator trace. These estimates hold for every version
with the frozen coordinates, so exact pointwise mass normalization does
not affect them. No Poincare gap or finite-horizon constant is required.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Chaos HRS.MS.S111X1

variable {d r : ℕ} {Pw : ℝ}

/-- Universe-polymorphic real-L2 form of the frozen Wick limit. The
accepted conversion of a TendstoL2 limit to real squared-integral
convergence is reused after obtaining membership from one finite
distance to a finite Wick section. -/
theorem wick_real_L2_of_sequence {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {mu : Measure (Euc d)} [IsProbabilityMeasure mu]
    {basis : ℕ → Euc d → ℝ} {z : ℕ → Omega → ℝ} {L : ℝ}
    {k : Euc d → Euc d → ℝ} {Q : Omega → ℝ}
    (hz : S94GSeq P z L) (hW : HRS.Whole.IsR2WickChaos P mu basis z k Q) :
    s94WickL2 P mu basis z k Q := by
  let S : ℕ → Omega → ℝ := s94Sec P z (HRS.Whole.r2WickCoeff mu basis k)
  have hS : ∀ n, MemLp (S n) 2 P := fun n => s94_sec_memLp hz _ n
  have hlim := HRS.TendstoL2.tendsto_eLpNorm
    (fun n => (hS n).aestronglyMeasurable) hW
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const ENNReal.zero_lt_top).exists
  have hD : MemLp (S n-Q) 2 P := hn
  have hQ : MemLp Q 2 P := by
    have hm := (hS n).sub hD
    refine (memLp_congr_ae (ae_of_all P fun w => ?_)).1 hm
    simp only [Pi.sub_apply]
    ring
  exact ⟨hQ, HRS.MS.S111K4.k4_tendsto_int P S Q hS hQ hW⟩

/-- A single uniform second-moment constant for both actual weighted
coefficient fields, chosen before density, preparation, chart, horizon,
time, and realization. -/
theorem physical_chart_field_uniform_moments (hd : 2 ≤ d)
    (s a beta : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ)/2)
    (ha : 0 < a) (hbeta : 0 < beta)
    (hr : (2 : ℝ)+(d : ℝ)/2 < r) (hPw : (d : ℝ) < 2*Pw) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsThermalEquilibrium d s a beta rho → ∀ gamma : ℝ, 0 ≤ gamma →
      ∀ (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega)
        [IsProbabilityMeasure P] (H : ℝ) (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d)),
      IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
        (wholeSpaceIndex d) beta⁻¹ H
        (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) Z →
      ∀ (E : r26t6_WeightedChart d r Pw) (basis : ℕ → Euc d → ℝ),
      HRS.Whole.IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis →
      ∀ qLin qQuad : ℝ × Omega → r26t6_Coeff,
      r26t6_PhysicalChartFields P rho s H E basis Z qLin qQuad →
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) H),
        (MemLp (fun w => qLin (t,w)) 2 P ∧ (∫ w, ‖qLin (t,w)‖^2 ∂P) ≤ C) ∧
        (MemLp (fun w => qQuad (t,w)) 2 P ∧ (∫ w, ‖qQuad (t,w)‖^2 ∂P) ≤ C) := by
  obtain ⟨L, hL, hcov⟩ := physical_covariance_all_time hd s a beta hs0 hs ha hbeta
  obtain ⟨M, hM, hseq⟩ := physical_gaussian_sequence_uniform hd s a beta hs0 hs ha hbeta
  obtain ⟨T, hT, htrace⟩ := physical_chart_thermal_traces
    hd s a beta Pw r hs0 hs ha hbeta hr hPw
  let C : ℝ := 1+(L+2*M^2)*T
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun rho hrho gamma hgamma Omega _ P _ H Z hZ E basis hbasis qLin qQuad hfields => ?_⟩
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  have hval := (htrace rho hrho E).1
  have hker := (htrace rho hrho E).2
  filter_upwards [hfields.linear_coordinates, hfields.wick_coordinates,
    ae_restrict_mem measurableSet_Icc] with t hlin hquad ht
  have hLin : ∀ j, MemLp (fun w => qLin (t,w) j) 2 P ∧
      (∫ w, qLin (t,w) j^2 ∂P) ≤ L * ∫ x, E.test j x^2 ∂mu := by
    intro j
    let phi : oscSub d (wholeSpaceIndex d) := ⟨E.test j, r2Test_isOscTest _ (E.test_smooth j)⟩
    let X : Omega → ℝ := fun w => OscDual.eval (Z t w) (E.test j)
    have hm : Measurable X := by
      have hm' : Measurable (fun w : Omega => gaussianOscEval phi (Z t w)) :=
        (gaussianOscEval phi).continuous.measurable.comp (hZ.meas t)
      have heq : (fun w : Omega => gaussianOscEval phi (Z t w)) = X := by
        funext w
        simp only [X, phi, gaussianOscEval_apply]
      rw [← heq]
      exact hm'
    have hcv := hcov rho hrho gamma hgamma t ht.1 (E.test j) phi.property
    obtain ⟨⟨v, hv⟩, hsecond⟩ := gaussian_observation_law_and_second hZ ht phi hcv.1
    have hX : MemLp X 2 P := by
      have hg : MemLp (id : ℝ → ℝ) 2 (P.map X) := by
        rw [hv]
        exact memLp_id_gaussianReal 2
      exact (memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable).1 hg
    refine ⟨(memLp_congr_ae (hlin j)).2 hX, ?_⟩
    have hsquare : (fun w => qLin (t,w) j ^ 2) =ᵐ[P] (fun w => X w ^ 2) := by
      filter_upwards [hlin j] with w hw
      rw [hw]
    calc
      _ = ∫ w, X w ^ 2 ∂P := integral_congr_ae hsquare
      _ = linearGaussianCov (r26t6_thermalCoeff d s a beta rho) beta⁻¹
          (HRS.Whole.susceptibilityCov (rieszKernel d s) mu gamma) t t
          (E.test j) (E.test j) := by simpa only [X, phi] using hsecond
      _ ≤ L * ∫ x, E.test j x ^ 2 ∂mu := hcv.2.trans (mul_le_mul_of_nonneg_left
        (centered_square_le_square mu (E.test j) (hval.1 j)) hL.le)
  have hz := hseq rho hrho gamma hgamma Omega P H Z hZ basis hbasis t ht
  have hQuad : ∀ j, MemLp (fun w => qQuad (t,w) j) 2 P ∧
      (∫ w, qQuad (t,w) j^2 ∂P) ≤ 2*M^2 * ∫ xy : Euc d × Euc d,
        HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2 ∂mu.prod mu := by
    intro j
    have hQ := wick_real_L2_of_sequence hz (hquad j)
    have hq : MemLp (fun w => qQuad (t,w) j) 2 P := by
      have hm := hQ.1.const_mul (-1/2 : ℝ)
      refine (memLp_congr_ae (ae_of_all P fun w => ?_)).1 hm
      ring
    have hb := s94_wick_bound hz hM.le hbasis.1 hbasis.2.1
      (HRS.MS.Comm.comm_meas _ (HRS.MH.DualityRd.db1_gradient_continuous
        ((E.test_smooth j).1.of_le (by norm_num))).measurable)
      (HRS.MS.Comm.comm_symm _) (hker.1 j) hQ
    have he : (fun w => (-2*qQuad (t,w) j)^2) = fun w => 4*(qQuad (t,w) j)^2 := by
      funext w
      ring
    rw [he, integral_const_mul] at hb
    have hn : 0 ≤ ∫ w, qQuad (t,w) j^2 ∂P := integral_nonneg fun _ => sq_nonneg _
    exact ⟨hq, by nlinarith⟩
  have hLinBound := coeff_second_moment_bound P (fun w => qLin (t,w))
    (fun j => (hLin j).1) (fun j => L * ∫ x, E.test j x^2 ∂mu)
    (hval.2.1.mul_left L) (fun j => (hLin j).2)
  have hQuadBound := coeff_second_moment_bound P (fun w => qQuad (t,w))
    (fun j => (hQuad j).1) (fun j => 2*M^2 * ∫ xy : Euc d × Euc d,
      HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2 ∂mu.prod mu)
    (hker.2.1.mul_left (2*M^2)) (fun j => (hQuad j).2)
  have hLB : (∫ w, ‖qLin (t,w)‖^2 ∂P) ≤ L*T := by
    refine hLinBound.2.trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hval.2.2 hL.le
  have hQB : (∫ w, ‖qQuad (t,w)‖^2 ∂P) ≤ 2*M^2*T := by
    refine hQuadBound.2.trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hker.2.2 (by positivity)
  exact ⟨⟨hLinBound.1, hLB.trans (by dsimp [C]; nlinarith [mul_nonneg (sq_nonneg M) hT])⟩,
    ⟨hQuadBound.1, hQB.trans (by dsimp [C]; nlinarith [mul_nonneg hL.le hT])⟩⟩

#print axioms physical_chart_field_uniform_moments

end HRS.MS.ProClosureS111
