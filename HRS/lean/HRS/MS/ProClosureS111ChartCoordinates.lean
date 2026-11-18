import HRS.MS.ProClosureS111ThermalTrace
import HRS.MS.ProClosureS111JointWick
import HRS.MS.ProClosureS111FieldL2

/-!
Physical linear and quadratic chart coordinates as genuine jointly
measurable coefficient fields. Thermal trace bounds prove product-time
L2 membership. The remaining pointwise mass normalization is supplied
separately by the constant-test argument and the verified orthogonal
projection, preserving these coordinate identities.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Chaos HRS.MS.S111X1

variable {d r : ℕ} {Pw : ℝ}

theorem centered_square_le_square (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (f : Euc d → ℝ) (hf : MemLp f 2 mu) :
    (∫ x, HRS.Whole.projMean mu f x ^ 2 ∂mu) ≤ ∫ x, f x ^ 2 ∂mu := by
  let m : ℝ := ∫ x, f x ∂mu
  have hfi := hf.integrable one_le_two
  have he : ∀ x, HRS.Whole.projMean mu f x ^ 2 = f x ^ 2 - 2*m*f x + m^2 := by
    intro x
    dsimp [HRS.Whole.projMean, HRS.Whole.pair, m]
    ring
  simp_rw [he]
  have hmu1 : mu.real univ = 1 := by simp
  have hform : (fun x : Euc d => f x ^ 2 - 2*m*f x + m^2) =
      (fun x : Euc d => f x ^ 2 - (2*m)*f x) + (fun _ : Euc d => m^2) := by
    funext x
    rfl
  have hInt : (∫ x, f x ^ 2 - 2*m*f x + m^2 ∂mu) =
      (∫ x, f x ^ 2 ∂mu) - 2*m*m + m^2 := by
    rw [hform]
    change (∫ x, (((fun x => f x ^ 2) - (fun x => (2*m)*f x)) x) + m^2 ∂mu) = _
    rw [integral_add (hf.integrable_sq.sub (hfi.const_mul _)) (integrable_const _)]
    change (∫ x, f x ^ 2 - (2*m)*f x ∂mu) + (∫ x, m^2 ∂mu) = _
    rw [integral_sub hf.integrable_sq (hfi.const_mul _), integral_const_mul,
      integral_const, hmu1]
    simp [m]
  rw [hInt]
  nlinarith [sq_nonneg m]

theorem wick_congr_ae {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {mu : Measure (Euc d)}
    {basis : ℕ → Euc d → ℝ} {z : ℕ → Omega → ℝ} {k : Euc d → Euc d → ℝ}
    {Q R : Omega → ℝ} (hQ : HRS.Whole.IsR2WickChaos P mu basis z k Q)
    (he : Q =ᵐ[P] R) : HRS.Whole.IsR2WickChaos P mu basis z k R := by
  refine ⟨hQ.1.congr he, ?_⟩
  apply hQ.2.congr'
  exact Eventually.of_forall fun n => lintegral_congr_ae (he.mono fun w hw => by
    simpa only [hw])

/-- All required measurable chart coordinates and product-time L2 moments
are constructed from the actual physical evolution. The native Wick
basis is unchanged; the quadratic coordinate is exactly minus one half
of the centered second chaos, as required by frozen D02. -/
theorem physical_chart_coordinate_fields (hd : 2 ≤ d)
    (s a beta gamma H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ)/2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hr : (2 : ℝ)+(d : ℝ)/2 < r) (hP : (d : ℝ) < 2*Pw)
    (rho : Euc d → ℝ) (hrho : HRS.Whole.IsThermalEquilibrium d s a beta rho)
    (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d))
    (hZ : IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
      (wholeSpaceIndex d) beta⁻¹ H
      (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) Z)
    (hZm : Measurable (fun p : ℝ × Omega => Z p.1 p.2))
    (E : r26t6_WeightedChart d r Pw) (basis : ℕ → Euc d → ℝ)
    (hbasis : HRS.Whole.IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis) :
    ∃ qLin qQuad : ℝ × Omega → r26t6_Coeff,
      Measurable qLin ∧ Measurable qQuad ∧
      MemLp qLin 2 ((volume.restrict (Icc (0 : ℝ) H)).prod P) ∧
      MemLp qQuad 2 ((volume.restrict (Icc (0 : ℝ) H)).prod P) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) H), ∀ j,
        (fun w => qLin (t,w) j) =ᵐ[P] (fun w => OscDual.eval (Z t w) (E.test j))) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) H), ∀ j,
        HRS.Whole.IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
          (fun i w => OscDual.eval (Z t w) (basis i))
          (HRS.Whole.commutatorKernel d s (gradient (E.test j)))
          (fun w => -2 * qQuad (t,w) j)) := by
  let mu := HRS.Whole.withDensityReal rho
  let dt : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  obtain ⟨B, hB, htrace⟩ := physical_chart_thermal_traces_at_density hd s a beta Pw r
    hs0 hs ha hbeta hr hP rho hrho
  have hvalue := (htrace E).1
  have hkernel := (htrace E).2
  obtain ⟨L, hL, hcov⟩ := physical_covariance_all_time hd s a beta hs0 hs ha hbeta
  let F : ℕ → ℝ × Omega → ℝ := fun j p => OscDual.eval (Z p.1 p.2) (E.test j)
  have hFm : ∀ j, Measurable (F j) := by
    intro j
    let phi : oscSub d (wholeSpaceIndex d) := ⟨E.test j, r2Test_isOscTest _ (E.test_smooth j)⟩
    change ∀ s, MeasurableSet s → MeasurableSet ((F j) ⁻¹' s)
    intro s hs
    have hm := (gaussianOscEval phi).continuous.measurable.comp hZm
    have heq : (fun p : ℝ × Omega => gaussianOscEval phi (Z p.1 p.2)) = F j := by
      funext p
      simp only [F, phi, gaussianOscEval_apply]
    rw [← heq]
    exact hm hs
  have hFsec : ∀ j, ∀ᵐ t ∂dt,
      MemLp (fun w => F j (t,w)) 2 P ∧
        (∫ w, F j (t,w)^2 ∂P) ≤ L * ∫ x, E.test j x ^ 2 ∂mu := by
    intro j
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    let phi : oscSub d (wholeSpaceIndex d) := ⟨E.test j, r2Test_isOscTest _ (E.test_smooth j)⟩
    have hcv := hcov rho hrho gamma hgamma t ht.1 (E.test j) phi.property
    obtain ⟨⟨v, hv⟩, hsecond⟩ := gaussian_observation_law_and_second hZ ht phi hcv.1
    have hmem : MemLp (fun w => F j (t,w)) 2 P := by
      have hg : MemLp (id : ℝ → ℝ) 2 (P.map (fun w => F j (t,w))) := by
        rw [hv]
        exact memLp_id_gaussianReal 2
      exact (memLp_map_measure_iff aestronglyMeasurable_id
        ((hFm j).comp (measurable_prodMk_left (x := t))).aemeasurable).1 hg
    refine ⟨hmem, ?_⟩
    change (∫ w, OscDual.eval (Z t w) (phi : Euc d → ℝ)^2 ∂P) ≤ _
    rw [hsecond]
    exact hcv.2.trans (mul_le_mul_of_nonneg_left
      (centered_square_le_square mu (E.test j) (hvalue.1 j)) hL.le)
  obtain ⟨qLin, hqLm, hqL2, hqLcoord, _⟩ := joint_coeff_field_from_section_bounds dt P F hFm
    (fun j => L * ∫ x, E.test j x^2 ∂mu)
    (fun _ => mul_nonneg hL.le (integral_nonneg fun _ => sq_nonneg _))
    (hvalue.2.1.mul_left L) hFsec
  obtain ⟨M, hM, hwick⟩ := physical_joint_wick_uniform hd s a beta hs0 hs ha hbeta
  have hQexists : ∀ j, ∃ Q : ℝ × Omega → ℝ, Measurable Q ∧ ∀ t ∈ Icc (0 : ℝ) H,
      MemLp (fun w => Q (t,w)) 2 P ∧
      HRS.Whole.IsR2WickChaos P mu basis (fun i w => OscDual.eval (Z t w) (basis i))
        (HRS.Whole.commutatorKernel d s (gradient (E.test j))) (fun w => Q (t,w)) ∧
      (∫ w, Q (t,w)^2 ∂P) ≤ 2*M^2 * ∫ xy : Euc d × Euc d,
        HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2 ∂mu.prod mu := by
    intro j
    exact hwick rho hrho gamma hgamma Omega P H Z hZ hZm basis hbasis _
      (HRS.MS.Comm.comm_meas _ (HRS.MH.DualityRd.db1_gradient_continuous
        ((E.test_smooth j).1.of_le (by norm_num))).measurable)
      (HRS.MS.Comm.comm_symm _) (hkernel.1 j)
  choose Q hQm hQ using hQexists
  have hQsec : ∀ j, ∀ᵐ t ∂dt, MemLp (fun w => Q j (t,w)) 2 P ∧
      (∫ w, Q j (t,w)^2 ∂P) ≤ 2*M^2 * ∫ xy : Euc d × Euc d,
        HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2 ∂mu.prod mu := by
    intro j
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨(hQ j t ht).1, (hQ j t ht).2.2⟩
  obtain ⟨qW, hqWm, hqW2, hqWcoord, _⟩ := joint_coeff_field_from_section_bounds dt P Q hQm
    (fun j => 2*M^2 * ∫ xy : Euc d × Euc d,
      HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2 ∂mu.prod mu)
    (fun _ => mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
    (hkernel.2.1.mul_left (2*M^2)) hQsec
  let qQuad : ℝ × Omega → r26t6_Coeff := fun p => (-1/2 : ℝ) • qW p
  have hqQm : Measurable qQuad :=
    (((-1/2 : ℝ) • ContinuousLinearMap.id ℝ r26t6_Coeff).continuous.measurable).comp hqWm
  have hqQ2 : MemLp qQuad 2 (dt.prod P) := hqW2.const_smul (-1/2 : ℝ)
  refine ⟨qLin, qQuad, hqLm, hqQm, hqL2, hqQ2,
    joint_coeffL2_coordinates_slices dt P hqLcoord, ?_⟩
  filter_upwards [joint_coeffL2_coordinates_slices dt P hqWcoord,
    ae_restrict_mem measurableSet_Icc] with t ht htime j
  apply wick_congr_ae (hQ j t htime).2.1
  filter_upwards [ht j] with w hw
  change Q j (t,w) = -2 * ((-1/2 : ℝ) • qW (t,w)) j
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hw]
  ring

#print axioms physical_chart_coordinate_fields

end HRS.MS.ProClosureS111
