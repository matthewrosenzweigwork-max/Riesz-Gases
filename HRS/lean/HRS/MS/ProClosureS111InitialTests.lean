import HRS.MS.ProClosureS111InitialTestsApprox
import HRS.MS.S111X1G2
import HRS.MS.S111X2Aux5

/-!
Extension of the physical initial response coordinates from Hermite tests
to every original `IsOscTest (wholeSpaceIndex d)` test.

The operator used below is the actual resolvent of the actual centered
thermal propagator. Its oscillator-to-L² bound follows from the accepted
all-test energy estimate and boundedness of the thermal density. Thus the
extension does not assume an all-test response continuity interface.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.MovOsc

variable {d : ℕ} {s a beta gamma : ℝ} {rho : Euc d → ℝ}

theorem initialProp_memLp (hX : X1Input d s a beta gamma rho)
    {t : ℝ} (ht : 0 ≤ t) (phi : oscSub d (wholeSpaceIndex d)) :
    MemLp (propagatorW (x1C d s a beta rho) 0 t (phi : Euc d → ℝ))
      2 (HRS.Whole.withDensityReal rho) := by
  letI := hX.finite
  exact x1_classical_memLp (x1_prop_classical (hX.exist t ht phi phi.property))
    ⟨le_rfl, ht⟩ (HRS.Whole.withDensityReal rho)

section Response

variable [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
variable {g : Euc d → ℝ}
variable {K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal rho)}
variable {Mg : ℝ}
variable (hX : X1Input d s a beta gamma rho)
variable (hK : KRep g (HRS.Whole.withDensityReal rho) K Mg) (hgamma : 0 ≤ gamma)
variable {t : ℝ} (ht : 0 ≤ t)

def initialScreenedClass (phi : oscSub d (wholeSpaceIndex d)) :
    Lp ℝ 2 (HRS.Whole.withDensityReal rho) :=
  s111x2_Res hK.posOp hgamma (s111x2_cl (initialProp_memLp hX ht phi))

theorem initialScreenedClass_linear (phi psi : oscSub d (wholeSpaceIndex d))
    (c : ℝ) :
    initialScreenedClass hX hK hgamma ht (phi + c • psi) =
      initialScreenedClass hX hK hgamma ht phi +
        c • initialScreenedClass hX hK hgamma ht psi := by
  have hf := initialProp_memLp hX ht phi
  have hk := initialProp_memLp hX ht psi
  have hh := initialProp_memLp hX ht (phi + c • psi)
  have hp := hX.prop_lin ht phi.property psi.property c 0 ⟨le_rfl, ht⟩
  have hcl : s111x2_cl hh = s111x2_cl hf + c • s111x2_cl hk := by
    apply Lp.ext
    filter_upwards [s111x2_cl_ae hh, s111x2_cl_ae hf, s111x2_cl_ae hk,
      Lp.coeFn_add (s111x2_cl hf) (c • s111x2_cl hk),
      Lp.coeFn_smul c (s111x2_cl hk)] with x h1 h2 h3 h4 h5
    rw [← h1, h4, Pi.add_apply, h5, Pi.smul_apply, smul_eq_mul, ← h2, ← h3]
    change HRS.Whole.projMean (HRS.Whole.withDensityReal rho)
        (propagatorW (x1C d s a beta rho) 0 t
          (fun y => (phi : Euc d → ℝ) y + c * (psi : Euc d → ℝ) y)) x = _
    rw [hp]
    exact s111x2_projMean_lin hf hk c x
  change s111x2_Res hK.posOp hgamma (s111x2_cl hh) = _
  rw [hcl, s111x2_Res_add, s111x2_Res_smul]
  rfl

theorem initialScreenedClass_zero :
    initialScreenedClass hX hK hgamma ht 0 = 0 := by
  have he := initialScreenedClass_linear hX hK hgamma ht 0 0 1
  simp only [one_smul, zero_add] at he
  exact add_left_cancel (he.symm.trans (add_zero _).symm)

def initialScreenedLinear :
    oscSub d (wholeSpaceIndex d) →ₗ[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal rho) where
  toFun := initialScreenedClass hX hK hgamma ht
  map_add' := fun phi psi => by
    simpa only [one_smul] using initialScreenedClass_linear hX hK hgamma ht phi psi 1
  map_smul' := fun c phi => by
    have he := initialScreenedClass_linear hX hK hgamma ht 0 phi c
    simpa only [zero_add, initialScreenedClass_zero hX hK hgamma ht, RingHom.id_apply] using he

theorem initialScreenedLinear_ae (phi : oscSub d (wholeSpaceIndex d)) :
    HRS.Whole.responseInverse g (HRS.Whole.withDensityReal rho) gamma
      (propagatorW (x1C d s a beta rho) 0 t (phi : Euc d → ℝ)) =ᵐ[HRS.Whole.withDensityReal rho]
      (initialScreenedLinear hX hK hgamma ht phi : Euc d → ℝ) :=
  s111x2_responseInverse_ae hK hgamma (initialProp_memLp hX ht phi)

/-- The energy estimate is applied to each actual propagated test, including
differences of tests. Centering is retained inside its L² norm. -/
theorem initialScreenedLinear_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ phi : oscSub d (wholeSpaceIndex d),
      ‖initialScreenedLinear hX hK hgamma ht phi‖ ≤
        B * oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ) := by
  obtain ⟨M, hM⟩ := hX.bdd
  have hM0 : 0 ≤ M := (hX.nonneg 0).trans (hM 0)
  obtain ⟨c, hc, henergy⟩ := hX.energy t ht
  refine ⟨Real.sqrt (c * M), Real.sqrt_nonneg _, fun phi => ?_⟩
  have hcls := x1_prop_classical (hX.exist t ht phi phi.property)
  have hbound := (henergy phi phi.property _ hcls).1
  have hinput := initialTest_sq_bound hX.meas hX.nonneg hM0 hM
    (Nat.cast_nonneg (wholeSpaceIndex d)) phi
  have hres := (s111x2_Res_bounds hK.posOp hgamma
    (s111x2_cl (initialProp_memLp hX ht phi))).2.2
  have hsq : ‖initialScreenedLinear hX hK hgamma ht phi‖ ^ 2 ≤
      (c * M) * oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ) ^ 2 := by
    calc
      _ ≤ ‖s111x2_cl (initialProp_memLp hX ht phi)‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hres 2
      _ = ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal rho)
          (propagatorW (x1C d s a beta rho) 0 t (phi : Euc d → ℝ)) x ^ 2
            ∂HRS.Whole.withDensityReal rho := s111x2_cl_norm_sq _
      _ ≤ c * ∫ x, (phi : Euc d → ℝ) x ^ 2 ∂HRS.Whole.withDensityReal rho := hbound
      _ ≤ c * (M * oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hinput hc
      _ = _ := by ring
  have hsqrt : (Real.sqrt (c * M) *
      oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ)) ^ 2 =
      (c * M) * oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hc hM0)]
  rw [← hsqrt] at hsq
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1 hsq

theorem initialScreenedLinear_section_tendsto (phi : oscSub d (wholeSpaceIndex d)) :
    Tendsto (fun n => initialScreenedLinear hX hK hgamma ht (initialTestSection phi n))
      atTop (𝓝 (initialScreenedLinear hX hK hgamma ht phi)) := by
  obtain ⟨B, hB, hbound⟩ := initialScreenedLinear_bound hX hK hgamma ht
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hlim : Tendsto (fun n => B * oscNorm (wholeSpaceIndex d)
      ((phi - initialTestSection phi n : oscSub d (wholeSpaceIndex d)) : Euc d → ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (initialTestSection_tail phi).const_mul B
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [norm_sub_rev, ← map_sub]
  exact hbound (phi - initialTestSection phi n)

include hX hK hgamma ht in
/-- A function with the physical Hermite response coordinates has the
physical response against every original oscillator test. The almost
everywhere equality is asserted separately for each test; no common
spatial null set over all tests is required. -/
theorem initial_all_tests_of_basis
    (Z : Euc d → OscDual d (wholeSpaceIndex d))
    (hcoord : ∀ alpha : MultiIndex d,
      (fun x => OscDual.coord (Z x) alpha) =ᵐ[HRS.Whole.withDensityReal rho]
        HRS.Whole.responseInverse g (HRS.Whole.withDensityReal rho) gamma
          (propagatorW (x1C d s a beta rho) 0 t
            (oscTestFun (wholeSpaceIndex d) alpha)))
    (phi : oscSub d (wholeSpaceIndex d)) :
    (fun x => OscDual.eval (Z x) (phi : Euc d → ℝ)) =ᵐ[HRS.Whole.withDensityReal rho]
      HRS.Whole.responseInverse g (HRS.Whole.withDensityReal rho) gamma
        (propagatorW (x1C d s a beta rho) 0 t (phi : Euc d → ℝ)) := by
  let A := initialScreenedLinear hX hK hgamma ht
  have hbasis : ∀ᵐ x ∂HRS.Whole.withDensityReal rho, ∀ alpha : MultiIndex d,
      (A (initialTestBasis (wholeSpaceIndex d) alpha) : Euc d → ℝ) x =
        OscDual.coord (Z x) alpha := by
    apply ae_all_iff.2
    intro alpha
    exact ((hcoord alpha).trans
      (initialScreenedLinear_ae hX hK hgamma ht
        (initialTestBasis (wholeSpaceIndex d) alpha))).symm
  have hsection : ∀ n : ℕ,
      (fun x => OscDual.eval (Z x) (initialTestSection phi n : Euc d → ℝ)) =ᵐ[HRS.Whole.withDensityReal rho]
        (A (initialTestSection phi n) : Euc d → ℝ) := by
    intro n
    let coeff : MultiIndex d → ℝ := fun alpha =>
      oscEigenvalue d alpha ^ ((wholeSpaceIndex d : ℝ) / 2) *
        HRS.Whole.hermiteCoeff (phi : Euc d → ℝ) alpha
    have hmap : A (initialTestSection phi n) =
        ∑ alpha ∈ mova2_S d n, coeff alpha • A (initialTestBasis (wholeSpaceIndex d) alpha) := by
      simp only [initialTestSection, map_sum, map_smul, coeff]
    have hsmul : ∀ᵐ x ∂HRS.Whole.withDensityReal rho, ∀ alpha : MultiIndex d,
        ((coeff alpha • A (initialTestBasis (wholeSpaceIndex d) alpha) :
          Lp ℝ 2 (HRS.Whole.withDensityReal rho)) : Euc d → ℝ) x =
        coeff alpha * (A (initialTestBasis (wholeSpaceIndex d) alpha) : Euc d → ℝ) x :=
      ae_all_iff.2 fun alpha => Lp.coeFn_smul (coeff alpha) _
    filter_upwards [hbasis, hsmul, Lp.coeFn_fun_finsetSum (mova2_S d n)
      (fun alpha => coeff alpha • A (initialTestBasis (wholeSpaceIndex d) alpha))]
        with x hx hsm hxsum
    rw [hmap, hxsum, initialTestSection_eval]
    refine Finset.sum_congr rfl fun alpha _ => ?_
    rw [hsm alpha, hx alpha]
  have hlim := initialScreenedLinear_section_tendsto hX hK hgamma ht phi
  obtain ⟨ns, hns, hns_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have heq : (fun x => OscDual.eval (Z x) (phi : Euc d → ℝ)) =ᵐ[HRS.Whole.withDensityReal rho]
      (A phi : Euc d → ℝ) := by
    filter_upwards [ae_all_iff.2 hsection, hns_ae] with x hx hlimx
    have hpoint := (initialTestSection_eval_tendsto phi (Z x)).comp hns.tendsto_atTop
    have hpoint' : Tendsto (fun k => (A (initialTestSection phi (ns k)) : Euc d → ℝ) x)
        atTop (𝓝 (OscDual.eval (Z x) (phi : Euc d → ℝ))) :=
      hpoint.congr fun k => hx (ns k)
    exact tendsto_nhds_unique hpoint' hlimx
  exact heq.trans (initialScreenedLinear_ae hX hK hgamma ht phi).symm

end Response

/-- Physical specialization: classical existence, centered energy control,
and the positive response operator are all produced from thermal data. -/
theorem physical_initial_all_tests (hd : 2 ≤ d)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hbeta : 0 < beta)
    (hgamma : 0 ≤ gamma) (hrho : IsThermalEquilibrium d s a beta rho)
    {t : ℝ} (ht : 0 ≤ t) (Z : Euc d → OscDual d (wholeSpaceIndex d))
    (hcoord : ∀ alpha : MultiIndex d,
      (fun x => OscDual.coord (Z x) alpha) =ᵐ[HRS.Whole.withDensityReal rho]
        HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma
          (propagatorW ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) 0 t
            (oscTestFun (wholeSpaceIndex d) alpha))) :
    ∀ phi : Euc d → ℝ, IsOscTest (wholeSpaceIndex d) phi →
      (fun x => OscDual.eval (Z x) phi) =ᵐ[HRS.Whole.withDensityReal rho]
        HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma
          (propagatorW ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) 0 t phi) := by
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  have hsd : s < (d : ℝ) := by
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))]
  obtain ⟨M0, c, S, hc, hTc⟩ :=
    HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hbeta hrho
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  have hX : X1Input d s a beta gamma rho :=
    x1Input_of_exist hd hs0 hs ha hbeta gamma hrho
      (exist_of_thermal hd hs0 hs ha hbeta hrho)
  intro phi hphi
  exact initial_all_tests_of_basis hX hK hgamma ht Z hcoord ⟨phi, hphi⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.initialScreenedLinear_bound
#print axioms HRS.MS.ProClosureS111.physical_initial_all_tests
