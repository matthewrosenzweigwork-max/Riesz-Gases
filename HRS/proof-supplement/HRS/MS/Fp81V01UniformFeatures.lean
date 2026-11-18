import HRS.MS.ProClosureS111InitialGaussianBounds
import HRS.MS.ProClosureS111OrbitSummable
import HRS.MS.ProClosureS111PhysicalFeatures
import HRS.MS.ProClosureS111PhysicalFeatureBounds

/-!
Horizon-free increment bounds for the physical initial Gaussian features.
The same constant works for every nonnegative preparation parameter.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.ProClosureS111 HRS.MS.R2WinOrb
  HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.R26T6

theorem fp81v01_initial_gaussian_increment_bound {d : ℕ} (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    {K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ]
      Lp ℝ 2 (HRS.Whole.withDensityReal rho)} {Mg : ℝ}
    (hK : KRep (rieszKernel d s) (HRS.Whole.withDensityReal rho) K Mg) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (theta : ℝ) (htheta : 0 ≤ theta),
      ∀ t v : ℝ, 0 ≤ t → 0 ≤ v →
        Summable (fun alpha : MultiIndex d =>
          ‖initialGaussianFeature hK htheta C t
              (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha) -
            initialGaussianFeature hK htheta C v
              (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha)‖ ^ 2) ∧
        (∑' alpha : MultiIndex d,
          ‖initialGaussianFeature hK htheta C t
              (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha) -
            initialGaussianFeature hK htheta C v
              (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha)‖ ^ 2)
          ≤ L * |t - v| := by
  classical
  have hsd : s < (d : ℝ) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := fun alpha : MultiIndex d =>
    oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  let mu := HRS.Whole.withDensityReal rho
  obtain ⟨B, hB, hmag, hinc⟩ :=
    physical_value_time_bound hd hs0 hsd ha hbeta hrho
  have hm : ∀ alpha t, 0 ≤ t → MemLp (propagatorW C 0 t (phi alpha)) 2 mu := by
    intro alpha t ht
    exact MemLp.of_bound (hmag alpha t ht).1.aestronglyMeasurable
      (B * s103_b d alpha)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using (hmag alpha t ht).2 x)
  have htoLp : ∀ alpha t, 0 ≤ t →
      ‖s111x2_toLp mu (propagatorW C 0 t (phi alpha))‖ ≤ B * s103_b d alpha := by
    intro alpha t ht
    have hpoint : ∀ᵐ x ∂mu,
        ‖s111x2_toLp mu (propagatorW C 0 t (phi alpha)) x‖ ≤ B * s103_b d alpha := by
      filter_upwards [s111x2_toLp_ae (hm alpha t ht)] with x hx
      rw [hx, Real.norm_eq_abs]
      exact (hmag alpha t ht).2 x
    have h := Lp.norm_le_of_ae_bound
      (mul_nonneg hB (s103_b_nonneg alpha)) hpoint
    have h1 : measureUnivNNReal mu = 1 := by simp [measureUnivNNReal]
    rw [h1] at h
    simpa using h
  have htoLp_inc : ∀ alpha t v, 0 ≤ t → 0 ≤ v →
      ‖s111x2_toLp mu (propagatorW C 0 t (phi alpha)) -
        s111x2_toLp mu (propagatorW C 0 v (phi alpha))‖ ≤
        B * s103_b d alpha * |t - v| := by
    intro alpha t v ht hv
    have hpoint : ∀ᵐ x ∂mu,
        ‖(s111x2_toLp mu (propagatorW C 0 t (phi alpha)) -
          s111x2_toLp mu (propagatorW C 0 v (phi alpha)) : Lp ℝ 2 mu) x‖ ≤
          B * s103_b d alpha * |t - v| := by
      filter_upwards [Lp.coeFn_sub (s111x2_toLp mu (propagatorW C 0 t (phi alpha)))
          (s111x2_toLp mu (propagatorW C 0 v (phi alpha))),
        s111x2_toLp_ae (hm alpha t ht), s111x2_toLp_ae (hm alpha v hv)] with x hx h1 h2
      rw [hx, Pi.sub_apply, h1, h2, Real.norm_eq_abs]
      exact hinc alpha t v ht hv x
    have h := Lp.norm_le_of_ae_bound
      (mul_nonneg (mul_nonneg hB (s103_b_nonneg alpha)) (abs_nonneg _)) hpoint
    have h1 : measureUnivNNReal mu = 1 := by simp [measureUnivNNReal]
    rw [h1] at h
    simpa using h
  have hA_norm : ∀ (theta : ℝ) (htheta : 0 ≤ theta) alpha t, 0 ≤ t →
      ‖initialGaussianFeature hK htheta C t (phi alpha)‖ ≤ B * s103_b d alpha := by
    intro theta htheta alpha t ht
    exact (initialGaussianFeature_norm_le hK htheta C t (phi alpha)).trans
      (htoLp alpha t ht)
  have hA_inc : ∀ (theta : ℝ) (htheta : 0 ≤ theta) alpha t v,
      0 ≤ t → 0 ≤ v →
      ‖initialGaussianFeature hK htheta C t (phi alpha) -
        initialGaussianFeature hK htheta C v (phi alpha)‖ ≤
        B * s103_b d alpha * |t - v| := by
    intro theta htheta alpha t v ht hv
    exact (initialGaussianFeature_sub_norm_le hK htheta C t v (phi alpha)).trans
      (htoLp_inc alpha t v ht hv)
  have hsquare := stationary_weight_square_summable (d := d) (by omega)
  refine ⟨2 * B ^ 2 * (∑' alpha : MultiIndex d, s103_b d alpha ^ 2), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B))
      (tsum_nonneg fun alpha => sq_nonneg (s103_b d alpha))
  · intro theta htheta t v ht hv
    let A := fun q (alpha : MultiIndex d) =>
      initialGaussianFeature hK htheta C q (phi alpha)
    have hsqinc : ∀ alpha : MultiIndex d,
        ‖A t alpha - A v alpha‖ ^ 2 ≤
          2 * B ^ 2 * s103_b d alpha ^ 2 * |t - v| := by
      intro alpha
      have hmagnitude : ‖A t alpha - A v alpha‖ ≤ 2 * B * s103_b d alpha := by
        calc
          _ ≤ ‖A t alpha‖ + ‖A v alpha‖ := norm_sub_le _ _
          _ ≤ B * s103_b d alpha + B * s103_b d alpha :=
            add_le_add (hA_norm theta htheta alpha t ht) (hA_norm theta htheta alpha v hv)
          _ = _ := by ring
      have htime := hA_inc theta htheta alpha t v ht hv
      have hbase : 0 ≤ B * s103_b d alpha :=
        mul_nonneg hB (s103_b_nonneg alpha)
      calc
        _ = ‖A t alpha - A v alpha‖ * ‖A t alpha - A v alpha‖ := by ring
        _ ≤ ‖A t alpha - A v alpha‖ *
              (B * s103_b d alpha * |t - v|) :=
          mul_le_mul_of_nonneg_left htime (norm_nonneg _)
        _ ≤ (2 * B * s103_b d alpha) *
              (B * s103_b d alpha * |t - v|) :=
          mul_le_mul_of_nonneg_right hmagnitude
            (mul_nonneg hbase (abs_nonneg _))
        _ = 2 * B ^ 2 * s103_b d alpha ^ 2 * |t - v| := by ring
    have hmajor : Summable (fun alpha : MultiIndex d =>
        2 * B ^ 2 * s103_b d alpha ^ 2 * |t - v|) :=
      (hsquare.mul_left (2 * B ^ 2)).mul_right _
    have hsum : Summable (fun alpha : MultiIndex d => ‖A t alpha - A v alpha‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hsqinc hmajor
    refine ⟨hsum, ?_⟩
    calc
      _ ≤ ∑' alpha : MultiIndex d, 2 * B ^ 2 * s103_b d alpha ^ 2 * |t - v| :=
        hsum.tsum_le_tsum hsqinc hmajor
      _ = (2 * B ^ 2 * (∑' alpha : MultiIndex d, s103_b d alpha ^ 2)) * |t - v| := by
        rw [tsum_mul_right, tsum_mul_left]

theorem fp81v01_physicalLinear_uniform_summability {d : ℕ} (hd : 2 ≤ d)
    {s a beta gamma : ℝ} {rho : Euc d → ℝ}
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    {K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ]
      Lp ℝ 2 (HRS.Whole.withDensityReal rho)} {Mg : ℝ}
    (hX : X1Input d s a beta 0 rho)
    (hK : KRep (rieszKernel d s) (HRS.Whole.withDensityReal rho) K Mg)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hbeta' : 0 < beta) (hrho : IsThermalEquilibrium d s a beta rho) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i : Fin 2, ∀ t : ℝ, 0 ≤ t →
      Summable (fun alpha : MultiIndex d =>
        ‖physicalLinear hX hK hbeta hgamma i t
          (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) ∧
      (∑' alpha : MultiIndex d,
        ‖physicalLinear hX hK hbeta hgamma i t
          (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) ≤ L := by
  classical
  obtain ⟨Lc, hLc, hcov⟩ := physical_covariance_all_time hd s a beta hs0 hs ha hbeta'
  obtain ⟨M, hM⟩ := hX.bdd
  have hM0 : 0 ≤ M := (hX.nonneg 0).trans (hM 0)
  have hsquare := stationary_weight_square_summable (d := d) (by omega)
  let m : ℝ := (wholeSpaceIndex d : ℝ)
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := fun alpha : MultiIndex d => oscTestFun m alpha
  have hphi0 : ∀ alpha, IsOscTest 0 (phi alpha) := by
    intro alpha
    have hbase : IsOscTest 0 (oscTestFun 0 alpha) :=
      HRS.MS.GenPath.s56_isOscTest 0 alpha
    have heq : phi alpha =
        oscEigenvalue d alpha ^ (-(m / 2)) • oscTestFun 0 alpha := by
      funext x
      simp [phi, m, oscTestFun]
    rw [heq]
    exact (HRS.MS.S111X1.oscSub d 0).smul_mem _
      (HRS.MS.S111X1.mem_oscSub.2 hbase)
  have hphi_bound : ∀ alpha, (∫ x, phi alpha x ^ 2 ∂HRS.Whole.withDensityReal rho) ≤
      M * (s103_b d alpha) ^ 2 := by
    intro alpha
    let psi0 : HRS.MS.S111X1.oscSub d 0 := ⟨phi alpha, hphi0 alpha⟩
    have hinput := initialTest_sq_bound hX.meas hX.nonneg hM0 hM
      (show 0 ≤ (0 : ℝ) by norm_num) psi0
    have hnorm0 := s103_oscNorm_test m 0 alpha
    have hnormle : oscNorm 0 (phi alpha) ≤ s103_b d alpha := by
      rw [hnorm0]
      unfold s103_b
      apply Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue alpha)
      dsimp [m, wholeSpaceIndex]
      push_cast
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      nlinarith
    have hnonneg : 0 ≤ oscNorm 0 (phi alpha) := Real.sqrt_nonneg _
    have hinput' : (∫ x, phi alpha x ^ 2 ∂HRS.Whole.withDensityReal rho) ≤
        M * (oscNorm 0 (phi alpha)) ^ 2 := by
      simpa only [psi0] using hinput
    calc
      _ ≤ M * (oscNorm 0 (phi alpha)) ^ 2 := hinput'
      _ ≤ M * (s103_b d alpha) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hnonneg hnormle 2) hM0
  have hpoint : ∀ i : Fin 2, ∀ t : ℝ, 0 ≤ t → ∀ alpha : MultiIndex d,
      ‖physicalLinear hX hK hbeta hgamma i t
        (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 ≤
        (Lc * M) * s103_b d alpha ^ 2 := by
    intro i t ht alpha
    let psi := initialTestBasis (wholeSpaceIndex d) alpha
    let theta := r26t6_preparation beta gamma i
    have htheta : 0 ≤ theta := by
      simp only [theta, r26t6_preparation]
      split_ifs <;> positivity
    have hsame : ‖physicalLinear hX hK hbeta hgamma i t psi‖ ^ 2 =
        linearGaussianCov (r26t6_thermalCoeff d s a beta rho) beta⁻¹
          (HRS.Whole.susceptibilityCov (rieszKernel d s)
            (HRS.Whole.withDensityReal rho) theta)
          t t (phi alpha) (phi alpha) := by
      rw [← real_inner_self_eq_norm_sq,
        physicalLinear_gram hd hs0 hs ha hbeta' hgamma hrho hX hK i i ht ht]
      rw [show (psi : Euc d → ℝ) = phi alpha by rfl]
      simp only [ite_true, linearGaussianCov, theta, r26t6_preparation]
    have hphiLp := x1_osc_memLp hX.meas hX.nonneg hM (HRS.MS.GenPath.s56_isOscTest m alpha)
    have hproj := projMean_sq_le hX.meas hX.nonneg hrho.1.1.integral_one hX.int hphiLp
    have hcov' := hcov rho hrho theta htheta t ht (phi alpha)
      (HRS.MS.GenPath.s56_isOscTest m alpha)
    calc
      _ = _ := hsame
      _ ≤ Lc * ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal rho)
          (phi alpha) x ^ 2 ∂HRS.Whole.withDensityReal rho := hcov'.2
      _ ≤ Lc * ∫ x, (phi alpha) x ^ 2 ∂HRS.Whole.withDensityReal rho :=
        mul_le_mul_of_nonneg_left hproj hLc.le
      _ ≤ Lc * (M * s103_b d alpha ^ 2) :=
        mul_le_mul_of_nonneg_left (hphi_bound alpha) hLc.le
      _ = _ := by ring
  let L := (Lc * M) * (∑' alpha : MultiIndex d, s103_b d alpha ^ 2)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (mul_nonneg hLc.le hM0)
      (tsum_nonneg fun alpha => sq_nonneg (s103_b d alpha))
  refine ⟨L, hL, fun i t ht => ?_⟩
  have hmajor : Summable (fun alpha : MultiIndex d =>
      (Lc * M) * s103_b d alpha ^ 2) := hsquare.mul_left (Lc * M)
  have hsum : Summable (fun alpha : MultiIndex d =>
      ‖physicalLinear hX hK hbeta hgamma i t
        (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (hpoint i t ht) hmajor
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' alpha : MultiIndex d, (Lc * M) * s103_b d alpha ^ 2 :=
      hsum.tsum_le_tsum (hpoint i t ht) hmajor
    _ = L := by rw [tsum_mul_left]

#print axioms fp81v01_initial_gaussian_increment_bound
#print axioms fp81v01_physicalLinear_uniform_summability

end HRS.Fp81.V01
