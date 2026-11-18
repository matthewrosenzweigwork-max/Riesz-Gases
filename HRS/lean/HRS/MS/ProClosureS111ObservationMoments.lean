import HRS.MS.ProClosureS111SharedThermalLaw
import HRS.MS.ProClosureS111GaussianSpace
import HRS.MS.S111X2Aux42

/-!
Actual mixed second moments of the shared physical Gaussian law. The
prescribed covariance matrix is proved positive semidefinite using the
concrete physical Gram representation before it is identified with a
Gaussian second moment. The same-time side difference cancels the common
noise exactly. Its fourth moment is reused from the accepted Gaussian
linear-space theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.R26T6
open HRS.MC.QRSpec.Wick

variable {d : ℕ} {Omega : Type} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {s a beta gamma H : ℝ} {rho : Euc d → ℝ}
variable {Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d)}

/-- The exact prescribed mixed covariance is the actual second moment,
for arbitrary sides, times, and original oscillator tests. -/
theorem physical_shared_observation_second (hd : 2 ≤ d)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hrho : IsThermalEquilibrium d s a beta rho)
    (hZ : r26t6_SharedThermalLaw P s a beta gamma H rho Z)
    (n : ℕ) (side : Fin n → Fin 2) (ts : Fin n → ℝ)
    (phi : Fin n → Euc d → ℝ) (hts : ∀ j, ts j ∈ Icc (0 : ℝ) H)
    (hphi : ∀ j, IsOscTest (wholeSpaceIndex d) (phi j)) (j k : Fin n) :
    (∫ w, OscDual.eval (Z (side j) (ts j) w) (phi j) *
      OscDual.eval (Z (side k) (ts k) w) (phi k) ∂P) =
      (if side j = side k then HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho)
        (r26t6_preparation beta gamma (side j))
        (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts j) (phi j))
        (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts k) (phi k))
      else 0) + noiseCovW (r26t6_thermalCoeff d s a beta rho) beta⁻¹
        (ts j) (ts k) (phi j) (phi k) := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  have hsd : s < (d : ℝ) := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hX : X1Input d s a beta 0 rho :=
    x1Input_of_exist hd hs0 hs ha hbeta 0 hrho
      (exist_of_thermal hd hs0 hs ha hbeta hrho)
  obtain ⟨M0, c, S0, hc, hTc⟩ :=
    HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hbeta hrho
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  let f : Fin n → PhysicalFeatureSpace mu := fun i =>
    physicalLinear hX hK hbeta.le hgamma (side i) (ts i) ⟨phi i, hphi i⟩
  let S : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i l =>
    (if side i = side l then HRS.Whole.susceptibilityCov (rieszKernel d s) mu
      (r26t6_preparation beta gamma (side i))
      (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts i) (phi i))
      (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts l) (phi l))
    else 0) + noiseCovW (r26t6_thermalCoeff d s a beta rho) beta⁻¹
      (ts i) (ts l) (phi i) (phi l)
  have hS : S.PosSemidef := by
    have hGram : S = Matrix.gram ℝ f := by
      ext i l
      exact (physicalLinear_gram hd hs0 hs ha hbeta hgamma hrho hX hK
        (side i) (side l) (hts i).1 (hts l).1 ⟨phi i, hphi i⟩ ⟨phi l, hphi l⟩).symm
    rw [hGram]
    exact Matrix.posSemidef_gram ℝ f
  let V : Omega → EuclideanSpace ℝ (Fin n) := fun w =>
    WithLp.toLp 2 (fun i => OscDual.eval (Z (side i) (ts i) w) (phi i))
  have hVm : Measurable V := by
    refine (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (measurable_pi_iff.2 fun i => ?_)
    have hm := (gaussianOscEval (⟨phi i, hphi i⟩ : oscSub d (wholeSpaceIndex d))).continuous.measurable.comp
      ((hZ.evolution (side i)).meas (ts i))
    change Measurable (fun w =>
      gaussianOscEval (⟨phi i, hphi i⟩ : oscSub d (wholeSpaceIndex d))
        (Z (side i) (ts i) w)) at hm
    simpa only [gaussianOscEval_apply] using hm
  have hLaw : P.map V = multivariateGaussian 0 S :=
    hZ.joint n side ts phi hts hphi
  have hsecond := s111x2_gauss_mixed S hS j k
  rw [← hLaw, integral_map hVm.aemeasurable
    (show AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) => x j * x k) (P.map V)
      from (by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x j * x k)).aestronglyMeasurable)]
    at hsecond
  exact hsecond

/-- On the frozen coupling, the variance of the side difference is the sum
of the two propagated initial susceptibilities. The entire common-noise
covariance cancels, including at time zero. -/
theorem physical_shared_difference_moments (hd : 2 ≤ d)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hrho : IsThermalEquilibrium d s a beta rho)
    (hZ : r26t6_SharedThermalLaw P s a beta gamma H rho Z)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) {phi : Euc d → ℝ}
    (hphi : IsOscTest (wholeSpaceIndex d) phi) :
    let D : Omega → ℝ := fun w =>
      OscDual.eval (Z 0 t w) phi - OscDual.eval (Z 1 t w) phi
    let f := propagatorW (r26t6_thermalCoeff d s a beta rho) 0 t phi
    MemLp D 4 P ∧
      (∫ w, D w ^ 2 ∂P) = HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma f f +
        HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) beta f f ∧
      (∫ w, D w ^ 4 ∂P) = 3 * (∫ w, D w ^ 2 ∂P) ^ 2 := by
  let X : Omega → ℝ := fun w => OscDual.eval (Z 0 t w) phi
  let Y : Omega → ℝ := fun w => OscDual.eval (Z 1 t w) phi
  let D : Omega → ℝ := fun w => X w - Y w
  obtain ⟨G, hG, hmem⟩ := physical_observation_gaussian_space Z hZ
  have hXm : X ∈ G := hmem 0 t ht phi hphi
  have hYm : Y ∈ G := hmem 1 t ht phi hphi
  have hDm : D ∈ G := G.sub_mem hXm hYm
  have hX4 := (hG X hXm).1
  have hY4 := (hG Y hYm).1
  have hD := hG D hDm
  let f := propagatorW (r26t6_thermalCoeff d s a beta rho) 0 t phi
  let A := HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma f f
  let B := HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) beta f f
  let N := noiseCovW (r26t6_thermalCoeff d s a beta rho) beta⁻¹ t t phi phi
  have hsec := physical_shared_observation_second hd hs0 hs ha hbeta hgamma hrho hZ
    2 (fun i : Fin 2 => i) (fun _ => t) (fun _ => phi) (fun _ => ht) (fun _ => hphi)
  have hXX : (∫ w, X w ^ 2 ∂P) = A + N := by
    simpa only [X, A, N, f, sq, r26t6_preparation, ite_true] using hsec 0 0
  have hYY : (∫ w, Y w ^ 2 ∂P) = B + N := by
    simpa [Y, B, N, f, sq, r26t6_preparation] using hsec 1 1
  have hXY : (∫ w, X w * Y w ∂P) = N := by
    simpa [X, Y, N] using hsec 0 1
  have hDsq : (∫ w, D w ^ 2 ∂P) = A + B := by
    have he : (fun w => D w ^ 2) =
        fun w => (X w ^ 2 + Y w ^ 2) - 2 * (X w * Y w) := by
      funext w
      dsimp [D]
      ring
    rw [he]
    change (∫ w, ((fun x => X x ^ 2) + (fun x => Y x ^ 2)) w -
      (fun x => 2 * (X x * Y x)) w ∂P) = A + B
    rw [integral_sub ((qrpw_int_sq hX4).add (qrpw_int_sq hY4))
      ((qrpw_int_mul hX4 hY4).const_mul 2)]
    change (∫ w, X w ^ 2 + Y w ^ 2 ∂P) -
      ∫ w, 2 * (X w * Y w) ∂P = A + B
    rw [integral_add (qrpw_int_sq hX4) (qrpw_int_sq hY4), integral_const_mul,
      hXX, hYY, hXY]
    ring
  exact ⟨hD.1, hDsq, hD.2⟩

#print axioms physical_shared_observation_second
#print axioms physical_shared_difference_moments

end HRS.MS.ProClosureS111
