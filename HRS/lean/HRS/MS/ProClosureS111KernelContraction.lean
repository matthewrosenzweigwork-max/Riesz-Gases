import HRS.MS.ProClosureS111CrossDensityZero
import HRS.MS.ProClosureS111ObservationMoments
import HRS.MS.S21G2_K11b
import HRS.MS.S21L_G11B

/-!
The accepted full Hilbert--Schmidt Wick contraction on the actual shared
thermal probability space.  The common Gaussian observation subspace,
the zero mass of arbitrary frozen cross-densities, and their actual
covariance coefficients are produced here.  The field realization supplies
the raw Wick variable; no Wick contraction or centered-density premise is
assumed.  The native drift normalization -2*b is retained exactly.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.R26T3 HRS.MS.R26T6
open HRS.MC.QRSpec.Wick

variable {d : ℕ} {Omega : Type} [MeasurableSpace Omega]

/-- The accepted coefficient-centering identity works on any probability
space; no ProductGaussian realization is needed for this algebraic step. -/
theorem wick_center_iff_any (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (P : Measure Omega) [IsProbabilityMeasure P] (basis : ℕ → Euc d → ℝ)
    (hbasis : ∀ i, IsR2Test (basis i)) (z : ℕ → Omega → ℝ)
    (h : Euc d → Euc d → ℝ)
    (hh : Integrable (fun xy : Euc d × Euc d => h xy.1 xy.2) (mu.prod mu))
    (Q : Omega → ℝ) :
    IsR2WickChaos P mu basis z (r2CenterKernel mu h) Q ↔
      IsR2WickChaos P mu basis z h Q := by
  have hc : (fun i j => r2WickCoeff mu basis (r2CenterKernel mu h) i j) =
      (fun i j => r2WickCoeff mu basis h i j) := by
    funext i j
    exact s21l_coeff_center hbasis hh i j
  change HRS.TendstoL2 P
      (HRS.MS.R2Chaos.s94Sec P z
        (fun i j => r2WickCoeff mu basis (r2CenterKernel mu h) i j)) Q ↔
    HRS.TendstoL2 P
      (HRS.MS.R2Chaos.s94Sec P z (fun i j => r2WickCoeff mu basis h i j)) Q
  rw [hc]

theorem cross_density_double_integral (rho chi eta : Euc d → ℝ)
    (hrho : HRS.Whole.IsProbDensity rho) (hpos : ∀ x, 0 < rho x)
    (h : Euc d → Euc d → ℝ) :
    (∫ x, ∫ y, h x y * (chi x / rho x) * (eta y / rho y)
      ∂HRS.Whole.withDensityReal rho ∂HRS.Whole.withDensityReal rho) =
        ∫ x, ∫ y, h x y * chi x * eta y := by
  rw [HRS.MS.Gap.gap1_integral_wdr hrho.measurable hrho.nonneg]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change rho x * (∫ y, h x y * (chi x / rho x) * (eta y / rho y)
      ∂HRS.Whole.withDensityReal rho) = ∫ y, h x y * chi x * eta y
  rw [HRS.MS.Gap.gap1_integral_wdr hrho.measurable hrho.nonneg
      (fun y => h x y * (chi x / rho x) * (eta y / rho y)),
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  have hx : rho x ≠ 0 := ne_of_gt (hpos x)
  have hy : rho y ≠ 0 := ne_of_gt (hpos y)
  field_simp

/-- Product-measure change of density preserves the absolute spatial
integrability required by the frozen cubic formula. -/
theorem cross_density_product_integrable (rho chi eta : Euc d → ℝ)
    (hrho : HRS.Whole.IsProbDensity rho) (hpos : ∀ x, 0 < rho x)
    (h : Euc d → Euc d → ℝ)
    (hi : Integrable (fun xy : Euc d × Euc d =>
      h xy.1 xy.2 * (chi xy.1 / rho xy.1) * (eta xy.2 / rho xy.2))
      ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho))) :
    Integrable (fun xy : Euc d × Euc d => h xy.1 xy.2 * chi xy.1 * eta xy.2)
      ((volume : Measure (Euc d)).prod volume) := by
  have hm : Measurable (fun x => ENNReal.ofReal (rho x)) :=
    ENNReal.measurable_ofReal.comp hrho.measurable
  have hp : Measurable (fun xy : Euc d × Euc d =>
      ENNReal.ofReal (rho xy.1) * ENNReal.ofReal (rho xy.2)) :=
    (hm.comp measurable_fst).mul (hm.comp measurable_snd)
  have hlt : ∀ᵐ xy ∂((volume : Measure (Euc d)).prod volume),
      ENNReal.ofReal (rho xy.1) * ENNReal.ofReal (rho xy.2) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  unfold HRS.Whole.withDensityReal at hi
  rw [prod_withDensity hm hm] at hi
  have hw := (integrable_withDensity_iff_integrable_smul' hp hlt).1 hi
  refine hw.congr (ae_of_all _ fun xy => ?_)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hrho.nonneg xy.1),
    ENNReal.toReal_ofReal (hrho.nonneg xy.2), smul_eq_mul]
  have hx : rho xy.1 ≠ 0 := ne_of_gt (hpos xy.1)
  have hy : rho xy.2 ≠ 0 := ne_of_gt (hpos xy.2)
  field_simp

/-- The physical drift pairing for the original arbitrary frozen
cross-densities.  This is the spatial contraction input to D02; time
integrability is handled by the weighted-field and interval estimates. -/
theorem physical_drift_wick_cross_density_pair (hd : 2 ≤ d)
    {s a beta gamma T u H : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma) (hu : 0 ≤ u)
    (hH : u + T ≤ H) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d))
    (hZ : r26t6_SharedThermalLaw P s a beta gamma H rho Z)
    (side : Fin 2) (tau : Fin 3 → Icc (0 : ℝ) T)
    (phi : Fin 3 → Euc d → ℝ)
    (hphi : ∀ i, IsOscTest (wholeSpaceIndex d : ℝ) (phi i))
    (chi : Fin 3 → ℝ → Euc d → ℝ)
    (hchi : IsR2CrossDensities d s a beta (r26t6_preparation beta gamma side)
      rho T u tau phi chi)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (u + T))
    (basis : ℕ → Euc d → ℝ) (hbasis : IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis)
    (b : Omega → ℝ) (hb : MemLp b 2 P)
    (h : Euc d → Euc d → ℝ) (hsym : ∀ x y, h x y = h y x)
    (hh : MemLp (fun xy : Euc d × Euc d => h xy.1 xy.2) 2
      ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho)))
    (hW : IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
      (fun i w => OscDual.eval (Z side r w) (basis i)) h (fun w => -2 * b w))
    (k l : Fin 3) :
    Integrable (fun xy : Euc d × Euc d => h xy.1 xy.2 * chi k r xy.1 * chi l r xy.2)
      ((volume : Measure (Euc d)).prod volume) ∧
    Integrable (fun w => b w * OscDual.eval (Z side (u + tau k) w) (phi k) *
      OscDual.eval (Z side (u + tau l) w) (phi l)) P ∧
      (∫ w, b w * OscDual.eval (Z side (u + tau k) w) (phi k) *
        OscDual.eval (Z side (u + tau l) w) (phi l) ∂P) =
          -∫ x, ∫ y, h x y * chi k r x * chi l r y := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  have hX : X1Input d s a beta 0 rho :=
    x1Input_of_exist hd hs0 hs ha hbeta 0 hrho
      (exist_of_thermal hd hs0 hs ha hbeta hrho)
  have hprep : 0 ≤ r26t6_preparation beta gamma side := by
    fin_cases side <;> simp [r26t6_preparation, hgamma, hbeta.le]
  have hrH : r ∈ Icc (0 : ℝ) H := ⟨hr.1, hr.2.trans hH⟩
  have htH : ∀ j, u + (tau j : ℝ) ∈ Icc (0 : ℝ) H := fun j =>
    ⟨add_nonneg hu (tau j).property.1,
      by linarith [ (tau j).property.2 ]⟩
  have hu0 := physical_cross_density_zero_mass hd hs0 hs ha hbeta hprep hu
    hrho tau phi hphi chi hchi
  let z : ℕ → Omega → ℝ := fun i w => OscDual.eval (Z side r w) (basis i)
  let X : Omega → ℝ := fun w => OscDual.eval (Z side (u + tau k) w) (phi k)
  let Y : Omega → ℝ := fun w => OscDual.eval (Z side (u + tau l) w) (phi l)
  let Q : Omega → ℝ := fun w => -b w
  obtain ⟨G, hG, hmem⟩ := physical_observation_gaussian_space Z hZ
  have hbasiso : ∀ i, IsOscTest (wholeSpaceIndex d : ℝ) (basis i) := fun i =>
    ⟨(hbasis.1 i).1, memOsc_schwartz _ ((hbasis.1 i).2.toSchwartzMap (hbasis.1 i).1)⟩
  have hz : ∀ i, z i ∈ G := fun i => hmem side r hrH (basis i) (hbasiso i)
  have hXm : X ∈ G := hmem side _ (htH k) (phi k) (hphi k)
  have hYm : Y ∈ G := hmem side _ (htH l) (phi l) (hphi l)
  have hQ : MemLp Q 2 P := hb.neg
  have hW' : IsR2WickChaos P mu basis z (r2CenterKernel mu h) (fun w => 2 * Q w) := by
    apply (wick_center_iff_any mu P basis hbasis.1 z h (hh.integrable one_le_two) _).2
    convert hW using 1
    funext w
    dsimp [Q]
    ring
  have hcov : ∀ i j, (∫ w, z i w * OscDual.eval (Z side (u + tau j) w) (phi j) ∂P) =
      ∫ x, basis i x * (chi j r x / rho x) ∂mu := by
    intro i j
    have hsecond := physical_shared_observation_second hd hs0 hs ha hbeta hgamma hrho hZ
      2 (fun _ => side) ![r, u + tau j] ![basis i, phi j]
      (by intro q; fin_cases q; exact hrH; exact htH j)
      (by intro q; fin_cases q; exact hbasiso i; exact hphi j) 0 1
    have he : (∫ x, basis i x * (chi j r x / rho x) ∂mu) = ∫ x, basis i x * chi j r x := by
      rw [show (fun x => basis i x * (chi j r x / rho x)) =
        (fun x => (chi j r x / rho x) * basis i x) by funext x; ring]
      exact cross_density_pair_relative rho (chi j r) (basis i) hrho.1.1 hX.pos
    rw [he, ((hchi j r hr).2 (basis i) (hbasiso i)).2]
    simpa [linearGaussianCov, r26t6_thermalCoeff, z] using hsecond
  have hpair := r26t3_kernel_wick_pair mu basis hbasis P G hG z hz X Y Q hXm hYm hQ
    h hsym hh hW' (fun x => chi k r x / rho x) (fun x => chi l r x / rho x)
    (hu0 k r hr) (hu0 l r hr) (fun i => hcov i k) (fun i => hcov i l)
  have hspatial := cross_density_product_integrable rho (chi k r) (chi l r)
    hrho.1.1 hX.pos h hpair.1
  have hint : Integrable (fun w => b w * X w * Y w) P := by
    have hXY : MemLp (fun w => X w * Y w) 2 P :=
      qrpw_memLp2_mul (hG X hXm).1 (hG Y hYm).1
    exact (hb.integrable_mul hXY).congr (ae_of_all _ fun w => by
      simp only [Pi.mul_apply]
      ring)
  refine ⟨hspatial, hint, ?_⟩
  have he := hpair.2
  rw [cross_density_double_integral rho (chi k r) (chi l r) hrho.1.1 hX.pos h] at he
  have hneg : (∫ w, Q w * X w * Y w ∂P) = -(∫ w, b w * X w * Y w ∂P) := by
    rw [show (fun w => Q w * X w * Y w) = (fun w => -(b w * X w * Y w)) by
      funext w; dsimp [Q]; ring]
    exact integral_neg _
  rw [hneg] at he
  linarith

#print axioms physical_drift_wick_cross_density_pair

end HRS.MS.ProClosureS111
