import HRS.MS.ProClosureS111InitialGaussianFeatures
import HRS.MS.ProClosureS111OrbitSummable

/-!
The actual initial Gaussian features satisfy the summed bounds required
for continuous paired paths. The positive square root and mean projection
are contractions; the physical scalar terminal derivative supplies the
time increment. No Poincare inequality is needed for this existence step.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.Whole.Q34 HRS.MS.R2WinOrb HRS.MS.S111X2

variable {d : ℕ}

theorem physical_value_time_bound (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := fun alpha : MultiIndex d =>
      oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ alpha t, 0 ≤ t → Continuous (propagatorW C 0 t (phi alpha)) ∧
        ∀ x, |propagatorW C 0 t (phi alpha) x| ≤ B * s103_b d alpha) ∧
      (∀ alpha t v, 0 ≤ t → 0 ≤ v → ∀ x,
        |propagatorW C 0 t (phi alpha) x - propagatorW C 0 v (phi alpha) x| ≤
          B * s103_b d alpha * |t - v|) := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := fun alpha : MultiIndex d => oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  obtain ⟨B, c, hB, hc, hbound⟩ := s103_orbit_iter hd hs0 hsd ha hbeta hrho
  have hspatial : ∀ alpha z, 0 ≤ z →
      Continuous (propagatorW C 0 z (phi alpha)) ∧ ∀ x,
        |propagatorW C 0 z (phi alpha) x| ≤ B * s103_b d alpha ∧
        |propagatorW C 0 z (generatorW C z (phi alpha)) x| ≤ B * s103_b d alpha := by
    intro alpha z hz
    obtain ⟨hex0, hex1⟩ := physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha hz
    have hb0 := hbound alpha z hz 0 (by norm_num) _
      (HRS.MS.Fcau.propagatorW_isClassical hex0) 0 ⟨le_rfl, hz⟩
    have hb1 := hbound alpha z hz 1 (by norm_num) _
      (HRS.MS.Fcau.propagatorW_isClassical hex1) 0 ⟨le_rfl, hz⟩
    have hA := mul_nonneg hB (s103_b_nonneg alpha)
    have hgen : generatorW C z = generatorW C 0 := by
      change generatorW ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) z =
        generatorW ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) 0
      rw [s103_coeff_eq s a beta rho]
      rfl
    refine ⟨hb0.1.continuous, fun x => ⟨?_, ?_⟩⟩
    · simpa only [C, phi, Function.iterate_zero, id_eq, norm_iteratedFDeriv_zero,
        Real.norm_eq_abs] using s103_cb_of_E hA hb0.2 0 (Nat.zero_le _) x
    · simpa only [C, phi, Function.iterate_one, hgen, norm_iteratedFDeriv_zero,
        Real.norm_eq_abs] using s103_cb_of_E hA hb1.2 0 (Nat.zero_le _) x
  refine ⟨B, hB, fun alpha t ht =>
    ⟨(hspatial alpha t ht).1, fun x => ((hspatial alpha t ht).2 x).1⟩, ?_⟩
  intro alpha t v ht hv x
  have hder : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun z => propagatorW C 0 z (phi alpha) x)
      (propagatorW C 0 z (generatorW C z (phi alpha)) x) (Ici (0 : ℝ)) z :=
    fun z hz => physical_terminal_derivative_zero hd hs0 hsd ha hbeta hrho alpha hz x
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => propagatorW C 0 z (phi alpha) x)
    (f' := fun z => propagatorW C 0 z (generatorW C z (phi alpha)) x)
    (s := Ici (0 : ℝ)) hder
    (fun z hz => by simpa only [Real.norm_eq_abs] using ((hspatial alpha z hz).2 x).2)
    (convex_Ici (0 : ℝ)) hv ht
  simpa only [Real.norm_eq_abs] using h

theorem physical_initial_gaussian_features_summable (hd : 2 ≤ d)
    {s a beta theta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) (htheta : 0 ≤ theta)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d s a beta rho)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    {K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal rho)}
    {Mg : ℝ} (hK : KRep (rieszKernel d s) (HRS.Whole.withDensityReal rho) K Mg)
    (H : ℝ) (hH : 0 ≤ H) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let A := fun t (alpha : MultiIndex d) => initialGaussianFeature hK htheta C t
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha)
    (∀ t ∈ Icc (0 : ℝ) H, Summable (fun alpha => ‖A t alpha‖ ^ 2)) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ t v, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
        Summable (fun alpha => ‖A t alpha - A v alpha‖ ^ 2) ∧
          (∑' alpha, ‖A t alpha - A v alpha‖ ^ 2) ≤ L * |t - v| := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let mu := HRS.Whole.withDensityReal rho
  let phi := fun alpha : MultiIndex d => oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  let A := fun t (alpha : MultiIndex d) => initialGaussianFeature hK htheta C t (phi alpha)
  obtain ⟨B, hB, hmag, hinc⟩ := physical_value_time_bound hd hs0 hsd ha hbeta hrho
  have hm : ∀ alpha t, 0 ≤ t → MemLp (propagatorW C 0 t (phi alpha)) 2 mu := by
    intro alpha t ht
    exact MemLp.of_bound (hmag alpha t ht).1.aestronglyMeasurable (B * s103_b d alpha)
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
  have hAnorm : ∀ alpha t, 0 ≤ t → ‖A t alpha‖ ≤ B * s103_b d alpha := by
    intro alpha t ht
    exact (initialGaussianFeature_norm_le hK htheta C t (phi alpha)).trans (htoLp alpha t ht)
  have hAinc : ∀ alpha t v, 0 ≤ t → 0 ≤ v →
      ‖A t alpha - A v alpha‖ ≤ B * s103_b d alpha * |t - v| := by
    intro alpha t v ht hv
    exact (initialGaussianFeature_sub_norm_le hK htheta C t v (phi alpha)).trans
      (htoLp_inc alpha t v ht hv)
  have hsquare := stationary_weight_square_summable (d := d) (by omega)
  have hsqinc : ∀ alpha t v, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
      ‖A t alpha - A v alpha‖ ^ 2 ≤ B ^ 2 * H * s103_b d alpha ^ 2 * |t - v| := by
    intro alpha t v ht hv
    have hdelta : |t - v| ≤ H := abs_le.2 ⟨by linarith [ht.1, hv.2], by linarith [ht.2, hv.1]⟩
    have htime : |t - v| ^ 2 ≤ H * |t - v| := by
      nlinarith [abs_nonneg (t - v)]
    calc
      _ ≤ (B * s103_b d alpha * |t - v|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hAinc alpha t v ht.1 hv.1) 2
      _ = (B * s103_b d alpha) ^ 2 * |t - v| ^ 2 := by ring
      _ ≤ (B * s103_b d alpha) ^ 2 * (H * |t - v|) := by gcongr
      _ = _ := by ring
  refine ⟨?_, B ^ 2 * H * (∑' alpha : MultiIndex d, s103_b d alpha ^ 2),
    mul_nonneg (mul_nonneg (sq_nonneg _) hH) (tsum_nonneg fun _ => sq_nonneg _), ?_⟩
  · intro t ht
    have hmajor : Summable (fun alpha : MultiIndex d => B ^ 2 * s103_b d alpha ^ 2) :=
      hsquare.mul_left _
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun alpha => ?_) hmajor
    exact (pow_le_pow_left₀ (norm_nonneg _) (hAnorm alpha t ht.1) 2).trans_eq (by ring)
  · intro t v ht hv
    have hmajor : Summable (fun alpha : MultiIndex d =>
        B ^ 2 * H * s103_b d alpha ^ 2 * |t - v|) :=
      (hsquare.mul_left (B ^ 2 * H)).mul_right _
    have hsum : Summable (fun alpha => ‖A t alpha - A v alpha‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun alpha => hsqinc alpha t v ht hv) hmajor
    refine ⟨hsum, ?_⟩
    calc
      _ ≤ ∑' alpha : MultiIndex d, B ^ 2 * H * s103_b d alpha ^ 2 * |t - v| :=
        hsum.tsum_le_tsum (fun alpha => hsqinc alpha t v ht hv) hmajor
      _ = _ := by rw [tsum_mul_right, tsum_mul_left]

#print axioms physical_initial_gaussian_features_summable

end HRS.MS.ProClosureS111
