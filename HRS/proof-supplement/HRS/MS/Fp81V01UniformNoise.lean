import HRS.MS.ProClosureS111PhysicalJets
import HRS.MS.ProClosureS111NoiseBounds
import HRS.MS.ProClosureS111PhysicalFeatureBounds
import HRS.MS.R2WinOrbAux15
import HRS.MS.Fp81V01UniformFeatures

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.ProClosureS111 HRS.MS.R2WinOrb
  HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.R26T6

variable {d : ℕ}

theorem fp81v01_physical_gradient_time_bound_decay (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := fun alpha : MultiIndex d =>
      oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    ∃ B c : ℝ, 0 ≤ B ∧ 0 < c ∧
      (∀ alpha r t, 0 ≤ r → r ≤ t → ∀ x,
        ‖gradient (propagatorW C r t (phi alpha)) x‖ ≤
          B * s103_b d alpha * Real.exp (-c * (t - r))) ∧
      (∀ alpha r t v, 0 ≤ r → r ≤ v → v ≤ t → ∀ x,
        ‖gradient (propagatorW C r t (phi alpha)) x -
          gradient (propagatorW C r v (phi alpha)) x‖ ≤
          B * s103_b d alpha * Real.exp (-c * (v - r)) * (t - v)) := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := fun alpha : MultiIndex d =>
    oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  obtain ⟨B0, c, hc, -, hstationary⟩ :=
    s103_stationary hd s hs0 hsd a beta ha hbeta 1 one_pos
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hstationary' : ∀ alpha z, 0 ≤ z →
      R2OrbitSup C (4 * d + 42) z (phi alpha) (B * s103_b d alpha) ∧
      R2OrbitGrad C (4 * d + 42) z (phi alpha) (B * s103_b d alpha) c ∧
      R2OrbitSup C (4 * d + 42) z (generatorW C z (phi alpha))
        (B * s103_b d alpha) ∧
      R2OrbitGrad C (4 * d + 42) z (generatorW C z (phi alpha))
        (B * s103_b d alpha) c ∧
      R2OrbitSup C (4 * d + 42) z
        (fun x => generatorW C z (generatorW C z (phi alpha)) x +
          deriv (fun t' => generatorW C t' (phi alpha) x) z)
        (B * s103_b d alpha) := by
    intro alpha z hz
    have h := (hstationary rho hrho alpha).1 z hz
    have hle : B0 * s103_b d alpha ≤ B * s103_b d alpha :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (s103_b_nonneg alpha)
    exact ⟨s103_orbitSup_mono h.1 hle,
      s103_orbitGrad_mono h.2.1 hle,
      s103_orbitSup_mono h.2.2.1 hle,
      s103_orbitGrad_mono h.2.2.2.1 hle,
      s103_orbitSup_mono h.2.2.2.2 hle⟩
  have hgrad : ∀ alpha z, 0 ≤ z → ∀ x,
      ‖gradient (propagatorW C 0 z (phi alpha)) x‖ ≤
        B * s103_b d alpha * Real.exp (-c * z) := by
    intro alpha z hz x
    have horb := (hstationary' alpha z hz).2.1
    have hpoint := HRS.MS.R2WinErr.s104_vec_bound C
      (mul_nonneg hB (s103_b_nonneg alpha)) horb
      (r := 0) ⟨le_rfl, hz⟩
    have h := hpoint.2 0 (Nat.zero_le _) x
    simpa only [norm_iteratedFDeriv_zero, sub_zero] using h
  have hterminal : ∀ alpha z, 0 ≤ z → ∀ x,
      ‖gradient (propagatorW C 0 z (generatorW C z (phi alpha))) x‖ ≤
        B * s103_b d alpha * Real.exp (-c * z) := by
    intro alpha z hz x
    have horb := (hstationary' alpha z hz).2.2.2.1
    have hpoint := HRS.MS.R2WinErr.s104_vec_bound C
      (mul_nonneg hB (s103_b_nonneg alpha)) horb
      (r := 0) ⟨le_rfl, hz⟩
    have h := hpoint.2 0 (Nat.zero_le _) x
    simpa only [norm_iteratedFDeriv_zero, sub_zero] using h
  have hderiv : ∀ alpha z, 0 ≤ z → ∀ x,
      HasDerivWithinAt
        (fun u => gradient (propagatorW C 0 u (phi alpha)) x)
        (gradient (propagatorW C 0 z (generatorW C z (phi alpha))) x)
        (Ici (0 : ℝ)) z := by
    intro alpha z hz x
    exact physical_gradient_terminal_derivative_zero hd hs0 hsd ha hbeta
      hrho alpha hz x
  have hshift : ∀ alpha r t, 0 ≤ r → r ≤ t →
      propagatorW C r t (phi alpha) = propagatorW C 0 (t - r) (phi alpha) := by
    intro alpha r t hr hrt
    exact HRS.MS.R2WinErr.s104_prop_shift hd hs0 hsd ha hbeta hrho ⟨hr, hrt⟩
      (physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha
        (hr.trans hrt)).1
  refine ⟨B, c, hB, hc, ?_, ?_⟩
  · intro alpha r t hr hrt x
    rw [hshift alpha r t hr hrt]
    have hz : 0 ≤ t - r := sub_nonneg.mpr hrt
    simpa only [sub_zero] using hgrad alpha (t - r) hz x
  · intro alpha r t v hr hrv hvt x
    rw [hshift alpha r t hr (hrv.trans hvt),
      hshift alpha r v hr hrv]
    let a0 := v - r
    let b0 := t - r
    have ha0 : 0 ≤ a0 := sub_nonneg.mpr hrv
    have hab : a0 ≤ b0 := by dsimp [a0, b0]; linarith
    have hder : ∀ z ∈ Icc a0 b0,
        HasDerivWithinAt
          (fun u => gradient (propagatorW C 0 u (phi alpha)) x)
          (gradient (propagatorW C 0 z (generatorW C z (phi alpha))) x)
          (Icc a0 b0) z := by
      intro z hz
      have hz0 : 0 ≤ z := ha0.trans hz.1
      exact (hderiv alpha z hz0 x).mono
        (fun y hy => ha0.trans hy.1)
    have hderbound : ∀ z ∈ Icc a0 b0,
        ‖gradient (propagatorW C 0 z (generatorW C z (phi alpha))) x‖ ≤
          B * s103_b d alpha * Real.exp (-c * a0) := by
      intro z hz
      have hz0 : 0 ≤ z := ha0.trans hz.1
      have hpoint := hterminal alpha z hz0 x
      have hexp : Real.exp (-c * z) ≤ Real.exp (-c * a0) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hz.1 hc.le]
      exact hpoint.trans
        (mul_le_mul_of_nonneg_left hexp
          (mul_nonneg hB (s103_b_nonneg alpha)))
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z => gradient (propagatorW C 0 z (phi alpha)) x)
      (f' := fun z => gradient
        (propagatorW C 0 z (generatorW C z (phi alpha))) x)
      (s := Icc a0 b0) hder hderbound (convex_Icc a0 b0)
      ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    have htime : b0 - a0 = t - v := by dsimp [a0, b0]; ring
    rw [htime] at hmean
    rw [Real.norm_eq_abs] at hmean
    rw [abs_of_nonneg (sub_nonneg.mpr hvt)] at hmean
    have hmean' : ‖gradient (propagatorW C 0 b0 (phi alpha)) x -
        gradient (propagatorW C 0 a0 (phi alpha)) x‖ ≤
        B * s103_b d alpha * Real.exp (-c * a0) * (t - v) := by
      exact hmean
    have htime' : (t - r) - (v - r) = t - v := by ring
    simpa only [a0, b0, htime'] using hmean'

theorem fp81v01_noiseClass_sub_norm_sq_le_ordered_decay
    {C : WholeCoeff d} {mu : Measure (Euc d)} [IsProbabilityMeasure mu]
    {v t A c : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t) (hA : 0 ≤ A) (hc : 0 < c)
    {phi : Euc d → ℝ}
    (hf : IsClassicalAdjointW C t phi (fun r => propagatorW C r t phi))
    (hg : IsClassicalAdjointW C v phi (fun r => propagatorW C r v phi))
    (hgrad : ∀ r ∈ Ioc v t, ∀ x,
      ‖gradient (propagatorW C r t phi) x‖ ≤ A)
    (hinc : ∀ r ∈ Icc (0 : ℝ) v, ∀ x,
      ‖gradient (propagatorW C r t phi) x -
        gradient (propagatorW C r v phi) x‖ ≤
        A * Real.exp (-c * (v - r)) * (t - v)) :
    ‖noiseClass C mu t phi - noiseClass C mu v phi‖ ^ 2 ≤
      A ^ 2 * ((t - v) ^ 2 / (2 * c) + (t - v)) := by
  have ht : 0 ≤ t := hv.trans hvt
  have hdelta : 0 ≤ t - v := sub_nonneg.mpr hvt
  have hm1 := noiseVector_memLp ht hf (mu := mu)
  have hm2 := noiseVector_memLp hv hg (mu := mu)
  have hi : Integrable
      (fun p => ‖noiseVector C t phi p - noiseVector C v phi p‖ ^ 2)
      ((volume : Measure ℝ).prod mu) := (hm1.sub hm2).integrable_norm_pow (by norm_num)
  let slab := Icc (0 : ℝ) v ×ˢ (univ : Set (Euc d))
  let slab2 := Ioc v t ×ˢ (univ : Set (Euc d))
  let f := (Icc (0 : ℝ) v).indicator
    (fun r : ℝ => (A * Real.exp (-c * (v - r)) * (t - v)) ^ 2)
  let A1 := fun p : ℝ × Euc d => f p.1
  let A2 := slab2.indicator (fun _ => A ^ 2)
  have hcoeff : 0 ≤ (A * (t - v)) ^ 2 := sq_nonneg _
  have hfmeas : Measurable f :=
    (by fun_prop : Measurable fun r : ℝ =>
      (A * Real.exp (-c * (v - r)) * (t - v)) ^ 2).indicator measurableSet_Icc
  have hi1 : Integrable A1 ((volume : Measure ℝ).prod mu) := by
    have hmajor := noise_slab_Icc_integrable (mu := mu) 0 v
      ((A * (t - v)) ^ 2)
    refine hmajor.mono' (hfmeas.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp : p.1 ∈ Icc (0 : ℝ) v
    · have harg : -c * (v - p.1) ≤ 0 := by
        have := mul_nonneg hc.le (sub_nonneg.mpr hp.2)
        nlinarith
      have hexp : Real.exp (-c * (v - p.1)) ≤ 1 :=
        Real.exp_le_one_iff.mpr harg
      have hinner : 0 ≤ A * Real.exp (-c * (v - p.1)) * (t - v) :=
        mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) hdelta
      have hval : ‖A1 p‖ =
          (A * Real.exp (-c * (v - p.1)) * (t - v)) ^ 2 := by
        simp only [A1, f, Set.indicator_of_mem hp, Real.norm_eq_abs]
        exact abs_of_nonneg (sq_nonneg _)
      have hmul : A * Real.exp (-c * (v - p.1)) * (t - v) ≤
          A * (t - v) := by
        calc
          _ ≤ A * 1 * (t - v) := by gcongr
          _ = _ := by ring
      have hle : (A * Real.exp (-c * (v - p.1)) * (t - v)) ^ 2 ≤
          (A * (t - v)) ^ 2 :=
        pow_le_pow_left₀ hinner hmul 2
      simpa [A1, A2, slab2, hp, hval] using hle
    · have hfzero : f p.1 = 0 := by
        dsimp [f]
        simp [hp]
      have hA1zero : A1 p = 0 := by simpa [A1] using hfzero
      rw [hA1zero]
      simp [slab, hp]
  have hi2 : Integrable A2 ((volume : Measure ℝ).prod mu) :=
    noise_slab_Ioc_integrable (mu := mu) v t (A ^ 2)
  have hbound : ∀ p : ℝ × Euc d,
      ‖noiseVector C t phi p - noiseVector C v phi p‖ ^ 2 ≤ A1 p + A2 p := by
    intro p
    by_cases hcommon : p.1 ∈ Icc (0 : ℝ) v
    · have hrt : p.1 ∈ Icc (0 : ℝ) t := ⟨hcommon.1, hcommon.2.trans hvt⟩
      have hshort : p.1 ∉ Ioc v t := fun h => not_lt_of_ge hcommon.2 h.1
      simp only [noiseVector, if_pos hrt, if_pos hcommon]
      have hsq := pow_le_pow_left₀ (norm_nonneg _)
        (hinc p.1 hcommon p.2) 2
      have hsq' : ‖gradient (propagatorW C p.1 t phi) p.2 -
          gradient (propagatorW C p.1 v phi) p.2‖ ^ 2 ≤ A1 p := by
        simpa [A1, f, hcommon, Real.norm_eq_abs] using hsq
      exact hsq'.trans (le_add_of_nonneg_right (by
        simp [A2, slab2, hshort]))
    · by_cases hshort : p.1 ∈ Ioc v t
      · have hrt : p.1 ∈ Icc (0 : ℝ) t := ⟨hv.trans hshort.1.le, hshort.2⟩
        have hsq := pow_le_pow_left₀ (norm_nonneg _)
          (hgrad p.1 hshort p.2) 2
        have hsq' : ‖gradient (propagatorW C p.1 t phi) p.2‖ ^ 2 ≤ A2 p := by
          simpa [A2, slab2, hcommon, hshort] using hsq
        simpa [noiseVector, hrt, hcommon, A1, f, A2, slab2, hshort] using hsq'
      · have hrt : p.1 ∉ Icc (0 : ℝ) t := by
          intro h
          have hpv : v < p.1 := lt_of_not_ge (fun hp => hcommon ⟨h.1, hp⟩)
          exact hshort ⟨hpv, h.2⟩
        simp [noiseVector, hrt, hcommon, A1, f, A2, slab2, hshort]
  have htime : ∫ r in Icc (0 : ℝ) v, Real.exp (-2 * c * (v - r)) ∂volume ≤
      1 / (2 * c) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hv]
    have hchange := intervalIntegral.integral_comp_sub_left
      (fun u : ℝ => Real.exp (-(2 * c) * u)) (a := 0) (b := v) v
    rw [sub_self] at hchange
    simp only [sub_zero] at hchange
    have hchange' : ∫ r in (0 : ℝ)..v, Real.exp (-2 * c * (v - r)) =
        ∫ u in (0 : ℝ)..v, Real.exp (-(2 * c) * u) := by
      convert hchange using 1 <;> congr 1 <;> ring
    calc
      _ = ∫ u in (0 : ℝ)..v, Real.exp (-(2 * c) * u) := by
        exact hchange'
      _ ≤ 1 / (2 * c) :=
        HRS.MS.R2WinOrb.s103_exp_integral_le (mul_pos (by norm_num) hc) hv
  have hintf : ∫ r, f r ∂volume =
      (A * (t - v)) ^ 2 *
        ∫ r in Icc (0 : ℝ) v, Real.exp (-2 * c * (v - r)) ∂volume := by
    calc
      _ = ∫ r in Icc (0 : ℝ) v,
          (A * Real.exp (-c * (v - r)) * (t - v)) ^ 2 ∂volume := by
        change ∫ r, (Icc (0 : ℝ) v).indicator
          (fun r : ℝ => (A * Real.exp (-c * (v - r)) * (t - v)) ^ 2) r ∂volume = _
        rw [integral_indicator measurableSet_Icc]
      _ = ∫ r in Icc (0 : ℝ) v,
          (A * (t - v)) ^ 2 * Real.exp (-2 * c * (v - r)) ∂volume := by
        apply integral_congr_ae
        filter_upwards with r
        have he : Real.exp (-c * (v - r)) ^ 2 =
            Real.exp (-2 * c * (v - r)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        calc
          _ = (A * (t - v)) ^ 2 * Real.exp (-c * (v - r)) ^ 2 := by ring
          _ = _ := by rw [he]
      _ = _ := by rw [integral_const_mul]
  have hprod : ∫ p, A1 p ∂((volume : Measure ℝ).prod mu) =
      ∫ r, f r ∂volume := by
    have h := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := mu)
      f (fun _ : Euc d => (1 : ℝ))
    have hone : ∫ x, (1 : ℝ) ∂mu = 1 := by simp
    simpa [A1, hone] using h
  rw [noiseClass_sub_norm_sq_integral hm1 hm2]
  calc
    _ ≤ ∫ p, (A1 p + A2 p) ∂((volume : Measure ℝ).prod mu) :=
      integral_mono hi (hi1.add hi2) hbound
    _ = (A * (t - v)) ^ 2 *
          ∫ r in Icc (0 : ℝ) v, Real.exp (-2 * c * (v - r)) ∂volume +
        A ^ 2 * (t - v) := by
      rw [integral_add hi1 hi2, hprod, hintf,
        noise_slab_Ioc_integral hvt]
      ring
    _ ≤ (A * (t - v)) ^ 2 * (1 / (2 * c)) + A ^ 2 * (t - v) := by
      have hmul := mul_le_mul_of_nonneg_left htime (sq_nonneg (A * (t - v)))
      linarith
    _ = A ^ 2 * ((t - v) ^ 2 / (2 * c) + (t - v)) := by ring

theorem fp81v01_noise_increment_bound_uniform (T : ℝ) (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let N := fun t (alpha : MultiIndex d) =>
      scaledNoiseClass C (HRS.Whole.withDensityReal rho) beta⁻¹ t
        (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha)
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t v, 0 ≤ t → 0 ≤ v → |t - v| ≤ T →
      Summable (fun alpha => ‖N t alpha - N v alpha‖ ^ 2) ∧
      (∑' alpha, ‖N t alpha - N v alpha‖ ^ 2) ≤ L * |t - v| := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let mu := HRS.Whole.withDensityReal rho
  let phi := fun alpha : MultiIndex d =>
    oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  let N := fun t (alpha : MultiIndex d) =>
    scaledNoiseClass C mu beta⁻¹ t (phi alpha)
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  obtain ⟨B, c, hB, hc, hmag, hinc⟩ :=
    fp81v01_physical_gradient_time_bound_decay hd hs0 hsd ha hbeta hrho
  have hq : 0 ≤ 2 * beta⁻¹ := by positivity
  have hphi : ∀ alpha t, 0 ≤ t →
      IsClassicalAdjointW C t (phi alpha) (fun r => propagatorW C r t (phi alpha)) := by
    intro alpha t ht
    exact HRS.MS.Fcau.propagatorW_isClassical
      (physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha ht).1
  have hsquare := stationary_weight_square_summable (d := d) (by omega)
  let T0 := max T 0
  let K := (2 * beta⁻¹) * B ^ 2 * (T0 / (2 * c) + 1)
  have hK : 0 ≤ K := by
    dsimp [K, T0]
    positivity
  have hpoint : ∀ alpha t v, 0 ≤ t → 0 ≤ v → |t - v| ≤ T →
      ‖N t alpha - N v alpha‖ ^ 2 ≤ K * s103_b d alpha ^ 2 * |t - v| := by
    intro alpha t v ht hv hTv
    have hdeltaT : |t - v| ≤ T0 := hTv.trans (le_max_left T 0)
    have hordered : ∀ t' v', 0 ≤ v' → v' ≤ t' → |t' - v'| ≤ T0 →
        ‖N t' alpha - N v' alpha‖ ^ 2 ≤
          K * s103_b d alpha ^ 2 * (t' - v') := by
      intro t' v' hv' hvt' hT'
      have hbase := fp81v01_noiseClass_sub_norm_sq_le_ordered_decay
        (mu := mu) hv' hvt' (mul_nonneg hB (s103_b_nonneg alpha)) hc
        (hphi alpha t' (hv'.trans hvt')) (hphi alpha v' hv')
        (fun r hr x => by
          have hpoint := hmag alpha r t' (hv'.trans hr.1.le) hr.2 x
          have hexp : Real.exp (-c * (t' - r)) ≤ 1 := by
            apply Real.exp_le_one_iff.mpr
            have := mul_nonneg hc.le (sub_nonneg.mpr hr.2)
            nlinarith
          simpa only [mul_one] using hpoint.trans
            (mul_le_mul_of_nonneg_left hexp
              (mul_nonneg hB (s103_b_nonneg alpha))))
        (fun r hr x => hinc alpha r t' v' hr.1 hr.2 hvt' x)
      have hdelta : 0 ≤ t' - v' := sub_nonneg.mpr hvt'
      have hquad : (t' - v') ^ 2 / (2 * c) + (t' - v') ≤
          (T0 / (2 * c) + 1) * (t' - v') := by
        have hTdelta : t' - v' ≤ T0 := by
          rw [abs_of_nonneg hdelta] at hT'
          exact hT'
        have hgap : 0 ≤ T0 - (t' - v') := sub_nonneg.mpr hTdelta
        have hsq : (t' - v') ^ 2 ≤ T0 * (t' - v') := by
          nlinarith [mul_nonneg hdelta hgap]
        have hc2 : 0 < 2 * c := by positivity
        have hdiv : (t' - v') ^ 2 / (2 * c) ≤
            T0 * (t' - v') / (2 * c) :=
          div_le_div_of_nonneg_right hsq hc2.le
        calc
          _ ≤ T0 * (t' - v') / (2 * c) + (t' - v') :=
            add_le_add_left hdiv (t' - v')
          _ = _ := by ring
      have hscale :
          ‖Real.sqrt (2 * beta⁻¹) • noiseClass C mu t' (phi alpha) -
              Real.sqrt (2 * beta⁻¹) • noiseClass C mu v' (phi alpha)‖ ^ 2 ≤
            K * s103_b d alpha ^ 2 * (t' - v') := by
        change ‖Real.sqrt (2 * beta⁻¹) •
          noiseClass C mu t' (phi alpha) -
          Real.sqrt (2 * beta⁻¹) • noiseClass C mu v' (phi alpha)‖ ^ 2 ≤ _
        rw [← smul_sub]
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hq]
        calc
          _ ≤ (2 * beta⁻¹) * ((B * s103_b d alpha) ^ 2 *
              ((t' - v') ^ 2 / (2 * c) + (t' - v'))) :=
            mul_le_mul_of_nonneg_left hbase (by positivity)
          _ = (2 * beta⁻¹) * (B * s103_b d alpha) ^ 2 *
              ((t' - v') ^ 2 / (2 * c) + (t' - v')) := by ring
          _ ≤ (2 * beta⁻¹) * (B * s103_b d alpha) ^ 2 *
              ((T0 / (2 * c) + 1) * (t' - v')) :=
            mul_le_mul_of_nonneg_left hquad (by positivity)
          _ = _ := by
            dsimp [K]
            ring
      simpa only [N, scaledNoiseClass] using hscale
    rcases le_total v t with hvt | htv
    · have h := hordered t v hv hvt hdeltaT
      calc
        _ ≤ K * s103_b d alpha ^ 2 * (t - v) := h
        _ = K * s103_b d alpha ^ 2 * |t - v| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hvt)]
    · have h := hordered v t ht htv (by simpa [abs_sub_comm] using hdeltaT)
      rw [norm_sub_rev] at h
      calc
        _ ≤ K * s103_b d alpha ^ 2 * (v - t) := h
        _ = K * s103_b d alpha ^ 2 * |t - v| := by
          rw [abs_of_nonpos (sub_nonpos.mpr htv)]
          ring
  change ∃ L : ℝ, 0 ≤ L ∧ ∀ t v, 0 ≤ t → 0 ≤ v → |t - v| ≤ T →
    Summable (fun alpha : MultiIndex d => ‖N t alpha - N v alpha‖ ^ 2) ∧
    (∑' alpha : MultiIndex d, ‖N t alpha - N v alpha‖ ^ 2) ≤ L * |t - v|
  refine ⟨K * (∑' alpha : MultiIndex d, s103_b d alpha ^ 2), ?_, ?_⟩
  · exact mul_nonneg hK (tsum_nonneg fun alpha => sq_nonneg (s103_b d alpha))
  · intro t v ht hv hTv
    have hmajor : Summable (fun alpha : MultiIndex d =>
        K * s103_b d alpha ^ 2 * |t - v|) :=
      (hsquare.mul_left K).mul_right _
    have hsum : Summable (fun alpha => ‖N t alpha - N v alpha‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun alpha => hpoint alpha t v ht hv hTv) hmajor
    refine ⟨hsum, ?_⟩
    calc
      _ ≤ ∑' alpha : MultiIndex d, K * s103_b d alpha ^ 2 * |t - v| :=
        hsum.tsum_le_tsum (fun alpha => hpoint alpha t v ht hv hTv) hmajor
      _ = _ := by rw [tsum_mul_right, tsum_mul_left]

theorem fp81v01_physicalLinear_increment_bound_uniform (T : ℝ) (hd : 2 ≤ d)
    {s a beta gamma : ℝ} {rho : Euc d → ℝ}
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    {K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ]
      Lp ℝ 2 (HRS.Whole.withDensityReal rho)} {Mg : ℝ}
    (hX : X1Input d s a beta 0 rho)
    (hK : KRep (rieszKernel d s) (HRS.Whole.withDensityReal rho) K Mg)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hbeta' : 0 < beta) (hrho : IsThermalEquilibrium d s a beta rho) :
    (∀ i : Fin 2, ∀ t : ℝ, 0 ≤ t →
      Summable (fun alpha : MultiIndex d =>
        ‖physicalLinear hX hK hbeta hgamma i t
          (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2)) ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i : Fin 2, ∀ t v : ℝ,
      0 ≤ t → 0 ≤ v → |t - v| ≤ T →
      Summable (fun alpha : MultiIndex d =>
        ‖physicalLinear hX hK hbeta hgamma i t
            (initialTestBasis (wholeSpaceIndex d) alpha) -
          physicalLinear hX hK hbeta hgamma i v
            (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) ∧
      (∑' alpha : MultiIndex d,
        ‖physicalLinear hX hK hbeta hgamma i t
            (initialTestBasis (wholeSpaceIndex d) alpha) -
          physicalLinear hX hK hbeta hgamma i v
            (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) ≤ L * |t - v| := by
  have hsd : s < (d : ℝ) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Lm, hLm, hmag⟩ := fp81v01_physicalLinear_uniform_summability
    hd hX hK hbeta hgamma hs0 hs ha hbeta' hrho
  have hG := fp81v01_initial_gaussian_increment_bound hd hs0 hs ha hbeta'
    hrho hK
  obtain ⟨Lg, hLg, hG⟩ := hG
  obtain ⟨Ln, hLn, hN⟩ :=
    fp81v01_noise_increment_bound_uniform T hd hs0 hsd ha hbeta' hrho
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let Ag := fun t (alpha : MultiIndex d) =>
    initialGaussianFeature hK hgamma C t
      (initialTestBasis (wholeSpaceIndex d) alpha : Euc d → ℝ)
  let Ab := fun t (alpha : MultiIndex d) =>
    initialGaussianFeature hK hbeta C t
      (initialTestBasis (wholeSpaceIndex d) alpha : Euc d → ℝ)
  let N := fun t (alpha : MultiIndex d) =>
    scaledNoiseClass C (HRS.Whole.withDensityReal rho) beta⁻¹ t
      (initialTestBasis (wholeSpaceIndex d) alpha : Euc d → ℝ)
  have hGgamma : ∀ t v, 0 ≤ t → 0 ≤ v →
      Summable (fun alpha : MultiIndex d => ‖Ag t alpha - Ag v alpha‖ ^ 2) ∧
      (∑' alpha : MultiIndex d, ‖Ag t alpha - Ag v alpha‖ ^ 2) ≤
        Lg * |t - v| := by
    intro t v ht hv
    simpa [Ag, C, initialTestBasis, wholeSpaceIndex] using
      hG gamma hgamma t v ht hv
  have hGbeta : ∀ t v, 0 ≤ t → 0 ≤ v →
      Summable (fun alpha : MultiIndex d => ‖Ab t alpha - Ab v alpha‖ ^ 2) ∧
      (∑' alpha : MultiIndex d, ‖Ab t alpha - Ab v alpha‖ ^ 2) ≤
        Lg * |t - v| := by
    intro t v ht hv
    simpa [Ab, C, initialTestBasis, wholeSpaceIndex] using
      hG beta (le_of_lt hbeta') t v ht hv
  have hNinc : ∀ t v, 0 ≤ t → 0 ≤ v → |t - v| ≤ T →
      Summable (fun alpha : MultiIndex d => ‖N t alpha - N v alpha‖ ^ 2) ∧
      (∑' alpha : MultiIndex d, ‖N t alpha - N v alpha‖ ^ 2) ≤
        Ln * |t - v| := by
    intro t v ht hv hTv
    simpa [N, C, initialTestBasis, wholeSpaceIndex] using
      hN t v ht hv hTv
  refine ⟨fun i t ht => (hmag i t ht).1, Lg + Ln, by positivity, ?_⟩
  intro i t v ht hv hTv
  obtain ⟨hgs, hgb⟩ := hGgamma t v ht hv
  obtain ⟨hbs, hbb⟩ := hGbeta t v ht hv
  obtain ⟨hns, hnb⟩ := hNinc t v ht hv hTv
  have he : ∀ alpha : MultiIndex d,
      ‖physicalLinear hX hK hbeta hgamma i t
          (initialTestBasis (wholeSpaceIndex d) alpha) -
        physicalLinear hX hK hbeta hgamma i v
          (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 =
      (if i = 0 then ‖Ag t alpha - Ag v alpha‖ ^ 2
        else ‖Ab t alpha - Ab v alpha‖ ^ 2) + ‖N t alpha - N v alpha‖ ^ 2 :=
    fun alpha => physicalLinear_sub_norm_sq hX hK hbeta hgamma i ht hv _
  simp_rw [he]
  by_cases hi : i = 0
  · simp only [if_pos hi]
    refine ⟨hgs.add hns, ?_⟩
    rw [hgs.tsum_add hns]
    calc
      _ ≤ Lg * |t - v| + Ln * |t - v| := add_le_add hgb hnb
      _ = (Lg + Ln) * |t - v| := by ring
  · simp only [if_neg hi]
    refine ⟨hbs.add hns, ?_⟩
    rw [hbs.tsum_add hns]
    calc
      _ ≤ Lg * |t - v| + Ln * |t - v| := add_le_add hbb hnb
      _ = (Lg + Ln) * |t - v| := by ring

#print axioms fp81v01_physical_gradient_time_bound_decay
#print axioms fp81v01_noiseClass_sub_norm_sq_le_ordered_decay
#print axioms fp81v01_noise_increment_bound_uniform
#print axioms fp81v01_physicalLinear_increment_bound_uniform

end HRS.Fp81.V01
