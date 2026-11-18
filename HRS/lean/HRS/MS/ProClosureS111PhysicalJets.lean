import HRS.MS.ProClosureS111PhysicalOrbit
import HRS.MS.R2WinOrbAux13
import Mathlib.Analysis.Calculus.MeanValue

/-!
Actual terminal derivatives of the first two spatial jets of the thermal
propagator. The accepted stationary family converges in the C² difference
quotient norm, so the gradient has an actual terminal derivative as well.
The resulting time Lipschitz bound retains one square-summable oscillator
envelope. These are physical inputs for the common Gaussian noise feature.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R2WinErr HRS.MS.R2WinOrb

def jetGradientEquiv (d : ℕ) :
    (Euc d [×1]→L[ℝ] ℝ) ≃ₗᵢ[ℝ] Euc d :=
  (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).trans
    (InnerProductSpace.toDual ℝ (Euc d)).symm

theorem jetGradientEquiv_apply {d : ℕ} (f : Euc d → ℝ) (x : Euc d) :
    jetGradientEquiv d (iteratedFDeriv ℝ 1 f x) = gradient f x := by
  change (InnerProductSpace.toDual ℝ (Euc d)).symm
    ((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ) (iteratedFDeriv ℝ 1 f x)) = _
  rw [← HRS.MS.TransOp.s611_fderiv_eq_curry]
  rfl

theorem physical_terminal_jet_derivative_zero {d : ℕ} (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) (alpha : MultiIndex d)
    {j : ℕ} (hj : j ≤ 2) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    HasDerivWithinAt (fun z => iteratedFDeriv ℝ j (propagatorW C 0 z phi) x)
      (iteratedFDeriv ℝ j (propagatorW C 0 t (generatorW C t phi)) x)
      (Ici (0 : ℝ)) t := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  have hH : 0 ≤ t + 1 := by linarith
  have htH : t ∈ Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  obtain ⟨G0, G1, G2, hG⟩ := s104_stat_orbit hd hs0 hsd ha hbeta hrho alpha hH
  have hder := s103_hasDeriv_iter
    (fun z hz => (hG.cb0 z hz).1.of_le (by exact_mod_cast hj))
    (fun z hz => (hG.cb1 z hz).1.of_le (by exact_mod_cast hj))
    (fun z hz eps heps => by
      obtain ⟨delta, hd, hdiff⟩ := hG.diff01 z hz eps heps
      exact ⟨delta, hd, fun h hne hlt hmem => hdiff h hne hlt hmem j hj⟩)
    x t htH
  have hactual : HasDerivWithinAt
      (fun z => iteratedFDeriv ℝ j (propagatorW C 0 z phi) x)
      (iteratedFDeriv ℝ j (G1 t) x) (Icc (0 : ℝ) (t + 1)) t :=
    hder.congr_of_mem
      (fun z hz => congrArg (fun f : Euc d → ℝ => iteratedFDeriv ℝ j f x)
        (hG.eq0 z hz).symm) htH
  rw [hG.eq1 t htH] at hactual
  have hlocal : Icc (0 : ℝ) (t + 1) ∈ 𝓝[Ici (0 : ℝ)] t := by
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [Iio_mem_nhds (by linarith : t < t + 1)] with z hz hz0
    exact ⟨hz0, hz.le⟩
  exact hactual.mono_of_mem_nhdsWithin hlocal

theorem physical_gradient_terminal_derivative_zero {d : ℕ} (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) (alpha : MultiIndex d)
    {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    HasDerivWithinAt (fun z => gradient (propagatorW C 0 z phi) x)
      (gradient (propagatorW C 0 t (generatorW C t phi)) x) (Ici (0 : ℝ)) t := by
  let L := (jetGradientEquiv d).toContinuousLinearEquiv.toContinuousLinearMap
  have hjet := physical_terminal_jet_derivative_zero hd hs0 hsd ha hbeta hrho
    alpha (j := 1) (by norm_num) ht x
  have h := L.hasFDerivAt.comp_hasDerivWithinAt t hjet
  change HasDerivWithinAt (fun z => jetGradientEquiv d
    (iteratedFDeriv ℝ 1 (propagatorW
      ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) 0 z
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha)) x))
    (jetGradientEquiv d (iteratedFDeriv ℝ 1 (propagatorW
      ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) 0 t
      (generatorW ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) t
        (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha))) x)) (Ici (0 : ℝ)) t at h
  simpa only [jetGradientEquiv_apply] using h

/-- One physical oscillator envelope controls both the gradient and its
terminal-time increments, uniformly over every nonnegative initial time.
The same constant works for all horizons. -/
theorem physical_gradient_time_bound {d : ℕ} (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := fun alpha : MultiIndex d =>
      oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ alpha r t, 0 ≤ r → r ≤ t → ∀ x,
        ‖gradient (propagatorW C r t (phi alpha)) x‖ ≤ B * s103_b d alpha) ∧
      (∀ alpha r t v, 0 ≤ r → r ≤ t → r ≤ v → ∀ x,
        ‖gradient (propagatorW C r t (phi alpha)) x -
          gradient (propagatorW C r v (phi alpha)) x‖ ≤
          B * s103_b d alpha * |t - v|) := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := fun alpha : MultiIndex d =>
    oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  obtain ⟨B, c, hB, hc, hbound⟩ := s103_orbit_iter hd hs0 hsd ha hbeta hrho
  have hgrad : ∀ alpha z, 0 ≤ z → ∀ x,
      ‖gradient (propagatorW C 0 z (phi alpha)) x‖ ≤ B * s103_b d alpha ∧
      ‖gradient (propagatorW C 0 z (generatorW C z (phi alpha))) x‖ ≤
        B * s103_b d alpha := by
    intro alpha z hz x
    obtain ⟨hex0, hex1⟩ := physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha hz
    have hb0 := hbound alpha z hz 0 (by norm_num) _
      (HRS.MS.Fcau.propagatorW_isClassical hex0) 0 ⟨le_rfl, hz⟩
    have hb1 := hbound alpha z hz 1 (by norm_num) _
      (HRS.MS.Fcau.propagatorW_isClassical hex1) 0 ⟨le_rfl, hz⟩
    have hA := mul_nonneg hB (s103_b_nonneg alpha)
    constructor
    · rw [HRS.MS.MovDec.mov2e_norm_gradient, ← norm_iteratedFDeriv_one]
      exact s103_cb_of_E hA hb0.2 1 (by omega) x
    · rw [HRS.MS.MovDec.mov2e_norm_gradient, ← norm_iteratedFDeriv_one]
      exact s103_cb_of_E hA hb1.2 1 (by omega) x
  have hinc : ∀ alpha t v, 0 ≤ t → 0 ≤ v → ∀ x,
      ‖gradient (propagatorW C 0 t (phi alpha)) x -
        gradient (propagatorW C 0 v (phi alpha)) x‖ ≤
        B * s103_b d alpha * |t - v| := by
    intro alpha t v ht hv x
    have hder : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt
        (fun z => gradient (propagatorW C 0 z (phi alpha)) x)
        (gradient (propagatorW C 0 z (generatorW C z (phi alpha))) x)
        (Ici (0 : ℝ)) z :=
      fun z hz => physical_gradient_terminal_derivative_zero hd hs0 hsd ha hbeta hrho
        alpha hz x
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z => gradient (propagatorW C 0 z (phi alpha)) x)
      (f' := fun z => gradient (propagatorW C 0 z (generatorW C z (phi alpha))) x)
      (s := Ici (0 : ℝ)) hder (fun z hz => (hgrad alpha z hz x).2)
      (convex_Ici (0 : ℝ)) hv ht
    simpa only [Real.norm_eq_abs] using h
  have hshift : ∀ alpha r t, 0 ≤ r → r ≤ t →
      propagatorW C r t (phi alpha) = propagatorW C 0 (t - r) (phi alpha) := by
    intro alpha r t hr hrt
    exact s104_prop_shift hd hs0 hsd ha hbeta hrho ⟨hr, hrt⟩
      (physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha (hr.trans hrt)).1
  refine ⟨B, hB, ?_, ?_⟩
  · intro alpha r t hr hrt x
    rw [hshift alpha r t hr hrt]
    exact (hgrad alpha (t - r) (sub_nonneg.2 hrt) x).1
  · intro alpha r t v hr hrt hrv x
    rw [hshift alpha r t hr hrt, hshift alpha r v hr hrv]
    have h := hinc alpha (t - r) (v - r) (sub_nonneg.2 hrt) (sub_nonneg.2 hrv) x
    have he : t - r - (v - r) = t - v := by ring
    simpa only [he] using h

#print axioms physical_terminal_jet_derivative_zero
#print axioms physical_gradient_time_bound

end HRS.MS.ProClosureS111
