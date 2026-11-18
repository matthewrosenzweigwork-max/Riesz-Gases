import HRS.MS.R2WinErrAux19
import HRS.MS.R2WinOrbAux10

/-!
Actual terminal derivatives for the stationary thermal propagator.
The derivative is produced by the accepted classical adjoint families,
including the right derivative when the terminal and initial times agree.
No `S111k2WindowOrbitInput` or tensor-relaxation assertion is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R2WinErr HRS.MS.R2WinOrb

theorem physical_classical_orbits {d : ℕ} (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) (alpha : MultiIndex d)
    {t : ℝ} (ht : 0 ≤ t) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    (∃ f, IsClassicalAdjointW C t phi f) ∧
      (∃ f, IsClassicalAdjointW C t (generatorW C t phi) f) := by
  obtain ⟨G0, G1, G2, hG⟩ := s104_stat_orbit hd hs0 hsd ha hbeta hrho alpha ht
  exact ⟨hG.ex0 t ⟨ht, le_rfl⟩, hG.ex1 t ⟨ht, le_rfl⟩⟩

theorem physical_terminal_derivative_zero {d : ℕ} (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) (alpha : MultiIndex d)
    {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    HasDerivWithinAt (fun z => propagatorW C 0 z phi x)
      (propagatorW C 0 t (generatorW C t phi) x) (Ici (0 : ℝ)) t := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  have hH : 0 ≤ t + 1 := by linarith
  have htH : t ∈ Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  obtain ⟨G0, G1, G2, hG⟩ := s104_stat_orbit hd hs0 hsd ha hbeta hrho alpha hH
  have hder := s103_hasDeriv_val
    (fun z hz => (hG.cb0 z hz).1.of_le (by norm_num))
    (fun z hz => (hG.cb1 z hz).1.of_le (by norm_num))
    (fun z hz eps heps => by
      obtain ⟨delta, hd, hdiff⟩ := hG.diff01 z hz eps heps
      exact ⟨delta, hd, fun h hne hlt hmem => hdiff h hne hlt hmem 0 (by norm_num)⟩)
    x t htH
  have hactual : HasDerivWithinAt (fun z => propagatorW C 0 z phi x)
      (G1 t x) (Icc (0 : ℝ) (t + 1)) t :=
    hder.congr_of_mem (fun z hz => congrFun (hG.eq0 z hz).symm x) htH
  rw [hG.eq1 t htH] at hactual
  have hlocal : Icc (0 : ℝ) (t + 1) ∈ 𝓝[Ici (0 : ℝ)] t := by
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [Iio_mem_nhds (by linarith : t < t + 1)] with z hz hz0
    exact ⟨hz0, hz.le⟩
  exact hactual.mono_of_mem_nhdsWithin hlocal

theorem physical_terminal_derivative {d : ℕ} (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) (alpha : MultiIndex d)
    {v t : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t) (x : Euc d) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    HasDerivWithinAt (fun z => propagatorW C v z phi x)
      (propagatorW C v t (generatorW C t phi) x) (Ici v) t := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  have hbase := physical_terminal_derivative_zero hd hs0 hsd ha hbeta hrho alpha
    (sub_nonneg.2 hvt) x
  have hshift : HasDerivWithinAt (fun z : ℝ => z - v) 1 (Ici v) t :=
    ((hasDerivAt_id t).sub_const v).hasDerivWithinAt
  have hmaps : MapsTo (fun z : ℝ => z - v) (Ici v) (Ici (0 : ℝ)) :=
    fun z hz => by
      change 0 ≤ z - v
      exact sub_nonneg.2 hz
  have hcomp : HasDerivWithinAt (fun z => propagatorW C 0 (z - v) phi x)
      (propagatorW C 0 (t - v) (generatorW C (t - v) phi) x) (Ici v) t := by
    simpa only [Function.comp_def, mul_one] using hbase.comp t hshift hmaps
  have heq : ∀ z ∈ Ici v,
      propagatorW C v z phi x = propagatorW C 0 (z - v) phi x := by
    intro z hz
    have hex := (physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha (hv.trans hz)).1
    exact congrFun (s104_prop_shift hd hs0 hsd ha hbeta hrho ⟨hv, hz⟩ hex) x
  have hactual := hcomp.congr_of_mem heq hvt
  have hexp := (physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha (hv.trans hvt)).2
  have hprop := s104_prop_shift hd hs0 hsd ha hbeta hrho ⟨hv, hvt⟩ hexp
  exact hactual.congr_deriv (congrFun hprop.symm x)

end HRS.MS.ProClosureS111
