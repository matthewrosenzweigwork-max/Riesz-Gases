import HRS.MS.Fp81S21WindowCovId7
import HRS.MS.Fp81S21WinRSBV
import HRS.MS.Fp81S21CovRS4

/-! Continuity of the physical-window covariance integrand. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The Hessian on the physical window is continuous along a continuous
full-horizon path, using the full-horizon heat regularity. -/
theorem fp81s21_window_covariance_pairing_continuousOn
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Y : ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hY : ContinuousOn Y (Icc 0 (a + p.T))) :
    ContinuousOn (fun τ => fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ)
        (HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
          (T := p.T) (H := a + p.T) ha le_rfl (Y τ)))) (Icc 0 (a + p.T)) := by
  let H := a + p.T
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl
  let E := fp81s21_physicalWindowExtension (d := p.d)
    (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) ha p.hT.le
  let Ψ : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ := fun w => Φ (W w)
  have hΨ : MemCb 5 Ψ := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
  have hWE : W.comp E = ContinuousLinearMap.id ℝ (Window p) :=
    fp81s21_physicalWindowRestriction_comp_extension ha p.hT.le
  have hcomp : ∀ τ,
      iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (Y τ)) =
      (iteratedFDeriv ℝ 2 (r2HeatFn (future H) Ψ τ) (Y τ)).compContinuousLinearMap
        (fun _ => E) := by
    intro τ
    have hpull := fp81s21_initialHeat_pullback_iteratedFDeriv
      future hfuture.1 a ha Φ hΦ τ 2 (by norm_num) (Y τ)
    rw [hpull]
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact (congrArg (fun f => f (v i)) hWE).symm
  have hreg := ((hfuture.2.2.2 H hH).2.2.2.1 Ψ hΨ Y hY 2 (by norm_num)).1
  have hc := (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := ℝ) (fun _ : Fin 2 => E)).continuous.comp_continuousOn hreg
  have hw : ContinuousOn (fun τ => iteratedFDeriv ℝ 2
      (initialHeat future a ha Φ τ) (W (Y τ))) (Icc 0 H) :=
    ContinuousOn.congr hc (fun τ _ => hcomp τ)
  exact fp81s21_covariance_pairingCLM_continuous.comp_continuousOn hw

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_window_covariance_pairing_continuousOn
