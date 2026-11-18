import HRS.MS.Fp81S21MovingHeat5
import HRS.MS.Fp81S21WinRSBV
import HRS.MS.Fp81S21CovRS3
import HRS.MS.Fp81S21VarCarrier
import HRS.MS.Fp81S21PredictionPhysicalDefs
import HRS.MS.Fp81S21RecentRSKernel

/-! Analytic input for the literal recent physical heat kernels. The observation
window starts at `a`; the recent integration start is a separate time. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- Window derivatives inherit time continuity from the retained full future,
by the contractive right inverse of physical restriction. -/
theorem fp81s21_recent_heat_derivative_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : fp81s21_moving_heat_full_clause p R future)
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Y : ℝ → Window p) (hY : ContinuousOn Y (Icc 0 (a + p.T)))
    (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (fun t => iteratedFDeriv ℝ j (initialHeat future a ha Φ t) (Y t))
      (Icc 0 (a + p.T)) := by
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
    (H := a + p.T) ha le_rfl
  let E := fp81s21_physicalWindowExtension (d := p.d)
    (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) ha p.hT.le
  let Ψ := fun w => Φ (W w)
  have hΨ : MemCb 5 Ψ := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
  have hWE : W.comp E = ContinuousLinearMap.id ℝ (Window p) :=
    fp81s21_physicalWindowRestriction_comp_extension ha p.hT.le
  have he (y : Window p) : W (E y) = y :=
    congrArg (fun f => f y) hWE
  have hreg := ((hf.2.2.2 (a + p.T) (by linarith [p.hT])).2.2.2.1
    Ψ hΨ (fun t => E (Y t)) (E.continuous.comp_continuousOn hY) j hj).1
  have hc := (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := ℝ) (fun _ : Fin j => E)).continuous.comp_continuousOn hreg
  apply ContinuousOn.congr hc
  intro t ht
  change iteratedFDeriv ℝ j (initialHeat future a ha Φ t) (Y t) =
    (iteratedFDeriv ℝ j (r2HeatFn (future (a + p.T)) Ψ t) (E (Y t))).compContinuousLinearMap
      (fun _ => E)
  rw [fp81s21_initialHeat_pullback_iteratedFDeriv future hf.1 a ha Φ hΦ t j
    (by omega), he]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  exact (he (v i)).symm

/-- The unit test norm bounds every heat derivative through order five. -/
theorem fp81s21_recent_heat_derivative_bound
    {p : Parameters}
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : ∀ H t, IsProbabilityMeasure (future H t))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5)
    (t : ℝ) (j : ℕ) (hj : j ≤ 5) (y : Window p) :
    ‖iteratedFDeriv ℝ j (initialHeat future a ha Φ t) y‖ ≤ 1 := by
  have hm : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  refine ((fp81s21_windowFuture_heat_derivs future hf a ha Φ hm t).2 j hj y).2.trans ?_
  apply ciSup_le
  intro z
  exact (HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hm hj z).trans hΦ.2.2

/-- The next spatial derivative gives a unit Lipschitz bound, uniformly in
both the heat time and the observation-window start. -/
theorem fp81s21_recent_heat_derivative_lipschitz
    {p : Parameters}
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : ∀ H t, IsProbabilityMeasure (future H t))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5)
    (t : ℝ) (j : ℕ) (hj : j ≤ 4) (y z : Window p) :
    ‖iteratedFDeriv ℝ j (initialHeat future a ha Φ t) y -
      iteratedFDeriv ℝ j (initialHeat future a ha Φ t) z‖ ≤ ‖y - z‖ := by
  have hm : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hd := (fp81s21_windowFuture_heat_derivs future hf a ha Φ hm t).1
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ j (initialHeat future a ha Φ t)) :=
    hd.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast (show j < 5 by omega))
  have hb (x : Window p) :
      ‖fderiv ℝ (iteratedFDeriv ℝ j (initialHeat future a ha Φ t)) x‖ ≤ 1 := by
    rw [norm_fderiv_iteratedFDeriv]
    exact fp81s21_recent_heat_derivative_bound future hf a ha Φ hΦ t (j + 1) (by omega) x
  simpa only [one_mul] using
    (convex_univ (𝕜 := ℝ) (E := Window p)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hdiff x) (fun x _ => hb x) (mem_univ z) (mem_univ y)

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recent_heat_derivative_continuous
#print axioms HRS.Fp81.S21.fp81s21_recent_heat_derivative_bound
#print axioms HRS.Fp81.S21.fp81s21_recent_heat_derivative_lipschitz
end
