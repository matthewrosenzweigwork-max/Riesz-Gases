import HRS.MS.Fp81S21WindowCovId6
import HRS.MS.Fp81S21IntervalRS
import HRS.MS.Fp81S21CovRS

/-! Scalar equality for the full-history and physically restricted covariance
Riemann--Stieltjes selections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MC.E213O

/-- The two covariance RS selections have the same scalar value on each fixed
admissible interval. The exceptional event may depend on the interval. -/
theorem fp81s21_unprojected_window_covariance_rs_values
    (p : Parameters) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : ℝ) (ha : 0 ≤ a)
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H τ, IsProbabilityMeasure (future H τ))
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Yh : Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (WSH : @fp81s21_RSBVWindow Ω
      (projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
      inferInstance inferInstance inferInstance
      (HRS.Fp81.V01.fp81v01_projTensorComplete
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
      μ (a + p.T)
      (fun ω τ => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2
          (r2HeatFn (future (a + p.T)) (fun w => Φ
            (HRS.MS.ProClosureS111.physicalWindowRestriction
              (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
              (T := p.T) (H := a + p.T) ha le_rfl w)) τ)
          (Yh ω τ))) Fj)
    (WSW : @fp81s21_RSBVWindow Ω (projTensor (Window p) 2)
      inferInstance inferInstance inferInstance
      (HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2)
      μ (a + p.T)
      (fun ω τ => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ)
          (HRS.MS.ProClosureS111.physicalWindowRestriction
            (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
            (T := p.T) (H := a + p.T) ha le_rfl (Yh ω τ))))
      (fun ω t => fp81s21_windowCovarianceMap p a ha (Fj ω t)))
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ a + p.T) :
    WSH.value q r =ᵐ[μ] WSW.value q r := by
  let H : ℝ := a + p.T
  let B := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  let W : B →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := H) ha le_rfl
  let Fw : Ω → ℝ → projTensor (Window p) 2 :=
    fun ω t => fp81s21_windowCovarianceMap p a ha (Fj ω t)
  let AH : Ω → ℝ → projTensor B 2 →L[ℝ] ℝ := fun ω τ =>
    fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2
        (r2HeatFn (future H) (fun w => Φ (W w)) τ) (Yh ω τ))
  let AW : Ω → ℝ → projTensor (Window p) 2 →L[ℝ] ℝ := fun ω τ =>
    fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (Yh ω τ)))
  letI : CompleteSpace (projTensor B 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete B 2
  letI : CompleteSpace (projTensor (Window p) 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
  have hFull : ∀ᵐ ω ∂μ,
      fp81s21_IsRSOn q r
        (fun τ u v => AH ω τ (Fj ω v - Fj ω u)) (WSH.value q r ω) := by
    simpa only [AH] using WSH.value_isRS q r hq hqr hr
  have hWindow : ∀ᵐ ω ∂μ,
      fp81s21_IsRSOn q r
        (fun τ u v => AW ω τ (Fw ω v - Fw ω u)) (WSW.value q r ω) := by
    simpa only [AW, Fw] using WSW.value_isRS q r hq hqr hr
  by_cases hlt : q < r
  · filter_upwards [hFull, hWindow] with ω hRSfull hRSw
    have hRSwindow' : IsR2RS (r - q)
        (fun t u v => AW ω (q + t) (Fw ω (q + v) - Fw ω (q + u)))
        (WSW.value q r ω) := by
      simpa only [fp81s21_IsRSOn] using hRSw
    have hRStrans : IsR2RS (r - q)
        (fun t u v => AH ω (q + t) (Fj ω (q + v) - Fj ω (q + u)))
        (WSW.value q r ω) := by
      refine (s102_isR2RS_iff _ _ _).2
        (HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr
          ((s102_isR2RS_iff _ _ _).1 hRSwindow') ?_)
      intro t u v ht hu huv hv
      have hmap : Fw ω (q + v) - Fw ω (q + u) =
          fp81s21_windowCovarianceMap p a ha
            (Fj ω (q + v) - Fj ω (q + u)) := by
        dsimp [Fw]
        rw [map_sub]
      have hpair := fp81s21_window_covariance_heat_pairing
        p a ha future hfuture Φ hΦ (q + t) (Yh ω (q + t))
        (Fj ω (q + v) - Fj ω (q + u) : TensorDual B 2)
      have hpairmap : fp81s21_windowCovarianceMap p a ha
          (Fj ω (q + v) - Fj ω (q + u)) =
          tensorPow' 2 W
            (Fj ω (q + v) - Fj ω (q + u) : TensorDual B 2) := by
        change tensorPow' 2 W
            ((Fj ω (q + v) - Fj ω (q + u) :
              projTensor B 2) : TensorDual B 2) =
          tensorPow' 2 W
            (Fj ω (q + v) - Fj ω (q + u) : TensorDual B 2)
        rfl
      change AW ω (q + t) (Fw ω (q + v) - Fw ω (q + u)) =
        AH ω (q + t) (Fj ω (q + v) - Fj ω (q + u))
      dsimp [AH, AW, fp81s21_covariance_pairingCLM]
      change ((Fw ω (q + v) - Fw ω (q + u) :
            projTensor (Window p) 2) : TensorDual (Window p) 2)
          (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ (q + t))
            (W (Yh ω (q + t)))) =
        ((Fj ω (q + v) - Fj ω (q + u) :
            projTensor B 2) : TensorDual B 2)
          (iteratedFDeriv ℝ 2
            (r2HeatFn (future H) (fun w => Φ (W w)) (q + t))
            (Yh ω (q + t)))
      rw [hmap, hpairmap]
      exact hpair
    have hRStransOn : fp81s21_IsRSOn q r
        (fun τ u v => AH ω τ (Fj ω v - Fj ω u)) (WSW.value q r ω) := by
      simpa only [fp81s21_IsRSOn] using hRStrans
    exact fp81s21_isRSOn_unique hlt hRSfull hRStransOn
  · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
    subst r
    filter_upwards [WSH.value_zero q hq hr, WSW.value_zero q hq hr]
      with ω hzeroH hzeroW
    exact hzeroH.trans hzeroW.symm

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_unprojected_window_covariance_rs_values
