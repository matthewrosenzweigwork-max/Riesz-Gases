import HRS.MS.Fp81S21WindowCovRSId
import HRS.MS.R2InterpAux24

/-! Identification of the selected whole-history scalar covariance RS value
with the same physical-window selection. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MC.E213O

/-- Any selected unprojected scalar RS value for the second heat derivative
equals the supplied physical-window covariance RS value on each fixed
admissible interval. -/
theorem fp81s21_unprojected_isRSOn_window_covariance_value
    (p : Parameters) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : ℝ) (ha : 0 ≤ a)
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H τ, IsProbabilityMeasure (future H τ))
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (C : WholeCoeff p.d)
    (z : Ω → ℝ → (Euc p.d → ℝ) → ℝ)
    (Yh : Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (hJ : ∀ᵐ ω ∂μ, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
      IsR2JValue C (wholeSpaceIndex p.d : ℝ) (a + p.T) (z ω) (Ioc u v)
        (((Fj ω v - Fj ω u :
          projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) :
          TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)))
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
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ a + p.T)
    (jval : Ω → ℝ)
    (hjval : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r
      (fun τ u v => r2JPair C (wholeSpaceIndex p.d : ℝ) (a + p.T)
        (z ω) (Ioc u v)
        (iteratedFDeriv ℝ 2
          (r2HeatFn (future (a + p.T))
            (fun w => Φ (HRS.MS.ProClosureS111.physicalWindowRestriction
              (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
              (T := p.T) (H := a + p.T) ha le_rfl w)) τ)
          (Yh ω τ))) (jval ω)) :
    jval =ᵐ[μ] WSW.value q r := by
  let H : ℝ := a + p.T
  let B := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  let W : B →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := H) ha le_rfl
  let Fw : Ω → ℝ → projTensor (Window p) 2 :=
    fun ω t => fp81s21_windowCovarianceMap p a ha (Fj ω t)
  let AW : Ω → ℝ → projTensor (Window p) 2 →L[ℝ] ℝ := fun ω τ =>
    fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (Yh ω τ)))
  let Jc : Ω → ℝ → TensorDual B 2 :=
    fun ω t => (Fj ω t : TensorDual B 2)
  letI : CompleteSpace (projTensor (Window p) 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
  have hH : 0 < H := by
    dsimp [H]
    linarith [p.hT, ha]
  have hWindow : ∀ᵐ ω ∂μ,
      fp81s21_IsRSOn q r
        (fun τ u v => AW ω τ (Fw ω v - Fw ω u)) (WSW.value q r ω) := by
    simpa only [AW, Fw] using WSW.value_isRS q r hq hqr hr
  by_cases hlt : q < r
  · filter_upwards [hjval, hWindow, hJ] with ω hRSfull hRSw hJω
    have hJc : ∀ u v, 0 ≤ u → u ≤ v → v ≤ H →
        IsR2JValue C (wholeSpaceIndex p.d : ℝ) H (z ω) (Ioc u v)
          (Jc ω v - Jc ω u) := by
      intro u v hu huv hv
      simpa [Jc] using hJω u v hu huv hv
    have hRSwindow' : IsR2RS (r - q)
        (fun t u v => AW ω (q + t) (Fw ω (q + v) - Fw ω (q + u)))
        (WSW.value q r ω) := by
      simpa only [fp81s21_IsRSOn] using hRSw
    have hkernel : ∀ t u v, t ∈ Icc (0 : ℝ) (r - q) →
        0 ≤ u → u ≤ v → v ≤ r - q →
        r2JPair C (wholeSpaceIndex p.d : ℝ) H (z ω) (Ioc (q + u) (q + v))
          (iteratedFDeriv ℝ 2
            (r2HeatFn (future H) (fun w => Φ (W w)) (q + t))
            (Yh ω (q + t))) =
          AW ω (q + t) (Fw ω (q + v) - Fw ω (q + u)) := by
      intro t u v ht hu huv hv
      have huH : 0 ≤ q + u := by linarith
      have huvH : q + u ≤ q + v := by linarith
      have hvH : q + v ≤ H := by
        have : q + v ≤ r := by linarith
        exact this.trans hr
      have hpair := HRS.MS.R2Interp.s102_jPair_eq
        C hH (z ω) (Jc ω) hJc (q + u) (q + v)
        huH huvH hvH
        (iteratedFDeriv ℝ 2
          (r2HeatFn (future H) (fun w => Φ (W w)) (q + t))
          (Yh ω (q + t)))
      have hheat := fp81s21_window_covariance_heat_pairing
        p a ha future hfuture Φ hΦ (q + t) (Yh ω (q + t))
        (Jc ω (q + v) - Jc ω (q + u))
      have hFinc : Fw ω (q + v) - Fw ω (q + u) =
          fp81s21_windowCovarianceMap p a ha
            (Fj ω (q + v) - Fj ω (q + u)) := by
        dsimp [Fw]
        rw [map_sub]
      have hpairmap : fp81s21_windowCovarianceMap p a ha
          (Fj ω (q + v) - Fj ω (q + u)) =
          tensorPow' 2 W (Jc ω (q + v) - Jc ω (q + u)) := by
        change tensorPow' 2 W
            ((Fj ω (q + v) - Fj ω (q + u) :
              projTensor B 2) : TensorDual B 2) =
          tensorPow' 2 W (Jc ω (q + v) - Jc ω (q + u))
        rfl
      calc
        _ = (Jc ω (q + v) - Jc ω (q + u))
            (iteratedFDeriv ℝ 2
              (r2HeatFn (future H) (fun w => Φ (W w)) (q + t))
              (Yh ω (q + t))) := hpair
        _ = tensorPow' 2 W (Jc ω (q + v) - Jc ω (q + u))
            (iteratedFDeriv ℝ 2
              (initialHeat future a ha Φ (q + t)) (W (Yh ω (q + t)))) := by
              rw [← hheat]
        _ = AW ω (q + t) (Fw ω (q + v) - Fw ω (q + u)) := by
              dsimp [AW, fp81s21_covariance_pairingCLM]
              change tensorPow' 2 W (Jc ω (q + v) - Jc ω (q + u))
                    (iteratedFDeriv ℝ 2
                      (initialHeat future a ha Φ (q + t))
                      (W (Yh ω (q + t)))) =
                ((Fw ω (q + v) - Fw ω (q + u) :
                    projTensor (Window p) 2) : TensorDual (Window p) 2)
                  (iteratedFDeriv ℝ 2
                    (initialHeat future a ha Φ (q + t))
                    (W (Yh ω (q + t))))
              rw [hFinc, hpairmap]
    have hRStrans : IsR2RS (r - q)
        (fun t u v => r2JPair C (wholeSpaceIndex p.d : ℝ) H (z ω)
          (Ioc (q + u) (q + v))
          (iteratedFDeriv ℝ 2
            (r2HeatFn (future H) (fun w => Φ (W w)) (q + t))
            (Yh ω (q + t)))) (WSW.value q r ω) := by
      refine (s102_isR2RS_iff _ _ _).2
        (HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr
          ((s102_isR2RS_iff _ _ _).1 hRSwindow') ?_)
      intro t u v ht hu huv hv
      exact (hkernel t u v ht hu huv hv).symm
    have hRStransOn : fp81s21_IsRSOn q r
        (fun τ u v => r2JPair C (wholeSpaceIndex p.d : ℝ) H (z ω) (Ioc u v)
          (iteratedFDeriv ℝ 2
            (r2HeatFn (future H) (fun w => Φ (W w)) τ)
            (Yh ω τ))) (WSW.value q r ω) := by
      simpa only [fp81s21_IsRSOn] using hRStrans
    exact fp81s21_isRSOn_unique hlt hRSfull hRStransOn
  · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
    subst r
    filter_upwards [hjval, hWindow] with ω hRSfull hRSw
    rw [fp81s21_isRSOn_zero_forces hRSfull,
      fp81s21_isRSOn_zero_forces hRSw]

/-- Whole-horizon specialization of the selected covariance RS value. -/
theorem fp81s21_unprojected_isR2RS_window_covariance_value
    (p : Parameters) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : ℝ) (ha : 0 ≤ a)
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H τ, IsProbabilityMeasure (future H τ))
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (C : WholeCoeff p.d)
    (z : Ω → ℝ → (Euc p.d → ℝ) → ℝ)
    (Yh : Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (hJ : ∀ᵐ ω ∂μ, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
      IsR2JValue C (wholeSpaceIndex p.d : ℝ) (a + p.T) (z ω) (Ioc u v)
        (((Fj ω v - Fj ω u :
          projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) :
          TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)))
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
    (jval : Ω → ℝ)
    (hjval : ∀ᵐ ω ∂μ, IsR2RS (a + p.T)
      (fun τ u v => r2JPair C (wholeSpaceIndex p.d : ℝ) (a + p.T)
        (z ω) (Ioc u v)
        (iteratedFDeriv ℝ 2
          (r2HeatFn (future (a + p.T))
            (fun w => Φ (HRS.MS.ProClosureS111.physicalWindowRestriction
              (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
              (T := p.T) (H := a + p.T) ha le_rfl w)) τ)
          (Yh ω τ))) (jval ω)) :
    jval =ᵐ[μ] WSW.value 0 (a + p.T) := by
  have hH : 0 < a + p.T := by linarith [ha, p.hT]
  apply fp81s21_unprojected_isRSOn_window_covariance_value
    p μ a ha future hfuture Φ hΦ C z Yh Fj hJ WSW
    0 (a + p.T) (le_refl 0) (le_of_lt hH) (le_refl _) jval
  simpa only [fp81s21_IsRSOn, sub_zero, zero_add] using hjval

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_unprojected_isRSOn_window_covariance_value
#print axioms HRS.Fp81.S21.fp81s21_unprojected_isR2RS_window_covariance_value
