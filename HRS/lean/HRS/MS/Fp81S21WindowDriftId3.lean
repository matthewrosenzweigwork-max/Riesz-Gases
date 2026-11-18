import HRS.MS.Fp81S21WindowDriftId2

/-! Identification of unprojected drift RS values with window values. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- Any specified unprojected RS value on an interval equals the window selection. -/
theorem fp81s21_unprojected_isRSOn_window_drift_value
    (p : Parameters) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : ℝ) (ha : 0 ≤ a)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H v, IsProbabilityMeasure (future H v))
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (C : WholeCoeff p.d) (b : Ω → ℝ → (Euc p.d → ℝ) → ℝ)
    (Y Fd : Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hFd : ∀ᵐ ω ∂μ, Fd ω 0 = 0 ∧
      ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
        Fd ω v - Fd ω u = r2DriftInc C (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fun t f => b ω t f) u v)
    (WSW : fp81s21_RSBVWindow μ (a + p.T)
      (fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ)
        (HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
          (T := p.T) (H := a + p.T) ha le_rfl (Y ω τ)))
      (fun ω t => fp81s21_weightedDrift_windowCum
        (m := (wholeSpaceIndex p.d : ℝ)) ha le_rfl C (fun u f => b ω u f) t))
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ a + p.T)
    (dval : Ω → ℝ)
    (hdval : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r
      (fun t u v => fderiv ℝ
        (r2HeatFn (future (a + p.T))
          (fun w => Φ (HRS.MS.ProClosureS111.physicalWindowRestriction
            (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
            (T := p.T) (H := a + p.T) ha le_rfl w)) t) (Y ω t)
        (r2DriftInc C (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fun s f => b ω s f) u v)) (dval ω)) :
    dval =ᵐ[μ] WSW.value q r := by
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
    (T := p.T) (H := a + p.T) ha le_rfl
  let Fw : Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) p.T :=
    fun ω t => fp81s21_weightedDrift_windowCum
      (m := (wholeSpaceIndex p.d : ℝ)) ha le_rfl C (fun u f => b ω u f) t
  let AH : Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T) →L[ℝ] ℝ :=
    fun ω τ => fderiv ℝ (r2HeatFn (future (a + p.T)) (fun w => Φ (W w)) τ) (Y ω τ)
  let AW : Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) p.T →L[ℝ] ℝ :=
    fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ) (W (Y ω τ))
  have hpull : ∀ ω τ h, AH ω τ h = AW ω τ (W h) := by
    intro ω τ h
    dsimp [AH, AW]
    have hpull := fp81s21_initialHeat_pullback_iteratedFDeriv
      future hfuture a ha Φ hΦ τ 1 (by norm_num) (Y ω τ)
    have heval := congrArg (fun D => D ![h]) hpull
    simpa [iteratedFDeriv_one_apply] using heval
  have hWindow : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r
      (fun t u v => AW ω t (Fw ω v - Fw ω u)) (WSW.value q r ω) := by
    simpa only [AW, Fw] using WSW.value_isRS q r hq hqr hr
  by_cases hlt : q < r
  · filter_upwards [hFd, hdval, hWindow] with ω hω hRSfull hRSw
    rcases hω with ⟨hzero, hinc⟩
    have hFw_eq : ∀ t, t ∈ Icc (0 : ℝ) (a + p.T) → Fw ω t = W (Fd ω t) := by
      intro t ht
      have hstart := hinc 0 t (by norm_num) ht.1 ht.2
      have hFd_t : Fd ω t = r2DriftInc C (wholeSpaceIndex p.d : ℝ)
          (a + p.T) (fun u f => b ω u f) 0 t := by
        simpa [hzero] using hstart
      change W (r2DriftInc C (wholeSpaceIndex p.d : ℝ)
          (a + p.T) (fun u f => b ω u f) 0 t) = W (Fd ω t)
      rw [← hFd_t]
    have hRSwindow' : IsR2RS (r - q)
        (fun t u v => AW ω (q + t) (Fw ω (q + v) - Fw ω (q + u)))
        (WSW.value q r ω) := by
      simpa only [fp81s21_IsRSOn] using hRSw
    have hRStrans : IsR2RS (r - q)
        (fun t u v => AH ω (q + t)
          (r2DriftInc C (wholeSpaceIndex p.d : ℝ) (a + p.T)
            (fun s f => b ω s f) (q + u) (q + v))) (WSW.value q r ω) := by
      refine (s102_isR2RS_iff _ _ _).2
        (HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr
          ((s102_isR2RS_iff _ _ _).1 hRSwindow') ?_)
      intro t u v ht hu huv hv
      have huH : q + u ∈ Icc (0 : ℝ) (a + p.T) := by
        constructor <;> linarith [hq, hu, huv, hv, hr]
      have hvH : q + v ∈ Icc (0 : ℝ) (a + p.T) := by
        constructor <;> linarith [hq, hu, huv, hv, hr]
      have hincW : Fw ω (q + v) - Fw ω (q + u) =
          W (r2DriftInc C (wholeSpaceIndex p.d : ℝ) (a + p.T)
            (fun s f => b ω s f) (q + u) (q + v)) := by
        rw [← hinc (q + u) (q + v) huH.1 (by linarith) hvH.2]
        rw [hFw_eq (q + v) hvH, hFw_eq (q + u) huH]
        simp
      rw [hincW]
      exact (hpull ω (q + t) _).symm
    have hRStransOn : fp81s21_IsRSOn q r
        (fun t u v => AH ω t (r2DriftInc C (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fun s f => b ω s f) u v)) (WSW.value q r ω) := by
      simpa only [fp81s21_IsRSOn] using hRStrans
    exact fp81s21_isRSOn_unique hlt hRSfull hRStransOn
  · have hqr' : q = r := le_antisymm hqr (le_of_not_gt hlt)
    subst r
    filter_upwards [hdval, hWindow] with ω hRSfull hRSw
    rw [fp81s21_isRSOn_zero_forces hRSfull, fp81s21_isRSOn_zero_forces hRSw]

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_unprojected_isRSOn_window_drift_value
