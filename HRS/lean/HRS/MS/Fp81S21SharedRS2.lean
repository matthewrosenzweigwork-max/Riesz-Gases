import HRS.MS.Fp81S21SharedRS
import HRS.MS.Fp81S21CovRSSelected
import HRS.MS.Fp81S21CovRS5
import HRS.MS.Fp81S21FinProj2

/-! Assemble the one-future finite drift/covariance RS package. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MC.Sec7.S7PIL

def fp81s21_moving_shared_rs_level_payload
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (Yh Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : A.Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (V : A.Ω → ℝ) (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    [CompleteSpace (projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)]
    (WS : ∀ L : ℕ, fp81s21_WindowRS A.P (a + p.T)
      (fp81s21_finproj_drift_adapter p R A a ha hH future L Φ Yh) Fd
      (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj) : Prop :=
  let H : ℝ := a + p.T
  let B : Type := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  letI : CompleteSpace (projTensor B 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete B 2
  let W : B →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := H) ha le_rfl
  let Ψ : B → ℝ := fun w => Φ (W w)
  ∃ dval : A.Ω → ℝ, ∃ MD MJ : A.Ω → ℝ,
    ∃ WSDW : fp81s21_RSBVWindow A.P H
      (fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ) (W (Yh ω τ)))
      (fun ω t => fp81s21_weightedDrift_windowCum
        (m := (wholeSpaceIndex p.d : ℝ)) ha le_rfl (r26t3_coeff R)
        (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t),
    Integrable dval A.P ∧ Integrable MD A.P ∧ Integrable MJ A.P ∧
    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable
        (fp81s21_rs_bv_variation_majorant
          (fp81s21_finproj_drift_adapter p R A a ha hH future L Φ Yh) Fd q r) A.P) ∧
    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r)) ∧
    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      (WS L).drift.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u) ∧
    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      fp81s21_rs_bv_variation_majorant
        (fp81s21_finproj_drift_adapter p R A a ha hH future L Φ Yh) Fd q r ω
        ≤ MD ω) ∧
    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable
        (fp81s21_rs_bv_variation_majorant
          (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj q r)
        A.P) ∧
    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r)) ∧
    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      (WS L).covariance.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u) ∧
    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      fp81s21_rs_bv_variation_majorant
        (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj q r ω
        ≤ MJ ω) ∧
    (∀ᵐ ω ∂A.P,
      IsR2RS H
        (fun t q r => fderiv ℝ (r2HeatFn (future H) Ψ t) (Yh ω t)
          (r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
            (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r))
        (dval ω) ∧
      Tendsto (fun L => (WS L).drift.value 0 H ω) atTop (𝓝 (dval ω)) ∧
      ∀ L, |(WS L).drift.value 0 H ω| ≤ cbNorm 5 Ψ * V ω) ∧
    Tendsto (fun L => ∫ ω, (WS L).drift.value 0 H ω ∂A.P) atTop
      (𝓝 (∫ ω, dval ω ∂A.P)) ∧
    (∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable
        (fp81s21_rs_bv_variation_majorant
          (fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ) (W (Yh ω τ)))
          (fun ω t => fp81s21_weightedDrift_windowCum
            (m := (wholeSpaceIndex p.d : ℝ)) ha le_rfl (r26t3_coeff R)
            (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t) q r)
        A.P) ∧
    dval =ᵐ[A.P] WSDW.value 0 H

theorem fp81s21_moving_shared_rs (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ future : (H : ℝ) → ℝ →
            Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
          fp81s21_moving_heat_full_clause p R future ∧
          ∀ (a : ℝ) (ha : 0 ≤ a)
            (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A),
            let H : ℝ := a + p.T
            let B : Type := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
            letI : CompleteSpace (projTensor B 2) :=
              HRS.Fp81.V01.fp81v01_projTensorComplete B 2
            ∃ (Yh Fd : A.Ω → ℝ → B)
              (Fj : A.Ω → ℝ → projTensor B 2) (V : A.Ω → ℝ),
              fp81s21_moving_shared_rs_core p R A a Yh Fd Fj V ∧
              ∀ Φ : Window p → ℝ, (hΦ : MemCb 5 Φ) →
                ∃ WS : ∀ L : ℕ, fp81s21_WindowRS A.P H
                  (fp81s21_finproj_drift_adapter p R A a ha (by linarith [ha, p.hT]) future L Φ Yh) Fd
                  (fp81s21_finproj_covariance_adapter p R A a ha (by linarith [ha, p.hT]) future L Φ Yh) Fj,
                  fp81s21_moving_shared_rs_level_payload p R A F a ha (by linarith [ha, p.hT]) future
                    Yh Fd Fj V Φ hΦ WS := by
  classical
  obtain ⟨δm, hδm, hmHalf, hmaster⟩ :=
    fp81s21_moving_window_rsbv_with_dval p
  obtain ⟨δi, hδi, hiHalf, hinputs⟩ := fp81s21_moving_inputs_all p
  let δ0 := min δm δi
  refine ⟨δ0, lt_min hδm hδi, (min_le_left _ _).trans hmHalf, ?_⟩
  intro δ hδ hδle R
  have hδm' : δ ≤ δm := hδle.trans (min_le_left _ _)
  have hδi' : δ ≤ δi := hδle.trans (min_le_right _ _)
  obtain ⟨future, hfuture, hmain⟩ := hmaster δ hδ hδm' R
  refine ⟨future, hfuture, ?_⟩
  intro a ha N hN A F
  have hH : 0 < a + p.T := by linarith [ha, p.hT]
  let H : ℝ := a + p.T
  let B := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  letI : CompleteSpace (projTensor B 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete B 2
  obtain ⟨c, hstd, hphysAll⟩ := hinputs δ hδ hδi' R a ha
  have hphys : Fp81MovingPhysicalInputs R hN A H := by
    simpa [H] using hphysAll N hN A
  have hδh : δ ≤ 1 / 2 := hδm'.trans hmHalf
  have horb : R2OrbitSummable (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H (2 * p.d + 8) :=
    fp81s21_R2OrbitSummable_of_S101Data hstd.hD
  have hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H :=
    fp81s21_S102Lin p R H
  obtain ⟨Fj, Vj, hJm, hJVi, hJzero, hJgood⟩ :=
    fp81s21_moving_raw_eta_measurable_cumulative_fixed
      p R hδ hδh hH horb hlin hN A hphys
  obtain ⟨Yh, Fd, Vd, hYm, hDm, hDVi, hDgood, hDlevel⟩ :=
    hmain a ha hH N hN A F
  obtain ⟨V, hVformula, hcore⟩ :=
    fp81s21_moving_shared_rs_core_of_producers p R A a ha
      Yh Fd Vd Fj Vj hYm hDm hDVi hDgood hJm hJVi hJzero hJgood
  have hcoreParts := hcore
  rcases hcoreParts with ⟨hYmCore, hDmCore, hJmCore, hVi, hJzeroCore, hcommonGood⟩
  have hgoodCov : ∀ᵐ ω ∂A.P,
      (∀ t ∈ Icc (0 : ℝ) H,
        Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          H A.P A.X ω t) ∧
      ContinuousOn (Yh ω) (Icc 0 H) ∧
      (∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
          (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
          (((Fj ω r - Fj ω q : projTensor B 2) : TensorDual B 2))) ∧
      ContinuousOn (Fj ω) (Icc 0 H) ∧
      BoundedVariationOn (Fj ω) (Icc 0 H) ∧
      (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ V ω := by
    filter_upwards [hcommonGood] with ω hg
    rcases hg with ⟨hYeq, hYc, hDzero, hDc, hDBV, hDvar, hDinc,
      hJinc, hJc, hJBV, hJvar⟩
    exact ⟨hYeq, hYc, hJinc, hJc, hJBV, hJvar⟩
  refine ⟨Yh, Fd, Fj, V, hcore, ?_⟩
  intro Φ hΦ
  obtain ⟨WSd, dval, MD, hdInt, hMDInt, hDlevels, hDlimit, hDexpect, hDwindow⟩ :=
    hDlevel Φ hΦ
  obtain ⟨WSDW, hWSDWmajor, hDident⟩ := hDwindow
  have hJfamily := fp81s21_moving_covariance_rs_on_selected
    p R a ha hH hN A F hstd future hfuture Yh Fj V hYm hJm hVi hgoodCov
  obtain ⟨MJ, hMJInt, hJlevels⟩ := hJfamily Φ hΦ
  let WSj : ∀ L : ℕ, fp81s21_RSBVWindow A.P H
      (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj :=
    fun L => Classical.choose (hJlevels L)
  let WS : ∀ L : ℕ, fp81s21_WindowRS A.P H
      (fp81s21_finproj_drift_adapter p R A a ha hH future L Φ Yh) Fd
      (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj :=
    fun L => ⟨hH.le, WSd L, WSj L⟩
  have hVdom : ∀ᵐ ω ∂A.P, Vd ω ≤ V ω := by
    filter_upwards [ae_of_all A.P fun ω => hVformula ω] with ω hVω
    rw [hVω]
    exact le_trans (le_abs_self _) (le_add_of_nonneg_right (abs_nonneg _))
  have hDlimitShared : ∀ᵐ ω ∂A.P,
      IsR2RS H
        (fun t q r => fderiv ℝ (r2HeatFn (future H)
          (fun w => Φ (HRS.MS.ProClosureS111.physicalWindowRestriction
            (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
            (T := p.T) (H := H) ha le_rfl w)) t) (Yh ω t)
          (r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
            (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r))
        (dval ω) ∧
      Tendsto (fun L => (WS L).drift.value 0 H ω) atTop (𝓝 (dval ω)) ∧
      ∀ L, |(WS L).drift.value 0 H ω| ≤
        cbNorm 5 (fun w => Φ (HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
          (T := p.T) (H := H) ha le_rfl w)) * V ω := by
    filter_upwards [hDlimit, hVdom] with ω hd hv
    rcases hd with ⟨hR2, hTend, hbound⟩
    refine ⟨hR2, ?_, ?_⟩
    · change Tendsto (fun L => (WSd L).value 0 H ω) atTop (𝓝 (dval ω))
      exact hTend
    · intro L
      have hCb : 0 ≤ cbNorm 5
          (fun w => Φ (HRS.MS.ProClosureS111.physicalWindowRestriction
            (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
            (T := p.T) (H := H) ha le_rfl w)) := by
        exact S7PIL_cbNorm_nonneg
          ((HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof
            (HRS.MS.ProClosureS111.physicalWindowRestriction
              (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
              (T := p.T) (H := H) ha le_rfl) hΦ).1) 0
      have hval := hbound L
      exact hval.trans (mul_le_mul_of_nonneg_left hv hCb)
  refine ⟨WS, ?_⟩
  dsimp [fp81s21_moving_shared_rs_level_payload]
  have hDmajInt : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant
        (fp81s21_finproj_drift_adapter p R A a ha hH future L Φ Yh) Fd q r) A.P := by
    intro L q r hq hqr hr
    exact (hDlevels L q r hq hqr hr).1
  have hDOn : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r) := by
    intro L q r hq hqr hr
    filter_upwards [(hDlevels L q r hq hqr hr).2.1] with ω hω
    exact hω.1
  have hDval : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      (WSd L).value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u := by
    intro L q r hq hqr hr
    filter_upwards [(hDlevels L q r hq hqr hr).2.1] with ω hω
    exact hω.2
  have hDmajBound : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      fp81s21_rs_bv_variation_majorant
        (fp81s21_finproj_drift_adapter p R A a ha hH future L Φ Yh) Fd q r ω
        ≤ MD ω := by
    intro L q r hq hqr hr
    exact (hDlevels L q r hq hqr hr).2.2
  have hJmajInt : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant
        (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj q r)
        A.P := by
    intro L q r hq hqr hr
    exact (Classical.choose_spec (hJlevels L) q r hq hqr hr).1
  have hJOn : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r) := by
    intro L q r hq hqr hr
    filter_upwards [(Classical.choose_spec (hJlevels L) q r hq hqr hr).2.1]
      with ω hω
    exact hω.1
  have hJval : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      (WSj L).value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u := by
    intro L q r hq hqr hr
    filter_upwards [(Classical.choose_spec (hJlevels L) q r hq hqr hr).2.1]
      with ω hω
    exact hω.2
  have hJmajBound : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      fp81s21_rs_bv_variation_majorant
        (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj q r ω
        ≤ MJ ω := by
    intro L q r hq hqr hr
    exact (Classical.choose_spec (hJlevels L) q r hq hqr hr).2.2
  refine ⟨dval, MD, MJ, WSDW, hdInt, hMDInt, hMJInt,
    hDmajInt, hDOn, hDval, hDmajBound, hJmajInt, hJOn, hJval,
    hJmajBound, hDlimitShared, ?_, hWSDWmajor, hDident⟩
  change Tendsto (fun L => ∫ ω, (WSd L).value 0 H ω ∂A.P) atTop
    (𝓝 (∫ ω, dval ω ∂A.P))
  exact hDexpect

#print axioms HRS.Fp81.S21.fp81s21_moving_shared_rs
end HRS.Fp81.S21
end
