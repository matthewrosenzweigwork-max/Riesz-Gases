import HRS.MS.Fp81S21DualMeas2
import HRS.MS.Fp81S21CovClose4
import HRS.MS.Fp81S21CovCumulative3

/-! Physical covariance measurability follows from `IsR2L1F`; the redundant
four dual-norm hypotheses are removed from the consumer contract. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.FixEq
open HRS.MS.GenPath HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R2WinOrb HRS.MS.R2Interp

/-- Physical covariance-measure contract with all dual-norm measurability
obligations derived from the two `IsR2L1F` hypotheses. -/
theorem fp81s21_window_covariance_measure_physical'
    (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ (Cs0 cdec Cmix : ℝ) (K : ℝ → ℝ),
        0 ≤ Cs0 ∧ 0 < cdec ∧ Summable (s104_b p.d) ∧
        0 ≤ Cmix ∧ Cs0 ≤ Cmix ∧
        (∀ P, K P = ((3 + Real.sqrt p.T) ^ 2 * fp81s21_blockC0) *
          |2 * (r26t3_coeff R).ν| *
          (s57pC p.d (2 * p.d + 8) P * ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
            (fp81s21_windowCovBlockAmp p.d (2 * p.d + 8) p.T Cmix) ^ 2))) ∧
        ∀ a : ℝ, 0 ≤ a → ∀ P : ℝ, (p.d : ℝ) < 2 * P →
        ∀ (z z' : ℝ → (Euc p.d → ℝ) → ℝ) (c : ℝ),
          IsR2L1F (2 * p.d + 8) P (a + p.T) z →
          IsR2L1F (2 * p.d + 8) P (a + p.T) z' →
          R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (a + p.T) z →
          R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (a + p.T) z' →
          ∃ (D : fp81s21_WindowLocalInput (r26t3_coeff R)
                (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P z Cmix cdec)
            (D' : fp81s21_WindowLocalInput (r26t3_coeff R)
                (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P z' Cmix cdec)
            (Dsum : fp81s21_WindowLocalInput (r26t3_coeff R)
                (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P
                (z + z') Cmix cdec)
            (Dsmul : fp81s21_WindowLocalInput (r26t3_coeff R)
                (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P
                (c • z) Cmix cdec),
            ∀ q s : ℝ, 0 ≤ q → q ≤ s → s ≤ a + p.T →
              fp81s21_covariance_interval_contract D D' Dsum Dsmul
                (K P) q s := by
  obtain ⟨δ0, hδ0, hhalf, hphysical⟩ :=
    fp81s21_window_covariance_measure_physical p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Cs0, cdec, Cmix, K, hCs0, hcdec, hsumb, hCmix, hCs0Cmix,
    hK, hbody⟩ := hphysical δ hδ hδle R
  refine ⟨Cs0, cdec, Cmix, K, hCs0, hcdec, hsumb, hCmix, hCs0Cmix,
    hK, ?_⟩
  intro a ha P hP z z' c hz hz' hm hm'
  have hd : 0 < p.d := by linarith [p.hd]
  have hdual := fp81s21_dualNormE_aemeasurable_of_IsR2L1F
    (d := p.d) (r := 2 * p.d + 8) (Pw := P) (T := a + p.T) hd hP hz
  have hdual' := fp81s21_dualNormE_aemeasurable_of_IsR2L1F
    (d := p.d) (r := 2 * p.d + 8) (Pw := P) (T := a + p.T) hd hP hz'
  have hdualSum := fp81s21_dualNormE_aemeasurable_add_of_IsR2L1F
    (d := p.d) (r := 2 * p.d + 8) (Pw := P) (T := a + p.T) hd hP hz hz'
  have hdualSmul := fp81s21_dualNormE_aemeasurable_smul_of_IsR2L1F
    (d := p.d) (r := 2 * p.d + 8) (Pw := P) (T := a + p.T) (c := c)
    hd hP hz
  exact hbody a ha P hP z z' c hz hz' hm hm' hdual hdual' hdualSum hdualSmul


/-- The raw moving-eta field has a.e.-measurable weighted-dual norm on
`[0,a+T]` at the fixed weight supplied by the integrated horizon theorem,
`Pw = d + 2`. -/
theorem fp81s21_moving_raw_eta_dualNormE_aemeasurable_ae
    (p : Parameters) {δ a : ℝ} (R : Trajectory p δ) (ha : 0 ≤ a)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphysical : Fp81MovingPhysicalInputs R hN A (a + p.T)) :
    ∀ᵐ ω ∂A.P,
      AEMeasurable
        (fun v => dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
          (fp81s21_movingRawEtaField p R A ω v))
        (volume.restrict (Icc (0 : ℝ) (a + p.T))) := by
  have hH : 0 < a + p.T := by linarith [ha, p.hT]
  have hd : 0 < p.d := by linarith [p.hd]
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    push_cast
    nlinarith [p.hd]
  filter_upwards [fp81s21_moving_raw_eta_horizonL1F_ae
      p R hH hN A hphysical] with ω hω
  have hExt := fp81s21_dualNormE_aemeasurable_of_IsR2L1F
    (d := p.d) (r := 2 * p.d + 8)
    (Pw := (p.d : ℝ) + 2) (T := a + p.T) hd hP hω
  have hEq :
      (fun v => dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
        (fp81s21_horizonFieldExtension (a + p.T)
          (fp81s21_movingRawEtaField p R A ω) v)) =ᵐ[
        volume.restrict (Icc (0 : ℝ) (a + p.T))]
      (fun v => dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
        (fp81s21_movingRawEtaField p R A ω v)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hpoint : fp81s21_horizonFieldExtension (a + p.T)
        (fp81s21_movingRawEtaField p R A ω) v =
        fp81s21_movingRawEtaField p R A ω v := by
      funext f
      exact fp81s21_horizonFieldExtension_eq (a + p.T)
        (fp81s21_movingRawEtaField p R A ω) hv f
    rw [hpoint]
  exact hExt.congr hEq

#print axioms HRS.Fp81.S21.fp81s21_window_covariance_measure_physical'
#print axioms HRS.Fp81.S21.fp81s21_moving_raw_eta_dualNormE_aemeasurable_ae

end HRS.Fp81.S21
end
