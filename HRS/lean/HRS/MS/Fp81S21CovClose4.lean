import HRS.MS.Fp81S21CovClose3

/-! Physical covariance-measure contract with start-independent constants. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Classical Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.FixEq
open HRS.MS.GenPath HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R2WinOrb HRS.MS.R2Interp

theorem fp81s21_window_covariance_measure_physical (p : Parameters) :
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
          R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T) z →
          R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T) z' →
          AEMeasurable (fun v => dualNormE (2 * p.d + 8) P (z v))
            (volume.restrict (Icc (0 : ℝ) (a + p.T))) →
          AEMeasurable (fun v => dualNormE (2 * p.d + 8) P (z' v))
            (volume.restrict (Icc (0 : ℝ) (a + p.T))) →
          AEMeasurable (fun v => dualNormE (2 * p.d + 8) P ((z + z') v))
            (volume.restrict (Icc (0 : ℝ) (a + p.T))) →
          AEMeasurable (fun v => dualNormE (2 * p.d + 8) P ((c • z) v))
            (volume.restrict (Icc (0 : ℝ) (a + p.T))) →
          ∃ (D : fp81s21_WindowLocalInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                p.T a (2 * p.d + 8) P z Cmix cdec)
            (D' : fp81s21_WindowLocalInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                p.T a (2 * p.d + 8) P z' Cmix cdec)
            (Dsum : fp81s21_WindowLocalInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                p.T a (2 * p.d + 8) P (z + z') Cmix cdec)
            (Dsmul : fp81s21_WindowLocalInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                p.T a (2 * p.d + 8) P (c • z) Cmix cdec),
            ∀ q s : ℝ, 0 ≤ q → q ≤ s → s ≤ a + p.T →
              fp81s21_covariance_interval_contract D D' Dsum Dsmul (K P) q s := by
  obtain ⟨δ0, hδ0, hhalf, hphysical⟩ :=
    fp81s21_window_covariance_block_physical_one_input p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Cs0, cdec, Cmix, hCs0, hcdec, hsumb, hCmix, hCs0Cmix, hbody⟩ :=
    hphysical δ hδ hδle R
  let K : ℝ → ℝ := fun P =>
    ((3 + Real.sqrt p.T) ^ 2 * fp81s21_blockC0) * |2 * (r26t3_coeff R).ν| *
      (s57pC p.d (2 * p.d + 8) P * ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
        (fp81s21_windowCovBlockAmp p.d (2 * p.d + 8) p.T Cmix) ^ 2))
  refine ⟨Cs0, cdec, Cmix, K, hCs0, hcdec, hsumb, hCmix, hCs0Cmix, ?_, ?_⟩
  · intro P; rfl
  intro a ha P hP z z' c hz hz' hm hm' hdual hdual' hdualSum hdualSmul
  obtain ⟨D, hblocks⟩ := hbody a ha P z hz hP hm
  obtain ⟨D', hblocks'⟩ := hbody a ha P z' hz' hP hm'
  obtain ⟨Dsum, hblocksSum⟩ := hbody a ha P (z + z')
    (fp81s21_IsR2L1F_add_of_aemeasurable_dualNorm hz hz' hdual) hP
    (s101_meas_add hm hm')
  obtain ⟨Dsmul, hblocksSmul⟩ := hbody a ha P (c • z)
    (fp81s21_IsR2L1F_smul hz) hP (s101_meas_smul c hm)
  refine ⟨D, D', Dsum, Dsmul, ?_⟩
  intro q s hq hqs hs
  simpa only [fp81s21_covariance_interval_contract, K] using
    (fp81s21_window_covariance_measure_spec D D' Dsum Dsmul
      (fp81s21_cov_block_linearity p R a) hblocks hblocks' hblocksSum hblocksSmul
      hdual hdual' hdualSum hdualSmul hq hqs hs)

#print axioms fp81s21_window_covariance_measure_physical
end HRS.Fp81.S21
end
