import HRS.MS.Fp81S21CovBlockAPI
import HRS.MS.Fp81S21CovBlockAPI2

/-! Packet 15-close: physical localized input and moving covariance blocks. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas
open HRS.MS.GenPath HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R2WinOrb
open HRS.MS.FixEq
/-- Construct the full physical localized input from the retained density
assumptions. The selected `Cmix` is the one returned together with the
positive derivative certificate, so the field `fp81s21_hPos` has exactly the
constants used in the block estimate. -/
theorem fp81s21_window_local_input_physical (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ Cs0 cdec Cmix : ℝ,
        0 ≤ Cs0 ∧ 0 < cdec ∧ Summable (s104_b p.d) ∧
        0 ≤ Cmix ∧ Cs0 ≤ Cmix ∧
        ∀ a : ℝ, 0 ≤ a → ∀ P : ℝ,
          ∀ z : ℝ → (Euc p.d → ℝ) → ℝ,
          IsR2L1F (2 * p.d + 8) P (a + p.T) z →
          (p.d : ℝ) < 2 * P →
          R2JIntegrandMeas (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) (a + p.T) z →
          ∃ D : fp81s21_WindowLocalInput (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P z Cmix cdec, True := by
  obtain ⟨δc, Co, co, hδc, hδcHalf, hco, hcommon⟩ :=
    fp81s21_common_radius p
  obtain ⟨δd, hδd, hδdHalf, hdecayAll⟩ :=
    fp81s21_moving_observation_window_orbit_decay p
  let δ0 : ℝ := min δc δd
  have hδ0 : 0 < δ0 := lt_min hδc hδd
  have hδ0Half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδcHalf
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R
  have hδc' : δ ≤ δc := hδle.trans (min_le_left _ _)
  have hδd' : δ ≤ δd := hδle.trans (min_le_right _ _)
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ hδc' R.ρβ R.thermal
  obtain ⟨Cs0, cdec, hCs0, hcdec, hsumb, _hsumbSq, hdecayRaw⟩ :=
    hdecayAll δ hδ hδd' R
  have hdecay : fp81s21_WindowOrbitDecay p R Cs0 cdec := by
    dsimp [fp81s21_WindowOrbitDecay]
    exact hdecayRaw
  obtain ⟨Cmix, hCmix, hCs0Cmix, hPosAll⟩ :=
    fp81s21_window_feature_hpos_of_decay_data p R hterm hCs0 hcdec hsumb hdecay
  refine ⟨Cs0, cdec, Cmix, hCs0, hcdec, hsumb, hCmix, hCs0Cmix, ?_⟩
  intro a ha P z hz hP hm
  have hHa : 0 < a + p.T := by linarith [ha, p.hT]
  obtain ⟨cData, hData⟩ := fp81s21_moving_s101data_of_common
    p R hHa hclaims hterm
  have horb : R2OrbitSummable (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) (a + p.T) (2 * p.d + 8) :=
    fp81s21_covLocal_orbit_summable p R hHa hclaims hterm
  have hterminal : ∀ v ∈ Icc (0 : ℝ) (a + p.T),
      ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
      propagatorW (r26t3_coeff R) v v
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x =
          oscTestFun (wholeSpaceIndex p.d : ℝ) α x := by
    intro v hv α x
    have horbα : S104nOrbit (r26t3_coeff R)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) (a + p.T) :=
      s104b_orbit_of_termRegGen hterm R.admissible R.resulting α
        (a + p.T) (by linarith [ha, p.hT])
    have hclass := HRS.MS.Fcau.propagatorW_isClassical (horbα.ex0 v hv)
    simpa using congrFun hclass.terminal x
  have hPos : ∀ v ∈ Icc (0 : ℝ) (a + p.T),
      ∀ j : ℕ, 1 ≤ j → j ≤ 2 * p.d + 9 → ∀ x : Euc p.d,
      ‖iteratedFDeriv ℝ j
        (fp81s21_window_feature (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) p.T a v) x‖ ≤
        fp81s21_window_feature_Bpos p.d (2 * p.d + 8) p.T
          Cmix cdec a v := by
    intro v hv j hj1 hjr x
    exact hPosAll a ha v hv cData hData j hj1 hjr x
  let D : fp81s21_WindowLocalInput (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P z Cmix cdec := {
    fp81s21_hd := by have := p.hd; omega
    fp81s21_hH := p.hT
    fp81s21_ha := ha
    fp81s21_horb := horb
    fp81s21_hterminal := hterminal
    fp81s21_hz := hz
    fp81s21_hP := hP
    fp81s21_hm := hm
    fp81s21_hCmix := hCmix
    fp81s21_hcdec := hcdec
    fp81s21_hPos := hPos
  }
  exact ⟨D, trivial⟩

theorem fp81s21_cov_block_linearity
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (a : ℝ) :
    ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + p.T →
      ∀ φ ψ : Euc p.d → ℝ, ∀ c : ℝ,
        IsR2DualCombo (wholeSpaceIndex p.d : ℝ) φ →
        IsR2DualCombo (wholeSpaceIndex p.d : ℝ) ψ →
        propagatorW (r26t3_coeff R) u t (φ + c • ψ) =
          propagatorW (r26t3_coeff R) u t φ + c • propagatorW (r26t3_coeff R) u t ψ := by
  have hlin := fp81s21_S102Lin p R (a + p.T)
  simpa [HRS.MS.R2Interp.S102Lin] using hlin

private lemma fp81s21_covLocal_feature_Bpos_sq_explicit
    (d r : ℕ) (H Cmix cdec a v : ℝ) :
    (fp81s21_window_feature_Bpos d r H Cmix cdec a v) ^ 2 =
      (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2 *
        Real.exp (-2 * cdec * max (a - v) 0) := by
  have hexp : (Real.exp (-cdec * max (a - v) 0)) ^ 2 =
      Real.exp (-2 * cdec * max (a - v) 0) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  dsimp [fp81s21_window_feature_Bpos, fp81s21_window_Bpos,
    fp81s21_windowCovBlockAmp]
  calc
    _ = ((2 + (d : ℝ) ^ (r + 1) *
          ((volume.restrict (Icc (0 : ℝ) H)) Set.univ).toReal ^ (1 / 2 : ℝ)) *
        Cmix * Real.sqrt (∑' α : MultiIndex d, (s104_b d α) ^ 2)) ^ 2 *
        (Real.exp (-cdec * max (a - v) 0)) ^ 2 := by ring
    _ = _ := by rw [hexp]

/-- Physical moving covariance blocks, with the input constructed at the same
`Cs0`, `cdec`, and `Cmix` selected by the positive feature estimate. The
weighted-bound and coordinate clauses assemble the staged block exports into
the `WindowCovarianceBlockContract` shape. The coordinate clause includes
projective membership. Propagator linearity is discharged by
`fp81s21_S102Lin`; block-value linearity and set-additivity remain packet 16a. -/
theorem fp81s21_window_covariance_block_physical (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ Cs0 cdec Cmix : ℝ,
        0 ≤ Cs0 ∧ 0 < cdec ∧ Summable (s104_b p.d) ∧
        0 ≤ Cmix ∧ Cs0 ≤ Cmix ∧
        ∀ a : ℝ, 0 ≤ a → ∀ P : ℝ,
          ∀ z : ℝ → (Euc p.d → ℝ) → ℝ,
          IsR2L1F (2 * p.d + 8) P (a + p.T) z →
          (p.d : ℝ) < 2 * P →
          R2JIntegrandMeas (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) (a + p.T) z →
          ∀ I : Set ℝ, MeasurableSet I → ∀ k : ℕ,
          ∃ D : fp81s21_WindowLocalInput (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P z Cmix cdec,
            fp81s21_WindowCovarianceBlockContract D
              (fp81s21_cov_block_linearity p R a)
              I k := by
  obtain ⟨δ0, hδ0, hδ0Half, hphysical⟩ :=
    fp81s21_window_local_input_physical p
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Cs0, cdec, Cmix, hCs0, hcdec, hsumb, hCmix, hCs0Cmix, hlocal⟩ :=
    hphysical δ hδ hδle R
  refine ⟨Cs0, cdec, Cmix, hCs0, hcdec, hsumb, hCmix, hCs0Cmix, ?_⟩
  intro a ha P z hz hP hm I hI k
  obtain ⟨D, -⟩ := hlocal a ha P z hz hP hm
  let hlin := fp81s21_cov_block_linearity p R a
  refine ⟨D, ?_⟩
  constructor
  · have hnorm := fp81s21_blockValue_norm_le D hI k
    have hweighted := fp81s21_windowLocal_lintegral_bound_weighted D hI k
    have hprofile : ∀ v : ℝ,
        (fp81s21_window_feature_Bpos p.d (2 * p.d + 8) p.T
          Cmix cdec a v) ^ 2 =
          (fp81s21_windowCovBlockAmp p.d (2 * p.d + 8) p.T Cmix) ^ 2 *
            Real.exp (-2 * cdec * max (a - v) 0) := by
      intro v
      exact fp81s21_covLocal_feature_Bpos_sq_explicit p.d
        (2 * p.d + 8) p.T Cmix cdec a v
    have hintegral :
        (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
          ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
            dualNormE (2 * p.d + 8) P (z v) *
            ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
              ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                (fp81s21_window_feature_Bpos p.d (2 * p.d + 8)
                  p.T Cmix cdec a v) ^ 2))) =
        ∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
          ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
            dualNormE (2 * p.d + 8) P (z v) *
            ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
              ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                ((fp81s21_windowCovBlockAmp p.d (2 * p.d + 8)
                    p.T Cmix) ^ 2 *
                  Real.exp (-2 * cdec * max (a - v) 0)))) := by
      refine lintegral_congr fun v => ?_
      rw [hprofile v]
    have hrawWeighted :
        (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
          ENNReal.ofReal (HRS.traceNormForm
            (fp81s21_windowDm (r26t3_coeff R)
              (wholeSpaceIndex p.d : ℝ) p.T a z D.fp81s21_ha
              (le_of_lt D.fp81s21_hH) v))) ≤
        (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
          ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
            dualNormE (2 * p.d + 8) P (z v) *
            ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
              ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                (fp81s21_window_feature_Bpos p.d (2 * p.d + 8)
                  p.T Cmix cdec a v) ^ 2))) := by
      rw [← fp81s21_blockValue_traceIntegral_eq D hI k]
      exact hweighted
    calc
      ‖fp81s21_blockValue D I k‖ₑ ≤
          ENNReal.ofReal ((3 + Real.sqrt p.T) ^ 2 * fp81s21_blockC0) *
            (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
              ENNReal.ofReal (HRS.traceNormForm
                (fp81s21_windowDm (r26t3_coeff R)
                  (wholeSpaceIndex p.d : ℝ) p.T a z D.fp81s21_ha
                  (le_of_lt D.fp81s21_hH) v))) := hnorm
      _ ≤ ENNReal.ofReal ((3 + Real.sqrt p.T) ^ 2 * fp81s21_blockC0) *
          (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
            ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
              dualNormE (2 * p.d + 8) P (z v) *
              ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
                ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                  (fp81s21_window_feature_Bpos p.d (2 * p.d + 8)
                    p.T Cmix cdec a v) ^ 2))) :=
          mul_le_mul' le_rfl hrawWeighted
      _ = ENNReal.ofReal ((3 + Real.sqrt p.T) ^ 2 * fp81s21_blockC0) *
          (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
            ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
              dualNormE (2 * p.d + 8) P (z v) *
              ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
                ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                  ((fp81s21_windowCovBlockAmp p.d (2 * p.d + 8)
                      p.T Cmix) ^ 2 *
                    Real.exp (-2 * cdec * max (a - v) 0))))) := by
        exact congrArg
          (fun t : ℝ≥0∞ => ENNReal.ofReal ((3 + Real.sqrt p.T) ^ 2 *
            fp81s21_blockC0) * t) hintegral
  · exact fp81s21_blockValue_isWindowJValue D hlin hI k

#print axioms fp81s21_window_local_input_physical
#print axioms fp81s21_cov_block_linearity
#print axioms fp81s21_window_covariance_block_physical

end HRS.Fp81.S21

end
