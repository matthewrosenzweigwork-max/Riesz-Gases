import HRS.MS.Fp81S21GaussianWindowRS

/-! Packet 36RS: arbitrary supplied realizations/histories, then the retained
physical source. The public WG projection has exactly the revised 38G type.
The cutoff section representatives retain 36A's precise adaptedness contract. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

local instance fp81s21_GRS_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
local instance fp81s21_GRS_meas (H : ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GRS_borel (H : ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Generic supplied-data existence: arbitrary realization, its supplied
histories, the retained separate operators, and any measurable continuous prediction. -/
theorem fp81s21_gaussian_window_rs_supplied
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : fp81s21_moving_heat_full_clause p R future)
    (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (UG UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))))
    (hUG : fp81s21_TimeL2Rep G.P
      (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G)) Q.MUG 0 (a + p.T) UG)
    (hUB : fp81s21_TimeL2Rep G.P (Q.S.qe G)
      (Q.S.Kstar ^ 4 * Q.S.B / 2) 0 (a + p.T) UB)
    (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5)
    (Y : G.Ω → C(Icc (0 : ℝ) (a + p.T), Window p)) (hY : Measurable Y) :
    Nonempty (fp81s21_remote_G_RS_at Q future G a ha UG UB Φ
      (fp81s21_remote_G_extend G a ha Y)) := by
  let H := a + p.T
  have hH : 0 ≤ H := add_nonneg ha p.hT.le
  let Z := fp81s21_remote_G_extend G a ha Y
  let T := fp81s21_timeL2L1 H hH
  let LD := (fp81s21_driftBV (Q.OD a ha) hH (le_refl 0) hH le_rfl
    (by simp [H]) Q.hKD Q.hcD.le).comp T
  let LJ := (fp81s21_covarianceBV (Q.OJ a ha) hH (le_refl 0) hH le_rfl
    (by simp [H]) Q.hKJ Q.hcJ.le).comp T
  let D := fun ω t => fp81s21_gaussian_Dcum (Q.OD a ha) hH UB t ω
  let J := fun ω t => fp81s21_gaussian_Jcum (Q.OJ a ha) hH UG t ω
  let AD := fun ω t => fderiv ℝ (initialHeat future a ha Φ t) (Z ω t)
  let AJ := fun ω t => fp81s21_covariance_pairingCLM
    (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ t) (Z ω t))
  haveI : SecondCountableTopology (projTensor (Window p) 2) := s21g2_k06_sc (B := Window p) 2
  have hZm (t : ℝ) : Measurable (fun ω => Z ω t) :=
    (continuous_eval_const _).measurable.comp hY
  have hZc (ω : G.Ω) : ContinuousOn (Z ω) (Icc 0 H) :=
    ((Y ω).continuous.comp (continuous_projIcc (h := hH))).continuousOn
  have hDm (t : ℝ) : Measurable (fun ω => D ω t) :=
    (((Q.OD a ha).drift 0 t).comp T).measurable.comp hUB.1
  have hJm (t : ℝ) : Measurable (fun ω => J ω t) :=
    (((Q.OJ a ha).covariance 0 t).comp T).measurable.comp hUG.1
  have hΦm : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hdiff (t : ℝ) : ContDiff ℝ 5 (initialHeat future a ha Φ t) :=
    (fp81s21_windowFuture_heat_derivs future hf.1 a ha Φ hΦm t).1
  have hder (j : ℕ) (hj : j ≤ 5) (t : ℝ) (x : Window p) :
      ‖iteratedFDeriv ℝ j (initialHeat future a ha Φ t) x‖ ≤ 1 := by
    refine ((fp81s21_windowFuture_heat_derivs future hf.1 a ha Φ hΦm t).2 j hj x).2.trans ?_
    exact ciSup_le fun z =>
      (HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hΦm hj z).trans hΦ.2.2
  have hADm (t : ℝ) : Measurable (fun ω => ‖AD ω t‖) :=
    (((hdiff t).continuous_fderiv (by norm_num)).comp_stronglyMeasurable
      (hZm t).stronglyMeasurable).norm.measurable
  have hAJm (t : ℝ) : Measurable (fun ω => ‖AJ ω t‖) :=
    ((fp81s21_covariance_pairingCLM_continuous.comp
      ((hdiff t).continuous_iteratedFDeriv (by norm_num))).comp_stronglyMeasurable
        (hZm t).stronglyMeasurable).norm.measurable
  have hADc (ω : G.Ω) : ContinuousOn (AD ω) (Icc 0 H) := by
    have hc := (continuousMultilinearCurryFin1 ℝ (Window p) ℝ).continuous.comp_continuousOn
      (fp81s21_gaussian_window_heat_continuous future hf a ha Φ hΦm (Z ω) (hZc ω) 1
        (by norm_num))
    simpa only [Function.comp_def, s102_curry_iter] using hc
  have hAJc (ω : G.Ω) : ContinuousOn (AJ ω) (Icc 0 H) :=
    fp81s21_covariance_pairingCLM_continuous.comp_continuousOn
      (fp81s21_gaussian_window_heat_continuous future hf a ha Φ hΦm (Z ω) (hZc ω) 2 le_rfl)
  obtain ⟨WD⟩ := fp81s21_gaussian_rs_of_transport G.P H hH UB
    (hUB.2.1.integrable one_le_two) LD AD D hDm (by
      intro ω t ht
      rw [fp81s21_bvExt_apply hH (LD (UB ω)) ⟨t, ht⟩,
        ← fp81s21_bvPath_apply hH]
      change (Q.OD a ha).drift 0 t (T (UB ω)) =
        fp81s21_bvPath hH
          (fp81s21_driftBV (Q.OD a ha) hH (le_refl 0) hH le_rfl
            (by simp [H]) Q.hKD Q.hcD.le (T (UB ω))) ⟨t, ht⟩
      rw [fp81s21_driftBV_apply]
      simp only [zero_add, min_eq_left ht.2]) hADm hADc (by
      intro ω t
      change ‖fderiv ℝ _ _‖ ≤ 1
      rw [← norm_iteratedFDeriv_one]
      exact hder 1 (by norm_num) t _) (fp81s21_derivative_increment_measurable
      (fun t => initialHeat future a ha Φ t) Z D
      (fun t => (hdiff t).of_le (by norm_num))
      (fun t => (hZm t).stronglyMeasurable) (fun t => (hDm t).stronglyMeasurable))
  obtain ⟨WJ⟩ := fp81s21_gaussian_rs_of_transport G.P H hH UG
    (hUG.2.1.integrable one_le_two) LJ AJ J hJm (by
      intro ω t ht
      rw [fp81s21_bvExt_apply hH (LJ (UG ω)) ⟨t, ht⟩,
        ← fp81s21_bvPath_apply hH]
      change (Q.OJ a ha).covariance 0 t (T (UG ω)) =
        fp81s21_bvPath hH
          (fp81s21_covarianceBV (Q.OJ a ha) hH (le_refl 0) hH le_rfl
            (by simp [H]) Q.hKJ Q.hcJ.le (T (UG ω))) ⟨t, ht⟩
      rw [fp81s21_covarianceBV_apply]
      simp only [zero_add, min_eq_left ht.2]) hAJm hAJc (by
      intro ω t
      exact (fp81s21_covariance_pairingCLM_norm_le _).trans (hder 2 (by norm_num) t _))
      (fp81s21_covariance_derivative_increment_measurable
        (fun t => initialHeat future a ha Φ t) Z J
        (fun t => (hdiff t).of_le (by norm_num))
        (fun t => (hZm t).stronglyMeasurable) (fun t => (hJm t).stronglyMeasurable))
  exact ⟨⟨hH, WD, WJ⟩⟩

/-- A retained physical prediction, its exact section-adaptedness, and literal
Gaussian RS certificate at that prediction, ready for the revised 38G consumer. -/
structure fp81s21_GRS {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ) where
  Y : Q.src.G0.Ω → C(Icc (0 : ℝ) (a + p.T), Window p)
  measurable_Y : Measurable Y
  adapted : ∀ r : Icc (0 : ℝ) (a + p.T), ∃ Yr : Q.src.G0.Ω → Window p,
    Measurable Yr ∧ Measurable[MeasurableSpace.comap
      (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection (r : ℝ)) inferInstance] Yr ∧
    (fun ω => Y ω r) =ᵐ[Q.src.G0.P] Yr
  physical : ∀ r : Icc (0 : ℝ) (a + p.T), ∀ τ : Icc (0 : ℝ) p.T,
    ∀ᵐ ω ∂Q.src.G0.P, OscPath.at' (Y ω r) τ =
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        (a + τ) (min (r : ℝ) (a + τ))
        (fp81s21_chartAction Q.E (fp81s21_gaussian35_qG
          Q.tofp81s21_Gaussian35Selection (min (r : ℝ) (a + τ)) ω))
  WG : fp81s21_remote_G_RS_at Q future Q.src.G0 a ha (Q.UG a ha) (Q.UB a ha) Φ
    (fp81s21_remote_G_extend Q.src.G0 a ha Y)

/-- Radius first; preserve the supplied source, charts, histories, future and
separate operators. This stops at RS existence, before conditioning identities. -/
theorem fp81s21_gaussian_window_rs (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∀ Q : fp81s21_Physical35 p R,
      ∀ future, fp81s21_moving_heat_full_clause p R future →
      ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
        Nonempty (fp81s21_GRS Q future a ha Φ)) := by
  obtain ⟨δ₀, hδ₀, hhalf, hpred⟩ := fp81s21_gaussian_prediction_continuous_ae_adapted p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R Q future hf a ha Φ hΦ
  obtain ⟨Y, hYm, hYa, hYp⟩ := hpred δ hδ hδle R Q a ha
  obtain ⟨WG⟩ := fp81s21_gaussian_window_rs_supplied Q future hf Q.src.G0 a ha
    (Q.UG a ha) (Q.UB a ha) (Q.hUG a ha) (Q.hUB a ha) Φ hΦ Y hYm
  exact ⟨⟨Y, hYm, hYa, hYp, WG⟩⟩

#print axioms fp81s21_gaussian_window_rs_supplied
#print axioms fp81s21_GRS
#print axioms fp81s21_gaussian_window_rs
end HRS.Fp81.S21
end
