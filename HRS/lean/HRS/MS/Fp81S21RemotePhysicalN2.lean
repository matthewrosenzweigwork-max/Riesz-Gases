import HRS.MS.Fp81S21RemotePhysicalN

/-! The particle remote correction, with the supplied future and shared paths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.FixEq

local instance fp81s21_remotePhysicalN_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2

/-- Uniform remote bound for the literal packet-20 particle correction.
The covariance certificate parameters are universally bound after the constants;
the proof obtains its own uniform analytic bounds without reselecting the future. -/
theorem fp81s21_remote_physical_N (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∃ CN cN : ℝ, 0 < CN ∧ 0 < cN ∧
    ∀ (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)),
    fp81s21_moving_heat_full_clause p R future →
    ∀ (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
      (a : ℝ) (ha : 0 ≤ a) (D : fp81s21_finproj_shared_data p R a A F)
      (Cmix cdec : ℝ) (K : ℝ → ℝ),
    fp81s21_shared_physical_window_covariance_identification p R a ha A Cmix cdec K D.Fj →
    ∀ (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      let H := a + p.T
      let W := HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl
      let Ad := fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ) (W (D.Yh ω τ))
      let Fdw := fun ω t => fp81s21_weightedDrift_windowCum
        (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl (r26t3_coeff R)
        (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t
      let Aj := fun ω τ => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (D.Yh ω τ)))
      let Fjw := fun ω t => fp81s21_windowCovarianceMap p a ha (D.Fj ω t)
      ∀ WN : fp81s21_WindowRS A.P H Ad Fdw Aj Fjw,
      ∀ L : ℝ, 0 < L →
        |fp81s21_WindowRS_corr WN 0 (max (a - L) 0)| ≤ CN * Real.exp (-cN * L) := by
  obtain ⟨Es, E, εAvg, _, _, δs, hδs, hδsh, hs⟩ :=
    fp81s21_physical_joint_comparison_centered_retained p
  obtain ⟨δo, Co0, co0, hδo, _, hco0, ho⟩ := fp81s21_common_radius p
  obtain ⟨δi, hδi, _, hi⟩ := fp81s21_moving_inputs_all p
  obtain ⟨δj, hδj, _, hj⟩ := fp81s21_window_covariance_block_physical_one_input p
  refine ⟨min δs (min δo (min δi δj)), lt_min hδs (lt_min hδo (lt_min hδi hδj)),
    (min_le_left _ _).trans hδsh, ?_⟩
  intro δ hδ hδle R
  have hds := hδle.trans (min_le_left δs _)
  have hdo := hδle.trans ((min_le_right δs _).trans (min_le_left δo _))
  have hdi := hδle.trans ((min_le_right δs _).trans
    ((min_le_right δo _).trans (min_le_left δi δj)))
  have hdj := hδle.trans ((min_le_right δs _).trans
    ((min_le_right δo _).trans (min_le_right δi δj)))
  obtain ⟨MUG, _, canon, εN, εG, εB, _, _, _, _, _, _, S31, _⟩ := hs δ hδ hds R
  obtain ⟨Co, co, hco, hdvar⟩ := fp81s21_moving_weightedDrift_variation_le p R
    ⟨Co0, co0, hco0, (ho δ hδ hdo R.ρβ R.thermal).1⟩
  obtain ⟨Cs0, cj, Cj, _, hcj, _, _, _, hblocks⟩ := hj δ hδ hdj R
  let KD := s57pC p.d (2 * p.d + 8) (((p.d : ℝ) + 2) - 1) * |Co| *
    Real.sqrt (∑' α : MultiIndex p.d, HRS.MS.R2WinOrb.s103_b p.d α ^ 2)
  let KJ := ((3 + Real.sqrt p.T) ^ 2 * fp81s21_blockC0) * |2 * (r26t3_coeff R).ν| *
    (s57pC p.d (2 * p.d + 8) ((p.d : ℝ) + 2) * ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
      (fp81s21_windowCovBlockAmp p.d (2 * p.d + 8) p.T Cj) ^ 2))
  have hKD : 0 ≤ KD := mul_nonneg
    (mul_nonneg (s57pC_nonneg _ _ _) (abs_nonneg _)) (Real.sqrt_nonneg _)
  have hKJ : 0 ≤ KJ := by
    dsimp [KJ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) fp81s21_blockC0_nonneg)
      (abs_nonneg _)) (mul_nonneg (s57pC_nonneg _ _ _) (by positivity))
  let cN := min co (2 * cj)
  let C0 := KD * (Real.sqrt S31.MN * co⁻¹) +
    (1 / 2 : ℝ) * KJ * (Real.sqrt S31.MN * (2 * cj)⁻¹)
  refine ⟨max 1 C0, cN, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    lt_min hco (by positivity), ?_⟩
  intro future hf N hN A F a ha D Cmix cdec K hcov Φ hΦ
  dsimp only
  intro WN L hL
  let H := a + p.T
  let b := max (a - L) 0
  have hH : 0 < H := by dsimp [H]; linarith [p.hT]
  have hb : 0 ≤ b := le_max_right _ _
  have hba : b ≤ a := max_le (by linarith) ha
  have hbH : b ≤ H := hba.trans (by dsimp [H]; linarith [p.hT])
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd0 : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl
  let Ad := fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ) (W (D.Yh ω τ))
  let Fdw := fun ω t => fp81s21_weightedDrift_windowCum
    (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl (r26t3_coeff R)
    (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t
  let Aj := fun ω τ => fp81s21_covariance_pairingCLM
    (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (D.Yh ω τ)))
  let Fjw := fun ω t => fp81s21_windowCovarianceMap p a ha (D.Fj ω t)
  let Jd := fun ω => ∫⁻ v in Ioc (0 : ℝ) b,
    ENNReal.ofReal (Real.exp (-co * max (a - v) 0)) *
      dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2) (fp81s21_particleQuadField R N A v ω)
  let Jj := fun ω => ∫⁻ v in Ioc (0 : ℝ) b,
    ENNReal.ofReal (Real.exp (-(2 * cj) * max (a - v) 0)) *
      dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2) (fp81s21_particleEmpField R N A v ω)
  rcases S31.particle N hN A with ⟨_, _, _, _, hη, hB, ht⟩
  obtain ⟨Uη, UB, htη, htB, _⟩ := ht 0 le_rfl H hH
  have hTa : a ≤ H := by dsimp [H]; linarith [p.hT]
  obtain ⟨hdfin, hdint, hdexp⟩ := fp81s21_remotePhysicalN_source_tail
    hP E A.P _ _ S31.MN H hB UB htB co a L hco ha hTa hL
  obtain ⟨hjfin, hjint, hjexp⟩ := fp81s21_remotePhysicalN_source_tail
    hP E A.P _ _ S31.MN H hη Uη htη (2 * cj) a L (by positivity) ha hTa hL
  obtain ⟨coef, hstd, hphysAll⟩ := hi δ hδ hdi R a ha
  have hphys := hphysAll N hN A
  obtain ⟨Mb, hMb, _⟩ := fp81s21_moving_M1 p R hH hN A hstd
    (by push_cast; nlinarith [p.hd]) hphys
  have hdv : ∀ᵐ ω ∂A.P, BoundedVariationOn (Fdw ω) (Icc 0 b) ∧
      (eVariationOn (Fdw ω) (Icc 0 b)).toReal ≤ KD * (Jd ω).toReal := by
    filter_upwards [hMb, hdfin] with ω hω hfin
    have hv := hdvar A ω hH hstd (fp81s21_S102Lin p R H) hω
      ha p.hT.le le_rfl le_rfl hb hbH
    have hv' : eVariationOn (Fdw ω) (Icc 0 b) ≤ ENNReal.ofReal KD * Jd ω := hv
    have htop : ENNReal.ofReal KD * Jd ω ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
    refine ⟨ne_top_of_le_ne_top htop hv', ?_⟩
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hKD] using ENNReal.toReal_mono htop hv'
  -- Compare the supplied cumulative to a uniformly bounded physical constructor.
  have hL1 := fp81s21_moving_raw_eta_horizonL1F_ae p R hH hN A hphys
  have hcont := (A.strong H).cont
  have hjv : ∀ᵐ ω ∂A.P, BoundedVariationOn (Fjw ω) (Icc 0 b) ∧
      (eVariationOn (Fjw ω) (Icc 0 b)).toReal ≤ KJ * (Jj ω).toReal := by
    filter_upwards [hL1, hcont, D.Fj_good] with ω hz hc hg
    let z := fp81s21_horizonFieldExtension H (fp81s21_movingRawEtaField p R A ω)
    have hdual := fp81s21_dualNormE_aemeasurable_of_IsR2L1F
      (by have hd := p.hd; omega : 0 < p.d) hP hz
    have hm := fp81s21_R2JIntegrandMeas_horizonFieldExtension
      (fp81s21_moving_raw_eta_JIntegrandMeas p R hδ (hds.trans hδsh) hH
        (by omega : 0 < N) A.X ω hc)
    obtain ⟨Dc, hDc⟩ := hblocks a ha ((p.d : ℝ) + 2) z hz hP hm
    have heq : EqOn (Fjw ω) (fp81s21_window_covariance_cumulative Dc 0) (Icc 0 b) := by
      intro t ht
      apply Subtype.ext
      have hh := fp81s21_restrict_eq_windowJValue (r26t3_coeff R) p.hT ha z (Ioc 0 t)
        (fp81s21_JValue_horizonFieldExtension _ _ _ (hg.1 0 t le_rfl ht.1 (ht.2.trans hbH)))
        (fp81s21_window_covariance_measure_isWindowJValue Dc
          (fp81s21_cov_block_linearity p R a) hDc hdual le_rfl ht.1)
      change HRS.MC.E213O.tensorPow' 2 W (D.Fj ω t) =
        (fp81s21_window_covariance_measure Dc 0 t : TensorDual (Window p) 2)
      simpa only [D.Fj_zero, sub_zero] using hh
    have hv := fp81s21_window_covariance_cumulative_eVariationOn_le Dc
      (fp81s21_cov_block_linearity p R a) hDc hdual le_rfl hb hbH
    have hext : (∫⁻ v in Ioc (0 : ℝ) b,
        dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2) (z v) *
          ENNReal.ofReal (Real.exp (-2 * cj * max (a - v) 0))) = Jj ω := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hvH : v ∈ Icc (0 : ℝ) H := ⟨hv.1.le, hv.2.trans hbH⟩
      have hzv : z v = fp81s21_particleEmpField R N A v ω := by
        funext f
        exact fp81s21_horizonFieldExtension_eq H _ hvH f
      change dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2) (z v) *
        ENNReal.ofReal (Real.exp (-2 * cj * max (a - v) 0)) =
        ENNReal.ofReal (Real.exp (-(2 * cj) * max (a - v) 0)) *
        dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2) (fp81s21_particleEmpField R N A v ω)
      rw [hzv]
      have hexp : -2 * cj * max (a - v) 0 = -(2 * cj) * max (a - v) 0 := by ring
      rw [hexp]
      exact mul_comm _ _
    rw [← eVariationOn.congr heq, hext] at hv
    exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv.1, hv.2⟩
  have hΦm : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hdac : ∀ᵐ ω ∂A.P, ContinuousOn (Ad ω) (Icc 0 b) := by
    filter_upwards [D.Yh_continuous] with ω hy
    have hc := fp81s21_recent_heat_derivative_continuous p R future hf a ha Φ hΦm
      (fun t => W (D.Yh ω t)) (W.continuous.comp_continuousOn hy) 1 (by norm_num)
    have hc' := (continuousMultilinearCurryFin1 ℝ (Window p) ℝ).continuous.comp_continuousOn hc
    simpa only [Ad, Function.comp_def, s102_curry_iter] using hc'.mono (Icc_subset_Icc le_rfl hbH)
  have hjac : ∀ᵐ ω ∂A.P, ContinuousOn (Aj ω) (Icc 0 b) := by
    filter_upwards [D.Yh_continuous] with ω hy
    exact (fp81s21_window_covariance_pairing_continuousOn p R a ha hH future hf Φ hΦm
      (D.Yh ω) hy).mono (Icc_subset_Icc le_rfl hbH)
  have hdan : ∀ᵐ ω ∂A.P, ∀ t ∈ Icc (0 : ℝ) b, ‖Ad ω t‖ ≤ 1 := by
    filter_upwards [] with ω
    intro t ht
    have hh := fp81s21_recent_heat_derivative_bound future hf.1 a ha Φ hΦ t 1 (by norm_num) (W (D.Yh ω t))
    have hn := (continuousMultilinearCurryFin1 ℝ (Window p) ℝ).norm_map
      (iteratedFDeriv ℝ 1 (initialHeat future a ha Φ t) (W (D.Yh ω t)))
    simpa only [Ad, s102_curry_iter] using hn.trans_le hh
  have hjan : ∀ᵐ ω ∂A.P, ∀ t ∈ Icc (0 : ℝ) b, ‖Aj ω t‖ ≤ 1 := by
    filter_upwards [] with ω
    intro t ht
    exact (fp81s21_covariance_pairingCLM_norm_le _).trans
      (fp81s21_recent_heat_derivative_bound future hf.1 a ha Φ hΦ t 2 (by norm_num) _)
  have hdval := fp81s21_remotePhysicalN_value_bound WN.drift hb hbH
    (by filter_upwards [hdac, hdv] with ω hc hv; exact ⟨hc, hv.1⟩) hdan
  have hjval := fp81s21_remotePhysicalN_value_bound WN.covariance hb hbH
    (by filter_upwards [hjac, hjv] with ω hc hv; exact ⟨hc, hv.1⟩) hjan
  have hbound := fp81s21_remotePhysicalN_corr_bound WN hb hbH
    (fun ω => KD * (Jd ω).toReal) (fun ω => KJ * (Jj ω).toReal)
    (hdint.const_mul KD) (hjint.const_mul KJ)
    (by filter_upwards [hdval, hdv] with ω hv hd; exact hv.trans hd.2)
    (by filter_upwards [hjval, hjv] with ω hv hj; exact hv.trans hj.2)
  rw [integral_const_mul, integral_const_mul] at hbound
  have hed : Real.exp (-co * L) ≤ Real.exp (-cN * L) :=
    Real.exp_le_exp.mpr (by dsimp [cN]; nlinarith [min_le_left co (2 * cj)])
  have hej : Real.exp (-(2 * cj) * L) ≤ Real.exp (-cN * L) :=
    Real.exp_le_exp.mpr (by dsimp [cN]; nlinarith [min_le_right co (2 * cj)])
  have hd := (mul_le_mul_of_nonneg_left hdexp hKD).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hed (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr hco.le))) hKD)
  have hj' := (mul_le_mul_of_nonneg_left hjexp hKJ).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hej (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (by positivity)))) hKJ)
  calc
    |fp81s21_WindowRS_corr WN 0 b| ≤
        KD * (∫ ω, (Jd ω).toReal ∂A.P) + (1 / 2 : ℝ) * (KJ * (∫ ω, (Jj ω).toReal ∂A.P)) := hbound
    _ ≤ C0 * Real.exp (-cN * L) := by dsimp [C0]; nlinarith [hd, hj']
    _ ≤ max 1 C0 * Real.exp (-cN * L) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

#print axioms fp81s21_remote_physical_N
end HRS.Fp81.S21
end
