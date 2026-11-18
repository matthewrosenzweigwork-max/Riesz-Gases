import HRS.MS.R2SeAux21

/-!
# S9.9 `r2_static_edgeworth`, packet 22: the linear statistic against a test function, general observable

Worker S99, namespace `S99`.  `s99_Ylin`: for an observable `w ∈ C_b^{k0}` and `ψ ∈ Bd 3`,
`|E[Y_w ψ(W_N)] - ∑_m κ_{w,m} E[∂_mψ(G)]| ≤ K_L ‖w‖_{C_b^{k0}} / √N`, `κ_{w,m} = ∫ w a_m dμ`.
(The computation of `s99_A_rate` for a general `w`.)
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- `κ_{w,m} = ∫ w a_m dμ`. -/
def kap (d : ℕ) (s a β γ : ℝ) (w : Euc d → ℝ) (φ : ℕ → Euc d → ℝ) (m : ℕ) : ℝ :=
  ∫ x, w x * aRep d s a β γ (φ m) x ∂(thermalMeasure d s a β)

theorem s99_Yi_bd {N : ℕ} (hN1 : 1 ≤ N) {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {w : Euc d → ℝ}
    {cw : ℝ} (hwbd : ∀ x, |w x| ≤ cw) (X : EucConfig d N) :
    |s45_Yi N w (pair ν w) X| ≤ 2 * Real.sqrt N * cw := by
  simp only [s45_Yi]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := s45_abs_pair_empirical_le hN1 hwbd X
  have h2 : |pair ν w| ≤ cw := HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hwbd x)
  calc Real.sqrt N * |pair (empirical X) w - pair ν w|
      ≤ Real.sqrt N * (|pair (empirical X) w| + |pair ν w|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt N * (cw + cw) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt N * cw := by ring

section Ylin

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_Ylin {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) :
    ∃ KL : ℝ, 0 ≤ KL ∧ ∀ N : ℕ, 2 ≤ N → ∀ {w : Euc d → ℝ}, MemCb (k0 d) w → ∀ {ψ : SeqL2 → ℝ}, Bd 3 ψ →
      |(∫ X, s45_Yi N w (pair (S46.s46_nu d s a β γ N) w) X *
          ψ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)) -
        ∑' m, kap d s a β γ w φ m * ∫ z, pd ψ m z ∂G| ≤ KL * cbNorm (k0 d) w / Real.sqrt N := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨K₂, hK₂, h2⟩ := s99_chi1 hd hs0 hsd ha hβ hγ hT
  obtain ⟨KB, hKB0, hKB⟩ := s99_Bq_bound hd hs0 hs ha hβ hγ hT hS
  obtain ⟨KT, hKT0, hTL2⟩ := s99_T_L2 hd hs0 hs ha hβ hγ hT hS
  obtain ⟨Kclt, hKclt0, hclt⟩ := s99_clt hd hs0 hs ha hβ hγ (J1_gt d) hφ hG
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  set Sb : ℝ := ∑' m, b m with hSb
  have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
  set KL : ℝ := KB * K₂ + (KT + Kclt) * γ⁻¹ * K₂ * Sb with hKL
  have hKL0 : 0 ≤ KL := by positivity
  refine ⟨KL, hKL0, fun N hN w hwcb ψ hψ => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hk0 : 1 ≤ k0 d := k0_ge_one d
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  set cw := cbNorm (k0 d) w with hcwdef
  have hcw0 : 0 ≤ cw := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hwbd : ∀ x, |w x| ≤ cw := fun x => by
    have := s99_norm_iter_le_cb hwcb (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hwc1 : ContDiff ℝ 1 w := hwcb.1.of_le (by exact_mod_cast hk0)
  have hwm : Measurable w := hwc1.continuous.measurable
  have hDw : ∀ x, ‖fderiv ℝ w x‖ ≤ cw := fun x => s45_cb_deriv_le hk0 hwcb x
  have hwL2 : MemLp w 2 (thermalMeasure d s a β) :=
    MemLp.of_bound hwm.aestronglyMeasurable cw (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hwbd x)
  obtain ⟨χw, hχw2, hwf, hgenw⟩ := h2 w hwcb
  have hψd : Bd 3 ψ := hψ
  have hJ0 : IsSummableFeatureFamily (k0 d) φ := by
    refine ⟨fun l => (HRS.MS.Tc5.tc5_cb_mono (J1_ge_k0 d |>.trans' (by omega)) (hφ.1 l)).1, ?_⟩
    refine Summable.of_nonneg_of_le (fun l => HRS.MS.Tc5.tc5_cb_nonneg _ _) (fun l => ?_) hφ.2
    exact (HRS.MS.Tc5.tc5_cb_mono (by have := J1_ge_k0 d; omega) (hφ.1 l)).2
  have hWc : Continuous (fun X : EucConfig d N => featureVec φ ν X) :=
    (s99_W_contDiff hN1 (by unfold J1; omega) hφ).continuous
  have hψW_bd : ∀ X : EucConfig d N, |ψ (featureVec φ ν X)| ≤ 1 := fun X => hψd.abs_le _
  have hψW_meas : Measurable fun X : EucConfig d N => ψ (featureVec φ ν X) :=
    (hψd.1.continuous.comp hWc).measurable
  set Y : EucConfig d N → ℝ := fun X => s45_Yi N w (pair ν w) X with hYdef
  -- the plain Stein identity for `w`
  have hE := s99_E1_plain hd hs0 hsd ha hβ hγ hT hN (hS N hN) (J := k0 d) hk0 hJ0 hwcb hwf
    (ψ := ψ) (hψd.of_le (by norm_num))
  have hv1 : ContDiff ℝ 1 (gradient χw) := s45_contDiff_gradient hχw2
  have hsqrt : ∀ X : EucConfig d N, Real.sqrt N * s45_Rp (thermalMeasure d s a β) ν P
      (commutatorKernel d s (gradient χw)) X = -(Bq d s a β γ N χw X) / Real.sqrt N := fun X =>
    s99_sqrt_Rp hd hs0 hsd hT hN (hS N hN) hχw2 hwf.B2 X
  obtain ⟨-, -, hBi, hB1⟩ := hKB N hN hχw2 hwf.B2
  have hBm : Measurable fun X : EucConfig d N => Bq d s a β γ N χw X := by
    unfold Bq
    exact measurable_const.mul ((HRS.MS.Wr.wr9_measurable_pairEnergy
      (HRS.MS.Comm.comm_meas (s := s) (gradient χw) hv1.continuous.measurable)).sub measurable_const)
  -- the remainder term
  set R : ℝ := ∫ X, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) ν P
      (commutatorKernel d s (gradient χw)) X) * ψ (featureVec φ ν X) ∂P with hRdef
  have hR : |R| ≤ KB * (K₂ * cw) / Real.sqrt N := by
    have hpt : ∀ X : EucConfig d N, ‖(Real.sqrt N * s45_Rp (thermalMeasure d s a β) ν P
        (commutatorKernel d s (gradient χw)) X) * ψ (featureVec φ ν X)‖ ≤
        |Bq d s a β γ N χw X| / Real.sqrt N := fun X => by
      rw [hsqrt X, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hsqN]
      calc |Bq d s a β γ N χw X| / Real.sqrt N * |ψ (featureVec φ ν X)|
          ≤ |Bq d s a β γ N χw X| / Real.sqrt N * 1 :=
            mul_le_mul_of_nonneg_left (hψW_bd X) (by positivity)
        _ = _ := mul_one _
    have hint : Integrable (fun X : EucConfig d N => |Bq d s a β γ N χw X| / Real.sqrt N) P :=
      hBi.abs.div_const _
    have h1 := norm_integral_le_integral_norm (μ := P) (fun X : EucConfig d N =>
      (Real.sqrt N * s45_Rp (thermalMeasure d s a β) ν P
        (commutatorKernel d s (gradient χw)) X) * ψ (featureVec φ ν X))
    have h2 : ∫ X, ‖(Real.sqrt N * s45_Rp (thermalMeasure d s a β) ν P
        (commutatorKernel d s (gradient χw)) X) * ψ (featureVec φ ν X)‖ ∂P ≤
        ∫ X, |Bq d s a β γ N χw X| / Real.sqrt N ∂P :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) hint
        (Filter.Eventually.of_forall hpt)
    have h3 : ∫ X, |Bq d s a β γ N χw X| / Real.sqrt N ∂P ≤ KB * (K₂ * cw) / Real.sqrt N := by
      rw [integral_div]
      exact div_le_div_of_nonneg_right hB1 hsqN.le
    rw [← Real.norm_eq_abs]
    exact h1.trans (h2.trans h3)
  -- the series
  set w2 : ℕ → Euc d → ℝ := fun m x => γ⁻¹ * ⟪gradient χw x, gradient (φ m) x⟫ with hw2
  have hDφ : ∀ m x, ‖fderiv ℝ (φ m) x‖ ≤ b m := fun m x =>
    s45_cb_deriv_le (by unfold J1; omega) (hφ.1 m) x
  have hBφ : ∀ m x, |φ m x| ≤ b m := fun m x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 m) x
    rwa [Real.norm_eq_abs] at this
  have hφm1 : ∀ m, ContDiff ℝ 1 (φ m) := fun m => (hφ.1 m).1.of_le (by
    exact_mod_cast (by unfold J1; omega : 1 ≤ J1 d))
  set Cm : ℕ → ℝ := fun m => γ⁻¹ * (K₂ * cw) * b m with hCm
  have hCm0 : ∀ m, 0 ≤ Cm m := fun m => by
    have := hb0 m; have := hK₂; positivity
  have hw2bd : ∀ m x, |w2 m x| ≤ Cm m := by
    intro m x
    simp only [hw2, hCm]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    exact mul_le_mul_of_nonneg_left (s99_inner_grad_le hwf.B1 (hDφ m) x) (inv_nonneg.2 hγ.le)
      |>.trans_eq (by ring)
  have hw2c : ∀ m, Continuous (w2 m) := fun m =>
    continuous_const.mul (hv1.continuous.inner
      (s45_gradient_continuous (hφm1 m)))
  have hcc : ∀ m, kap d s a β γ w φ m = ∫ x, w2 m x ∂(thermalMeasure d s a β) := by
    intro m
    have h1 := s99_cov_ibp hd hs0 hsd hγ hT (w := w) (ψ := φ m) (χ := F.χ m)
      (af := aRep d s a β γ (φ m)) hwc1 hwbd hDw (HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 m))
      (F.feat hT hγ m) (F.gen m)
    have h2 := s99_cov_corr hd hs0 hsd hγ hT hwL2 hwf (hφm1 m) (hBφ m) (hDφ m)
    have h3 : kap d s a β γ w φ m =
        ∫ x, w x * aRep d s a β γ (φ m) x ∂(thermalMeasure d s a β) := rfl
    rw [h3, ← h1, h2]
  have hcm_bd : ∀ m, |∫ x, w2 m x ∂(thermalMeasure d s a β)| ≤ Cm m := fun m => by
    have := norm_integral_le_of_norm_le_const (μ := thermalMeasure d s a β) (f := w2 m)
      (C := Cm m) (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hw2bd m x)
    simpa [Real.norm_eq_abs] using this
  set T2 : ℕ → EucConfig d N → ℝ := fun m X =>
    γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χw x, gradient (φ m) x⟫) with hT2
  have hT2e : ∀ m X, T2 m X = pair (empirical X) (w2 m) := fun m X =>
    (s99_pair_smul hN1 γ⁻¹ _ X).symm
  have hT2m : ∀ m, Measurable (T2 m) := fun m => by
    have : T2 m = fun X => pair (empirical X) (w2 m) := funext (hT2e m)
    rw [this]
    exact s45_measurable_pair_empirical hN1 (hw2c m).measurable
  have hT2bd : ∀ m X, |T2 m X| ≤ Cm m := fun m X => by
    rw [hT2e]; exact s45_abs_pair_empirical_le hN1 (hw2bd m) X
  have hpdm : ∀ m, Bd 2 (pd ψ m) := fun m => hψ.pd m
  have hpdm_m : ∀ m, Measurable fun X : EucConfig d N => pd ψ m (featureVec φ ν X) := fun m =>
    ((hpdm m).1.continuous.comp hWc).measurable
  have hTm_int : ∀ m, Integrable (fun X : EucConfig d N => T2 m X * pd ψ m (featureVec φ ν X)) P :=
    fun m => Integrable.of_bound ((hT2m m).mul (hpdm_m m)).aestronglyMeasurable (Cm m)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |T2 m X| * |pd ψ m (featureVec φ ν X)| ≤ Cm m * 1 :=
              mul_le_mul (hT2bd m X) ((hpdm m).abs_le _) (abs_nonneg _) (hCm0 m)
          _ = _ := mul_one _)
  have hdiff : ∀ m, |(∫ X, T2 m X * pd ψ m (featureVec φ ν X) ∂P) -
      kap d s a β γ w φ m * ∫ z, pd ψ m z ∂G| ≤ (KT + Kclt) * Cm m / Real.sqrt N := by
    intro m
    obtain ⟨hi1, hi2, hcl⟩ := hclt N hN (hpdm m)
    set cmv : ℝ := ∫ x, w2 m x ∂(thermalMeasure d s a β) with hcmv
    rw [hcc m]
    have hpdm_int : Integrable (fun X : EucConfig d N => pd ψ m (featureVec φ ν X)) P := hi1
    have hdec : (∫ X, T2 m X * pd ψ m (featureVec φ ν X) ∂P) - cmv * ∫ z, pd ψ m z ∂G =
        (∫ X, (T2 m X - cmv) * pd ψ m (featureVec φ ν X) ∂P) +
          cmv * ((∫ X, pd ψ m (featureVec φ ν X) ∂P) - ∫ z, pd ψ m z ∂G) := by
      have : ∫ X, (T2 m X - cmv) * pd ψ m (featureVec φ ν X) ∂P =
          (∫ X, T2 m X * pd ψ m (featureVec φ ν X) ∂P) - cmv * ∫ X, pd ψ m (featureVec φ ν X) ∂P := by
        rw [← integral_const_mul, ← integral_sub (hTm_int m) (hpdm_int.const_mul cmv)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
        simp only; ring
      rw [this]; ring
    rw [hdec]
    have hu : Measurable (w2 m) := (hw2c m).measurable
    have hL1 := s99_T_L1 hT hS hKT0 hTL2 hN (hCm0 m) hu (hw2bd m)
    have e1 : |∫ X, (T2 m X - cmv) * pd ψ m (featureVec φ ν X) ∂P| ≤ KT * Cm m / Real.sqrt N := by
      have hpt : ∀ X : EucConfig d N, ‖(T2 m X - cmv) * pd ψ m (featureVec φ ν X)‖ ≤
          |pair (empirical X) (w2 m) - pair (thermalMeasure d s a β) (w2 m)| := fun X => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hT2e]
        have : pair (thermalMeasure d s a β) (w2 m) = cmv := rfl
        rw [this]
        calc |pair (empirical X) (w2 m) - cmv| * |pd ψ m (featureVec φ ν X)|
            ≤ |pair (empirical X) (w2 m) - cmv| * 1 :=
              mul_le_mul_of_nonneg_left ((hpdm m).abs_le _) (abs_nonneg _)
          _ = _ := mul_one _
      have hint : Integrable (fun X : EucConfig d N =>
          |pair (empirical X) (w2 m) - pair (thermalMeasure d s a β) (w2 m)|) P := by
        refine Integrable.of_bound (((s45_measurable_pair_empirical hN1 hu).sub
          measurable_const).abs).aestronglyMeasurable (Cm m + Cm m)
          (Filter.Eventually.of_forall fun X => ?_)
        rw [Real.norm_eq_abs, abs_abs]
        have h1 := s45_abs_pair_empirical_le hN1 (hw2bd m) X
        have h2 : |pair (thermalMeasure d s a β) (w2 m)| ≤ Cm m :=
          HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hw2bd m x)
        calc _ ≤ |pair (empirical X) (w2 m)| + |pair (thermalMeasure d s a β) (w2 m)| := abs_sub _ _
          _ ≤ Cm m + Cm m := add_le_add h1 h2
      have h1 := norm_integral_le_integral_norm (μ := P) (fun X : EucConfig d N =>
        (T2 m X - cmv) * pd ψ m (featureVec φ ν X))
      have h2 := integral_mono_of_nonneg (μ := P) (Filter.Eventually.of_forall fun X =>
        norm_nonneg ((T2 m X - cmv) * pd ψ m (featureVec φ ν X))) hint (Filter.Eventually.of_forall hpt)
      rw [← Real.norm_eq_abs]
      exact h1.trans (h2.trans hL1)
    have e2 : |cmv * ((∫ X, pd ψ m (featureVec φ ν X) ∂P) - ∫ z, pd ψ m z ∂G)| ≤
        Kclt * Cm m / Real.sqrt N := by
      rw [abs_mul]
      calc |cmv| * |(∫ X, pd ψ m (featureVec φ ν X) ∂P) - ∫ z, pd ψ m z ∂G|
          ≤ Cm m * (Kclt / Real.sqrt N) := mul_le_mul (hcm_bd m) hcl (abs_nonneg _) (hCm0 m)
        _ = Kclt * Cm m / Real.sqrt N := by ring
    calc _ ≤ |∫ X, (T2 m X - cmv) * pd ψ m (featureVec φ ν X) ∂P| +
          |cmv * ((∫ X, pd ψ m (featureVec φ ν X) ∂P) - ∫ z, pd ψ m z ∂G)| := abs_add_le _ _
      _ ≤ KT * Cm m / Real.sqrt N + Kclt * Cm m / Real.sqrt N := add_le_add e1 e2
      _ = (KT + Kclt) * Cm m / Real.sqrt N := by ring
  -- the series
  set Tm : ℕ → ℝ := fun m => ∫ X, T2 m X * pd ψ m (featureVec φ ν X) ∂P with hTm
  set Gm : ℕ → ℝ := fun m => ∫ z, pd ψ m z ∂G with hGm
  have hCmS : Summable Cm := hbs.mul_left (γ⁻¹ * (K₂ * cw))
  have hTm_bd : ∀ m, ‖Tm m‖ ≤ Cm m := fun m => by
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X : EucConfig d N => T2 m X * pd ψ m (featureVec φ ν X)) (C := Cm m)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |T2 m X| * |pd ψ m (featureVec φ ν X)| ≤ Cm m * 1 :=
              mul_le_mul (hT2bd m X) ((hpdm m).abs_le _) (abs_nonneg _) (hCm0 m)
          _ = _ := mul_one _)
    simpa using this
  have hGm_bd : ∀ m, |Gm m| ≤ 1 := fun m => by
    have := norm_integral_le_of_norm_le_const (μ := G) (f := pd ψ m) (C := 1)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hpdm m).abs_le z)
    simpa [Real.norm_eq_abs] using this
  have hccGm_bd : ∀ m, ‖kap d s a β γ w φ m * Gm m‖ ≤ Cm m := fun m => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hcc m]
    calc |∫ x, w2 m x ∂(thermalMeasure d s a β)| * |Gm m| ≤ Cm m * 1 :=
          mul_le_mul (hcm_bd m) (hGm_bd m) (abs_nonneg _) (hCm0 m)
      _ = _ := mul_one _
  have hsumT : Summable Tm := Summable.of_norm_bounded hCmS hTm_bd
  have hsumG : Summable fun m => kap d s a β γ w φ m * Gm m :=
    Summable.of_norm_bounded hCmS hccGm_bd
  have hE' : ∫ X, Y X * ψ (featureVec φ ν X) ∂P = R + ∑' m, Tm m := hE
  have hdecomp : (∫ X, Y X * ψ (featureVec φ ν X) ∂P) - ∑' m, kap d s a β γ w φ m * Gm m =
      R + ∑' m, (Tm m - kap d s a β γ w φ m * Gm m) := by
    rw [hE', hsumT.tsum_sub hsumG]; ring
  have hser : |∑' m, (Tm m - kap d s a β γ w φ m * Gm m)| ≤
      (KT + Kclt) / Real.sqrt N * (γ⁻¹ * (K₂ * cw) * Sb) := by
    have hg : HasSum (fun m => (KT + Kclt) / Real.sqrt N * Cm m)
        ((KT + Kclt) / Real.sqrt N * ∑' m, Cm m) := hCmS.hasSum.mul_left _
    have hCsum : ∑' m, Cm m = γ⁻¹ * (K₂ * cw) * Sb := by
      simp only [hCm]; rw [tsum_mul_left]
    rw [hCsum] at hg
    have := tsum_of_norm_bounded hg (f := fun m => Tm m - kap d s a β γ w φ m * Gm m) (fun m => by
      rw [Real.norm_eq_abs]
      refine (hdiff m).trans (le_of_eq ?_)
      ring)
    rwa [Real.norm_eq_abs] at this
  show |(∫ X, Y X * ψ (featureVec φ ν X) ∂P) - ∑' m, kap d s a β γ w φ m * Gm m| ≤ _
  rw [hdecomp]
  calc |R + ∑' m, (Tm m - kap d s a β γ w φ m * Gm m)|
      ≤ |R| + |∑' m, (Tm m - kap d s a β γ w φ m * Gm m)| := abs_add_le _ _
    _ ≤ KB * (K₂ * cw) / Real.sqrt N + (KT + Kclt) / Real.sqrt N * (γ⁻¹ * (K₂ * cw) * Sb) :=
        add_le_add hR hser
    _ = KL * cw / Real.sqrt N := by simp only [hKL]; ring

end Ylin

end S99

end
