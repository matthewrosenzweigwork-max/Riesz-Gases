import HRS.MS.R2SeAux17

/-!
# S9.9 `r2_static_edgeworth`, packet 18: the linear-term limit with a rate (main estimate)

Worker S99, namespace `S99`.  See `R2SeAux17` for the statement of `s99_A_rate`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section A

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_A_rate {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ N : ℕ, 2 ≤ N → ∀ f : SeqL2 → ℝ, SteinCl f → ∀ p : ℕ × ℕ,
      |Aterm d s a β γ F N f p - Alim d s a β γ F G f p| ≤
        KA * (cbNorm (J1 d) (φ p.1) * cbNorm (J1 d) (φ p.2)) / Real.sqrt N := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨K₂, hK₂, h2⟩ := s99_chi1 hd hs0 hsd ha hβ hγ hT
  obtain ⟨KB, hKB0, hKB⟩ := s99_Bq_bound hd hs0 hs ha hβ hγ hT hS
  obtain ⟨Kb, hKb0, hbias⟩ := s99_bias hd hs0 hs ha hβ hγ hT hS
  obtain ⟨KT, hKT0, hTL2⟩ := s99_T_L2 hd hs0 hs ha hβ hγ hT hS
  obtain ⟨Kclt, hKclt0, hclt⟩ := s99_clt hd hs0 hs ha hβ hγ (J1_gt d) hφ hG
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  set Sb : ℝ := ∑' m, b m with hSb
  have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
  have hKw0 := s99_Kw_nonneg F hγ
  set KA' : ℝ := KB * K₂ + Kb + (KT + Kclt) * γ⁻¹ * K₂ * Sb with hKA'
  have hKA'0 : 0 ≤ KA' := by positivity
  refine ⟨KA' * Kw d γ F, mul_nonneg hKA'0 hKw0, fun N hN f hf p => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hk0 : 1 ≤ k0 d := k0_ge_one d
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  obtain ⟨j, k⟩ := p
  -- the observable
  set w := wF F j k with hwdef
  have hwcb := s99_wF_cb hd hγ hφ.1 F j k
  set cw := cbNorm (k0 d) w with hcwdef
  have hcw0 : 0 ≤ cw := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hcw : cw ≤ Kw d γ F * (b j * b k) := by
    refine hwcb.2.trans (le_of_eq ?_)
    unfold Kw; ring
  have hwbd : ∀ x, |w x| ≤ cw := fun x => by
    have := s99_norm_iter_le_cb hwcb.1 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hwc1 : ContDiff ℝ 1 w := hwcb.1.1.of_le (by exact_mod_cast hk0)
  have hwm : Measurable w := hwc1.continuous.measurable
  have hDw : ∀ x, ‖fderiv ℝ w x‖ ≤ cw := fun x => s45_cb_deriv_le hk0 hwcb.1 x
  have hwL2 : MemLp w 2 (thermalMeasure d s a β) :=
    MemLp.of_bound hwm.aestronglyMeasurable cw (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hwbd x)
  obtain ⟨χw, hχw2, hwf, hgenw⟩ := h2 w hwcb.1
  -- the test function
  set ψ := pd (pd f j) k with hψdef
  have hψ : Bd 3 ψ := (hf.pd j).pd k
  have hJ0 : IsSummableFeatureFamily (k0 d) φ := by
    refine ⟨fun l => (HRS.MS.Tc5.tc5_cb_mono (J1_ge_k0 d |>.trans' (by omega)) (hφ.1 l)).1, ?_⟩
    refine Summable.of_nonneg_of_le (fun l => HRS.MS.Tc5.tc5_cb_nonneg _ _) (fun l => ?_) hφ.2
    exact (HRS.MS.Tc5.tc5_cb_mono (by have := J1_ge_k0 d; omega) (hφ.1 l)).2
  have hWc : Continuous (fun X : EucConfig d N => featureVec φ ν X) :=
    (s99_W_contDiff hN1 (by unfold J1; omega) hφ).continuous
  have hψW_bd : ∀ X : EucConfig d N, |ψ (featureVec φ ν X)| ≤ 1 := fun X => hψ.abs_le _
  have hψW_meas : Measurable fun X : EucConfig d N => ψ (featureVec φ ν X) :=
    (hψ.1.continuous.comp hWc).measurable
  have hψW_int : Integrable (fun X : EucConfig d N => ψ (featureVec φ ν X)) P :=
    Integrable.of_bound hψW_meas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hψW_bd X)
  -- Step 1: the algebra
  set Y : EucConfig d N → ℝ := fun X => s45_Yi N w (pair ν w) X with hYdef
  set β0 : ℝ := Real.sqrt N * (pair ν w - pair (thermalMeasure d s a β) w) with hβ0
  have hCf : Cf d s a β γ φ j k = pair (thermalMeasure d s a β) w :=
    s99_cov_eq_w hd hs0 hsd hγ hT hφ F j k
  have hYm : Measurable Y :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hwm).sub measurable_const)
  have hYbd : ∀ X : EucConfig d N, |Y X| ≤ 2 * Real.sqrt N * cw := by
    intro X
    simp only [hYdef, s45_Yi]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := s45_abs_pair_empirical_le hN1 hwbd X
    have h2 : |pair ν w| ≤ cw := HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hwbd x)
    calc Real.sqrt N * |pair (empirical X) w - pair ν w|
        ≤ Real.sqrt N * (|pair (empirical X) w| + |pair ν w|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (cw + cw) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N * cw := by ring
  have hYψ_int : Integrable (fun X : EucConfig d N => Y X * ψ (featureVec φ ν X)) P :=
    Integrable.of_bound (hYm.mul hψW_meas).aestronglyMeasurable (2 * Real.sqrt N * cw)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |Y X| * |ψ (featureVec φ ν X)| ≤ (2 * Real.sqrt N * cw) * 1 :=
              mul_le_mul (hYbd X) (hψW_bd X) (abs_nonneg _) (by positivity)
          _ = _ := mul_one _)
  have hA1 : Aterm d s a β γ F N f (j, k) =
      -(∫ X, Y X * ψ (featureVec φ ν X) ∂P) - β0 * ∫ X, ψ (featureVec φ ν X) ∂P := by
    unfold Aterm
    simp only
    rw [← integral_const_mul, ← integral_const_mul, ← integral_neg, ← integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only [hYdef, hβ0, s45_Yi, hCf]
      ring
    · exact hYψ_int.neg
    · exact hψW_int.const_mul _
  -- Step 2: the plain Stein identity for `w`
  have hE := s99_E1_plain hd hs0 hsd ha hβ hγ hT hN (hS N hN) (J := k0 d) hk0 hJ0 hwcb.1 hwf
    (ψ := ψ) (hψ.of_le (by norm_num))
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
  have hcc : ∀ m, cc d s a β γ F (j, k) m = ∫ x, w2 m x ∂(thermalMeasure d s a β) := by
    intro m
    have h1 := s99_cov_ibp hd hs0 hsd hγ hT (w := w) (ψ := φ m) (χ := F.χ m)
      (af := aRep d s a β γ (φ m)) hwc1 hwbd hDw (HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 m))
      (F.feat hT hγ m) (F.gen m)
    have h2 := s99_cov_corr hd hs0 hsd hγ hT hwL2 hwf (hφm1 m) (hBφ m) (hDφ m)
    have h3 : cc d s a β γ F (j, k) m =
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
      cc d s a β γ F (j, k) m * ∫ z, pd ψ m z ∂G| ≤ (KT + Kclt) * Cm m / Real.sqrt N := by
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
  have hccGm_bd : ∀ m, ‖cc d s a β γ F (j, k) m * Gm m‖ ≤ Cm m := fun m => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hcc m]
    calc |∫ x, w2 m x ∂(thermalMeasure d s a β)| * |Gm m| ≤ Cm m * 1 :=
          mul_le_mul (hcm_bd m) (hGm_bd m) (abs_nonneg _) (hCm0 m)
      _ = _ := mul_one _
  have hsumT : Summable Tm := Summable.of_norm_bounded hCmS hTm_bd
  have hsumG : Summable fun m => cc d s a β γ F (j, k) m * Gm m :=
    Summable.of_norm_bounded hCmS hccGm_bd
  have hE' : ∫ X, Y X * ψ (featureVec φ ν X) ∂P = R + ∑' m, Tm m := hE
  have hAlim : Alim d s a β γ F G f (j, k) = -∑' m, cc d s a β γ F (j, k) m * Gm m := rfl
  have hdecomp : Aterm d s a β γ F N f (j, k) - Alim d s a β γ F G f (j, k) =
      -R - β0 * ∫ X, ψ (featureVec φ ν X) ∂P - ∑' m, (Tm m - cc d s a β γ F (j, k) m * Gm m) := by
    rw [hA1, hAlim, hE', hsumT.tsum_sub hsumG]
    ring
  -- the three bounds
  have hβ0b : |β0| ≤ Kb * cw / Real.sqrt N := by
    have hb := hbias N hN cw hcw0 w hwm hwbd
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    simp only [hβ0]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt N * |pair ν w - pair (thermalMeasure d s a β) w|
        ≤ Real.sqrt N * (Kb * cw / N) := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
      _ = Kb * cw / Real.sqrt N := by
          rw [eq_div_iff hsqN.ne']
          calc Real.sqrt N * (Kb * cw / N) * Real.sqrt N =
              (Real.sqrt N * Real.sqrt N) * (Kb * cw) / N := by ring
            _ = Kb * cw := by rw [hsq]; field_simp
  have hψint : |∫ X, ψ (featureVec φ ν X) ∂P| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun X : EucConfig d N => ψ (featureVec φ ν X))
      (C := 1) (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hψW_bd X)
    simpa [Real.norm_eq_abs] using this
  have hser : |∑' m, (Tm m - cc d s a β γ F (j, k) m * Gm m)| ≤
      (KT + Kclt) / Real.sqrt N * (γ⁻¹ * (K₂ * cw) * Sb) := by
    have hg : HasSum (fun m => (KT + Kclt) / Real.sqrt N * Cm m)
        ((KT + Kclt) / Real.sqrt N * ∑' m, Cm m) := hCmS.hasSum.mul_left _
    have hCsum : ∑' m, Cm m = γ⁻¹ * (K₂ * cw) * Sb := by
      simp only [hCm]; rw [tsum_mul_left]
    rw [hCsum] at hg
    have := tsum_of_norm_bounded hg (f := fun m => Tm m - cc d s a β γ F (j, k) m * Gm m) (fun m => by
      rw [Real.norm_eq_abs]
      refine (hdiff m).trans (le_of_eq ?_)
      ring)
    rwa [Real.norm_eq_abs] at this
  rw [hdecomp]
  have htot : |-R - β0 * ∫ X, ψ (featureVec φ ν X) ∂P - ∑' m, (Tm m - cc d s a β γ F (j, k) m * Gm m)| ≤
      |R| + |β0| * 1 + (KT + Kclt) / Real.sqrt N * (γ⁻¹ * (K₂ * cw) * Sb) := by
    calc _ ≤ |-R - β0 * ∫ X, ψ (featureVec φ ν X) ∂P| +
          |∑' m, (Tm m - cc d s a β γ F (j, k) m * Gm m)| := abs_sub _ _
      _ ≤ (|R| + |β0| * 1) + (KT + Kclt) / Real.sqrt N * (γ⁻¹ * (K₂ * cw) * Sb) := by
          refine add_le_add ?_ hser
          calc |-R - β0 * ∫ X, ψ (featureVec φ ν X) ∂P| ≤ |-R| + |β0 * ∫ X, ψ (featureVec φ ν X) ∂P| :=
                abs_sub _ _
            _ ≤ |R| + |β0| * 1 := by
                rw [abs_neg, abs_mul]
                exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hψint (abs_nonneg _))
      _ = _ := by ring
  refine htot.trans ?_
  have hsum_eq : KA' * cw / Real.sqrt N = KB * (K₂ * cw) / Real.sqrt N + Kb * cw / Real.sqrt N +
      (KT + Kclt) / Real.sqrt N * (γ⁻¹ * (K₂ * cw) * Sb) := by
    simp only [hKA']; ring
  have hmain : |R| + |β0| * 1 + (KT + Kclt) / Real.sqrt N * (γ⁻¹ * (K₂ * cw) * Sb) ≤
      KA' * cw / Real.sqrt N := by
    rw [hsum_eq]
    have := hR; have := hβ0b
    linarith
  refine hmain.trans ?_
  calc KA' * cw / Real.sqrt N ≤ KA' * (Kw d γ F * (b j * b k)) / Real.sqrt N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcw hKA'0) hsqN.le
    _ = KA' * Kw d γ F * (cbNorm (J1 d) (φ (j, k).1) * cbNorm (J1 d) (φ (j, k).2)) / Real.sqrt N := by
        simp only [hbdef]; ring

end A

end S99

end
