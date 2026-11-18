import HRS.MS.R2SeAux23

/-!
# S9.9 `r2_static_edgeworth`, packet 24: the `l`-th term of the quadratic expansion

Worker S99, namespace `S99`.  `s99_Mab_l`: for corrected `u` (corrector `χ`) and bounded `C¹` `v`,
`E[T_{ul} Y_v ∂_lψ(W)] ≈ κ_{u,l} ∑_q κ_{v,q} E[∂_q∂_lψ(G)]` with error `K ‖∇χ‖ ‖v‖ b_l / √N`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section MabL

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_Mab_l {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ {u v : Euc d → ℝ}, MemCb (J1 d) u → MemCb (J1 d) v →
      ∀ {χ : Euc d → ℝ} {Bu : ℝ}, S46.S46Feat d s a β γ u χ Bu →
      (∀ x, thermalGen d s a β χ x = γ * aRep d s a β γ u x) →
      ∀ {ψ : SeqL2 → ℝ}, Bd 4 ψ → ∀ l : ℕ,
      |(∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
          (s45_Yi N v (pair (S46.s46_nu d s a β γ N) v) X *
            pd ψ l (featureVec φ (S46.s46_nu d s a β γ N) X)) ∂(S46.s46_P d s a β γ N)) -
        kap d s a β γ u φ l * ∑' q, kap d s a β γ v φ q * ∫ z, pd (pd ψ l) q z ∂G| ≤
      K * Bu * cbNorm (J1 d) v * cbNorm (J1 d) (φ l) / Real.sqrt N := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨KT, hKT0, hTL2⟩ := s99_T_L2 hd hs0 hs ha hβ hγ hT hS
  obtain ⟨KY, hKY0, hY2⟩ := s99_Y_L2 hd hs0 hs ha hβ hγ hT hS
  obtain ⟨KL, hKL0, hYlin⟩ := s99_Ylin hd hs0 hs ha hβ hγ hT hS hφ F hG
  refine ⟨γ⁻¹ * (KT * KY + KL), by positivity, fun N hN u v hu hv χ Bu hwf hgen ψ hψ l => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hk0 : 1 ≤ k0 d := k0_ge_one d
  have hJ1 : 1 ≤ J1 d := by unfold J1; omega
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  have hBu0 : 0 ≤ Bu := (norm_nonneg _).trans (hwf.B1 0)
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  -- the observables
  set cv := cbNorm (J1 d) v with hcvdef
  have hcv0 : 0 ≤ cv := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hvbd : ∀ x, |v x| ≤ cv := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le hv x
    rwa [Real.norm_eq_abs] at this
  have hvc1 : ContDiff ℝ 1 v := hv.1.of_le (by exact_mod_cast hJ1)
  have hvm : Measurable v := hvc1.continuous.measurable
  have hv0 : MemCb (k0 d) v := (HRS.MS.Tc5.tc5_cb_mono (J1_ge_k0 d |>.trans' (by omega)) hv).1
  have hcvk : cbNorm (k0 d) v ≤ cv := (HRS.MS.Tc5.tc5_cb_mono (J1_ge_k0 d |>.trans' (by omega)) hv).2
  have hcvk0 : 0 ≤ cbNorm (k0 d) v := HRS.MS.Tc5.tc5_cb_nonneg _ _
  set cu := cbNorm (J1 d) u with hcudef
  have hcu0 : 0 ≤ cu := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hubd : ∀ x, |u x| ≤ cu := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le hu x
    rwa [Real.norm_eq_abs] at this
  have huc1 : ContDiff ℝ 1 u := hu.1.of_le (by exact_mod_cast hJ1)
  have hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ cu := fun x => s45_cb_deriv_le hJ1 hu x
  -- the weight `w_{ul}`
  have hDφ : ∀ m x, ‖fderiv ℝ (φ m) x‖ ≤ b m := fun m x => s45_cb_deriv_le hJ1 (hφ.1 m) x
  have hBφ : ∀ m x, |φ m x| ≤ b m := fun m x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 m) x
    rwa [Real.norm_eq_abs] at this
  have hφm1 : ∀ m, ContDiff ℝ 1 (φ m) := fun m => (hφ.1 m).1.of_le (by exact_mod_cast hJ1)
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hwf.smooth
  set w2 : Euc d → ℝ := fun x => γ⁻¹ * ⟪gradient χ x, gradient (φ l) x⟫ with hw2
  set Cl : ℝ := γ⁻¹ * Bu * b l with hCl
  have hCl0 : 0 ≤ Cl := by have := hb0 l; positivity
  have hw2bd : ∀ x, |w2 x| ≤ Cl := by
    intro x
    simp only [hw2, hCl]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    exact (mul_le_mul_of_nonneg_left (s99_inner_grad_le hwf.B1 (hDφ l) x) (inv_nonneg.2 hγ.le)).trans_eq
      (by ring)
  have hw2c : Continuous w2 :=
    continuous_const.mul (hv1.continuous.inner (s45_gradient_continuous (hφm1 l)))
  have hw2m : Measurable w2 := hw2c.measurable
  have hκ : kap d s a β γ u φ l = ∫ x, w2 x ∂(thermalMeasure d s a β) := by
    have hw1 := s99_cov_ibp hd hs0 hsd hγ hT (w := u) (ψ := φ l) (χ := F.χ l)
      (af := aRep d s a β γ (φ l)) huc1 hubd hDu (HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 l))
      (F.feat hT hγ l) (F.gen l)
    have hu2 : MemLp u 2 (thermalMeasure d s a β) := s99_memLp_two_of_bdd huc1.continuous.measurable hubd
    have h2 := s99_cov_corr hd hs0 hsd hγ hT hu2 hwf (hφm1 l) (hBφ l) (hDφ l)
    have h3 : kap d s a β γ u φ l = ∫ x, u x * aRep d s a β γ (φ l) x ∂(thermalMeasure d s a β) := rfl
    rw [h3, ← hw1, h2]
  set κl := kap d s a β γ u φ l with hκl
  have hκb : |κl| ≤ Cl := by
    have := norm_integral_le_of_norm_le_const (μ := thermalMeasure d s a β) (f := w2) (C := Cl)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hw2bd x)
    rw [hκ]; simpa [Real.norm_eq_abs] using this
  have hpw : pair (thermalMeasure d s a β) w2 = κl := by rw [hκ]; rfl
  -- the integrand
  have hTe : ∀ X : EucConfig d N, γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫) =
      pair (empirical X) w2 := fun X => (s99_pair_smul hN1 γ⁻¹ _ X).symm
  simp_rw [hTe]
  have hTm : Measurable fun X : EucConfig d N => pair (empirical X) w2 :=
    s45_measurable_pair_empirical hN1 hw2m
  have hTbd : ∀ X : EucConfig d N, |pair (empirical X) w2| ≤ Cl := fun X =>
    s45_abs_pair_empirical_le hN1 hw2bd X
  set Yv : EucConfig d N → ℝ := fun X => s45_Yi N v (pair ν v) X with hYvdef
  have hYvm : Measurable Yv :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hvm).sub measurable_const)
  have hYvb : ∀ X, |Yv X| ≤ 2 * Real.sqrt N * cv := fun X => s99_Yi_bd hN1 hvbd X
  have hψl : Bd 3 (pd ψ l) := hψ.pd l
  have hWc : Continuous (fun X : EucConfig d N => featureVec φ ν X) :=
    (s99_W_contDiff hN1 hJ1 hφ).continuous
  have hψm : Measurable fun X : EucConfig d N => pd ψ l (featureVec φ ν X) :=
    (hψl.1.continuous.comp hWc).measurable
  have hψb : ∀ X : EucConfig d N, |pd ψ l (featureVec φ ν X)| ≤ 1 := fun X => hψl.abs_le _
  -- integrability
  have hI2 : Integrable (fun X : EucConfig d N => Yv X * pd ψ l (featureVec φ ν X)) P :=
    Integrable.of_bound (hYvm.mul hψm).aestronglyMeasurable (2 * Real.sqrt N * cv)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |Yv X| * |pd ψ l (featureVec φ ν X)| ≤ (2 * Real.sqrt N * cv) * 1 :=
              mul_le_mul (hYvb X) (hψb X) (abs_nonneg _) (by positivity)
          _ = _ := mul_one _)
  have hI1 : Integrable (fun X : EucConfig d N => (pair (empirical X) w2 - κl) *
      (Yv X * pd ψ l (featureVec φ ν X))) P :=
    Integrable.of_bound ((hTm.sub measurable_const).mul (hYvm.mul hψm)).aestronglyMeasurable
      ((Cl + |κl|) * (2 * Real.sqrt N * cv)) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact (abs_sub _ _).trans (add_le_add (hTbd X) le_rfl)
        · calc |Yv X| * |pd ψ l (featureVec φ ν X)| ≤ (2 * Real.sqrt N * cv) * 1 :=
                mul_le_mul (hYvb X) (hψb X) (abs_nonneg _) (by positivity)
            _ = _ := mul_one _)
  have hdec : (∫ X, pair (empirical X) w2 * (Yv X * pd ψ l (featureVec φ ν X)) ∂P) =
      (∫ X, (pair (empirical X) w2 - κl) * (Yv X * pd ψ l (featureVec φ ν X)) ∂P) +
        κl * ∫ X, Yv X * pd ψ l (featureVec φ ν X) ∂P := by
    rw [← integral_const_mul, ← integral_add hI1 (hI2.const_mul κl)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only; ring
  -- first term: Cauchy-Schwarz
  have hf2 : MemLp (fun X : EucConfig d N => pair (empirical X) w2 - κl) 2 P :=
    s99_memLp_two_of_bdd (C := Cl + |κl|) (hTm.sub measurable_const) (fun X =>
      (abs_sub _ _).trans (add_le_add (hTbd X) le_rfl))
  have hg2 : MemLp Yv 2 P := s99_memLp_two_of_bdd hYvm hYvb
  have hA : ∫ X, (pair (empirical X) w2 - κl) ^ 2 ∂P ≤ (KT * Cl / Real.sqrt N) ^ 2 := by
    have := hTL2 N hN Cl hCl0 w2 hw2m hw2bd
    rw [hpw] at this
    refine this.trans (le_of_eq ?_)
    rw [div_pow, Real.sq_sqrt hN0.le, mul_pow]
  have hB : ∫ X, (Yv X) ^ 2 ∂P ≤ (KY * cv) ^ 2 := (hY2 N hN cv hcv0 v hvm hvbd).2
  have e1 : |∫ X, (pair (empirical X) w2 - κl) * (Yv X * pd ψ l (featureVec φ ν X)) ∂P| ≤
      KT * Cl / Real.sqrt N * (KY * cv) := by
    have hA0 : 0 ≤ KT * Cl / Real.sqrt N := div_nonneg (mul_nonneg hKT0 hCl0) hsqN.le
    have hB0 : 0 ≤ KY * cv := mul_nonneg hKY0 hcv0
    have hcs := s99_cs_bd hf2 hg2 hA hB hA0 hB0
    refine le_trans ?_ hcs
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) ?_
      (Filter.Eventually.of_forall fun X => ?_)
    · have hfa : MemLp (fun X : EucConfig d N => |pair (empirical X) w2 - κl|) 2 P := hf2.abs
      have hga : MemLp (fun X : EucConfig d N => |Yv X|) 2 P := hg2.abs
      exact hfa.integrable_mul hga
    · beta_reduce
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |pair (empirical X) w2 - κl| * (|Yv X| * |pd ψ l (featureVec φ ν X)|)
          ≤ |pair (empirical X) w2 - κl| * (|Yv X| * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hψb X) (abs_nonneg _)) (abs_nonneg _)
        _ = |pair (empirical X) w2 - κl| * |Yv X| := by rw [mul_one]
  -- second term: the linear statistic
  have hYl := hYlin N hN hv0 hψl
  have e2 : |κl * ((∫ X, Yv X * pd ψ l (featureVec φ ν X) ∂P) -
      ∑' q, kap d s a β γ v φ q * ∫ z, pd (pd ψ l) q z ∂G)| ≤
      Cl * (KL * cbNorm (k0 d) v / Real.sqrt N) := by
    rw [abs_mul]
    exact mul_le_mul hκb hYl (abs_nonneg _) hCl0
  rw [hdec]
  have e3 : ((∫ X, (pair (empirical X) w2 - κl) * (Yv X * pd ψ l (featureVec φ ν X)) ∂P) +
      κl * ∫ X, Yv X * pd ψ l (featureVec φ ν X) ∂P) -
      κl * ∑' q, kap d s a β γ v φ q * ∫ z, pd (pd ψ l) q z ∂G =
      (∫ X, (pair (empirical X) w2 - κl) * (Yv X * pd ψ l (featureVec φ ν X)) ∂P) +
        κl * ((∫ X, Yv X * pd ψ l (featureVec φ ν X) ∂P) -
          ∑' q, kap d s a β γ v φ q * ∫ z, pd (pd ψ l) q z ∂G) := by ring
  rw [e3]
  refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
  have hKL' : KL * cbNorm (k0 d) v ≤ KL * cv := mul_le_mul_of_nonneg_left hcvk hKL0
  have hfin : KT * Cl / Real.sqrt N * (KY * cv) + Cl * (KL * cbNorm (k0 d) v / Real.sqrt N) ≤
      γ⁻¹ * (KT * KY + KL) * Bu * cv * b l / Real.sqrt N := by
    have : KT * Cl / Real.sqrt N * (KY * cv) + Cl * (KL * cbNorm (k0 d) v / Real.sqrt N) =
        (Cl * (KT * KY * cv + KL * cbNorm (k0 d) v)) / Real.sqrt N := by ring
    rw [this]
    refine div_le_div_of_nonneg_right ?_ hsqN.le
    have : Cl * (KT * KY * cv + KL * cbNorm (k0 d) v) ≤ Cl * ((KT * KY + KL) * cv) :=
      mul_le_mul_of_nonneg_left (by linarith [hKL']) hCl0
    refine this.trans (le_of_eq ?_)
    simp only [hCl]; ring
  exact hfin

end MabL

end S99

end
