import HRS.MS.R2SeAux14

/-!
# S9.9 `r2_static_edgeworth`, packet 15: the exact expansion (D1), final form

Worker S99, namespace `S99`.  `s99_D1`: for `f` in the Stein class solving the Stein equation of `Φ` for the Gaussian `G`,

`E Φ(W_N) - E Φ(G) = ∑'_{(j,k)} E[(C_{jk} - μ_N(w_{jk})) ∂_k∂_j f(W_N)] + ∑'_j E[(Bq_j/√N) ∂_j f(W_N)]`,

obtained from `s99_D1_integrated` and the plain Stein identity `s99_E1_plain` for each coordinate.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section D1b

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

/-- The coordinate identity: `E[Y_j ∂_jf(W)] = -E[(Bq_j/√N) ∂_jf(W)] + ∑_k E[T_{jk} ∂_k∂_j f(W)]`. -/
theorem s99_coord_identity {f : SeqL2 → ℝ} (hf : SteinCl f) {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    ∫ X, SeqL2.coord (featureVec φ (S46.s46_nu d s a β γ N) X) j *
        pd f j (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) =
      -(∫ X, (Bq d s a β γ N (F.χ j) X / Real.sqrt N) *
          pd f j (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)) +
      ∑' k, ∫ X, pair (empirical X) (wF F j k) *
          pd (pd f j) k (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hN1 : 1 ≤ N := by omega
  have hJ : 1 ≤ J1 d := by unfold J1; omega
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
  have hcoord : ∀ X : EucConfig d N, SeqL2.coord (featureVec φ (S46.s46_nu d s a β γ N) X) j =
      s45_Yi N (φ j) (pair (S46.s46_nu d s a β γ N) (φ j)) X := fun X =>
    s45_coord_ofSeq (s45_feature_memℓp hN1 hφ X) j
  simp_rw [hcoord]
  have hE := s99_E1_plain hd hs0 hsd ha hβ hγ hT hN (hS N hN) hJ hφ (hφ.1 j) (F.feat hT hγ j)
    ((hf.pd j).of_le (by norm_num : 1 ≤ 4))
  rw [hE]
  have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
    exact_mod_cast (by unfold k0; omega : 2 ≤ k0 d + 1))
  have hsqrt : ∀ X : EucConfig d N, Real.sqrt N * s45_Rp (thermalMeasure d s a β)
      (S46.s46_nu d s a β γ N) (S46.s46_P d s a β γ N) (commutatorKernel d s (gradient (F.χ j))) X =
      -(Bq d s a β γ N (F.χ j) X) / Real.sqrt N := fun X =>
    s99_sqrt_Rp hd hs0 hsd hT hN (hS N hN) hχ2 (s99_chi_B2 F j) X
  have e1 : ∫ X, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) (S46.s46_nu d s a β γ N)
        (S46.s46_P d s a β γ N) (commutatorKernel d s (gradient (F.χ j))) X) *
        pd f j (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) =
      -(∫ X, (Bq d s a β γ N (F.χ j) X / Real.sqrt N) *
        pd f j (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only
    rw [hsqrt X]; ring
  rw [e1]
  congr 1
  refine tsum_congr fun k => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only
  rw [s99_pair_wF hN1 F j k X]

theorem s99_D1 {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) {Φ f : SeqL2 → ℝ} (hΦc : Continuous Φ)
    {CΦ : ℝ} (hΦb : ∀ z, |Φ z| ≤ CΦ) (hf : SteinCl f)
    (hst : ∀ x, ∫ z, iteratedFDeriv ℝ 2 f x ![z, z] ∂G - fderiv ℝ f x x =
      Φ x - ∫ z, Φ z ∂G) {N : ℕ} (hN : 2 ≤ N) :
    ∫ X, Φ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) - ∫ z, Φ z ∂G =
      (∑' p : ℕ × ℕ, ∫ X, (Cf d s a β γ φ p.1 p.2 - pair (empirical X) (wF F p.1 p.2)) *
          pd (pd f p.1) p.2 (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)) +
        ∑' j, ∫ X, (Bq d s a β γ N (F.χ j) X / Real.sqrt N) *
          pd f j (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hJ : 1 ≤ J1 d := by unfold J1; omega
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  have hWc : Continuous (fun X : EucConfig d N => featureVec φ ν X) :=
    (s99_W_contDiff hN1 hJ hφ).continuous
  have hI := s99_D1_integrated hd hs0 hs ha hβ hγ hT hS hφ F hG hΦc hΦb hf hst hN
  have hCs := s99_C_summable hd hs0 hs ha hβ hγ hT hS hφ F
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hs1 : Summable b := hφ.2
  have hnn : (0 : ℕ → ℝ) ≤ b := hb0
  have hbb : Summable fun p : ℕ × ℕ => b p.1 * b p.2 :=
    Summable.mul_of_nonneg (f := b) (g := b) hs1 hs1 hnn hnn
  set g : ℕ × ℕ → SeqL2 → ℝ := fun p z => pd (pd f p.1) p.2 z with hgdef
  have hg_cont : ∀ p : ℕ × ℕ, Continuous (g p) := fun p => s99_pdpd_cont hf p.1 p.2
  have hg_bd : ∀ (p : ℕ × ℕ) z, |g p z| ≤ 1 := fun p z => ((hf.pd p.1).pd p.2).abs_le z
  have hpd_bd : ∀ j z, |pd f j z| ≤ 1 := fun j z => (hf.pd j).abs_le z
  set Tint : ℕ × ℕ → ℝ := fun p => ∫ X, pair (empirical X) (wF F p.1 p.2) * g p (featureVec φ ν X) ∂P
    with hTint
  have hTm : ∀ p : ℕ × ℕ, Measurable fun X : EucConfig d N => pair (empirical X) (wF F p.1 p.2) := by
    intro p
    refine s45_measurable_pair_empirical hN1 ?_
    have := (s99_wF_cb hd hγ hφ.1 F p.1 p.2).1.1
    exact (this.continuous).measurable
  have hTg_int : ∀ p : ℕ × ℕ, Integrable (fun X : EucConfig d N =>
      pair (empirical X) (wF F p.1 p.2) * g p (featureVec φ ν X)) P := by
    intro p
    refine Integrable.of_bound ((hTm p).mul ((hg_cont p).comp hWc).measurable).aestronglyMeasurable
      (Kw d γ F * (b p.1 * b p.2)) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |pair (empirical X) (wF F p.1 p.2)| * |g p (featureVec φ ν X)|
        ≤ (Kw d γ F * (b p.1 * b p.2)) * 1 :=
          mul_le_mul (s99_T_bound hd hγ hφ F hN1 p.1 p.2 X) (hg_bd p _) (abs_nonneg _) (by
            have := s99_Kw_nonneg F hγ; have := hb0 p.1; have := hb0 p.2; positivity)
      _ = _ := mul_one _
  have hTsum : Summable Tint := by
    refine Summable.of_norm_bounded (hbb.mul_left (Kw d γ F)) fun p => ?_
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X : EucConfig d N => pair (empirical X) (wF F p.1 p.2) * g p (featureVec φ ν X))
      (C := Kw d γ F * (b p.1 * b p.2)) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |pair (empirical X) (wF F p.1 p.2)| * |g p (featureVec φ ν X)|
            ≤ (Kw d γ F * (b p.1 * b p.2)) * 1 :=
              mul_le_mul (s99_T_bound hd hγ hφ F hN1 p.1 p.2 X) (hg_bd p _) (abs_nonneg _) (by
                have := s99_Kw_nonneg F hγ; have := hb0 p.1; have := hb0 p.2; positivity)
          _ = _ := mul_one _)
    simpa [hTint] using this
  -- the `Bq` terms
  obtain ⟨KB, hKB0, hKB⟩ := s99_Bq_bound hd hs0 hs ha hβ hγ hT hS
  set Aint : ℕ → ℝ := fun j => ∫ X, (Bq d s a β γ N (F.χ j) X / Real.sqrt N) *
    pd f j (featureVec φ ν X) ∂P with hAint
  have hχ2 : ∀ j, ContDiff ℝ 2 (F.χ j) := fun j => (F.smooth j).of_le (by
    exact_mod_cast (by unfold k0; omega : 2 ≤ k0 d + 1))
  have hAsum : Summable Aint := by
    refine Summable.of_norm_bounded (hs1.mul_left (KB * F.K / Real.sqrt N)) fun j => ?_
    obtain ⟨-, -, hBi, hB1⟩ := hKB N hN (hχ2 j) (s99_chi_B2 F j)
    have hBm : Measurable fun X : EucConfig d N => Bq d s a β γ N (F.χ j) X := by
      have hv1 : ContDiff ℝ 1 (gradient (F.χ j)) := s45_contDiff_gradient (hχ2 j)
      unfold Bq
      exact measurable_const.mul ((HRS.MS.Wr.wr9_measurable_pairEnergy
        (HRS.MS.Comm.comm_meas (s := s) (gradient (F.χ j)) hv1.continuous.measurable)).sub
        measurable_const)
    have hpm : Measurable fun X : EucConfig d N => pd f j (featureVec φ ν X) :=
      ((s99_pd_cont hf j).comp hWc).measurable
    have hpt : ∀ X : EucConfig d N, ‖(Bq d s a β γ N (F.χ j) X / Real.sqrt N) *
        pd f j (featureVec φ ν X)‖ ≤ |Bq d s a β γ N (F.χ j) X| / Real.sqrt N := fun X => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hsqN]
      calc |Bq d s a β γ N (F.χ j) X| / Real.sqrt N * |pd f j (featureVec φ ν X)|
          ≤ |Bq d s a β γ N (F.χ j) X| / Real.sqrt N * 1 :=
            mul_le_mul_of_nonneg_left (hpd_bd j _) (by positivity)
        _ = _ := mul_one _
    have hint : Integrable (fun X : EucConfig d N => |Bq d s a β γ N (F.χ j) X| / Real.sqrt N) P :=
      hBi.abs.div_const _
    have h1 := norm_integral_le_integral_norm (μ := P) (fun X : EucConfig d N =>
      (Bq d s a β γ N (F.χ j) X / Real.sqrt N) * pd f j (featureVec φ ν X))
    have h2 : ∫ X, ‖(Bq d s a β γ N (F.χ j) X / Real.sqrt N) * pd f j (featureVec φ ν X)‖ ∂P ≤
        ∫ X, |Bq d s a β γ N (F.χ j) X| / Real.sqrt N ∂P := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) hint
        (Filter.Eventually.of_forall hpt)
    have h3 : ∫ X, |Bq d s a β γ N (F.χ j) X| / Real.sqrt N ∂P ≤ KB * (F.K * b j) / Real.sqrt N := by
      rw [integral_div]
      exact div_le_div_of_nonneg_right hB1 hsqN.le
    calc ‖Aint j‖ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ KB * (F.K * b j) / Real.sqrt N := h3
      _ = KB * F.K / Real.sqrt N * b j := by ring
  -- assemble
  have hcoord : ∀ j, ∫ X, SeqL2.coord (featureVec φ ν X) j * pd f j (featureVec φ ν X) ∂P =
      -(Aint j) + ∑' k, Tint (j, k) := fun j =>
    s99_coord_identity hd hs0 hs ha hβ hγ hT hS hφ F hf hN j
  have hsplit : ∀ p : ℕ × ℕ, ∫ X, (Cf d s a β γ φ p.1 p.2 - pair (empirical X) (wF F p.1 p.2)) *
      g p (featureVec φ ν X) ∂P =
      (∫ X, Cf d s a β γ φ p.1 p.2 * g p (featureVec φ ν X) ∂P) - Tint p := by
    intro p
    have hCg : Integrable (fun X : EucConfig d N => Cf d s a β γ φ p.1 p.2 *
        g p (featureVec φ ν X)) P :=
      Integrable.of_bound (continuous_const.mul ((hg_cont p).comp hWc)).aestronglyMeasurable
        (‖Cf d s a β γ φ p.1 p.2‖) (Filter.Eventually.of_forall fun X => by
          rw [norm_mul]
          calc ‖Cf d s a β γ φ p.1 p.2‖ * ‖g p (featureVec φ ν X)‖
              ≤ ‖Cf d s a β γ φ p.1 p.2‖ * 1 :=
                mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hg_bd p _) (norm_nonneg _)
            _ = _ := mul_one _)
    rw [← integral_sub hCg (hTg_int p)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only; ring
  have hCsum : Summable fun p : ℕ × ℕ => ∫ X, Cf d s a β γ φ p.1 p.2 *
      g p (featureVec φ ν X) ∂P := by
    refine Summable.of_norm_bounded hCs fun p => ?_
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X : EucConfig d N => Cf d s a β γ φ p.1 p.2 * g p (featureVec φ ν X))
      (C := ‖Cf d s a β γ φ p.1 p.2‖) (Filter.Eventually.of_forall fun X => by
        rw [norm_mul]
        calc ‖Cf d s a β γ φ p.1 p.2‖ * ‖g p (featureVec φ ν X)‖
            ≤ ‖Cf d s a β γ φ p.1 p.2‖ * 1 :=
              mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hg_bd p _) (norm_nonneg _)
          _ = _ := mul_one _)
    simpa using this
  have hrowsum : Summable fun j : ℕ => ∑' k, Tint (j, k) := hTsum.prod
  have hS2 : ∑' j, ∫ X, SeqL2.coord (featureVec φ ν X) j * pd f j (featureVec φ ν X) ∂P =
      -(∑' j, Aint j) + ∑' p : ℕ × ℕ, Tint p := by
    simp_rw [hcoord]
    rw [hAsum.neg.tsum_add hrowsum, tsum_neg, hTsum.tsum_prod]
  have hS1 : ∑' p : ℕ × ℕ, ∫ X, (Cf d s a β γ φ p.1 p.2 - pair (empirical X) (wF F p.1 p.2)) *
      g p (featureVec φ ν X) ∂P =
      (∑' p : ℕ × ℕ, ∫ X, Cf d s a β γ φ p.1 p.2 * g p (featureVec φ ν X) ∂P) -
        ∑' p : ℕ × ℕ, Tint p := by
    simp_rw [hsplit]
    rw [hCsum.tsum_sub hTsum]
  rw [hI, hS2]
  show _ = (∑' p : ℕ × ℕ, ∫ X, (Cf d s a β γ φ p.1 p.2 - pair (empirical X) (wF F p.1 p.2)) *
      g p (featureVec φ ν X) ∂P) + ∑' j, Aint j
  rw [hS1]
  ring

end D1b

end S99

end
