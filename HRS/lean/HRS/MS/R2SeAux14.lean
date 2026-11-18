import HRS.MS.R2SeAux13

/-!
# S9.9 `r2_static_edgeworth`, packet 14: the exact expansion (D1)

Worker S99, namespace `S99`.  `s99_D1`: for `f` in the Stein class solving the Stein equation of `Φ` for the Gaussian `G` (coordinate
covariances `C_{jk} = Cov(φ_j, φ_k)`),

`E Φ(W_N) - E Φ(G) = ∑'_{(j,k)} E[(C_{jk} - μ_N(w_{jk})) ∂_k∂_j f(W_N)] + ∑'_j E[(Bq_j/√N) ∂_j f(W_N)]`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The covariance `C_{jk} = Cov(φ_j, φ_k)`. -/
abbrev Cf (d : ℕ) (s a β γ : ℝ) (φ : ℕ → Euc d → ℝ) (j k : ℕ) : ℝ :=
  susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ (φ j) (φ k)

/-- Measurable/continuous facts for the Stein class. -/
theorem s99_pd_cont {f : SeqL2 → ℝ} (hf : SteinCl f) (j : ℕ) : Continuous (pd f j) :=
  (hf.pd j).1.continuous

theorem s99_pdpd_cont {f : SeqL2 → ℝ} (hf : SteinCl f) (j k : ℕ) : Continuous (pd (pd f j) k) :=
  ((hf.pd j).pd k).1.continuous

section D1

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_C_summable : Summable fun p : ℕ × ℕ => ‖Cf d s a β γ φ p.1 p.2‖ := by
  have hs1 : Summable fun j => cbNorm (J1 d) (φ j) := hφ.2
  have hnn : (0 : ℕ → ℝ) ≤ fun j => cbNorm (J1 d) (φ j) := fun j =>
    HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hb : Summable fun p : ℕ × ℕ => cbNorm (J1 d) (φ p.1) * cbNorm (J1 d) (φ p.2) :=
    Summable.mul_of_nonneg (f := fun j => cbNorm (J1 d) (φ j)) (g := fun j => cbNorm (J1 d) (φ j))
      hs1 hs1 hnn hnn
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) (hb.mul_left (Kw d γ F))
  rw [Real.norm_eq_abs]
  refine (s99_cov_bound hd hs0 hs ha hβ hγ hT hS hφ F p.1 p.2).trans (le_of_eq ?_)
  unfold Kw
  ring

theorem s99_D1_pointwise {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) {Φ f : SeqL2 → ℝ} (hf : SteinCl f)
    (hst : ∀ x, ∫ z, iteratedFDeriv ℝ 2 f x ![z, z] ∂G - fderiv ℝ f x x =
      Φ x - ∫ z, Φ z ∂G) (z : SeqL2) :
    Φ z - ∫ z', Φ z' ∂G = (∑' p : ℕ × ℕ, Cf d s a β γ φ p.1 p.2 * pd (pd f p.1) p.2 z) -
      ∑' j, SeqL2.coord z j * pd f j z := by
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (by norm_num)
  have hCs := s99_C_summable hd hs0 hs ha hβ hγ hT hS hφ F
  have h := hst z
  rw [s99_contraction hG hCs hf2 z, s99_euler] at h
  have hsm : Summable fun p : ℕ × ℕ => Cf d s a β γ φ p.1 p.2 * pd (pd f p.1) p.2 z := by
    refine Summable.of_norm_bounded hCs fun p => ?_
    rw [norm_mul]
    have h1 : |pd (pd f p.1) p.2 z| ≤ 1 := ((hf.pd p.1).pd p.2).abs_le z
    calc ‖Cf d s a β γ φ p.1 p.2‖ * ‖pd (pd f p.1) p.2 z‖ ≤ ‖Cf d s a β γ φ p.1 p.2‖ * 1 :=
          mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact h1) (norm_nonneg _)
      _ = ‖Cf d s a β γ φ p.1 p.2‖ := mul_one _
  have e : ∑' j, ∑' k, Cf d s a β γ φ j k * fderiv ℝ (fderiv ℝ f) z (s45_e1 k (1 : ℝ)) (s45_e1 j (1 : ℝ)) =
      ∑' p : ℕ × ℕ, Cf d s a β γ φ p.1 p.2 * pd (pd f p.1) p.2 z := by
    rw [hsm.tsum_prod]
    refine tsum_congr fun j => tsum_congr fun k => ?_
    rw [s99_pd_pd hf2]
  rw [e] at h
  exact h.symm

theorem s99_D1_integrated {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) {Φ f : SeqL2 → ℝ} (hΦc : Continuous Φ)
    {CΦ : ℝ} (hΦb : ∀ z, |Φ z| ≤ CΦ) (hf : SteinCl f)
    (hst : ∀ x, ∫ z, iteratedFDeriv ℝ 2 f x ![z, z] ∂G - fderiv ℝ f x x =
      Φ x - ∫ z, Φ z ∂G) {N : ℕ} (hN : 2 ≤ N) :
    ∫ X, Φ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) - ∫ z, Φ z ∂G =
      (∑' p : ℕ × ℕ, ∫ X, Cf d s a β γ φ p.1 p.2 *
          pd (pd f p.1) p.2 (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)) -
        ∑' j, ∫ X, SeqL2.coord (featureVec φ (S46.s46_nu d s a β γ N) X) j *
          pd f j (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) := by
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  haveI hν : IsProbabilityMeasure ν := s99_nu_prob hN1
  have hJ : 1 ≤ J1 d := by unfold J1; omega
  set W : EucConfig d N → SeqL2 := fun X => featureVec φ ν X with hWdef
  have hWc : Continuous W := (s99_W_contDiff hN1 hJ hφ).continuous
  have hCs := s99_C_summable hd hs0 hs ha hβ hγ hT hS hφ F
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  set g : ℕ × ℕ → SeqL2 → ℝ := fun p z => pd (pd f p.1) p.2 z with hgdef
  have hg_cont : ∀ p, Continuous (g p) := fun p => s99_pdpd_cont hf p.1 p.2
  have hg_bd : ∀ p z, |g p z| ≤ 1 := fun p z => ((hf.pd p.1).pd p.2).abs_le z
  have hpd_bd : ∀ j z, |pd f j z| ≤ 1 := fun j z => (hf.pd j).abs_le z
  set Fi : (ℕ × ℕ) ⊕ ℕ → EucConfig d N → ℝ := Sum.elim
    (fun p X => Cf d s a β γ φ p.1 p.2 * g p (W X))
    (fun j X => -(SeqL2.coord (W X) j * pd f j (W X))) with hFi
  set Mi : (ℕ × ℕ) ⊕ ℕ → ℝ := Sum.elim (fun p => ‖Cf d s a β γ φ p.1 p.2‖)
    (fun j => 2 * Real.sqrt N * b j) with hMi
  have hM1 : Summable (Mi ∘ Sum.inl) := hCs
  have hM2 : Summable (Mi ∘ Sum.inr) := hbs.mul_left _
  have hMs : Summable Mi := Summable.sum Mi hM1 hM2
  have hmeas : ∀ i, AEStronglyMeasurable (Fi i) P := by
    intro i
    rcases i with p | j
    · exact (continuous_const.mul ((hg_cont p).comp hWc)).aestronglyMeasurable
    · exact (((S45.s45_coord_continuous j).comp hWc).mul ((s99_pd_cont hf j).comp hWc)).neg.aestronglyMeasurable
  have hbd : ∀ i X, |Fi i X| ≤ Mi i := by
    intro i X
    rcases i with p | j
    · simp only [hFi, hMi, Sum.elim_inl]
      rw [abs_mul, ← Real.norm_eq_abs (Cf d s a β γ φ p.1 p.2)]
      calc ‖Cf d s a β γ φ p.1 p.2‖ * |g p (W X)| ≤ ‖Cf d s a β γ φ p.1 p.2‖ * 1 :=
            mul_le_mul_of_nonneg_left (hg_bd p _) (norm_nonneg _)
        _ = _ := mul_one _
    · simp only [hFi, hMi, Sum.elim_inr, abs_neg]
      rw [abs_mul]
      calc |SeqL2.coord (W X) j| * |pd f j (W X)| ≤ (2 * Real.sqrt N * b j) * 1 :=
            mul_le_mul (s99_Wc_bound hN1 hφ j X) (hpd_bd j _) (abs_nonneg _) (by
              have := hb0 j; positivity)
        _ = _ := mul_one _
  have h1 := s99_integral_tsum hMs hmeas hbd
  -- pointwise identification of the series
  have hpt : ∀ X : EucConfig d N, ∑' i, Fi i X = Φ (W X) - ∫ z, Φ z ∂G := by
    intro X
    have hs1 : Summable fun p : ℕ × ℕ => Fi (Sum.inl p) X :=
      Summable.of_norm_bounded hCs fun p => by
        simp only [hFi, Sum.elim_inl, norm_mul]
        calc ‖Cf d s a β γ φ p.1 p.2‖ * ‖g p (W X)‖ ≤ ‖Cf d s a β γ φ p.1 p.2‖ * 1 :=
              mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hg_bd p _) (norm_nonneg _)
          _ = _ := mul_one _
    have hs2 : Summable fun j : ℕ => Fi (Sum.inr j) X :=
      Summable.of_norm_bounded (hbs.mul_left (2 * Real.sqrt N)) fun j => by
        simp only [hFi, Sum.elim_inr, norm_neg, norm_mul]
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        calc |SeqL2.coord (W X) j| * |pd f j (W X)| ≤ (2 * Real.sqrt N * b j) * 1 :=
              mul_le_mul (s99_Wc_bound hN1 hφ j X) (hpd_bd j _) (abs_nonneg _) (by
                have := hb0 j; positivity)
          _ = _ := by rw [mul_one]
    rw [Summable.tsum_sum (f := fun i => Fi i X) hs1 hs2]
    have := s99_D1_pointwise hd hs0 hs ha hβ hγ hT hS hφ F hG hf hst (W X)
    rw [this]
    simp only [hFi, Sum.elim_inl, Sum.elim_inr, tsum_neg]
    ring
  have hint_pt : ∫ X, ∑' i, Fi i X ∂P = ∫ X, Φ (featureVec φ ν X) ∂P - ∫ z, Φ z ∂G := by
    simp_rw [hpt]
    have hΦW : Integrable (fun X : EucConfig d N => Φ (W X)) P :=
      Integrable.of_bound (hΦc.comp hWc).aestronglyMeasurable CΦ
        (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hΦb _)
    rw [integral_sub hΦW (integrable_const _), integral_const]
    simp
    rfl
  rw [← hint_pt, ← h1]
  have hI1 : Summable fun p : ℕ × ℕ => ∫ X, Fi (Sum.inl p) X ∂P := by
    refine Summable.of_norm_bounded hCs fun p => ?_
    have := norm_integral_le_of_norm_le_const (μ := P) (f := Fi (Sum.inl p))
      (C := ‖Cf d s a β γ φ p.1 p.2‖) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact (hbd (Sum.inl p) X))
    simpa using this
  have hI2 : Summable fun j : ℕ => ∫ X, Fi (Sum.inr j) X ∂P := by
    refine Summable.of_norm_bounded (hbs.mul_left (2 * Real.sqrt N)) fun j => ?_
    have := norm_integral_le_of_norm_le_const (μ := P) (f := Fi (Sum.inr j))
      (C := 2 * Real.sqrt N * b j) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact (hbd (Sum.inr j) X))
    simpa using this
  rw [Summable.tsum_sum (f := fun i => ∫ X, Fi i X ∂P) hI1 hI2]
  simp only [hFi, Sum.elim_inl, Sum.elim_inr]
  rw [tsum_congr fun j => integral_neg _, tsum_neg]
  ring

end D1

end S99

end
