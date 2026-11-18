import HRS.MP.SelfSimP5DsCalc

/-!
# P5 dissipation on `Fin N`: the hypotheses `P4PotHyp` and `P4FlowHyp` of the transported data
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSimP4 HRS.MP.SelfSimP5
  HRS.MP.SelfSimP5Core
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Ds

theorem p5d_grad_cont {N : ℕ} {U : EuclideanSpace ℝ (Fin N) → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) : Continuous (p5d_b U) := by
  unfold p5d_b
  exact (p5d_e N).continuous.comp (hK.continuous.comp (p5d_e N).symm.continuous).neg

theorem p5d_V_cont {N : ℕ} {U : EuclideanSpace ℝ (Fin N) → ℝ} (hU : ContDiff ℝ 2 U) :
    Continuous (p5d_V U) :=
  hU.continuous.comp (p5d_e N).symm.continuous

theorem p5d_potHyp {N : ℕ} {U : EuclideanSpace ℝ (Fin N) → ℝ} (hU : ContDiff ℝ 2 U) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * ‖z‖ ^ 2 - C ≤ U z)
    (T : ℝ) : P4PotHyp (fun _ => p5d_V U) (fun _ => p5d_b U) T where
  grad := by
    intro τ x
    have hd : HasFDerivAt U (fderiv ℝ U ((p5d_e N).symm x)) ((p5d_e N).symm x) :=
      (hU.differentiable (by norm_num) _).hasFDerivAt
    have h1 := hd.comp x (p5d_e N).symm.hasFDerivAt
    have key : -(p4InnerL (p5d_b U x)) =
        (fderiv ℝ U ((p5d_e N).symm x)).comp
          ((p5d_e N).symm : EucConfig 1 N →L[ℝ] EuclideanSpace ℝ (Fin N)) := by
      ext w
      obtain ⟨v, rfl⟩ := (p5d_e N).surjective w
      have hb : p5d_b U x = p5d_e N (-(gradient U ((p5d_e N).symm x))) := rfl
      rw [hb, ContinuousLinearMap.neg_apply, p5d_innerL_e, inner_neg_left, p5d_inner_gradient]
      simp
    rw [key]
    exact h1
  cont_b := (p5d_grad_cont hK).comp continuous_snd
  lip := by
    refine ⟨K * NNReal.sqrt N, fun τ _ => ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 : dist (p5d_b U x) (p5d_b U y) ≤
        dist (gradient U ((p5d_e N).symm x)) (gradient U ((p5d_e N).symm y)) := by
      rw [dist_eq_norm, dist_eq_norm, p5d_b, p5d_b, ← map_sub]
      refine (p5d_norm_e_le _).trans (le_of_eq ?_)
      rw [← norm_neg]
      congr 1
      abel
    have h2 : dist (gradient U ((p5d_e N).symm x)) (gradient U ((p5d_e N).symm y)) ≤
        K * dist ((p5d_e N).symm x) ((p5d_e N).symm y) := hK.dist_le_mul _ _
    have h3 : dist ((p5d_e N).symm x) ((p5d_e N).symm y) ≤ Real.sqrt N * dist x y := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      have := p5d_norm_le_sqrt ((p5d_e N).symm (x - y))
      simpa using this
    calc dist (p5d_b U x) (p5d_b U y) ≤ K * (Real.sqrt N * dist x y) :=
          h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 K.2))
      _ = ((K * NNReal.sqrt N : ℝ≥0) : ℝ) * dist x y := by
          push_cast
          ring
  cont_V := (p5d_V_cont hU).comp continuous_snd
  dtime := ⟨fun _ _ => 0, continuous_const, fun _ _ => hasDerivAt_const _ _,
    fun _ _ _ => le_refl _, 0, fun _ _ _ => by simp⟩
  conf := by
    obtain ⟨c, C, hc, h⟩ := hconf
    refine ⟨c, C, hc, fun τ _ x => ?_⟩
    have h1 := h ((p5d_e N).symm x)
    have h2 : ‖x‖ ≤ ‖(p5d_e N).symm x‖ := by
      simpa using p5d_norm_e_le ((p5d_e N).symm x)
    have h3 : c * ‖x‖ ^ 2 ≤ c * ‖(p5d_e N).symm x‖ ^ 2 := by
      gcongr
    simp only [p5d_V]
    linarith

/-- The transported flow. -/
def p5d_mu {N : ℕ} (μ : ℝ → Measure (EuclideanSpace ℝ (Fin N))) : ℝ → Measure (EucConfig 1 N) :=
  fun t => (μ (max t 0)).map (p5d_e N)

theorem p5d_mu_of_nonneg {N : ℕ} (μ : ℝ → Measure (EuclideanSpace ℝ (Fin N))) {t : ℝ} (ht : 0 ≤ t) :
    p5d_mu μ t = (μ t).map (p5d_e N) := by
  simp [p5d_mu, max_eq_left ht]

theorem p5d_flowHyp {N : ℕ} {U : EuclideanSpace ℝ (Fin N) → ℝ} (hU : ContDiff ℝ 2 U) {θ : ℝ}
    {μ : ℝ → Measure (EuclideanSpace ℝ (Fin N))}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (μ t)) {T : ℝ}
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂(μ t) ≤ M)
    (hnar : ∀ g : EuclideanSpace ℝ (Fin N) → ℝ, Continuous g → (∃ C : ℝ, ∀ z, |g z| ≤ C) →
      ContinuousOn (fun t => ∫ z, g z ∂(μ t)) (Icc (0 : ℝ) T))
    (hfp : ss5_WeakFP θ U μ) :
    P4FlowHyp θ (fun _ => p5d_b U) T (p5d_mu μ) where
  prob := fun t => by
    haveI := hprob (max t 0) (le_max_right _ _)
    unfold p5d_mu
    infer_instance
  mom := by
    obtain ⟨M, hM, hM'⟩ := hmom
    refine ⟨M, hM, fun t ht => ?_⟩
    rw [p5d_mu_of_nonneg μ ht.1, (p5d_measurableEmbedding N).lintegral_map]
    refine le_trans (lintegral_mono fun z => ?_) (hM' t ht)
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (p5d_norm_e_le z) 2)
  narrow := by
    intro g hg ⟨C, hC⟩
    have h1 := hnar (fun z => g (p5d_e N z)) (hg.comp (p5d_e N).continuous) ⟨C, fun z => hC _⟩
    refine h1.congr fun t ht => ?_
    rw [p5d_mu_of_nonneg μ ht.1, (p5d_measurableEmbedding N).integral_map]
  fp := by
    intro h hh t ht
    have hfp' := hfp _ (p5d_test hh) t ht.1
    have e1 : ∀ s, 0 ≤ s → ∫ x, h x ∂(p5d_mu μ s) = ∫ z, h (p5d_e N z) ∂(μ s) := fun s hs => by
      rw [p5d_mu_of_nonneg μ hs, (p5d_measurableEmbedding N).integral_map]
    rw [e1 t ht.1, e1 0 le_rfl, hfp']
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [p5d_mu_of_nonneg μ hr.1, (p5d_measurableEmbedding N).integral_map]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact (p5d_gen hh.smooth r z).symm

end HRS.MP.SelfSimP5Ds
