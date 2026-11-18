import HRS.MS.R2SeAux11

/-!
# S9.9 `r2_static_edgeworth`, packet 12: the exact expansion (D1)

Worker S99, namespace `S99`.  For `f` in the Stein class solving the Stein equation of `Φ` for the Gaussian `G`:

`E Φ(W_N) - E Φ(G) = ∑'_{(j,k)} E[(C_{jk} - μ_N(w_{jk})) ∂_k∂_j f(W_N)] + ∑'_j E[(Bq_j/√N) ∂_j f(W_N)]`

(`s99_D1`), from the pointwise Stein equation, `s99_contraction`, `s99_euler`, and the plain Stein identity `s99_E1_plain`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_pd_pd {f : SeqL2 → ℝ} (hf : ContDiff ℝ 2 f) (j k : ℕ) (z : SeqL2) :
    pd (pd f j) k z = fderiv ℝ (fderiv ℝ f) z (s45_e1 k (1 : ℝ)) (s45_e1 j (1 : ℝ)) := by
  have hd1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  unfold pd
  rw [fderiv_clm_apply (hd1 z) (differentiableAt_const _)]
  simp

/-- Integral of a series with a summable pointwise bound. -/
theorem s99_integral_tsum {ι : Type*} [Countable ι] {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {F : ι → α → ℝ} {M : ι → ℝ} (hM : Summable M)
    (hm : ∀ i, AEStronglyMeasurable (F i) μ) (hb : ∀ i x, |F i x| ≤ M i) :
    ∑' i, ∫ x, F i x ∂μ = ∫ x, ∑' i, F i x ∂μ := by
  have hint : ∀ i, Integrable (F i) μ := fun i =>
    Integrable.of_bound (hm i) (M i) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hb i x)
  refine integral_tsum_of_summable_integral_norm hint ?_
  refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _) (fun i => ?_) hM
  calc ∫ x, ‖F i x‖ ∂μ ≤ ∫ x, M i ∂μ :=
        integral_mono (hint i).norm (integrable_const _) (fun x => by
          rw [Real.norm_eq_abs]; exact hb i x)
    _ = M i := by simp

section D1

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

/-- Bound `|C_{jk}| ≤ K_w b_j b_k` for the covariance. -/
theorem s99_cov_bound (j k : ℕ) :
    |susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ (φ j) (φ k)| ≤
      ((k0 d : ℝ) + 1) * 2 ^ k0 d * (γ⁻¹ * F.K) * cbNorm (J1 d) (φ j) * cbNorm (J1 d) (φ k) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hmem : ∀ j, MemLp (φ j) 2 (thermalMeasure d s a β) := fun j =>
    HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 j)
  have hDφ : ∀ l x, ‖fderiv ℝ (φ l) x‖ ≤ cbNorm (J1 d) (φ l) := fun l x =>
    s45_cb_deriv_le (by unfold J1; omega) (hφ.1 l) x
  have hBφ : ∀ l x, |φ l x| ≤ cbNorm (J1 d) (φ l) := fun l x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 l) x
    rwa [Real.norm_eq_abs] at this
  rw [s99_cov_corr hd hs0 hsd hγ hT (hmem j) (F.feat hT hγ j) ((hφ.1 k).1.of_le (by
    exact_mod_cast (by unfold J1; omega : 1 ≤ J1 d))) (hBφ k) (hDφ k)]
  have hw := (s99_wF_cb hd hγ hφ.1 F j k)
  have hint : ∫ x, γ⁻¹ * ⟪gradient (F.χ j) x, gradient (φ k) x⟫ ∂(thermalMeasure d s a β) =
      ∫ x, wF F j k x ∂(thermalMeasure d s a β) := rfl
  rw [hint]
  have hsup : ∀ x, |wF F j k x| ≤ cbNorm (k0 d) (wF F j k) := fun x => by
    have := s99_norm_iter_le_cb hw.1 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have h1 : |∫ x, wF F j k x ∂(thermalMeasure d s a β)| ≤ cbNorm (k0 d) (wF F j k) := by
    have := norm_integral_le_of_norm_le_const (μ := thermalMeasure d s a β) (f := wF F j k)
      (C := cbNorm (k0 d) (wF F j k)) (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hsup x)
    simpa [Real.norm_eq_abs] using this
  refine h1.trans (hw.2.trans ?_)
  have : (0 : ℝ) ≤ cbNorm (J1 d) (φ k) := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have : (0 : ℝ) ≤ cbNorm (J1 d) (φ j) := HRS.MS.Tc5.tc5_cb_nonneg _ _
  nlinarith

end D1

end S99

end
