import HRS.Whole.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# N3a, part B: mollification of `C²_c` functions

`mo n f = φ_n ⋆ f` with `φ_n` the normed bump of outer radius `1/(n+1)`.  For `f ∈ C¹_c`:
`mo n f` is smooth with compact support in the `1`-neighbourhood of `tsupport f`,
`D_a (mo n f) = mo n (D_a f)`, and `mo n f → f` uniformly if `f` is continuous with compact support.
-/

noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff Convolution

namespace HRS.MS.UniqN3a
open HRS

variable {d : ℕ}

/-- The bump of radii `1/(2(n+1))`, `1/(n+1)`. -/
def bumpN (d n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]; nlinarith⟩

theorem bumpN_rOut (d n : ℕ) : (bumpN d n).rOut = 1 / ((n : ℝ) + 1) := rfl

/-- The mollification `φ_n ⋆ f`. -/
def mo (n : ℕ) (f : Euc d → ℝ) : Euc d → ℝ :=
  ((bumpN d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)

theorem mo_contDiff (n : ℕ) {f : Euc d → ℝ} (hf : Continuous f) : ContDiff ℝ ∞ (mo n f) :=
  (bumpN d n).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (bumpN d n).contDiff_normed hf.locallyIntegrable

theorem mo_support (n : ℕ) {f : Euc d → ℝ} {R : ℝ} (hsupp : Function.support f ⊆ closedBall 0 R) :
    Function.support (mo n f) ⊆ closedBall 0 (R + 1) := by
  intro x hx
  have h := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (f := (bumpN d n).normed volume) (g := f) hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  rw [(bumpN d n).support_normed_eq] at ha
  have ha' : ‖a‖ < 1 / ((n : ℝ) + 1) := by
    rw [← bumpN_rOut]; simpa using ha
  have hb' : ‖b‖ ≤ R := by simpa using hsupp hb
  have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [mem_closedBall_zero_iff]
  exact (norm_add_le a b).trans (by linarith)

theorem mo_hasCompactSupport (n : ℕ) {f : Euc d → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (mo n f) :=
  (bumpN d n).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfc

/-- Derivative commutes with mollification. -/
theorem mo_fderiv (n : ℕ) {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (a : Euc d) (x : Euc d) :
    fderiv ℝ (mo n f) x a = mo n (fun z => fderiv ℝ f z a) x := by
  have hloc : LocallyIntegrable ((bumpN d n).normed volume) volume :=
    ((bumpN d n).continuous_normed).locallyIntegrable
  have h := hfc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hloc hf x
  unfold mo
  rw [h.fderiv]
  have hint : Integrable (fun t => ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Euc d))
      ((bumpN d n).normed volume t) (fderiv ℝ f (x - t))) volume := by
    have hc : Continuous (fun t => ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Euc d))
      ((bumpN d n).normed volume t) (fderiv ℝ f (x - t))) := by
      have h1 := (hf.continuous_fderiv one_ne_zero)
      exact ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Euc d)).continuous₂.comp
        ((bumpN d n).continuous_normed.prodMk (h1.comp (continuous_const.sub continuous_id)))
    refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (K := tsupport ((bumpN d n).normed volume))
      (bumpN d n).hasCompactSupport_normed (fun t ht => ?_)
    rw [image_eq_zero_of_notMem_tsupport ht]
    simp
  rw [convolution_def, convolution_def, ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp [ContinuousLinearMap.precompR]

/-- Uniform convergence of mollifications of a continuous compactly supported function. -/
theorem mo_unif {f : Euc d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, |mo n f x - f x| ≤ ε := by
  have hu := hfc.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.1 hu ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hn x => ?_⟩
  have hr : (bumpN d n).rOut ≤ δ := by
    rw [bumpN_rOut]
    refine le_trans ?_ hN.le
    gcongr
  have := (bumpN d n).dist_normed_convolution_le (μ := volume) (g := f) (x₀ := x) (ε := ε)
    hf.aestronglyMeasurable (fun z hz => (hδf (lt_of_lt_of_le (by simpa using hz) hr)).le)
  simpa [mo, Real.dist_eq] using this

end HRS.MS.UniqN3a
