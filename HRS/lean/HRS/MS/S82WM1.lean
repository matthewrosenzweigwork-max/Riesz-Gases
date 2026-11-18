import Mathlib
import HRS.MS.S82WJ1

/-!
# S8.2 A04 (S82W), part 8: mollification of a compactly supported `C²` function in `C²`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff Convolution

namespace HRS.MS.S82W

section mollify
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- the derivative of a mollification is the mollification of the derivative -/
lemma w_mol_hasFDerivAt (φ : ContDiffBump (0 : E)) {g : E → V} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (x : E) :
    HasFDerivAt (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g)
      ((φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] fderiv ℝ g) x) x := by
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
    (φ.continuous_normed (μ := μ)).locallyIntegrable (μ := μ) hg x
  convert h using 1
  simp only [convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ext v
  simp

lemma w_mol_fderiv (φ : ContDiffBump (0 : E)) {g : E → V} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    fderiv ℝ (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) =
      φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] fderiv ℝ g :=
  funext fun x => (w_mol_hasFDerivAt μ φ hg hc x).fderiv

omit [CompleteSpace V] in
lemma w_mol_contDiff (φ : ContDiffBump (0 : E)) {g : E → V} (hg : Continuous g) :
    ContDiff ℝ ∞ (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed (hg.locallyIntegrable (μ := μ))

lemma w_mol_close {g : E → V} (hg : Continuous g) (K : Set E) (hK : IsCompact K) (hz : ∀ x ∉ K, g x = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ φ : ContDiffBump (0 : E), φ.rOut ≤ η → ∀ x,
      ‖(φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x - g x‖ ≤ δ := by
  have hc : HasCompactSupport g := HasCompactSupport.intro hK hz
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuous_iff.1 (hc.uniformContinuous_of_continuous hg) δ hδ
  refine ⟨η, hη, fun φ hφ x => ?_⟩
  have := ContDiffBump.dist_normed_convolution_le (μ := μ) (φ := φ) (g := g) (x₀ := x) (ε := δ)
    hg.aestronglyMeasurable (fun y hy => (hu (by
      have : dist y x < φ.rOut := hy
      linarith)).le)
  simpa [dist_eq_norm] using this

include μ in
theorem w_density {D : Set E} (hD : IsOpen D) {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hfD : tsupport f ⊆ D) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ D ∧ tsupport f ⊆ K ∧ ∀ δ : ℝ, 0 < δ →
      ∃ h : E → ℝ, ContDiff ℝ ∞ h ∧ tsupport h ⊆ K ∧
      ∀ x, |h x - f x| ≤ δ ∧ ‖fderiv ℝ h x - fderiv ℝ f x‖ ≤ δ ∧
        ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ f) x‖ ≤ δ := by
  haveI : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  obtain ⟨ε0, hε0, hK⟩ := (show IsCompact (tsupport f) from hc).exists_cthickening_subset_open hD hfD
  have hKc : IsCompact (cthickening ε0 (tsupport f)) := (show IsCompact (tsupport f) from hc).cthickening
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := by
    have : ContDiff ℝ (1 + 1) f := by rwa [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]
    exact (contDiff_succ_iff_fderiv.1 this).2.2
  have hcd1 : HasCompactSupport (fderiv ℝ f) := hc.fderiv ℝ
  have hc0 : Continuous f := hf.continuous
  have hc1 : Continuous (fderiv ℝ f) := hdf.continuous
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ f)) := hdf.continuous_fderiv one_ne_zero
  have hKc0 : IsCompact (tsupport f) := hc
  have hz0 : ∀ x ∉ tsupport f, f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hz1 : ∀ x ∉ tsupport f, fderiv ℝ f x = 0 := by
    intro x hx
    have : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [this.fderiv_eq]; simp
  have hz2 : ∀ x ∉ tsupport f, fderiv ℝ (fderiv ℝ f) x = 0 := by
    intro x hx
    have : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have h1 : fderiv ℝ f =ᶠ[𝓝 x] fun _ => (0 : E →L[ℝ] ℝ) := by
      filter_upwards [this.eventuallyEq_nhds] with y hy
      rw [hy.fderiv_eq]; simp
    rw [h1.fderiv_eq]; simp
  refine ⟨cthickening ε0 (tsupport f), hKc, hK, self_subset_cthickening _, fun δ hδ => ?_⟩
  obtain ⟨η0, hη0, h0⟩ := w_mol_close μ (g := f) hc0 _ hKc0 hz0 hδ
  obtain ⟨η1, hη1, h1⟩ := w_mol_close μ (g := fderiv ℝ f) hc1 _ hKc0 hz1 hδ
  obtain ⟨η2, hη2, h2⟩ := w_mol_close μ (g := fderiv ℝ (fderiv ℝ f)) hc2 _ hKc0 hz2 hδ
  set r : ℝ := min (min η0 η1) (min η2 ε0) with hr
  have hr0 : 0 < r := lt_min (lt_min hη0 hη1) (lt_min hη2 hε0)
  obtain ⟨φ, hφ⟩ : ∃ φ : ContDiffBump (0 : E), φ.rOut = r := ⟨⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩, rfl⟩
  refine ⟨φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f, w_mol_contDiff μ φ hc0, ?_, ?_⟩
  · -- support
    have hs : Function.support (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) ⊆
        cthickening ε0 (tsupport f) := by
      intro x hx
      have := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx
      obtain ⟨a, ha, b, hb, rfl⟩ := this
      rw [φ.support_normed_eq] at ha
      refine mem_cthickening_of_dist_le (a + b) b ε0 (tsupport f) (subset_tsupport f hb) ?_
      have : ‖a‖ < r := by rw [mem_ball_zero_iff, hφ] at ha; exact ha
      rw [dist_eq_norm, add_sub_cancel_right]
      exact this.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    exact closure_minimal hs isClosed_cthickening
  · intro x
    have hle : φ.rOut ≤ η0 := by rw [hφ]; exact (min_le_left _ _).trans ((min_le_left _ _).trans le_rfl)
    have hle1 : φ.rOut ≤ η1 := by rw [hφ]; exact (min_le_left _ _).trans (min_le_right _ _)
    have hle2 : φ.rOut ≤ η2 := by rw [hφ]; exact (min_le_right _ _).trans (min_le_left _ _)
    refine ⟨?_, ?_, ?_⟩
    · have := h0 φ hle x
      simpa [Real.norm_eq_abs] using this
    · rw [w_mol_fderiv μ φ hf1 hc]
      exact h1 φ hle1 x
    · rw [w_mol_fderiv μ φ hf1 hc, w_mol_fderiv μ φ hdf hcd1]
      exact h2 φ hle2 x

end mollify

end HRS.MS.S82W
