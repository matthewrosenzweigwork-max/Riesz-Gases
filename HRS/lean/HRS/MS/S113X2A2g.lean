import HRS.MS.S113X2A2e

/-!
# S11.3 X2 part A2g: from the weak equation to the pointwise Fokker-Planck equation for a smooth density
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113a_integrable_of_compact {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ] {h : α → ℝ} {K : Set α} (hK : IsCompact K)
    (hc : ContinuousOn h K) (h0 : ∀ p, p ∉ K → h p = 0) : Integrable h μ := by
  have hon : IntegrableOn h K μ := hc.integrableOn_compact hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
  intro p hp
  by_contra h'
  exact hp (h0 p h')

/-- Integration by parts against a compactly supported smooth function with support inside `O`. -/
theorem s113a_ibp {O : Set (ℝ × EucConfig d N)} {G g : ℝ × EucConfig d N → ℝ} {v : ℝ × EucConfig d N}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (hgO : tsupport g ⊆ O)
    (hGd : ∀ p ∈ O, DifferentiableAt ℝ G p) (hGc : ContinuousOn G O)
    (hGc' : ContinuousOn (fun p => fderiv ℝ G p v) O) :
    ∫ p, G p * fderiv ℝ g p v = -∫ p, fderiv ℝ G p v * g p := by
  haveI : (volume : Measure (ℝ × EucConfig d N)).IsAddHaarMeasure := HRS.MC.CepP3.isAddHaar_volume_cov
  have hgc' : Continuous (fun p => fderiv ℝ g p v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hK := hgc.isCompact
  have hz : ∀ p, p ∉ tsupport g → g p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport hp
  have hz' : ∀ p, p ∉ tsupport g → fderiv ℝ g p = 0 := fun p hp =>
    Function.notMem_support.1 (fun h => hp (support_fderiv_subset ℝ h))
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ (fun x hx => hGd x (hgO hx))
    (fun x _ => hg.differentiable (by simp) x)
  · exact s113a_integrable_of_compact hK ((hGc'.mono hgO).mul hg.continuous.continuousOn)
      (fun p hp => by simp [hz p hp])
  · exact s113a_integrable_of_compact hK ((hGc.mono hgO).mul hgc'.continuousOn)
      (fun p hp => by simp [hz' p hp])
  · exact s113a_integrable_of_compact hK ((hGc.mono hgO).mul hg.continuous.continuousOn)
      (fun p hp => by simp [hz p hp])

theorem s113a_fderiv_clm_const {Φ : ℝ × EucConfig d N → ℝ} {p : ℝ × EucConfig d N}
    (hD : DifferentiableAt ℝ (fderiv ℝ Φ) p) (v w : ℝ × EucConfig d N) :
    fderiv ℝ (fun q => fderiv ℝ Φ q v) p w = fderiv ℝ (fderiv ℝ Φ) p w v := by
  rw [fderiv_clm_apply hD (differentiableAt_const v)]
  simp

/-- Integration by parts for a function that is `C¹` on `O`. -/
theorem s113a_ibp' {O : Set (ℝ × EucConfig d N)} (hO : IsOpen O) {G g : ℝ × EucConfig d N → ℝ}
    {v : ℝ × EucConfig d N} (hG : ContDiffOn ℝ 1 G O)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (hgO : tsupport g ⊆ O) :
    ∫ p, G p * fderiv ℝ g p v = -∫ p, fderiv ℝ G p v * g p := by
  refine s113a_ibp hg hgc hgO (fun p hp => (hG.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))
    hG.continuousOn ?_
  have h1 : ContinuousOn (fderiv ℝ G) O := hG.continuousOn_fderiv_of_isOpen hO le_rfl
  exact h1.clm_apply continuousOn_const

end HRS.MS.S113X2

end
