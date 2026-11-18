import HRS.MS.S82P2Cent6

/-!
# S8.2 (S82P2): the gradient of the corrector has zero `mu`-mean in every row
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

theorem s82p2_gt_centered {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) {rho : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x : Euc d) :
    ∫ z, s82p2_gt Q x z ∂HRS.Whole.withDensityReal rho = 0 := by
  set mu := HRS.Whole.withDensityReal rho with hmu
  haveI : IsProbabilityMeasure mu := HRS.Whole.Q09A.measure_isProb hρ
  obtain ⟨K0, hK00, hrow⟩ := s82p2_gt_row hd M hM G c hG hc rho hρ hρG
  obtain ⟨hg2, -⟩ := hrow a beta A hA f Q hQ x
  have hgm : Measurable (s82p2_gt Q x) :=
    (s82p2_gt_measurable Q).comp (measurable_prodMk_left (x := x))
  have hgi : Integrable (s82p2_gt Q x) mu :=
    ((memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).2 hg2).integrable one_le_two
  ext c'
  have h1 := (EuclideanSpace.proj c' : Euc d →L[ℝ] ℝ).integral_comp_comm hgi
  simp only [PiLp.proj_apply] at h1
  have h2 : ∫ z, (s82p2_gt Q x z) c' ∂mu = 0 := by
    have := s82p2_centering_dir hd hM hA G c hG hc hρ hρG hQ x (EuclideanSpace.single c' (1 : ℝ))
      (by simp)
    simpa [EuclideanSpace.inner_single_right] using this
  rw [h1] at h2
  simpa using h2

end HRS.MS.S82P2
