import HRS.MS.PROS13CrossL2Bridge
import HRS.MS.S21T4ProdZ

/-!
# Generic S13: Gaussian squared-integral convergence is stable under addition

This is used for arbitrary pairs of finite-rank approximations of different
kernel functions on a common canonical Gaussian probability space.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem pro_s13_integral_sq_sum_limits
    (F G : ℕ → Ω → ℝ) (Q R : Ω → ℝ)
    (hF : ∀ j, MemLp (F j) 2 P) (hG : ∀ j, MemLp (G j) 2 P)
    (hQ : MemLp Q 2 P) (hR : MemLp R 2 P)
    (hlimF : Tendsto (fun j => ∫ ω, (F j ω - Q ω) ^ 2 ∂P) atTop (𝓝 0))
    (hlimG : Tendsto (fun j => ∫ ω, (G j ω - R ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ ω,
      (F j ω + G j ω - (Q ω + R ω)) ^ 2 ∂P) atTop (𝓝 0) := by
  have hFl2 := pro_s13_tendstoL2_of_integral_sq F Q hF hQ hlimF
  have hGl2 := pro_s13_tendstoL2_of_integral_sq G R hG hR hlimG
  have hsum := s21t4_tendstoL2_add
    (fun j => (hF j).aestronglyMeasurable)
    (fun j => (hG j).aestronglyMeasurable) hFl2 hGl2
  have hmeas : ∀ j, MemLp (fun ω =>
      (F j ω + G j ω) - (Q ω + R ω)) 2 P :=
    fun j => ((hF j).add (hG j)).sub (hQ.add hR)
  have hnorm : Tendsto (fun j => eLpNorm (fun ω =>
      (F j ω + G j ω) - (Q ω + R ω)) 2 P) atTop (𝓝 0) :=
    hsum.tendsto_eLpNorm (fun j => ((hF j).add (hG j)).aestronglyMeasurable)
  exact s21t4_integral_sq_tendsto_zero
    (fun j ω => F j ω + G j ω - (Q ω + R ω)) hmeas hnorm

end HRS.MS.R26T3
