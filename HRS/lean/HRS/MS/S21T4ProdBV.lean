import HRS.MS.S21T4ProdBU
import HRS.MS.S21L_G11F

/-!
# S13: genuinely nontrivial finite-rank Gaussian quadratic forms are in second chaos

The arbitrary-probability-measure result includes finite atomic laws, without
postulating an infinite norm-one orthonormal family in the centred L² space.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MC.E213U13 HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_generic_product_finite_rank_quadratic_second
    (I : ProductGaussian μ) {r : ℕ}
    (u : Fin r → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin r → Fin r → ℝ) :
    InSecondChaos I.P I.ξ 3 (fun ω : I.Ω => (1 / 2 : ℝ) *
      ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) := by
  letI := I.mΩ
  letI := I.prob
  let ξ' : ℕ → I.Ω → ℝ := fun i => (I.standard.aemeasurable i).mk (I.ξ i)
  have hm' : ∀ i, Measurable (ξ' i) := fun i => (I.standard.aemeasurable i).measurable_mk
  have hae : ∀ i, I.ξ i =ᵐ[I.P] ξ' i := fun i => (I.standard.aemeasurable i).ae_eq_mk
  have hξ'G : HRS.IsStdGaussianSeq I.P ξ' := by
    refine ⟨(ProbabilityTheory.iIndepFun_congr hae).1 I.standard.1, fun i => ?_⟩
    have h1 : I.P.map (I.ξ i) = gaussianReal 0 1 := I.standard.2 i
    show I.P.map (ξ' i) = gaussianReal 0 1
    rw [← Measure.map_congr (hae i)]
    exact h1
  have hfirst : ∀ i, InQ1 hξ'G hm' (I.η (u i)) := fun i =>
    s21l_inQ1_of_first hξ'G hm' (s21l_first_congr hae (I.first (u i) (hu i)))
  have hprod : ∀ i j : Fin r,
      InQ2 hξ'G (fun ω => I.η (u i) ω * I.η (u j) ω -
        ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P) := fun i j =>
    InQ2.mul_centered hξ'G hm' (hfirst i) (hfirst j)
  have hY : InQ2 hξ'G (fun ω : I.Ω => (1 / 2 : ℝ) *
      ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) :=
    InQ2.const_mul _ (InQ2.sum _ fun i _ =>
      InQ2.sum _ fun j _ => InQ2.const_mul _ (hprod i j))
  have hY2 := s21t4_generic_product_finite_rank_quadratic_L2 I u hu c
  have hsecond : InSecondChaos I.P ξ' 3 (fun ω : I.Ω => (1 / 2 : ℝ) *
      ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) := by
    refine s21l_inSecondChaos_of_coords hξ'G hm' hY2.aestronglyMeasurable hY2 ?_
    intro v
    convert InQ2.const_mul v hY using 1
    funext ω
    simp [mul_comm]
  exact s21l_second_congr (fun i => (hae i).symm) hsecond

end HRS.MS.R26T3
