import HRS.MS.PROS13ActualQuadratic
import HRS.MS.S21T4ProdBV
import HRS.MS.S21L_G11H

/-!
# S13: a product-L² Gaussian quadratic limit belongs to second Wiener chaos

The limit is the actual L² limit of finite-rank quadratic polynomials
on the original isonormal field. Finite atomic measures are allowed.
No infinite norm-one orthonormal basis is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos HRS.MC.E213U13
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_quadratic_limit_in_second_chaos
    (I : ProductGaussian μ)
    (r : ℕ → ℕ)
    (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
    (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
    (hd : ∀ j, IsR2FiniteRankData (c j) (u j))
    (Q : I.Ω → ℝ)
    (hQ : MemLp Q 2 I.P)
    (hlim : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
        (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         Q ω) ^ 2 ∂I.P) atTop (𝓝 0)) :
    InSecondChaos I.P I.ξ 3 Q := by
  letI := I.mΩ
  letI := I.prob
  let ξ' : ℕ → I.Ω → ℝ := fun i =>
    (I.standard.aemeasurable i).mk (I.ξ i)
  have hm' : ∀ i, Measurable (ξ' i) :=
    fun i => (I.standard.aemeasurable i).measurable_mk
  have hae : ∀ i, I.ξ i =ᵐ[I.P] ξ' i :=
    fun i => (I.standard.aemeasurable i).ae_eq_mk
  have hξ'G : HRS.IsStdGaussianSeq I.P ξ' := by
    refine ⟨(ProbabilityTheory.iIndepFun_congr hae).1 I.standard.1, fun i => ?_⟩
    have h1 : I.P.map (I.ξ i) = gaussianReal 0 1 := I.standard.2 i
    show I.P.map (ξ' i) = gaussianReal 0 1
    rw [← Measure.map_congr (hae i)]
    exact h1
  let Qj : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
      (I.η (u j a) ω * I.η (u j b) ω -
        ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)
  have hQj2 : ∀ j, MemLp (Qj j) 2 I.P := by
    intro j
    have hu : ∀ i, MemLp (u j i) 2 μ :=
      fun i => ((hd j).smooth i).continuous.memLp_of_hasCompactSupport
        ((hd j).compactSupport i)
    exact s21t4_generic_product_finite_rank_quadratic_L2 I (u j) hu (c j)
  have hQjIn : ∀ j, InQ2 hξ'G (Qj j) := by
    intro j
    have hu : ∀ i, MemLp (u j i) 2 μ :=
      fun i => ((hd j).smooth i).continuous.memLp_of_hasCompactSupport
        ((hd j).compactSupport i)
    have hfirst : ∀ i : Fin (r j), InQ1 hξ'G hm' (I.η (u j i)) :=
      fun i => s21l_inQ1_of_first hξ'G hm'
        (s21l_first_congr hae (I.first (u j i) (hu i)))
    have hprod : ∀ a b : Fin (r j),
        InQ2 hξ'G (fun ω => I.η (u j a) ω * I.η (u j b) ω -
          ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P) :=
      fun a b => InQ2.mul_centered hξ'G hm' (hfirst a) (hfirst b)
    exact InQ2.const_mul _ (InQ2.sum _ fun a _ =>
      InQ2.sum _ fun b _ => InQ2.const_mul _ (hprod a b))
  have hIn : InQ2 hξ'G Q := by
    refine InQ2.of_tendsto (l := atTop) hQjIn hQ.aestronglyMeasurable ?_
    exact s21l_tendsto_lintegral hQ hQj2 hlim
  have hSecond : InSecondChaos I.P ξ' 3 Q := by
    refine s21l_inSecondChaos_of_coords hξ'G hm'
      hQ.aestronglyMeasurable hQ ?_
    intro v
    convert InQ2.const_mul v hIn using 1
    funext ω
    simp [mul_comm]
  exact s21l_second_congr (fun i => (hae i).symm) hSecond

theorem pro_s13_generic_actual_second_chaos_witness
    (I : ProductGaussian μ)
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) :
    ∃ Q : I.Ω → ℝ,
      MemLp Q 2 I.P ∧ InSecondChaos I.P I.ξ 3 Q ∧
      ∃ (r : ℕ → ℕ)
        (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
        (u : (j : ℕ) → Fin (r j) → Euc d → ℝ),
        (∀ j, IsR2FiniteRankData (c j) (u j)) ∧
        Tendsto (fun j => eLpNorm
          (fun z : Euc d × Euc d =>
            r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
          2 (μ.prod μ)) atTop (𝓝 0) ∧
        Tendsto (fun j : ℕ => ∫ ω : I.Ω,
          (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
            (I.η (u j a) ω * I.η (u j b) ω -
              ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
           Q ω) ^ 2 ∂I.P) atTop (𝓝 0) := by
  obtain ⟨r, c, u, Q, hd, hT, hQ, hlim⟩ :=
    pro_s13_generic_actual_quadratic_L2_witness I h hh hs
  exact ⟨Q, hQ, pro_s13_quadratic_limit_in_second_chaos I r c u hd Q hQ hlim,
    r, c, u, hd, hT, hlim⟩

end HRS.MS.R26T3
