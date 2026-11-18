import HRS.MS.S21T4ProdCA

/-!
# S13: L²-stability of quadratic Gaussian variables for distinct factor families

Two separate smooth finite-rank representations are combined with a
block-diagonal symmetric coefficient matrix. The original Gaussian
field is unchanged. This removes the shared-factor restriction in CA.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_generic_product_finite_rank_quadratic_distinct_factors_bound
    (I : ProductGaussian μ) {r s : ℕ}
    (c : Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (c' : Fin s → Fin s → ℝ) (v : Fin s → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) (hv : IsR2FiniteRankData c' v) :
    (∫ ω : I.Ω,
      (((1 / 2 : ℝ) *
        ∑ i : Fin r, ∑ j : Fin r, c i j *
          (I.η (u i) ω * I.η (u j) ω -
            ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) -
        (1 / 2 : ℝ) *
        ∑ i : Fin s, ∑ j : Fin s, c' i j *
          (I.η (v i) ω * I.η (v j) ω -
            ∫ ζ, I.η (v i) ζ * I.η (v j) ζ ∂I.P)) ^ 2 ∂I.P) ≤
    18 * ∫ z : Euc d × Euc d,
      (r2FiniteRankKernel c u z.1 z.2 -
        r2FiniteRankKernel c' v z.1 z.2) ^ 2 ∂(μ.prod μ) := by
  letI := I.mΩ
  letI := I.prob
  let w : Fin (r + s) → Euc d → ℝ := Fin.append u v
  let C : Fin (r + s) → Fin (r + s) → ℝ :=
    Fin.addCases
      (fun i => Fin.addCases (c i) (fun _ => 0))
      (fun i => Fin.addCases (fun _ => 0) (fun j => -c' i j))
  have hC : IsR2FiniteRankData C w := by
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) b
        · simpa [C] using hu.symm i j
        · simp [C]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) b
        · simp [C]
        · simpa [C] using congrArg Neg.neg (hv.symm i j)
    · intro a
      refine Fin.addCases (fun i => ?_) (fun j => ?_) a
      · simpa [w] using hu.smooth i
      · simpa [w] using hv.smooth j
    · intro a
      refine Fin.addCases (fun i => ?_) (fun j => ?_) a
      · simpa [w] using hu.compactSupport i
      · simpa [w] using hv.compactSupport j
  have hkernel : ∀ x y, r2FiniteRankKernel C w x y =
      r2FiniteRankKernel c u x y - r2FiniteRankKernel c' v x y := by
    intro x y
    simp [r2FiniteRankKernel, Fin.sum_univ_add, C, w, Fin.append_left, Fin.append_right]
    ring
  let Q : (t : ℕ) → (Fin t → Fin t → ℝ) → (Fin t → Euc d → ℝ) → I.Ω → ℝ :=
    fun t a f ω =>
      (1 / 2 : ℝ) * ∑ i : Fin t, ∑ j : Fin t, a i j *
        (I.η (f i) ω * I.η (f j) ω -
          ∫ ζ, I.η (f i) ζ * I.η (f j) ζ ∂I.P)
  have hQ : ∀ ω, Q (r + s) C w ω = Q r c u ω - Q s c' v ω := by
    intro ω
    simp [Q, Fin.sum_univ_add, C, w, Fin.append_left, Fin.append_right]
    ring
  have hbd := s21t4_generic_product_finite_rank_quadratic_sq_bound I C w hC
  simpa only [hQ, hkernel, Q] using hbd

end HRS.MS.R26T3
