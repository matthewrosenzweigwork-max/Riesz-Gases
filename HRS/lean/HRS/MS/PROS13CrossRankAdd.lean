import HRS.MS.PROS13CrossUnique
import HRS.MS.S21T4ProdCB

/-!
# Generic S13: addition of arbitrary finite-rank pair-kernel representations

The two finite-rank data sets may have distinct ranks and completely distinct
smooth factor functions. A block-diagonal matrix and the concatenated factors
give the exact sum of kernels and the exact sum of the *actual* half-Wick
Gaussian polynomials on the unchanged ProductGaussian probability space.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- An exact block-diagonal addition identity, without a shared factor
family or a nonempty ONB assumption. -/
theorem pro_s13_generic_finite_rank_add
    (I : ProductGaussian μ) {r s : ℕ}
    (c : Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (c' : Fin s → Fin s → ℝ) (v : Fin s → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) (hv : IsR2FiniteRankData c' v) :
    ∃ (C : Fin (r + s) → Fin (r + s) → ℝ)
      (w : Fin (r + s) → Euc d → ℝ),
      IsR2FiniteRankData C w ∧
      (∀ x y, r2FiniteRankKernel C w x y =
        r2FiniteRankKernel c u x y + r2FiniteRankKernel c' v x y) ∧
      (∀ ω : I.Ω,
        (1 / 2 : ℝ) * ∑ i : Fin (r + s), ∑ j : Fin (r + s), C i j *
          (I.η (w i) ω * I.η (w j) ω -
            ∫ ζ, I.η (w i) ζ * I.η (w j) ζ ∂I.P) =
        (1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r, c i j *
          (I.η (u i) ω * I.η (u j) ω -
            ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P) +
        (1 / 2 : ℝ) * ∑ i : Fin s, ∑ j : Fin s, c' i j *
          (I.η (v i) ω * I.η (v j) ω -
            ∫ ζ, I.η (v i) ζ * I.η (v j) ζ ∂I.P)) := by
  let w : Fin (r + s) → Euc d → ℝ := Fin.append u v
  let C : Fin (r + s) → Fin (r + s) → ℝ :=
    Fin.addCases
      (fun i => Fin.addCases (c i) (fun _ => 0))
      (fun i => Fin.addCases (fun _ => 0) (fun j => c' i j))
  have hC : IsR2FiniteRankData C w := by
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) b
        · simpa [C] using hu.symm i j
        · simp [C]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) b
        · simp [C]
        · simpa [C] using hv.symm i j
    · intro a
      refine Fin.addCases (fun i => ?_) (fun j => ?_) a
      · simpa [w] using hu.smooth i
      · simpa [w] using hv.smooth j
    · intro a
      refine Fin.addCases (fun i => ?_) (fun j => ?_) a
      · simpa [w] using hu.compactSupport i
      · simpa [w] using hv.compactSupport j
  refine ⟨C, w, hC, ?_, ?_⟩
  · intro x y
    simp [r2FiniteRankKernel, Fin.sum_univ_add, C, w,
      Fin.append_left, Fin.append_right]
  · intro ω
    simp [Fin.sum_univ_add, C, w, Fin.append_left, Fin.append_right]
    ring

end HRS.MS.R26T3
