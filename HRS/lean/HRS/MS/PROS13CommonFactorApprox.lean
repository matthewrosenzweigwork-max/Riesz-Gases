import HRS.MS.PROS13SeparatedB
import HRS.MS.R2ChaosAux27

/-!
# S13: shared finite-rank smooth test family for arbitrary finite kernel families

For each approximation index, all finitely many symmetric product-L² kernels
are approximated by coefficient matrices over the same smooth test family.
This holds for every probability measure, including purely atomic measures.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_common_factors_approx
    {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, MemLp (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ k x y, h k x y = h k y x) :
    ∃ (r : ℕ → ℕ)
      (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
      (c : (j : ℕ) → Fin m → Fin (r j) → Fin (r j) → ℝ),
      (∀ j a, IsR2Test (u j a)) ∧
      (∀ j k, IsR2FiniteRankData (c j k) (u j)) ∧
      (∀ k, Tendsto
        (fun j => eLpNorm (fun z : Euc d × Euc d =>
          r2FiniteRankKernel (c j k) (u j) z.1 z.2 - h k z.1 z.2)
          2 (μ.prod μ)) atTop (𝓝 0)) := by
  classical
  have hall : ∀ k : Fin m,
      ∃ hj : ℕ → Euc d → Euc d → ℝ,
        (∀ j, ∃ (r : ℕ) (c : Fin r → Fin r → ℝ)
          (u : Fin r → Euc d → ℝ),
          IsR2FiniteRankData c u ∧ hj j = r2FiniteRankKernel c u) ∧
        Tendsto (fun j => eLpNorm
          (fun z : Euc d × Euc d => hj j z.1 z.2 - h k z.1 z.2)
          2 (μ.prod μ)) atTop (𝓝 0) :=
    fun k => pro_s13_generic_separated_sequence μ (h k) (hh k) (hs k)
  choose hj hdata hlimit using hall
  have hdata2 : ∀ j : ℕ, ∀ k : Fin m,
      ∃ (r : ℕ) (c : Fin r → Fin r → ℝ)
        (u : Fin r → Euc d → ℝ),
        IsR2FiniteRankData c u ∧ hj k j = r2FiniteRankKernel c u :=
    fun j k => hdata k j
  choose r c u hd heq using hdata2
  have hconcat : ∀ j : ℕ,
      ∃ (R : ℕ) (U : Fin R → Euc d → ℝ)
        (C : Fin m → Fin R → Fin R → ℝ),
        (∀ a, IsR2Test (U a)) ∧
        (∀ k a b, C k a b = C k b a) ∧
        ∀ k x y, r2FiniteRankKernel (C k) U x y =
          r2FiniteRankKernel (c j k) (u j k) x y := by
    intro j
    exact s94_concat (r j) (c j) (u j)
      (fun k a b => (hd j k).symm a b)
      (fun k a => ⟨(hd j k).smooth a, (hd j k).compactSupport a⟩)
  choose R U C htest hsym hkernel using hconcat
  refine ⟨R, U, C, htest, ?_, ?_⟩
  · intro j k
    exact ⟨hsym j k, (fun a => (htest j a).1),
      (fun a => (htest j a).2)⟩
  · intro k
    convert hlimit k using 1
    funext j
    apply congrArg (fun H : Euc d × Euc d → ℝ =>
      eLpNorm H 2 (μ.prod μ))
    funext z
    rw [hkernel j k, ← heq j k]

end HRS.MS.R26T3
