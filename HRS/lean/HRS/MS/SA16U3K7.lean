import HRS.MS.SA16U3K7a
import HRS.MS.SA16U3K7d

/-!
# S.A.16 K7: `jump_commutator_low` (worker SA16U3)

Assembly of `sa16u3_k7_lt_one` (`0 < θ < 1`: Lipschitz near zero, bounded far away, Young) and `sa16u3_k7_one`
(`θ = 1`: Taylor remainder plus the uniform truncated Calderon-Zygmund bound for the gradient term).
The statement is copied verbatim from `SA16-COMPATIBLE-CUTOFF.lean`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA

/-- K7: the endpoint needs the existing uniform theta=1 CZ theorem;
the quadratic Taylor remainder is an L1 kernel. -/
theorem jump_commutator_low (d : ℕ) (hd : 1 ≤ d) (θ p : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∀ μ : Euc d → ℝ, MemCb 2 μ → ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (fun x => jumpCut d θ δ (fun y => μ y*W y) x-
          μ x*jumpCut d θ δ W x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C*cbNorm 2 μ)*eLpNorm W (ENNReal.ofReal p) volume := by
  rcases hθ1.lt_or_eq with hlt | heq
  · exact sa16u3_k7_lt_one d hd θ p hθ0 hlt hp
  · subst heq
    exact sa16u3_k7_one d hd p hp

end HRS.Whole.AppendixA.Phase2SA16Cutoff
