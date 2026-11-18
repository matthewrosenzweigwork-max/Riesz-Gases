import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part I: weak sequential compactness in a separable real Hilbert space

`sa12de7_weak_subseq`: a sequence bounded by `B` in a separable real Hilbert space has a subsequence converging weakly to some
`g` with `‖g‖ ≤ B` (sequential Banach-Alaoglu `WeakDual.isSeqCompact_closedBall` and the Riesz representation).
-/

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace HRS.MS.SA12DE7

theorem sa12de7_weak_subseq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (J : ℕ → H) {B : ℝ} (hB : ∀ n, ‖J n‖ ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : H), StrictMono φ ∧ ‖g‖ ≤ B ∧
      ∀ v : H, Tendsto (fun n => inner ℝ (J (φ n)) v) atTop (𝓝 (inner ℝ g v)) := by
  let x : ℕ → WeakDual ℝ H := fun n => StrongDual.toWeakDual (innerSL ℝ (J n))
  have hx : ∀ n, x n ∈ (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) B) := by
    intro n
    simp only [Set.mem_preimage, mem_closedBall_zero_iff]
    show ‖innerSL ℝ (J n)‖ ≤ B
    rw [innerSL_apply_norm]
    exact hB n
  obtain ⟨a, ha, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) B hx
  set g : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual a) with hg
  refine ⟨φ, g, hφ, ?_, ?_⟩
  · have h1 : ‖g‖ = ‖WeakDual.toStrongDual a‖ := by
      rw [hg]; exact (InnerProductSpace.toDual ℝ H).symm.norm_map _
    rw [h1]
    simpa using ha
  · intro v
    have h2 := ((WeakDual.eval_continuous v).tendsto a).comp hlim
    have e1 : ∀ n, (x (φ n)) v = inner ℝ (J (φ n)) v := fun n => by
      show innerSL ℝ (J (φ n)) v = _
      simp
    have e2 : (a v) = inner ℝ g v := by
      rw [hg, InnerProductSpace.toDual_symm_apply]; rfl
    rw [← e2]
    refine h2.congr fun n => ?_
    exact e1 n

end HRS.MS.SA12DE7
