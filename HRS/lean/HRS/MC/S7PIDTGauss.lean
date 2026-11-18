import HRS.MC.S7PIDGVector
import HRS.MC.S7PIDDefs

/-!
# Packet PI-D, sub-packet T (part 2): the Gaussian vector family with integrability

`s7_PID_gauss_vector_proof` does not record the integrability of the Gaussian vectors (its conclusions are plain integrals).  We rerun
its construction (the multivariate Gaussian on `EuclideanSpace ℝ κ`) and add `MemLp 4` of every `Y i`, `Y' i`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDG

theorem S7PIDT_gauss_vec {r : ℕ} {ι : Type} [Fintype ι] (I : Set ℝ)
    (w w' : ι → ℝ → EuclideanSpace ℝ (Fin r))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict I)) (hw' : ∀ i, MemLp (w' i) 2 (volume.restrict I)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y Y' : ι → Ω → EuclideanSpace ℝ (Fin r)),
      (∀ i, Measurable (Y i)) ∧ (∀ i, Measurable (Y' i)) ∧
      (∀ (B : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ) (i j : ι),
        ∫ ω, B (Y i ω) (Y' j ω) ∂P = ∫ u in I, B (w i u) (w' j u)) ∧
      (∀ i j, ∫ ω, ‖Y i ω - Y j ω‖ ^ 4 ∂P ≤ 3 * (∫ u in I, ‖w i u - w j u‖ ^ 2) ^ 2) ∧
      (∀ i j, ∫ ω, ‖Y' i ω - Y' j ω‖ ^ 4 ∂P ≤ 3 * (∫ u in I, ‖w' i u - w' j u‖ ^ 2) ^ 2) ∧
      (∀ i, ∫ ω, ‖Y i ω‖ ^ 2 ∂P = ∫ u in I, ‖w i u‖ ^ 2) ∧
      (∀ i, ∫ ω, ‖Y' i ω‖ ^ 2 ∂P = ∫ u in I, ‖w' i u‖ ^ 2) ∧
      (∀ i, MemLp (Y i) 4 P) ∧ (∀ i, MemLp (Y' i) 4 P) := by
  classical
  set F : (ι × Fin r) ⊕ (ι × Fin r) → ℝ → ℝ :=
    Sum.elim (fun p : ι × Fin r => fun u => w p.1 u p.2)
      (fun p : ι × Fin r => fun u => w' p.1 u p.2) with hFdef
  have hF : ∀ α, MemLp (F α) 2 (volume.restrict I) := S7PIDG_vec_family I w w' hw hw'
  have : ProbabilityTheory.IsGaussian (ProbabilityTheory.multivariateGaussian
      (0 : EuclideanSpace ℝ ((ι × Fin r) ⊕ (ι × Fin r))) (S7PIDG_gram I F)) := inferInstance
  have hcoord : ∀ α, MemLp (fun ω : EuclideanSpace ℝ ((ι × Fin r) ⊕ (ι × Fin r)) => ω α) 4
      (ProbabilityTheory.multivariateGaussian
        (0 : EuclideanSpace ℝ ((ι × Fin r) ⊕ (ι × Fin r))) (S7PIDG_gram I F)) := fun α =>
    (EuclideanSpace.proj α : EuclideanSpace ℝ ((ι × Fin r) ⊕ (ι × Fin r)) →L[ℝ] ℝ).comp_memLp'
      (ProbabilityTheory.IsGaussian.memLp_id _ 4 (by norm_num))
  refine ⟨EuclideanSpace ℝ ((ι × Fin r) ⊕ (ι × Fin r)), inferInstance,
    ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ ((ι × Fin r) ⊕ (ι × Fin r)))
      (S7PIDG_gram I F), inferInstance,
    fun i ω => WithLp.toLp 2 (fun a => ω (Sum.inl (i, a))),
    fun i ω => WithLp.toLp 2 (fun a => ω (Sum.inr (i, a))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fun_prop
  · intro i
    fun_prop
  · intro B i j
    exact S7PIDG_cross_expect I F hF (fun a => Sum.inl (i, a)) (fun a => Sum.inr (j, a)) B
  · intro i j
    exact S7PIDG_norm4_expect I F hF (fun a => Sum.inl (i, a)) (fun a => Sum.inl (j, a))
  · intro i j
    exact S7PIDG_norm4_expect I F hF (fun a => Sum.inr (i, a)) (fun a => Sum.inr (j, a))
  · intro i
    exact S7PIDG_norm2_expect I F hF (fun a => Sum.inl (i, a))
  · intro i
    exact S7PIDG_norm2_expect I F hF (fun a => Sum.inr (i, a))
  · intro i
    exact (memLp_piLp_iff).2 fun a => hcoord (Sum.inl (i, a))
  · intro i
    exact (memLp_piLp_iff).2 fun a => hcoord (Sum.inr (i, a))

end HRS.MC.Sec7.S7PIDT

end
