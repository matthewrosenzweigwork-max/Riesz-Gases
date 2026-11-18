import HRS.MC.S7PIDDefs
import HRS.MC.S7PIDGCore

/-!
# Packet PI-D: proof of the scalar Gaussian family (`s7_PID_gauss_scalar`)

`s7_PID_gauss_scalar_proof` is the proof of `HRS.MC.Sec7.PIDPlan.s7_PID_gauss_scalar` (`HRS/MC/S7PIDPlan.lean`).
Route: the Gram matrix `G i j = ∫_I f_i f_j` is positive semidefinite (`S7PIDG_gram_psd`), so the multivariate
Gaussian `multivariateGaussian 0 G` on `EuclideanSpace ℝ ι` exists (Mathlib); its coordinates are the `Z i`, the
cross moments are `G` and every linear form `∑ c_i Z_i` has law `gaussianReal 0 (c⬝Gc)`, whose fourth moment is
`3 (c⬝Gc)²` (`S7PIDG_lin_law_moments`); finally `c⬝Gc = ∫_I (∑ c_i f_i)²` (`S7PIDG_gram_quad`).
The helper file `HRS/MC/S7PIDGCore.lean` imports Mathlib only.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDG

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

theorem s7_PID_gauss_scalar_proof {ι : Type} [Fintype ι] (I : Set ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (volume.restrict I)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P) (Z : ι → Ω → ℝ),
      (∀ i, Measurable (Z i)) ∧
      (∀ i j, ∫ ω, Z i ω * Z j ω ∂P = ∫ u in I, f i u * f j u) ∧
      ∀ c : ι → ℝ, ∫ ω, (∑ i, c i * Z i ω) ^ 4 ∂P = 3 * (∫ u in I, (∑ i, c i * f i u) ^ 2) ^ 2 := by
  classical
  have hG : (S7PIDG_gram I f).PosSemidef := S7PIDG_gram_psd I f hf
  obtain ⟨-, hcross⟩ := S7PIDG_build (S7PIDG_gram I f) hG
  refine ⟨EuclideanSpace ℝ ι, inferInstance,
    ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ ι) (S7PIDG_gram I f), inferInstance,
    fun i ω => ω i, ?_, ?_, ?_⟩
  · intro i
    fun_prop
  · intro i j
    exact hcross i j
  · intro c
    rw [← S7PIDG_gram_quad I f hf c]
    exact (S7PIDG_lin_law_moments (S7PIDG_gram I f) hG c).1.2

end HRS.MC.Sec7.S7PIDG

end
