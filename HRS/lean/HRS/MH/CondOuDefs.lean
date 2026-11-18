import HRS.ME.FamVC
import HRS.ME.RetPathLaw
import HRS.Main.HeadlineEquilibrium
import HRS.Sections.Q38bAux4

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MH.CondOuPackets

open HRS HRS.Main HRS.LZ

variable {d : ℕ}

/-- The point `t` of the window `[0, t]`. -/
def endpt {t : ℝ} (ht : 0 ≤ t) : Set.Icc (0 : ℝ) t := ⟨t, ht, le_rfl⟩

/-- The continuous linear functional `w ↦ ⟨w(τ), ψ_k⟩ = NegSobolev.eval (w.at' τ) (cosTest k)` on `𝒳_{m,T}`,
realised as `√2` times the inner product with the `ℓ²` vector `cosVec d m k` (`ψ_k = √2 cos_k`), so that it is
continuous without a separate bound.  Same construction as `HRS.ME.FamV.rateEval` at an arbitrary time. -/
def condouEvalAt (d : ℕ) (m T : ℝ) (τ : Set.Icc (0 : ℝ) T) (k : Lattice d) : PathSpace d m T →L[ℝ] ℝ :=
  Real.sqrt 2 • ((innerSL ℝ (HRS.ME.FamV.cosVec d m k)).comp (ContinuousMap.evalCLM ℝ τ))

/-- The two-time observable `w ↦ (⟨w(0), ψ_k⟩, ⟨w(t), ψ_k⟩) ∈ ℝ²` on the window space `𝒳_{m,t}`. -/
def condouEval2 (d : ℕ) (m t : ℝ) (ht : 0 ≤ t) (k : Lattice d) :
    PathSpace d m t →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((EuclideanSpace.equiv (Fin 2) ℝ).symm : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
    (ContinuousLinearMap.pi ![condouEvalAt d m t (HRS.ME.FamV.t0 ht) k, condouEvalAt d m t (endpt ht) k])

/-- The covariance `v · [[1, e], [e, 1]]` of the stationary Gaussian pair `(Z^0, Z^t)` of the mode `ψ_k`:
`v = (1 + β ĝ(k))⁻¹`, `e = exp(-λ_{β,k} t)`. -/
def condouCov (d : ℕ) (s β : ℝ) (k : Lattice d) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + β * rieszCoeff d s k)⁻¹, (1 + β * rieszCoeff d s k)⁻¹ * Real.exp (-PDE.transientRate d s β k * t);
     (1 + β * rieszCoeff d s k)⁻¹ * Real.exp (-PDE.transientRate d s β k * t), (1 + β * rieszCoeff d s k)⁻¹]

theorem condouEvalAt_apply {m T : ℝ} (τ : Set.Icc (0 : ℝ) T) (k : Lattice d)
    (w : PathSpace d m T) :
    condouEvalAt d m T τ k w = NegSobolev.eval (w.at' τ) (PDE.cosTest k) := by
  have h1 : ∀ F : NegSobolev d m, NegSobolev.eval F (PDE.cosTest k) =
      Real.sqrt 2 * NegSobolev.eval F (Torus.cosMode k) := by
    intro F
    unfold NegSobolev.eval
    rw [← tsum_mul_left]
    refine tsum_congr fun l => ?_
    have : Torus.funRealCoeff (PDE.cosTest k) l = Real.sqrt 2 * Torus.funRealCoeff (Torus.cosMode k) l := by
      unfold Torus.funRealCoeff PDE.cosTest
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [this]; ring
  rw [h1, HRS.ME.FamV.eval_eq_inner_cos, real_inner_comm]
  rfl

theorem condouEval2_apply {m t : ℝ} (ht : 0 ≤ t) (k : Lattice d) (w : PathSpace d m t) :
    condouEval2 d m t ht k w = (WithLp.toLp 2 ![NegSobolev.eval (w.at' (HRS.ME.FamV.t0 ht)) (PDE.cosTest k),
      NegSobolev.eval (w.at' (endpt ht)) (PDE.cosTest k)] : EuclideanSpace ℝ (Fin 2)) := by
  ext i
  fin_cases i
  · simp [condouEval2, condouEvalAt_apply]
  · simp [condouEval2, condouEvalAt_apply]


end HRS.MH.CondOuPackets
