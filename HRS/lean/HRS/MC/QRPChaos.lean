import HRS.MC.QRVocab
import HRS.MC.QRPChaosAux4

/-!
# Packet CHAOS-LP: `L^p` moments of Gaussian quadratic forms (finite form)

`qrs_chaos_lp_fin_proof` is the relocated proof of `HRS.MC.QRSpec.qrs_chaos_lp_fin` (statement copied verbatim;
the tie `example` is in `HRS/MC/QRPChaosTie.lean`).  Route: decoupling by the rotation
`((x+y)/√2, (x-y)/√2)` of two independent copies, Jensen for the symmetrisation, and conditional Gaussianity
(no diagonalisation); see `QRPChaosAux1`-`QRPChaosAux4`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.QRSpec.Chaos

theorem qrs_chaos_lp_fin_proof : ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] (ξ : ι → Ω → ℝ), HasGaussianLaw (fun ω i => ξ i ω) P →
      (∀ i, ∫ ω, ξ i ω ∂P = 0) → ∀ K : ℝ, 0 ≤ K →
      (∀ a : ι → ℝ, ∫ ω, (∑ i, a i * ξ i ω) ^ 2 ∂P ≤ K * ∑ i, a i ^ 2) →
      ∀ A : ι → ι → ℝ,
        eLpNorm (fun ω => ∑ i, ∑ j, A i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P))
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C * K * Real.sqrt (∑ i, ∑ j, A i j ^ 2)) := by
  intro p hp
  have hGfin : HRS.MC.QRPChaos.qpcG p ≠ ∞ := (HRS.MC.QRPChaos.qpcG_lt_top p).ne
  set g : ℝ := (HRS.MC.QRPChaos.qpcG p).toReal with hg
  refine ⟨2 * g ^ 2 + 1, by positivity, ?_⟩
  intro Ω _ P _ ι _ ξ hξ hc K hK hKop A
  set ξv : Ω → ι → ℝ := fun ω i => ξ i ω with hξv
  set ν : Measure (ι → ℝ) := P.map ξv with hν
  haveI : IsGaussian ν := hξ.isGaussian_map
  have hmeas : ∀ f : (ι → ℝ) → ℝ, Measurable f → ∫ x, f x ∂ν = ∫ ω, f (ξv ω) ∂P :=
    fun f hf => integral_map hξ.aemeasurable hf.aestronglyMeasurable
  have h0 : ∀ i, ∫ x, x i ∂ν = 0 := fun i => by
    rw [hmeas (fun x => x i) (by fun_prop)]; exact hc i
  have hKν : ∀ a : ι → ℝ, ∫ x, (∑ i, a i * x i) ^ 2 ∂ν ≤ K * ∑ i, a i ^ 2 := fun a => by
    rw [hmeas (fun x => (∑ i, a i * x i) ^ 2) (by fun_prop)]; exact hKop a
  have hbound := HRS.MC.QRPChaos.qpc_nu_bound ν h0 hK hKν A hp
  have hS : ∀ i j, ∫ y, y i * y j ∂ν = ∫ ω', ξ i ω' * ξ j ω' ∂P := fun i j =>
    hmeas (fun y => y i * y j) (by fun_prop)
  have hfun : (fun x : ι → ℝ => ∑ i, ∑ j, A i j * (x i * x j - ∫ y, y i * y j ∂ν)) ∘ ξv =
      fun ω => ∑ i, ∑ j, A i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P) := by
    funext ω; simp only [Function.comp, hξv, hS]
  rw [← hfun, ← eLpNorm_map_measure (by exact (by fun_prop : Measurable _).aestronglyMeasurable)
    hξ.aemeasurable]
  refine hbound.trans ?_
  set x : ℝ := K * Real.sqrt (∑ i, ∑ j, A i j ^ 2) with hx
  have hx0 : 0 ≤ x := by positivity
  have e : (2 * g ^ 2 + 1) * K * Real.sqrt (∑ i, ∑ j, A i j ^ 2) = (2 * g ^ 2 + 1) * x := by
    rw [hx]; ring
  rw [e]
  have hGeq : HRS.MC.QRPChaos.qpcG p = ENNReal.ofReal g := (ENNReal.ofReal_toReal hGfin).symm
  rw [hGeq, ← ENNReal.ofReal_pow (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul hx0, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg g])

end HRS.MC.QRSpec.Chaos

end
