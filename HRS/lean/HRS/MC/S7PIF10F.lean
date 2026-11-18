import HRS.MC.S7PIF10E
import HRS.MC.S7PIS2Proj
import HRS.MC.S7PIS2Cb

/-!
# Packet piF10 (F11): `s7_PI_F_projected_identity_assembly_proof` (namespace `HRS.MC.Sec7.S7PIF10`)

Statement copied verbatim from `HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PI_F_projected_identity_assembly`).  Take the grid data
`(q,t,φ,Λ)` of `Pj L` (`s7_PIS_obs_proj_proof`), `G = Φ ∘ Λ ∈ C_b^5 ⊂ C_b^4` (`s7_PIS_memCb_comp_proof`); then `Φ ∘ Pj L = G ∘ obsVec`
and `s7_PIF_cyl_concl_proof` applies after rewriting the functional.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF10

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- **F11 (assembly of PI-F)** (statement of `HRS.MC.Sec7.PIPlan.s7_PI_F_projected_identity_assembly`, verbatim). -/
theorem s7_PI_F_projected_identity_assembly_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    (N : ℕ) (hN : 1 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
    (Pj : ℕ → (PathSpace d m T →L[ℝ] PathSpace d m T)) (hPj : ∀ L w, Pj L w = projPoly m T hT.le L w)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (L : ℕ) :
    ∃ A J : Ω → ℝ, Integrable A P ∧ Integrable J P ∧
      (∀ᵐ ω ∂P, IsRS T (fun τ a b =>
        fderiv ℝ (heatFn γ (fun w => Φ (Pj L w)) τ) (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ)
          (driftInc R.D R.ρ m T
            (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω) a b)) (A ω)) ∧
      (∀ᵐ ω ∂P, IsRS T (fun τ a b =>
        jPair R.D R.ρ m T (fun u => etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u))) (Set.Ioc a b)
          (iteratedFDeriv ℝ 2 (heatFn γ (fun w => Φ (Pj L w)) τ)
            (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ))) (J ω)) ∧
      ∫ ω, Φ (Pj L (zetaWin m T 0 P X ω)) ∂P =
        ∫ ω, heatFn γ (fun w => Φ (Pj L w)) 0 (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) ∂P -
          (Real.sqrt N)⁻¹ * ∫ ω, A ω ∂P + (1 / (2 * Real.sqrt N)) * ∫ ω, J ω ∂P := by
  obtain ⟨q, t, φ, Λ, ht, hφ, hP⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_obs_proj_proof (d := d) m T hT L
  have hφs : ∀ i, Torus.IsSmooth (φ i) := fun i => by
    obtain ⟨k, hk⟩ := hφ i
    rw [hk]; exact HRS.FieldSingAux.isSmooth_realMode k
  have hG := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof Λ hΦ).1
  have hG4 : MemCb 4 (fun x => Φ (Λ x)) := S7PIF10_memCb_mono hG (by norm_num)
  have key := s7_PIF_cyl_concl_proof R m hm T hT N hN P X₀ W X hreal γ hγ t φ ht hφs
    (fun x => Φ (Λ x)) hG4
  have hpt : ∀ w, Φ (Pj L w) = Φ (Λ (obsVec m T t φ w)) := fun w => by rw [hPj, hP]
  unfold PathItoConcl at key
  simp only [ContinuousLinearMap.id_apply] at key
  simp only [hpt]
  exact key

end HRS.MC.Sec7.S7PIF10

end
