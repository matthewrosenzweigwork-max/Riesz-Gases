import HRS.MC.CepC0

/-!
# Packet CEPS2: existence of the maximal solution under `C^{1,1}` potentials

Proof of `HRS.MC.Cepa.cep_S2_maximal_c11` (spec file `HRS/MC/CepaSpec.lean`, kept as `sorry`).
It is `particle_maximal` (`HRS/Stochastic/Particle.lean:2082`) with `cep_C0_locLipschitz` in place of
`liftedDrift_locLipschitz`: the local Lipschitz drift comes from the C0 packet
(`HRS.MC.CepC0.cep_C0_locLipschitz_proof`), and existence is `exists_sde_solution_maximal`.

This file does not import the spec file; the predicate `cep_IsC11` is written as the duplicate
`HRS.MC.CepC0.cep_IsC11` (same body as `HRS.MC.Cepa.cep_IsC11`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepS2

open HRS

section Existence

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- **S2 (existence of the maximal solution under `C^{1,1}`)**: `particle_maximal` (`Particle.lean:2082`) with
`cep_C0_locLipschitz` in place of `liftedDrift_locLipschitz` (the proof is `exists_sde_solution_maximal`
applied to the local Lipschitz drift; ten lines once C0 is available). -/
theorem cep_S2_maximal_c11_proof [IsProbabilityMeasure P] {d : ℕ} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (D : DynData d) (hK : KernelLocal d D.s)
    (hV : HRS.MC.CepC0.cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W') (Y₀ : Ω → (Fin N → Euc d))
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) (hY₀U : ∀ ω, Y₀ ω ∈ liftedFree d N) :
    ∃ (τ : Ω → WithTop ℝ) (Y : ℝ → Ω → (Fin N → Euc d)), IsMaximalParticleSolution P ℱ W' D Y₀ τ Y := by
  have hb := HRS.MC.CepC0.cep_C0_locLipschitz_proof (N := N) D hK.smoothOffZero hV
  obtain ⟨τ, Y, hstop, hpos, hsol, hmem, hexit, _⟩ := exists_sde_solution_maximal hW'
    (liftedFree d N) (isOpen_liftedFree d N) (fun _ Z => liftedDrift D Z) hb (liftedNoise D) Y₀
    hY₀ hY₀U
  exact ⟨τ, Y, hY₀, hstop, hpos, hsol, hmem, hexit⟩

end Existence

end HRS.MC.CepS2
