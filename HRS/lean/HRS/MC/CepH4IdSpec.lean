import HRS.MC.CepaSpec

/-!
# Packet CEPH4ID (specification): the flow of B.14 on one cyclic component is `mk ∘ unrank_{σ₀} ∘ Zl`

SPECIFICATION FILE (the statement has a `sorry` by design; not for root import).

`cep_H4_identify`: let `X` be a Cépa–Lépingle flow (`IsCepaLepingleFlow`) and let `Zl` be a chamber process with the
properties delivered by `cep_E6_limit_solution` for `π := fun _ => σ₀`, `a = 1`, `σ' = √(2 invβ)`, `F = -∇Ψ`
(`Ψ` from E1, whose drift identification is the hypothesis `hΨdr`), started at an alcove point `z₀ ω` whose unranked,
projected lift is `X₀ ω`.  Then `X t = mk ∘ unrank_{σ₀} (Zl t)` for all `t ≤ T`, almost surely.  Proof: `mk ∘ unrank_{σ₀} ∘ Zl`
is itself a Cépa–Lépingle flow with the same data (E7) and U2 gives uniqueness.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH4Id

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- **Identification of the flow on one cyclic component.** -/
theorem cep_H4_identify [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {D : DynData 1} (hs : D.s = 0) (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ)) (hV : cep_IsC11 D.V)
    {T : ℝ} {X₀ : Ω → Config 1 N} (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    (σ₀ : Equiv.Perm (Fin N))
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    (hWW' : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j)
    {X : ℝ≥0 → Ω → Config 1 N} (hX : IsCepaLepingleFlow P D T X₀ W X)
    {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨL : LipschitzWith L (gradient Ψ))
    (hΨdr : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y → ∀ k : Fin N,
      liftedDrift D y (π k) 0 =
        -(gradient (cep_chamberPot 1 N) (cep_toCh π y)) k - (gradient Ψ (cep_toCh π y)) k)
    {z₀ : Ω → Ch N} (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀X : ∀ᵐ ω ∂P, (fun i => Torus.mk (cep_unrank σ₀ (z₀ ω) i)) = X₀ ω)
    {Zl : ℝ → Ω → Ch N} (hZlc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlm : ∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t))
    (hZlcl : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N))
    (hZlnull : ∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0)
    (hZlint : ∀ᵐ ω ∂P, ∀ T : ℝ,
      IntegrableOn (fun s : ℝ => ‖gradient (cep_chamberPot 1 N) (Zl s ω)‖) (Set.Icc 0 T))
    (hZleq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Zl t ω = z₀ ω +
      (∫ s in (0 : ℝ)..t, (-(gradient (cep_chamberPot 1 N) (Zl s ω)) + -(gradient Ψ (Zl s ω)))) +
        Real.sqrt (2 * D.invβ) • cep_noise (fun _ : Ω => σ₀) W' t ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = fun i => Torus.mk (cep_unrank σ₀ (Zl (t : ℝ) ω) i) := by
  sorry

end HRS.MC.CepH4Id
