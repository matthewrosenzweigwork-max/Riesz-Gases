import HRS.MC.CepaSpec

/-!
# Packet CEPH4 (specification): inputs of the entropy inequality H4 on one cyclic component

SPECIFICATION FILE (each statement has a `sorry` by design; not for root import).  Three statements prepare the
application of the cylinder entropy dissipation H2 to the Yosida potentials `U_n = Φ_n + Ψ`:

* `cep_E2_envelope_props`: the Moreau envelopes of E2 are diagonally periodic, `C¹` with Lipschitz gradient, and
  satisfy the transverse lower bound `Φ_n(z) ≥ (n/2) dist(z, alcove)² - C` (this is `Φ_n(z) = Φ(J_n z) + (n/2)|z - J_n z|²`
  and `Φ` bounded below on the alcove).  Strengthens E2 by extra conjuncts; the first conjuncts are those of E2.
* `cep_H4_potential_conf`: `Φ_n + Ψ` is quadratically confining for `n > L`, from the lower bound above and the `C^{1,1}`
  periodic `Ψ` of E1.
* `cep_H2_c11_cylinder_entropy`: H2 with `U ∈ C¹` with Lipschitz gradient in place of `U ∈ C²`.  The moreau envelope
  `Φ_n` is not `C²` in general, so H2 as first stated (`ContDiff ℝ 2 U`) does not apply to `U_n`.  The conclusion and
  all other hypotheses are those of `cep_H2_cylinder_entropy`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH4

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- **E2 with envelope properties.**  Same data `(J, Φ_n)` as `cep_E2_moreau_yosida`, together with: `Φ_n` is invariant
under translation by the diagonal vector, `Φ_n` is `C¹` with `n`-Lipschitz gradient, and
`Φ_n(z) ≥ (n/2) dist(z, alcove)² - C` for one constant `C` and every `n > 0`. -/
theorem cep_E2_envelope_props (a : ℝ) (ha : 0 < a) (N : ℕ) [NeZero N] :
    ∃ (J : ℝ → Ch N → Ch N) (Φn : ℝ → Ch N → ℝ), cep_Yosida a N J ∧
      (∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z) ∧
      (∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot a N z) ∧
      (∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot a N z))) ∧
      (∀ n z, 0 < n → Φn n (z + cep_diag N) = Φn n z) ∧
      (∀ n, 0 < n → ContDiff ℝ 1 (Φn n) ∧ LipschitzWith (Real.toNNReal n) (gradient (Φn n))) ∧
      (∃ C : ℝ, ∀ n z, 0 < n → n / 2 * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Φn n z) := by
  sorry

/-- **Quadratic confinement of `Φ_n + Ψ`.**  If `Ψ` is `C¹` with `L`-Lipschitz gradient and invariant under the diagonal
translation (E1), and `Φ_n ≥ (n/2) dist(·, alcove)² - C`, then for every `n ≥ L + 1` there are `c > 0` and `C'` with
`c dist(z, alcove)² - C' ≤ Φ_n z + Ψ z`. -/
theorem cep_H4_potential_conf [NeZero N] {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ)
    (hΨL : LipschitzWith L (gradient Ψ)) (hΨper : ∀ z, Ψ (z + cep_diag N) = Ψ z)
    {Φn : ℝ → Ch N → ℝ} {C : ℝ}
    (hΦlow : ∀ n z, 0 < n → n / 2 * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Φn n z) :
    ∀ n : ℝ, (L : ℝ) + 1 ≤ n → ∃ c C' : ℝ, 0 < c ∧
      ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C' ≤ Φn n z + Ψ z := by
  sorry

/-- **H2 with a `C^{1,1}` potential.**  Statement of `cep_H2_cylinder_entropy` with `hU : ContDiff ℝ 2 U` replaced by
`hU : ContDiff ℝ 1 U` and `hK : LipschitzWith K (gradient U)`. -/
theorem cep_H2_c11_cylinder_entropy [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    (hUper : ∀ z, U (z + cep_diag N) = U z)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {invβ : ℝ} (hβ : 0 < invβ) {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀)
    {Z : ℝ → Ω → Ch N}
    (hZ : cep_IsChamberSolution P ℱ W' π (Real.sqrt (2 * invβ)) (fun z => -(gradient U z)) z₀ Z)
    (hfin : cep_cylEntropy invβ U (P.map fun ω => cep_reduce (z₀ ω)) < ⊤) :
    ∀ t : ℝ, 0 ≤ t →
      cep_cylEntropy invβ U (P.map fun ω => cep_reduce (Z t ω))
        + ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) t,
            cep_cylFisher invβ U (P.map fun ω => cep_reduce (Z r ω)) : ℝ≥0∞) : EReal)
        ≤ cep_cylEntropy invβ U (P.map fun ω => cep_reduce (z₀ ω)) := by
  sorry

/-- **H4 core (entropy inequality for the limit flow `mk ∘ unrank_{σ₀} ∘ Zl`).**  The hypotheses of
`cep_H3_limit_semicontinuity` (single cyclic component, `U_n = Φ_n + Ψ`, `Z^n` the Yosida chamber flows, `Zl` their limit),
together with the extra properties of the data supplied by `cep_E2_envelope_props` and E1 (periodicity of `Φ_n`, `Ψ`; `C¹`
with Lipschitz gradient for `Φ_n`; the lower bound for `Φ_n`) and a finite initial entropy, give the entropy inequality for
the limit flow.  Route: for `n ≥ L + 1` apply `cep_H2_c11_cylinder_entropy` to `U_n` (the confinement of `Φ_n + Ψ` is
`cep_H4_potential_conf`; the finiteness of the initial cylinder entropy holds for large `n` by part (c) of H3 and `hH0`), then
combine with parts (a), (b), (c) of H3 through `liminf a_n + liminf b_n ≤ liminf (a_n + b_n) ≤ limsup c_n`. -/
theorem cep_H4_core [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ))
    (hV : cep_IsC11 D.V) (σ₀ : Equiv.Perm (Fin N))
    {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida 1 N J) {Φn : ℝ → Ch N → ℝ}
    (hΦ : ∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z)
    (hΦle : ∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot 1 N z)
    (hΦlim : ∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot 1 N z)))
    (hΦper : ∀ n z, 0 < n → Φn n (z + cep_diag N) = Φn n z)
    (hΦC : ∀ n, 0 < n → ContDiff ℝ 1 (Φn n) ∧ LipschitzWith (Real.toNNReal n) (gradient (Φn n)))
    (hΦlow : ∃ C : ℝ, ∀ n z, 0 < n → n / 2 * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Φn n z)
    {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ) (hΨL : LipschitzWith L (gradient Ψ))
    (hΨper : ∀ z, Ψ (z + cep_diag N) = Ψ z)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' (fun _ => σ₀) (Real.sqrt (2 * D.invβ))
      (fun z => -(gradient (fun w => Φn n w + Ψ w) z)) z₀ (Z n))
    {Zl : ℝ → Ω → Ch N}
    (hZl : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0))
    (hZlc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlA : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N))
    (hZlnull : ∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0)
    (hH0 : gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) 0) < ⊤) :
    ∀ t : ℝ, 0 ≤ t →
      gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) t)
        + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N
            (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) r) : ℝ≥0∞) : EReal)
        ≤ gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) 0) := by
  sorry

end HRS.MC.CepH4
