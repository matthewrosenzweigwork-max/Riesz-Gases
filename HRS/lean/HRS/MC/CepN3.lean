import Mathlib
import HRS.MC.CepN3Aux5

/-!
# Packet CEPN3: steering of the maximal solution to a contact-ready configuration

`cep_N3_steering_proof` (statement of `HRS.MC.Cepa.cep_N3_steering`, with the duplicated vocabulary of
`HRS.MC.CepN4` and `HRS.MC.CepC0.cep_IsC11`).

Route.  `CepN3Aux5.cepn3_fixed`: for a fixed permutation `σ` and strictly `σ`-ordered `y₀` there is `η₀ > 0`
such that every `ℱ₀`-event of positive probability on which `π = σ` and `‖Y₀ - y₀‖ < η₀` contains a
positive-probability `ℱ_{T'}`-event on which the solution is at time `T'` close to the target (convex path of
strictly ordered configurations, Brownian tube independent of `ℱ₀`, deterministic tube stability, exit from
compacts).  The random `(π, Y₀)` is handled by contradiction: if no `(σ, y₀)` produced a positive-probability
event, then every ball `B(y₀, η(y₀))` around a `σ`-ordered `y₀` carries `{π = σ}`-mass zero; by second
countability countably many such balls cover the `σ`-ordered configurations, so `P(π = σ) = 0` for all `σ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN3

open HRS HRS.MC.CepN4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cep_N3_steering_proof [IsProbabilityMeasure P] (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : HRS.MC.CepC0.cep_IsC11 D.V)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → Fin N → Euc 1} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → Fin N → Euc 1}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {π : Ω → Equiv.Perm (Fin N)}
    (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) (hπ0 : ∀ ω, cep_StrictlyOrdered (π ω) (Y₀ ω))
    {T' : ℝ} (hT' : 0 < T') {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ T' ∧ ∃ A : Set Ω, MeasurableSet[ℱ t₁] A ∧ 0 < P A ∧
      ∀ ω ∈ A, ((t₁ : ℝ) : WithTop ℝ) < τ ω ∧ cep_StrictlyOrdered (π ω) (Y t₁ ω) ∧
        0 < Y t₁ ω (π ω (cep_i1 hN)) 0 - Y t₁ ω (π ω (cep_i0 hN)) 0 ∧ Y t₁ ω (π ω (cep_i1 hN)) 0 - Y t₁ ω (π ω (cep_i0 hN)) 0 ≤ ε / 2 ∧
        cep_PairIsolated hN (π ω) (Y t₁ ω) (1 / (8 * (N : ℝ))) ∧
        (∀ k l : Fin N, k ≠ l → k ≠ π ω (cep_i0 hN) → k ≠ π ω (cep_i1 hN) →
          l ≠ π ω (cep_i0 hN) → l ≠ π ω (cep_i1 hN) → ∀ m : ℤ,
            1 / (8 * (N : ℝ)) ≤ |Y t₁ ω k 0 - Y t₁ ω l 0 - m|) := by
  classical
  by_contra hcon
  -- for each ordered datum, the corresponding event has probability zero
  have hclaim : ∀ (σ : Equiv.Perm (Fin N)) (y₀ : Fin N → Euc 1), cep_StrictlyOrdered σ y₀ →
      ∃ η₀ : ℝ, 0 < η₀ ∧ P {ω | π ω = σ ∧ ‖Y₀ ω - y₀‖ < η₀} = 0 := by
    intro σ y₀ h0
    obtain ⟨η₀, hη₀, hfix⟩ := cepn3_fixed hN hs hβ hV hW' hsol (π := π) hT' hε hε1 h0
    refine ⟨η₀, hη₀, ?_⟩
    by_contra hne
    have hE : MeasurableSet[ℱ 0] {ω | π ω = σ ∧ ‖Y₀ ω - y₀‖ < η₀} := by
      have hg : Continuous fun x : Fin N → Euc 1 => ‖x - y₀‖ := (continuous_id.sub continuous_const).norm
      have h2 : Measurable[ℱ 0] (fun ω => ‖Y₀ ω - y₀‖) := hg.measurable.comp (hsol.init_meas 0)
      have h3 : MeasurableSet[ℱ 0] {ω | ‖Y₀ ω - y₀‖ < η₀} := h2 measurableSet_Iio
      exact (hπ σ).inter h3
    obtain ⟨A, hAm, hAP, hA⟩ := hfix _ hE (pos_iff_ne_zero.2 hne) (fun ω hω => hω)
    exact hcon ⟨T', hT', le_rfl, A, hAm, hAP, hA⟩
  choose! η hη hηP using hclaim
  have hσ0 : ∀ σ : Equiv.Perm (Fin N), P {ω | π ω = σ} = 0 := by
    intro σ
    set S : Set (Fin N → Euc 1) := {y | cep_StrictlyOrdered σ y} with hS
    have hnhds : ∀ y ∈ S, Metric.ball y (η σ y) ∈ 𝓝[S] y := fun y hy =>
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds y (hη σ y hy))
    obtain ⟨t, hts, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hnhds
    refine measure_mono_null (t := ⋃ y ∈ t, {ω | π ω = σ ∧ ‖Y₀ ω - y‖ < η σ y}) ?_ ?_
    · intro ω hω
      have hmem : Y₀ ω ∈ S := by
        have := hπ0 ω
        rw [show π ω = σ from hω] at this
        exact this
      obtain ⟨y, hy, hy2⟩ := Set.mem_iUnion₂.1 (hcov hmem)
      refine Set.mem_iUnion₂.2 ⟨y, hy, hω, ?_⟩
      rwa [Metric.mem_ball, dist_eq_norm] at hy2
    · exact (measure_biUnion_null_iff htc).2 fun y hy => hηP σ y (hts hy)
  have hall : P Set.univ = 0 := by
    have : (Set.univ : Set Ω) = ⋃ σ : Equiv.Perm (Fin N), {ω | π ω = σ} := by
      ext ω; simp
    rw [this]
    exact measure_iUnion_null hσ0
  simp at hall

end HRS.MC.CepN3
