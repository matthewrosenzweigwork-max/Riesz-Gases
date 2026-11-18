import HRS.MC.CepE5bAux16

/-!
# Packet CEPE5B: `E ∫_0^T (1/n)|G_n(Z^n_s)|² ds → 0` (`cep_E5b_yosida_defect_nonneg`)

Route (not the occupation-measure route of the plan, which has a gap at distances `d ≪ n^{-1/2}`): Itô's formula for the
`C²` Moreau envelope `Φ_n(z) = Φ(J_n z) + (n/2)|z - J_n z|²` (`∇Φ_n = G_n`) along `Z^n`, whose Hessian trace
satisfies `(1/n) tr D²Φ_n ≤ c₁ r ⟨z - ρ, G_n z⟩ + c₂ r + c₃/(n r²)` (pair-wise cutoff at distance `r`, the Lyapunov
functional `⟨z - ρ, G_n z⟩` being controlled uniformly in `n` by the second-moment identity of E4); with `r = n^{-1/3}`.

NOTE.  The statement `cep_E5b_yosida_defect` of `CepaSpec.lean` quantifies over all `T : ℝ`; for `T < 0` it is false
as stated (the hypotheses place no constraint on `Z^n_s` for `s < 0`, where `Z^n` may leave the alcove and then
`∫_0^T (1/n)|G_n|² = -∫_T^0 (1/n)|G_n|² → -∞`).  The theorem below is the statement with the additional hypothesis
`0 ≤ T`, which is the only case used (E5c is trivial for `T < 0`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cep_E5b_yosida_defect_nonneg [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) (hT : 0 ≤ T) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ ω, (∫ s in (0 : ℝ)..T, (1 / (n : ℝ)) * ‖(n : ℝ) • (Z n s ω - J n (Z n s ω))‖ ^ 2) ∂P)
      Filter.atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hz₀b
  have hz0m : Measurable z₀ := hz₀.mono (ℱ.le 0) le_rfl
  have hu := e5b_u_tendsto (P := P) ha hJ hz0m hz₀A hR
  obtain ⟨K₁, K₂, -, -, hbd⟩ := e5b_bound hW' hπ ha hJ hF σ' hz₀ hR hZ T hT
  have hq : Tendsto (fun n : ℕ => ((n : ℝ) ^ (1 / 3 : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hqinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) ^ (1 / 3 : ℝ))) atTop (𝓝 0) := by
    have := hq.inv_tendsto_atTop
    refine this.congr fun n => ?_
    simp [one_div]
  have hninv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hb : Tendsto (fun n : ℕ => 2 * ((1 / (n : ℝ)) * ∫ ω, e5b_Pn a N J n (z₀ ω) ∂P) +
      K₁ * (1 / (n : ℝ)) + K₂ * (1 / ((n : ℝ) ^ (1 / 3 : ℝ)))) atTop (𝓝 0) := by
    have := ((hu.const_mul 2).add (hninv.const_mul K₁)).add (hqinv.const_mul K₂)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    refine integral_nonneg fun ω => ?_
    exact intervalIntegral.integral_nonneg hT fun s _ => by positivity
  · filter_upwards [eventually_ge_atTop 8] with n hn8
    exact hbd n hn8

end HRS.MC.CepE5b
