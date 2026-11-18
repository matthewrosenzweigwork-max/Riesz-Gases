import HRS.MC.Q714Asm

/-!
# Packet ASM (row 7.14): the frozen statements

`critical_edgeworth_proof` and `critical_edgeworth_equal_temperature_proof`: the statements of
`HRS.Sec7.critical_edgeworth` and `HRS.Sec7.critical_edgeworth_equal_temperature` (`HRS/Sections/Sec7Quench.lean`, copied
verbatim), proved from the four proved packets by the assemblies of `HRS/MC/Q714Asm.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.Asm

open HRS HRS.Sec7

variable {d : ℕ}

theorem critical_edgeworth_proof (hd : 2 ≤ d) {s β β₀ : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hne : β₀ ≠ β) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0))
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization D (P N)
      (modulatedGibbs (periodicRiesz d s) N β₀ volume) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P' Z)
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Zs : ℝ → Ω'' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m P'' Zs)
    (Kinf : TensorDual (PathSpace d m T) 3) (hKmem : Kinf ∈ projTensor (PathSpace d m T) 3)
    (hK : ∀ a : ℕ → ℝ, Tendsto a atTop atTop → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
      ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
            ∫ ω, Φ (procWin m T (a N) Z ω) ∂P') -
          (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P''| ≤ ε) :
    (∀ N, 1 ≤ N → ∀ t : ℝ, 0 ≤ t → meanEmpirical ((P N).map (X N t.toNNReal)) = volume ∧
        ∀ ω, zetaAt m (P N) (X N) t ω = etaE m (X N t.toNNReal ω) volume) ∧
    (∀ (a : ℕ → ℝ) (τ : ℝ),
      Tendsto (fun N : ℕ => a N - Real.log N / (4 * lamStar d s β) - τ) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
              ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') -
            (Real.exp (-2 * lamStar d s β * τ) / 2 *
                ∫ ω, slowTensor d s β β₀ m T (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂P'' +
              (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P'')| ≤ ε) ∧
    (∀ a : ℕ → ℝ, Tendsto a atTop atTop →
      ((∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
          |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
                ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') -
            (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P''| ≤ ε) ↔
        Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * lamStar d s β * a N)) atTop (𝓝 0)) ∧
      (Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * lamStar d s β * a N)) atTop (𝓝 0) ↔
        Tendsto (fun N : ℕ => a N - Real.log N / (4 * lamStar d s β)) atTop atTop)) := 
  assembly_critical_edgeworth_proof HRS.MC.Q714.GT.gaussian_taylor_proof
    HRS.MC.Q714.GW.gaussian_window_proof HRS.MC.Q714.HI.haar_invariance_proof
    HRS.MC.Q714.CT.cos_test_proof hd hs0 hs hβ hβ₀ hne m hm T hT D hD P X₀ W X hreal P' Z hZ P'' Zs hZs
    Kinf hKmem hK

theorem critical_edgeworth_equal_temperature_proof (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hβ : 0 < β) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0))
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization D (P N)
      (modulatedGibbs (periodicRiesz d s) N β volume) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β m P' Z)
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Zs : ℝ → Ω'' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m P'' Zs)
    (Kinf : TensorDual (PathSpace d m T) 3) (hKmem : Kinf ∈ projTensor (PathSpace d m T) 3)
    (hK : ∀ a : ℕ → ℝ, Tendsto a atTop atTop → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
      ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
            ∫ ω, Φ (procWin m T (a N) Z ω) ∂P') -
          (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P''| ≤ ε) :
    ∀ a : ℕ → ℝ, Tendsto a atTop atTop →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
              ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') -
            (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P''| ≤ ε :=
  assembly_equal_temperature_proof HRS.MC.Q714.GT.gaussian_taylor_proof
    HRS.MC.Q714.GW.gaussian_window_proof hd hs0 hs hβ m hm T hT D hD P X₀ W X hreal P' Z hZ P'' Zs hZs
    Kinf hKmem hK

end HRS.MC.Q714.Asm

end
