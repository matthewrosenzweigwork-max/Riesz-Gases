import HRS.MD.EQ29Vocab

/-!
# EQ-INTERP packet: the statements of the three intermediate packets used by `eq_interp_assembly`, as `Prop`-valued definitions

Verbatim copies of the statements of `HRS.MD.EQ29.eq_strong_moment`, `HRS.MD.EQ29.eq_gauss_lift`, `HRS.MD.EQ29.eq_flow_exists`
(`HRS/MD/EQ29Spec.lean`), so that the assembly of `HRS/MD/EQInterpMain.lean` does not import the (heavy) proofs of these packets.  The tie file
`HRS/MD/EQInterpTie.lean` checks that `eq_interp_assembly_proof` has exactly the type of the spec statement, i.e. that these definitions unfold to the
spec statements; the proved theorems `eq_strong_moment_proof`, `eq_gauss_lift_proof`, `eq_flow_exists_proof` have these types by their own ties.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MD

namespace EQInterp

open HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQ29

/-- Statement of `eq_strong_moment`. -/
def StrongMomentStmt (d : ℕ) : Prop :=
  ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m q : ℝ) (hq : (d : ℝ) / 2 + 1 < q) (hqm : q < m) (T : ℝ) (hT : 0 ≤ T),
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      (∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (u + T) X₀ W X →
          ∫⁻ ω, ⨆ t ∈ ratTimes u T, coordEnergy q (fun k => NegSobolev.fourierCoeff
              (zetaE m (P.map (X t.toNNReal)) (X t.toNNReal ω)) k) ∂P ≤ ENNReal.ofReal C) ∧
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, coordEnergy q (fun k => NegSobolev.fourierCoeff (Z t ω) k) ∂P' ≤
          ENNReal.ofReal C

/-- Statement of `eq_gauss_lift`. -/
def GaussLiftStmt (d : ℕ) : Prop :=
  ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ) (m m₁ : ℝ) (hm : (d : ℝ) / 2 < m)
    (hmm₁ : m ≤ m₁)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z),
    IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m₁ (fun t ω => NegSobolev.embed m₁ (Z t ω))

/-- Statement of `eq_flow_exists`. -/
def FlowExistsStmt (d : ℕ) : Prop :=
  ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    (H : ℝ) (hH : 0 ≤ H),
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X

end EQInterp

end MD

end HRS
