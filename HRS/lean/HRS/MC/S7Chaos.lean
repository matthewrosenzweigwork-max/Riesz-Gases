import HRS.Main.Headline
import HRS.Sections.Sec3
import HRS.MC.Sec7Vocab
import HRS.Prob.Gaussian

/-!
# Proposition 7.18 (`M:E:prop:chaos`): non-tightness and absence of a square-mean limit

Statements only (every theorem ends in `sorry`); relocated from `HRS/SA/Drafts/SAD1.lean` after the independent review
recorded in `docs/ISSUES.md` and subsequent approval.  TeX L9782-9820.  Displays 1-6 are stated elsewhere
(`HRS.chaos_tendsto/_moments/_basis_independent`; the plan statements `s7_E1` ... `s7_E5` of `HRS/MC/Sec7Spec.lean`).
Not stated anywhere else:

* `chaos_laws_not_tight`: the sentence "In particular its laws are not tight" (`E:eq:nontight` is stated only as
  `P(|Q_ε| > R) → 1`);
* `chaos_no_L2_limit`: the last sentence, "No instantaneous Wick quadratic commutator obtained by these cutoffs exists in
  square mean at or above `d/2`, even when tested against this single smooth nonconstant `φ`".

The hypotheses are exactly those of `s7_E5_not_tight`.  RESTRICTION (recorded in ISSUES): both statements use the
correlated representation (a Gaussian field with covariance `C` and kernel `H`, `s7_GaussData`), not the printed
`E:eq:Qepsilon` (iid `G`, `A = C^{1/2} H C^{1/2}`); the law of `Q_ε` is the same, but the bridge lemma is not stated, so
row 7.18 stays `partial`.  The statements are over every sequence `ε_n ↓ 0`, which implies the printed continuum form.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS

open HRS.MC.Sec7

variable {d : ℕ}

/-- (b1) Proposition 7.18, "In particular its laws are not tight": for `d/2 ≤ s < d`, along EVERY sequence
`ε_n ↓ 0` the laws `Law(Q_{ε_n})` on `ℝ` do not form a tight family.  (Follows from `E:eq:nontight`: for every `R`,
`P(|Q_ε| ≤ R) → 0`, so no compact set carries mass `≥ 1/2` of all the laws.) -/
theorem chaos_laws_not_tight (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ) (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ IsTightMeasureSet (Set.range fun n : ℕ => P.map (Q (ε n))) := by
  sorry

/-- (b2) Proposition 7.18, last sentence: for `d/2 ≤ s < d` there is no limit in square mean of the cut-off
quadratic chaoses: for every sequence `ε_n ↓ 0` there is no (a.e. measurable) `Q₀` with
`E|Q_{ε_n} - Q₀|² → 0`.  (`φ` is a single smooth nonconstant test.  Follows from `E:eq:variance-asymptotic`:
`‖Q_ε‖_{L²} = √Var Q_ε → ∞`, while an `L²` limit would force boundedness.) -/
theorem chaos_no_L2_limit (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ) (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ ∃ Q₀ : Ω → ℝ, AEMeasurable Q₀ P ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ‖Q (ε n) ω - Q₀ ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  sorry

end HRS
