import HRS.ME.CritDefs
import HRS.ME.Mode417
import HRS.ME.Fourier417B

/-!
# Chunk E, row 2.10 path clauses: the uniform-in-`β` inputs of Proposition 4.17 (definitions, sorry-free)

The frozen `HRS.Main.critical_centered_path` has one constant `C` chosen before `β ∈ [βm,βp]`, whereas the proved row 4.17 has
`C` chosen after `β` and the thermal density.  Row 4.17 factors through two constant-producing lemmas of Chunk E, both proved
for fixed `β`:

* `fourier_coeff_decay_proof` (`HRS/ME/Fourier417B.lean`), the decay of the Fourier coefficients of the equilibrium semigroup
  applied to a normalised mode;
* `mode_package_proof` (`HRS/ME/Mode417.lean`), the decomposition of `√N/2 · (centered quadratic statistic)` into a Lyons-Zheng
  test function, a closed-generator part and a remainder.

All the other constants of the proof (`mode_window_bound_proof`, the Lyons-Zheng constant, the summation over modes) are
independent of `β`, or depend on it only through `β⁻¹ ≤ βm⁻¹`.  The three definitions below are the statements of these two lemmas
and of `mode_forcing_bound_proof` with the constant chosen before `β ∈ [βm,βp]` (at the critical exponent `s = d/2`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Crit

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- `fourier_coeff_decay_proof` (`p = 9 d + 82`) at `s = d/2` with `C, c` chosen before `β ∈ [βm, βp]` and the thermal density. -/
def UnifDecay (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (V : Torus d → ℝ) (βm βp : ℝ) (hβm : 0 < βm) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
    ∀ (m : ℝ) (j : NonzeroLattice d) (v : ℝ), 0 ≤ v →
      Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ (9 * d + 82) *
        (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
            (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
          |Torus.funRealCoeff (PDE.equilibriumGen d ((d : ℝ) / 2) ρβ β⁻¹
            (PDE.equilibriumSemigroup (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|)) ∧
      ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (9 * d + 82) *
        (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
            (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
          |Torus.funRealCoeff (PDE.equilibriumGen d ((d : ℝ) / 2) ρβ β⁻¹
            (PDE.equilibriumSemigroup (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|) ≤
        C * Lattice.jp j.1 ^ (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ)) * Real.exp (-c * v)

/-- `mode_package_proof` at `s = d/2` with the constant chosen before `β ∈ [βm, βp]` and the thermal density. -/
def UnifModePackage (d : ℕ) (hd : 2 ≤ d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
    ∀ (N : ℕ), 2 ≤ N → ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      ∃ F G E : Config d N → ℝ,
        Measurable F ∧ Measurable G ∧ Measurable E ∧
        IsLZTest (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) F ∧
        ContDiffOn ℝ 1 (configLift (fun _ => F) 0) (coverFree d N) ∧
        MD.DOM.IsInClosedGenerator d ((d : ℝ) / 2) V β (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) F G ∧
        ∫ Y, F Y ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) = 0 ∧
        (∀ X : Config d N, X ∉ collisionSet d N →
          Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β)
              (quadStat (hTransport d ((d : ℝ) / 2) f) (withDensityReal ρβ)) X = -G X + E X) ∧
        ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ENNReal.ofReal (configGradSq F Y) ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N)

/-- `mode_forcing_bound_proof` at `s = d/2` with `C` chosen before `β ∈ [βm, βp]` and the thermal density (`c`, `T` fixed first). -/
def UnifModeForcing (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (V : Torus d → ℝ) (βm βp : ℝ)
    (hβm : 0 < βm) (c T : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
    ∀ {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a)
      (hflow : IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X)
      (l : NonzeroLattice d) (Γ : ℝ) (hΓ : 0 ≤ Γ) (γ γ' : ℝ → ℝ)
      (hγ : ∀ x, 0 ≤ x → HasDerivWithinAt γ (γ' x) (Set.Ici 0) x) (hγ' : ContinuousOn γ' (Set.Ici 0))
      (hbd : ∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧ |γ' v| ≤ Γ * Real.exp (-c * v)),
      ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
              forcingStat ((d : ℝ) / 2) V β ρβ (Torus.realMode l) (X r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (C * Γ ^ 2 * Lattice.jp l.1 ^ (2 * (8 * d + 80)) / N)

end HRS.ME.Crit

end
