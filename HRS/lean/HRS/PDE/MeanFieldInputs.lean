import HRS.PDE.MeanFieldDefs
import HRS.PDE.Hadamard
import HRS.PDE.MeanFieldKernelD1
import HRS.PDE.MeanFieldGlobal

/-!
# Named analytic inputs of package MF-01

Each `sorry` below is a named, still-open input of the MF-01 proofs; none is an accepted result.
A target of `HRS/PDE/MeanField.lean` whose proof uses one of them is accepted only once the input
is proved (check with `#print axioms`).  Plan: `HRS/PDE/MeanFieldPlan.md`, §0.3.

* (I1) `MFKernelFacts d s`: the kernel facts used by the thermal and mean-field arguments.
  Proved for `2 ≤ d` from KERN-01 (`mfKernelFacts_of_two`); the case `d = 1` (allowed by
  Proposition 5.1, `d ≥ 1`, TeX L5772) needs the one-dimensional kernel facts
  (`mfKernelFacts_one`, owner: kernel package).
* (I3) `mf_apriori_bound`: the time-uniform two-sided `L^∞` and `H^{m₁}` bounds of Proposition 5.1
  (TeX L5793–5814: paraproduct flux estimate, Nash / Lévy-kernel maximum principle, Volterra
  iteration, LaSalle-type lower bound).
* (I6) removed: the symmetrisation identity for the interaction pairing was stated here for merely
  continuous `ρ`, which is false in general for `s ≥ d − 1` (`convGradConv` then takes its junk
  value); the correct version, for `ρ ∈ C¹`, is proved as `MFPairing.interactionPairing_eq_of_isCk`
  (`HRS/PDE/MeanFieldPairing.lean`).
* (I7) removed: proved as `MFThermalRegB.thermal_memSobolev_general` (`HRS/PDE/MeanFieldThermalRegB.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFInputs

variable {d : ℕ}

/-- (I1) The kernel facts used by MF-01: `g ∈ L¹`, `ĝ = rieszCoeff`, `g` bounded below, and
nonnegativity of the zero-mass interaction form `∑ ĝ(k)|c(k)|²`. -/
structure MFKernelFacts (d : ℕ) (s : ℝ) : Prop where
  integrable : Integrable (periodicRiesz d s)
  fourierCoeff : ∀ k : Lattice d, Torus.funFourierCoeff (fun x => (periodicRiesz d s x : ℂ)) k =
    (rieszCoeff d s k : ℂ)
  bddBelow : ∃ B : ℝ, ∀ x, -B ≤ periodicRiesz d s x
  energy_nonneg : ∀ c : Coeff d, MemHs 0 c → 0 ≤ (∑' k, (rieszCoeff d s k : ℂ) * ‖c k‖ ^ 2).re

/-- (I1) for `2 ≤ d`, from the KERN-01 facts. -/
theorem mfKernelFacts_of_two (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    MFKernelFacts d s := by
  refine ⟨(integral_periodicRiesz hd hs0 hsd).1, periodicRiesz_fourierCoeff hd hs0 hsd,
    periodicRiesz_ge hd hs0 hsd, fun c _ => ?_⟩
  have hnn : ∀ k : Lattice d, 0 ≤ rieszCoeff d s k * ‖c k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · simp [rieszCoeff, hk]
    · exact mul_nonneg (rieszCoeff_pos hd hs0 hsd k hk).le (sq_nonneg _)
  have : ∑' k, (rieszCoeff d s k : ℂ) * (‖c k‖ : ℂ) ^ 2 =
      ((∑' k, rieszCoeff d s k * ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    push_cast
    rfl
  simpa [this] using tsum_nonneg hnn

/-- (I1) for `d = 1` (open: the one-dimensional kernel facts are not yet in the project). -/
theorem mfKernelFacts_one (hd : d = 1) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    MFKernelFacts d s := by
  subst hd
  have hd1 : 1 ≤ (1 : ℕ) := le_rfl
  have hs1 : s < 1 := by simpa using hsd
  refine ⟨(integral_periodicRiesz_d1 hs0 hs1).1, periodicRiesz_fourierCoeff_d1 hs0 hs1,
    periodicRiesz_ge_of_one_le hd1 hs0 hsd, fun c _ => ?_⟩
  have hnn : ∀ k : Lattice 1, 0 ≤ rieszCoeff 1 s k * ‖c k‖ ^ 2 := fun k => by
    by_cases hk : k = 0
    · simp [rieszCoeff, hk]
    · exact mul_nonneg (rieszCoeff_pos' hd1 hs0 hsd k hk).le (sq_nonneg _)
  have : ∑' k, (rieszCoeff 1 s k : ℂ) * (‖c k‖ : ℂ) ^ 2 =
      ((∑' k, rieszCoeff 1 s k * ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    push_cast
    rfl
  simpa [this] using tsum_nonneg hnn

/-- (I3) The a priori bounds of Proposition 5.1 (TeX L5793–5814): for every solution in
`C([0,∞);H^K)` and `m₁ ∈ (d/2+1, K]`, uniformly in `t ≥ 0` and `β ∈ [β₋,β₊]`, two-sided bounds
`c ≤ ρ^t ≤ C` and `‖ρ^t‖_{H^{m₁}} ≤ C`. -/
theorem mf_apriori_bound (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (m₁ : ℝ) (hm₁ : (d : ℝ) / 2 + 1 < m₁) (hm₁K : m₁ ≤ K) :
    ∃ c C : ℝ, 0 < c ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρc : ℝ → Coeff d,
      IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc → ∀ t, 0 ≤ t →
        (∀ x, c ≤ mfPath ρc t x ∧ mfPath ρc t x ≤ C) ∧ hsNorm m₁ (ρc t) ≤ C := by
  exact MFGlobal.mf_apriori_bound hd s βm βp K V ρ₀ H m₁ hm₁ hm₁K

end HRS.PDE.MFInputs
