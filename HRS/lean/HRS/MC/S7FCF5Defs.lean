import HRS.MC.S7FCDefs

/-!
# Vocabulary of the F5/F6 sub-packets of `field_chaos` (sorry-free)

Definitions used by the statements of `HRS/MC/S7FCF5Plan.lean` and by their proofs.  Namespace `HRS.MC.Sec7.FCF5Plan`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCF5Plan

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-! ### Vocabulary (sorry-free) -/

/-- The countable dense set of window times `{a + q : q ∈ ℚ ∩ [0,T]}` of the window `[a, a+T]`. -/
def fcf5Rat (a T : ℝ) : Set ℝ := {t | ∃ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) T ∧ t = a + q}

/-- The mode statistic `η_N^t(f) = √N (μ_N^t(f) - μ^t(f))` of a bounded measurable `f`
(`f = e_k` gives the real Fourier coefficient of `etaE r (X_t) μ^t`). -/
def fcf5Eta (R : Regime d) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (f : Torus d → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt N * (pair (empirical (X t.toNNReal ω)) f - pair (withDensityReal (R.ρ t)) f)

/-- The commutator term `N F_N^{h_f}(X_u, μ^u)` of the mode identity (F2 bounds it by `C ⟨k⟩²` for `f = e_k`). -/
def fcf5Comm (R : Regime d) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (f : Torus d → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  (N : ℝ) * modulatedEnergy (hTransport d R.D.s f) (X u.toNNReal ω) (withDensityReal (R.ρ u))

/-- The drift integrand `η^u(L_u f) - N^{-1/2} · N F^{h_f}(X_u, μ^u)` of the mode identity F3 (`S7FCPlan.lean`,
`s7_FC_F3_mode_identity`; definitionally the integrand there, see `S7FCF5PlanTie.lean`). -/
def fcf5Drift (R : Regime d) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (f : Torus d → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  fcf5Eta R X (fcGen R u f) u ω - (Real.sqrt N)⁻¹ * fcf5Comm R X f u ω

/-- The supremum over the countable window times of the `E_r`-norm of `η_N^t = √N(μ_N^t - μ^t)`.  Measurable
(countable supremum of measurable functions) and, for a continuous window, `≥ ‖windowFluc‖`. -/
def fcf5Shat (R : Regime d) (r a T : ℝ) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t ∈ fcf5Rat a T, ‖etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t))‖ₑ

/-- `Z_r = ∑_k ⟨k⟩^{4-2r}` (finite for `r = 2d+6`: `2r - 4 = 4d + 8 > d`). -/
def fcf5Z (d : ℕ) (r : ℝ) : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (4 - 2 * r)

/-- The realisation hypothesis of the packets F1-F6, bundled (a reducible abbreviation of the `PreparedRealization`
hypothesis written out in `S7FCPlan.lean`). -/
abbrev FCPrepared (R : Regime d) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) : Prop :=
  PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X

end HRS.MC.Sec7.FCF5Plan

end
