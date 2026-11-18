import HRS.Whole.Basic

/-!
# THM core (abstract form): definitions only (no theorems)

Abstract setting of the constrained strict-convexity route of `HRS/MS/ThermalSpecPlan.md` for `thermalDensity_spec`
(`K = g`, `r = γ` = the Gaussian reference density) and `logThermalDensity_spec` (`K = K̃`, `r = γ̄`).
There is no confinement `V` in the abstract form: `G(ρ) = β⁻¹ H(ρ | r) + ½ E_K(ρ)`.

All integrals are Bochner integrals, so each statement using these definitions carries explicit integrability
hypotheses where a junk value `0` would otherwise be possible (`ThmSetting.k2` is stated only for `f` with
absolutely integrable energy integrand).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- Relative entropy `∫ l log (l / ν)` of densities (Bochner integral; meaningful when the integrand is integrable). -/
def relEnt (l ν : Euc d → ℝ) : ℝ := ∫ x, l x * Real.log (l x / ν x)

/-- The pairing energy `∬ K(x,y) f(x) h(y) dx dy` (iterated Bochner integral). -/
def pairE (K : Euc d → Euc d → ℝ) (f h : Euc d → ℝ) : ℝ := ∫ x, ∫ y, K x y * f x * h y

/-- The reduced free energy `G(ρ) = β⁻¹ H(ρ | r) + ½ E_K(ρ)`. -/
def Gfun (K : Euc d → Euc d → ℝ) (r : Euc d → ℝ) (β : ℝ) (ρ : Euc d → ℝ) : ℝ :=
  β⁻¹ * relEnt ρ r + (1 / 2) * pairE K ρ ρ

/-- The Euler map `T μ = r e^{-β K * μ} / ∫ r e^{-β K * μ}`. -/
def Tmap (K : Euc d → Euc d → ℝ) (r : Euc d → ℝ) (β : ℝ) (μ : Euc d → ℝ) (x : Euc d) : ℝ :=
  r x * Real.exp (-β * ∫ y, K x y * μ y) / ∫ z, r z * Real.exp (-β * ∫ y, K z y * μ y)

/-- The constrained class `C_M = {ρ probability density, ρ ≤ M r everywhere}`. -/
def Cset (r : Euc d → ℝ) (M : ℝ) : Set (Euc d → ℝ) :=
  {ρ | HRS.Whole.IsProbDensity ρ ∧ ∀ x, ρ x ≤ M * r x}

/-- Standing hypotheses of the abstract setting.  (K1) `K * r` is bounded by `B` and integrable pointwise;
(K2) the energy is nonnegative on mass-zero differences whose energy integrand is absolutely integrable. -/
structure ThmSetting (K : Euc d → Euc d → ℝ) (r : Euc d → ℝ) (B : ℝ) : Prop where
  meas : Measurable (Function.uncurry K)
  symm : ∀ x y, K x y = K y x
  nonneg : ∀ x y, 0 ≤ K x y
  r_prob : HRS.Whole.IsProbDensity r
  r_pos : ∀ x, 0 < r x
  k1 : ∀ x, Integrable (fun y => K x y * r y) ∧ ∫ y, K x y * r y ≤ B
  k2 : ∀ f : Euc d → ℝ, Integrable f →
    Integrable (fun p : Euc d × Euc d => |K p.1 p.2 * f p.1 * f p.2|)
      ((volume : Measure (Euc d)).prod volume) →
    ∫ x, f x = 0 → 0 ≤ pairE K f f

end HRS.MS.Thm

end
