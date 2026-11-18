import HRS.Whole.Basic

/-!
# CoercLower: definitions shared by the packets (no unproved statements); see `HRS/MH/CoercLowerPlan.md`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- The Gaussian `x ↦ exp(-t‖x‖²)`. -/
def gaussK (t : ℝ) (x : Euc d) : ℝ := Real.exp (-t * ‖x‖ ^ 2)

/-- `∬ h(x-y) ρ(x) ρ(y) dx dy`, written as `∫ ρ(x) (h*ρ)(x) dx`. -/
def energyDens (h ρ : Euc d → ℝ) : ℝ := ∫ x, ρ x * HRS.Whole.convFun h ρ x

/-- The quadratic form of the plan (diagonal terms included). -/
def Qform (h : Euc d → ℝ) (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, h (X i - X j) - (2 / (N : ℝ)) * ∑ i, HRS.Whole.convFun h ρ (X i) + energyDens h ρ

/-- `K` is a dominating kernel for `ρ`: `K*ρ` is finite everywhere and `ρ (K*ρ)` is integrable. -/
def DomK (K ρ : Euc d → ℝ) : Prop :=
  (∀ x, Integrable (fun y => K (x - y) * ρ y)) ∧ Integrable (fun x => ρ x * HRS.Whole.convFun K ρ x)

/-- The function `u` of Step 1: `u(z) = N⁻¹ ∑_i e^{-2t‖x_i-z‖²} - ∫ e^{-2t‖y-z‖²} ρ(y) dy`. -/
def gaussU (t : ℝ) (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ) (z : Euc d) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, gaussK (2 * t) (X i - z) - ∫ y, gaussK (2 * t) (y - z) * ρ y

/-- Truncated Gamma-representation kernel (`s > 0`): `Γ(s/2)⁻¹ ∫_0^T t^{s/2-1} e^{-t‖x‖²} dt`. -/
def gTpos (s T : ℝ) (x : Euc d) : ℝ :=
  (1 / Real.Gamma (s / 2)) * ∫ t in Set.Ioc (0 : ℝ) T, t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2)

/-- The tail `fT = g - gT` (`s > 0`), defined on all of `ℝ^d` (junk value `-gT(0)` at `0`). -/
def fTpos (d : ℕ) (s T : ℝ) (x : Euc d) : ℝ := HRS.Whole.rieszKernel d s x - gTpos s T x

/-- Truncated Frullani kernel (`s = 0`): `½ ∫_0^T (e^{-t‖x‖²} - e^{-t}) dt/t`. -/
def gTlog (T : ℝ) (x : Euc d) : ℝ :=
  (1 / 2) * ∫ t in Set.Ioc (0 : ℝ) T, (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t

/-- The tail `fT = g - gT` (`s = 0`). -/
def fTlog (d : ℕ) (T : ℝ) (x : Euc d) : ℝ := HRS.Whole.rieszKernel d 0 x - gTlog T x

/-- `E_T = ∫_T^∞ e^{-t} dt/t`. -/
def Etail (T : ℝ) : ℝ := ∫ t in Set.Ioi T, Real.exp (-t) / t

/-- `φ_T(x) = ½ ∫_T^∞ e^{-t‖x‖²} dt/t` (junk `0` at `x = 0`). -/
def phiLog (T : ℝ) (x : Euc d) : ℝ := (1 / 2) * ∫ t in Set.Ioi T, Real.exp (-t * ‖x‖ ^ 2) / t

/-- The constant for `s > 0`: `C(d,s) = 1/(s Γ(s/2)) + π^{d/2}/Γ(s/2) · 2/(d-s)`. -/
def Cpos (d : ℕ) (s : ℝ) : ℝ :=
  1 / (s * Real.Gamma (s / 2)) + Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * (2 / ((d : ℝ) - s))

end HRS.MH.CoercLower
