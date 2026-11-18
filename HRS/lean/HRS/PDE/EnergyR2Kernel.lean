import HRS.PDE.Toolbox
import HRS.PDE.Convention
import HRS.PDE.KernelInputsD1

/-!
# Kernel facts used by the R2 estimate

The proof of the regime-R2 estimates (`R2Aux.r2_main`, `R2Aux.r2c_main`) uses three facts about
the periodic Riesz gradient kernel `periodicRieszGrad d s`: the symmetrized pairing identity, the
`tdist` bound, and smoothness off the origin.  They are bundled in `R2KernelFacts` so that the
dimension-dependent proofs (`d ≥ 2` and `d = 1`) are kept apart from the dimension-independent
estimate.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.R2Aux

variable {d : ℕ}

/-- The kernel facts about `periodicRieszGrad d s` used by the R2 estimates, with no dimension
hypothesis. -/
structure R2KernelFacts (d : ℕ) (s : ℝ) : Prop where
  /-- Fourier-side pairing equals the symmetrized real-space pairing
  (`rieszGrad_pairing_symmetrized`). -/
  pairing : ∀ (v : Euc d) (La : ℝ) (a : Torus d → ℝ), Torus.IsLipschitz La a →
    ∀ (n : ℕ) (w : Torus d → ℝ), Torus.IsCk 1 w → IsTrigPoly n (coeffOf w) →
      (∑' k, ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) *
          ((rieszCoeff d s k : ℝ) : ℂ)) *
          (coeffOf (fun x => a x * w x) k * conj (coeffOf w k))).re =
        (1 / 2) * ∫ p : Torus d × Torus d,
          inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) * w p.1 * w p.2 * (a p.2 - a p.1)
  /-- `|∇g(z)| ≤ C(|z|^{-s-1} + 1)` (`periodicRieszGrad_bound_tdist`). -/
  bound : ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
    ‖periodicRieszGrad d s z‖ ≤ C * (Torus.tdist z 0 ^ (-s - 1) + 1)
  /-- `∇g` is smooth away from the origin (`periodicRieszGrad_smoothOffZero`). -/
  smooth : Torus.IsSmoothOffZero (periodicRieszGrad d s)

/-- The kernel facts for `d ≥ 2`, from the existing kernel lemmas. -/
theorem r2KernelFacts_of_two_le (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    R2KernelFacts d s :=
  ⟨fun v La a ha n w hw hwt => rieszGrad_pairing_symmetrized (by omega) s hs0 hsd v La a ha n w hw hwt,
    periodicRieszGrad_bound_tdist hd hs0 hsd, periodicRieszGrad_smoothOffZero hd hs0 hsd⟩

/-- The kernel facts for `d = 1`, from the `d = 1` kernel facts of `HRS/Kernel/GradD1.lean`. -/
theorem r2KernelFacts_one (hd : d = 1) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    R2KernelFacts d s :=
  ⟨fun v La a ha n w hw hwt => rieszGrad_pairing_symmetrized (by omega) s hs0 hsd v La a ha n w hw hwt,
    periodicRieszGrad_bound_tdist_of_one_le (by omega) hs0 hsd,
    periodicRieszGrad_smoothOffZero_of_one_le (by omega) hs0 hsd⟩

end HRS.PDE.R2Aux
