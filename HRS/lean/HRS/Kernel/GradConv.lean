import HRS.Kernel.GradOp
import HRS.Kernel.GradFourier
import HRS.Kernel.GradSmooth
import HRS.Kernel.GradReg
import HRS.Kernel.GradPairing

/-!
# Kernel facts for the periodic Riesz force and the cancellation convolution

This file proves the kernel facts that `HRS/PDE/Convention.lean` and `HRS/PDE/Toolbox.lean` state
with `sorry`; every theorem below is a verbatim copy of the corresponding PDE statement (the
small local definitions `tdist`, `IsLipschitz`, `IsSmoothOffZero`, `coeffOf`, `gradRieszCoeff`,
`IsTrigPoly` are copied verbatim in `HRS/Kernel/GradBasic.lean`, namespace `HRS.KernelGrad`).
See the comment at the end of the file for the correspondence.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

/-- `∇g` is smooth away from the origin. -/
theorem periodicRieszGrad_smoothOffZero (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    IsSmoothOffZero (periodicRieszGrad d s) :=
  periodicRieszGrad_smoothOffZero' hd hs0 hsd

/-- Kernel bound in torus-distance form: `|∇g(z)| ≤ C(|z|^{-s-1} + 1)` for `z ≠ 0`
(KERN-01 `periodicRiesz_grad_bound` restated with `tdist`). -/
theorem periodicRieszGrad_bound_tdist (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      ‖periodicRieszGrad d s z‖ ≤ C * (tdist z 0 ^ (-s - 1) + 1) :=
  periodicRieszGrad_bound_tdist_aux hd hs0 hsd

/-- The cancellation convention agrees with the plain integral for `0 ≤ s < d-1` and bounded
measurable `h` (line 10092: absolute convergence; line 10096: oddness). -/
theorem convGradConv_eq_plain (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 1)
    (h : Torus d → ℝ) (hm : Measurable h) (hb : ∃ B, ∀ x, |h x| ≤ B) (x : Torus d) :
    convGradConv (periodicRieszGrad d s) h x = ∫ y, h y • periodicRieszGrad d s (x - y) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad hd hs0 (by linarith)
  obtain ⟨B, hB⟩ := hb
  exact hG.eq_plain (by linarith) hm hB x

/-- **Required kernel fact.** The convention "agrees with distributional convolution"
(lines 10099–10101): for `0 ≤ s < d` and `C¹` `h`, the Fourier coefficients of the `i`-th
component of `∇g * h` are `2πi k_i ĝ(k) ĥ(k)` (`gradRieszCoeff`).  Extends KERN-01's
`periodicRiesz_fourierCoeff`. -/
theorem convGradConv_coeff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (h : Torus d → ℝ)
    (hh : Torus.IsCk 1 h) (i : Fin d) :
    coeffOf (fun x => convGradConv (periodicRieszGrad d s) h x i) =
      gradRieszCoeff d s i (coeffOf h) := by
  funext k
  rw [coeffOf_eq_integral, coeff_convGradConv hd hs0 hsd hh k i]
  unfold gradRieszCoeff derivCoeff rieszMult
  rw [coeffOf_eq_integral]
  ring

/-- **Required kernel fact.** For `C¹` `h` the convention yields a bounded continuous vector field
(lines 10097–10099). -/
theorem convGradConv_continuous (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (h : Torus d → ℝ)
    (hh : Torus.IsCk 1 h) : Continuous (convGradConv (periodicRieszGrad d s) h) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad hd hs0 hsd
  obtain ⟨B, hB0, hB⟩ := isCk_bounded hh
  obtain ⟨L, hL0, hL⟩ := isLipschitz_of_isCk hh
  exact hG.continuous_op (isCk_continuous hh) hB hL hL0 hB0

/-- **Required kernel fact** (Lemma C.1 input, lines 12229–12233): for `h ∈ C^{m+1}`, `∇g * h` is
`C^m` with `‖∇g*h‖_{C^m} ≤ C ‖h‖_{C^{m+1}}` (the convention loses at most one derivative,
uniformly in `0 ≤ s < d`). -/
theorem convGradConv_cbNorm (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) :
    ∃ C : ℝ, ∀ h : Torus d → ℝ, Torus.IsCk (m + 1) h →
      Torus.IsCk m (convGradConv (periodicRieszGrad d s) h) ∧
        Torus.cbNorm m (convGradConv (periodicRieszGrad d s) h) ≤ C * Torus.cbNorm (m + 1) h := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad hd hs0 hsd
  obtain ⟨K, _, hK⟩ := hG.regularity m
  exact ⟨K, fun h hh => hK h (by exact_mod_cast hh)⟩

/-- **Required kernel fact.**  The Fourier-side pairing of Lemma C.4 equals the symmetrized
real-space pairing for `κ = v·∇g`. -/
theorem rieszGrad_pairing_symmetrized (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d)
    (La : ℝ) (a : Torus d → ℝ) (ha : IsLipschitz La a) (n : ℕ) (w : Torus d → ℝ)
    (hw : Torus.IsCk 1 w) (hwtrig : IsTrigPoly n (coeffOf w)) :
    (∑' k, ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) *
        (coeffOf (fun x => a x * w x) k * conj (coeffOf w k))).re =
      (1 / 2) * ∫ p : Torus d × Torus d,
        inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) * w p.1 * w p.2 * (a p.2 - a p.1) := by
  have haL : IsLipschitz (max La 0) a := fun x y =>
    (ha x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (tdist_nonneg x y))
  have haC : Continuous a := haL.continuous (le_max_right _ _)
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ x, |a x| ≤ A := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn haC.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun x => by
      have := hB x (Set.mem_univ x)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)⟩
  have hwC := isCk_continuous hw
  obtain ⟨Bw, hBw0, hBw⟩ := isCk_bounded hw
  obtain ⟨Lw, hLw0, hLw⟩ := isLipschitz_of_isCk hw
  obtain ⟨huB, huL⟩ := prod_data hA haL hA0 hBw hLw hBw0
  have huC : Continuous fun y => a y * w y := haC.mul hwC
  obtain ⟨h1, h2⟩ := fourier_side hd hs0 hsd v huC huB huL (by positivity) (by positivity) hwC hBw hLw
    hLw0 hBw0 hwtrig
  rw [h1, realspace_identity hd hs0 hsd v haC hA haL (le_max_right _ _) hA0 hwC hBw hLw hLw0 hBw0]
  have : ∫ x, a x * w x * Phi d s v w x = ∫ x, (fun y => a y * w y) x * Phi d s v w x := rfl
  rw [this, h2]
  ring

end HRS.KernelGrad

/-!
## Correspondence with the `sorry`-ed statements in `HRS/PDE`

Each theorem below (namespace `HRS.KernelGrad`) is a verbatim copy of the PDE declaration named on
the right, with `Torus.tdist`, `Torus.IsLipschitz`, `Torus.IsSmoothOffZero` replaced by the local
copies `tdist`, `IsLipschitz`, `IsSmoothOffZero` (and `coeffOf`, `gradRieszCoeff`, `IsTrigPoly`
copied from `HRS.PDE`), so that this file does not depend on `HRS.PDE.*`.

* `periodicRieszGrad_smoothOffZero`   ↔ `HRS.PDE.periodicRieszGrad_smoothOffZero` (Convention.lean)
* `periodicRieszGrad_bound_tdist`     ↔ `HRS.PDE.periodicRieszGrad_bound_tdist` (Convention.lean)
* `convGradConv_eq_plain`             ↔ `HRS.PDE.convGradConv_eq_plain` (Convention.lean)
* `convGradConv_coeff`                ↔ `HRS.PDE.convGradConv_coeff` (Convention.lean)
* `convGradConv_continuous`           ↔ `HRS.PDE.convGradConv_continuous` (Convention.lean)
* `convGradConv_cbNorm`               ↔ `HRS.PDE.convGradConv_cbNorm` (Convention.lean)
* `rieszGrad_pairing_symmetrized`     ↔ `HRS.PDE.rieszGrad_pairing_symmetrized` (Toolbox.lean)
* `periodicRieszGrad_neg_of_lt` (GradBasic.lean, `s < d` added) ↔ `HRS.PDE.periodicRieszGrad_neg`.
  The PDE statement has no hypothesis on `s`; it is not provable as stated (for parameters where
  the heat limit does not exist both sides are the same junk value `a₀`, so the claim would be
  `a₀ = -a₀`).  Adding `(hsd : s < d)` makes it provable (done here).
* `periodicRieszGrad_hasGradientAt` (GradSmooth.lean): extra result requested by the stochastic
  thread; `periodicRieszGrad d s x` is the gradient of the lifted `periodicRiesz d s` at any lift
  of `x ≠ 0`.

Helper modules: `GradBasic`, `GradOp`, `GradFourier`, `GradSmooth`, `GradReg`, `GradPairing`.
-/

end
