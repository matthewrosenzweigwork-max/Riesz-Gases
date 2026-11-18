import HRS.PDE.KernelInputsD1
import HRS.PDE.MeanFieldHolder

/-!
# The cancellation convention `B:eq:nabla-g-convolution` in its printed Hölder form

Statements only (every theorem ends in `sorry`); relocated from `HRS/SA/Drafts/SAD2.lean` after the independent review
recorded in `docs/ISSUES.md` and subsequent approval.  Row `M:prose:L10036-10126` (TeX L10089-10101).  `HRS.IsRegularMF`,
`HRS.PDE.IsRegularMFProviso` and `HRS.convGradConv` already exist; what was missing is the literal two-integral
form with the Euclidean ball cutoff and the printed well-definedness and agreement-with-distributional-convolution clauses
for Hölder densities.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS

variable {d : ℕ}

open HRS.Torus in
/-- The force `∇g * μ` of `B:eq:nabla-g-convolution` (M L10091-10093) **literally as printed**:
two separate integrals, the increment integral over the Euclidean ball `|x-y| ≤ 1/4` (here
`tdist x y`, the norm of the centred representative of `x-y`) and the far-field integral over
`|x-y| > 1/4` against `dμ(y) = ρ(y) dy`.  (`HRS.convGradConv` is the same thing with the sup-norm
cube `‖x-y‖ ≤ 1/4` and a single integral.) -/
def convGradHolder (G : Torus d → Euc d) (ρ : Torus d → ℝ) (x : Torus d) : Euc d :=
  (∫ y, if Torus.tdist x y ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else 0) +
    ∫ y, if 1 / 4 < Torus.tdist x y then ρ y • G (x - y) else 0

/-- **The cube convention equals the printed ball convention** (M L10091-10096, "the subtracted
constant contributes zero by oddness").  For a measurable odd kernel `G` with the order
`|z|^{-s-1}` bound (`KernelGrad.GoodKernel`), a bounded measurable density `ρ`, and a point `x` at
which the near-field increment integral of the printed formula converges, the printed two-integral
formula equals `HRS.convGradConv`.  The convergence hypothesis is necessary: otherwise the printed
first integral is the junk `0`. -/
theorem convGradConv_eq_convGradHolder {s C : ℝ} {G : Torus d → Euc d}
    (hG : KernelGrad.GoodKernel d s C G) {ρ : Torus d → ℝ} (hρm : Measurable ρ)
    (hρb : ∃ B, ∀ y, |ρ y| ≤ B) (x : Torus d)
    (hint : Integrable (fun y => if Torus.tdist x y ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else 0)) :
    convGradConv G ρ x = convGradHolder G ρ x := by
  sorry

/-- **Well-definedness for Hölder densities** (M L10089-10097: "defined for `μ ∈ C^{0,α}`,
`α > s+1-d` ... Near the origin, the Hölder increment makes the integrand locally integrable
precisely when `α > s+1-d`"; sufficiency direction).  For `0 ≤ s < d`, `0 < α ≤ 1`,
`α > s+1-d` and `ρ ∈ C^{0,α}` the integrand of the cancellation convolution is integrable, so
the Bochner integral in `convGradConv` is not a junk value.  (Hölder is with respect to the
torus norm, as in `MFHolder.Hol0`.) -/
theorem integrable_convGradConv_integrand_of_holder {s α : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s)
    (hsd : s < d) (hα0 : 0 < α) (hα1 : α ≤ 1) (hα : s + 1 - d < α) {ρ : Torus d → ℝ}
    (hρ : PDE.MFHolder.Hol0 α ρ) (x : Torus d) :
    Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • periodicRieszGrad d s (x - y)
      else ρ y • periodicRieszGrad d s (x - y)) := by
  sorry

/-- **Agreement with distributional convolution for Hölder densities** (M L10098-10101: "The
formula is therefore well defined and agrees with distributional convolution").  For
`0 ≤ s < d`, `0 < α ≤ 1`, `α > s+1-d` and `ρ ∈ C^{0,α}`, the Fourier coefficients of the `i`-th
component of `∇g * ρ` (cancellation convention) are `2πi k_i ĝ(k) ρ̂(k)` (`PDE.gradRieszCoeff`).
This extends `PDE.convGradConv_coeff_of_one_le` from `ρ ∈ C¹` to the Hölder class actually used
in the printed definition (needed for `s ≥ d-1`, where `C¹` is stronger than the source). -/
theorem convGradConv_coeff_of_holder {s α : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hα : s + 1 - d < α) {ρ : Torus d → ℝ}
    (hρ : PDE.MFHolder.Hol0 α ρ) (i : Fin d) :
    PDE.coeffOf (fun x => convGradConv (periodicRieszGrad d s) ρ x i) =
      PDE.gradRieszCoeff d s i (PDE.coeffOf ρ) := by
  sorry

end HRS
