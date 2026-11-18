import HRS.Energy.Modulated

/-!
# HRS.Energy.Pressure — Proposition 5.5 (perturbed partition functions)

Proposition 5.5 `N:prop:pressure` (main paper, source lines 6118-6137; context 6110-6117).

Representation decisions (recorded in `docs/ISSUES.md` §H):
* `|log K^{g-θh}_{N,β}(μ)| ≤ C N δ_N` is stated as two-sided bounds on the `lintegral`
  `∫⁻ e^{-βN F_N^{g-θh}} dμ^{⊗N}`, so finiteness and positivity are part of the conclusion
  (no junk `log 0` or Bochner value 0).
* `log E_Q[e^{θ₀N|F_N^h|}] ≤ C N δ_N` is a `lintegral` bound against `Q = modulatedGibbs g N β μ`.
* `E_f[N|F_N^h|] ≤ C(H(f | Q) + Nδ_N)` is stated for every probability measure `ν` on configurations
  with finite relative entropy `relEntropy ν Q` (Mathlib `klDiv`).
* "Shrinking θ₀ is allowed between the two lines": two parameters `θ₀`, `θ₁`.
* "The constants are uniform for backgrounds in a bounded smooth positive family": the constants are
  chosen before the density `ρ`, depending only on a lower bound `c₀` and bounds `Λ k` for every
  `C^k` norm; a fixed smooth positive background is the special case of a one-element family.
* `w = g + c_*` with any `c_*` such that `w ≥ 1` off zero (the source fixes one such `c_*`).
* The pair kernel `h` is assumed measurable (implicit in the source's integrals).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS

variable {d : ℕ}

-- `perturbed_pressure` (Proposition 5.5, the statement specified above) is stated and proved in
-- `HRS/Energy/PressureProof.lean`: its proof uses Lemma 5.7 (`HRS/Energy/WeakReference.lean`), which
-- imports this file.

end HRS
