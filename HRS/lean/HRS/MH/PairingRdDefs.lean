import HRS.Duality.PairingExpansionRd

/-!
# Vocabulary for the proof of `HRS.Duality.pairing_expansion_rd` (Lemma 3.1 on `ℝ^d`)

Sorry-free definitions moved out of `HRS/MH/PairingRdSpec.lean` so that the proof modules do not import a statement-only
file.  See `HRS/MH/PairingRdPlan.md`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRd

open HRS HRS.Duality

variable {d N : ℕ}

/-- The cancellation-convention integrand of `Whole.convGradConvW G h` at the point `x`, as a function of `y`
(`convGradConvW G h x = ∫ y, convInt G h x y` is `rfl`). -/
abbrev convInt (G : Euc d → Euc d) (h : Euc d → ℝ) (x : Euc d) : Euc d → Euc d :=
  fun y => if ‖x - y‖ ≤ 1 / 4 then (h y - h x) • G (x - y) else h y • G (x - y)

/-- The scalar density `ψ_a(y) = ρ(y) (Mᵀ ∇f(y))_a` whose convolution with `∇g` gives the `a`-th summand of `divConvBRd`. -/
abbrev psiRd (f : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (a : Fin d) : Euc d → ℝ :=
  fun y => ρ y * Torus.matVec M.transpose (gradient f y) a

theorem convGradConvW_eq_integral_convInt (G : Euc d → Euc d) (h : Euc d → ℝ) (x : Euc d) :
    Whole.convGradConvW G h x = ∫ y, convInt G h x y := rfl

end HRS.MH.PairingRd
