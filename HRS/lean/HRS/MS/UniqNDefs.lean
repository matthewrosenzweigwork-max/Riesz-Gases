import HRS.Whole.AppendixALemmas

/-!
# Common definition for the nonlocal-term estimates of S.A.33 (`uloc_uniqueness`)

`nMain D ρ' f ψ'` is the third term of `HRS.Whole.forwardPairing D ρ t σ f ψ'` with `ρ' = ρ (t - σ)`, i.e.
`- ∑_{i,j} M_{ji} ∫ f ∂_j(ρ' · (g * ∂_iψ'))`, written for a test function `ψ'` (here `ς f`) and a "solution" `f`.
It is the quantity bounded in each regime of the energy estimate (packets N1–N4, route in `UniqPlan.md`).
-/

noncomputable section

open MeasureTheory

namespace HRS.MS.UniqNDefs

open HRS.Whole HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- The nonlocal term of `forwardPairing` for density `ρ'`, solution `f`, test function `ψ'`. -/
def nMain (D : WholeDyn d) (ρ' : Euc d → ℝ) (f ψ' : Euc d → ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, D.M j i *
      ∫ x, f x * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ' y) x
        (EuclideanSpace.single j (1 : ℝ))

/-- `forwardPairing` splits as diffusion, transport and `- nMain`. -/
theorem forwardPairing_eq (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t σ : ℝ) (z ψ : Euc d → ℝ) :
    forwardPairing D ρ t σ z ψ =
      D.invβ * (∫ x, z x * Laplacian.laplacian ψ x) -
        (∫ x, z x * ∑ i : Fin d, fderiv ℝ (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) x
          (EuclideanSpace.single i (1 : ℝ))) - nMain D (ρ (t - σ)) z ψ := rfl

end HRS.MS.UniqNDefs
