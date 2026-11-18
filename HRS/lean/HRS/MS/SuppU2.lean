import HRS.MS.SuppU2Aux13

/-!
# U2: proof of the frozen statement `HRS.Whole.far_derivatives` (S4.10)

Supplement Lemma S4.10: far-field derivatives of the nonlocal term `∇g * h` and `div g * (ρ Mᵀ ∇f)`.
Proof: differentiation under the integral with the derivatives on `h` (domination by Peetre's
inequality), and, for the decay of `D^j`, the near/far split of the supplement proof with the
radial cutoff `ν(y/R)`: the far part `ν(·/R) h` has the derivatives on `h` (tails of `h`), the near
part has them on the kernel (homogeneity bounds `‖D^j κ(z)‖ ≤ C ‖z‖^{-(s+1)-j}`).
-/

noncomputable section

namespace HRS.Whole

theorem far_derivatives_proof : type_of% @HRS.Whole.far_derivatives := by
  intro d hd s hs0 hsd k L hL
  exact ⟨u2_partA hd s hs0 hsd k L hL, fun M Λρ => u2_partB hd s hs0 hsd k L hL M Λρ⟩

end HRS.Whole
