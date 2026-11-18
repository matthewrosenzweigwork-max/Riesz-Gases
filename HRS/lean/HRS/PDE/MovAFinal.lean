import HRS.PDE.MovAAux23

/-!
# MOVA: relocated proofs of MovSpec1 packets 2 and 7, and the closure of packet 11

* `movT_traj_bounds_proof` (packet 2): statement verbatim, tied to `movT_traj_bounds`.
* Packet 7 `movT_srcReg_decomp` is **false as written for `T = 0`** (the field `IsC12Test.time_deriv` is vacuous on
  `Ioo 0 0`, so `ρt 0` is an arbitrary continuous function and the one-body terms `-ψ_t + E_Q ψ_t` of `S^M` do not
  tend to zero with `‖g - g_M‖_{L¹}`; counterexample: `ρ ≡ 1`, `V = 0`, `ρt 0 = cos(2π x₁)`).  It is proved here
  for `0 < T` as `movT_srcReg_decomp_proof_pos` (extra hypothesis `0 < T`; the mean-field equation then holds on
  `[0,T]` pointwise, `mova_pde_pointwise`).
* Packet 11 `movT_source_exp_uniform` is true for all `T`; `movT_source_exp_uniform_proof'` proves it without
  extra hypotheses (case `0 < T` through `movsx_source_exp_uniform_of` and packets 2, 7; case `T = 0` through
  `mova_source_exp_uniform_zero`, case `T < 0` vacuous).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movT_traj_bounds_proof {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (h : MovTraj D T ρ) :
    ∃ c₀ Lu : ℝ, 0 < c₀ ∧ 0 < Lu ∧ (∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x) ∧
      ∀ r ∈ Set.Icc 0 T, IsLipschitzVF Lu (mfeTransport D (ρ r)) :=
  mova_traj_bounds h

example := (@movT_traj_bounds_proof : type_of% @HRS.movT_traj_bounds)

/-- `movT_srcReg_decomp` with the extra hypothesis `0 < T` (the statement is false for `T = 0`). -/
theorem movT_srcReg_decomp_proof_pos (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hT : 0 < T) :
    ∃ Cι : ℝ, 0 ≤ Cι ∧ ∀ M : ℝ, 0 ≤ M → ∀ r ∈ Set.Icc 0 T,
      (∀ X : Config d N, |movT_srcReg D N M ρ ρt r X -
          (-(D.invβ⁻¹ * N) * (movT_commReg D N M (ρ r) X -
            ∫ Y, movT_commReg D N M (ρ r) Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)))| ≤
        Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|) ∧
      ∀ L : ℝ, IsLipschitzVF L (mfeTransport D (ρ r)) →
        IsLipschitzVF (L + Cι * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|)
          (movT_uReg D M (ρ r)) :=
  mova_srcReg_decomp_pos hN h hρt hT

theorem movT_source_exp_uniform_proof' (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) :
    ∃ l C M₀ : ℝ, 0 < l ∧ ∀ M : ℝ, M₀ ≤ M → ∀ r ∈ Set.Icc 0 T,
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt r X|))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp C) := by
  rcases lt_trichotomy 0 T with hT | hT | hT
  · exact movsx_source_exp_uniform_of hN htr (movT_srcReg_decomp_proof_pos hN htr hρt hT)
      (movT_traj_bounds_proof htr)
  · subst hT
    exact mova_source_exp_uniform_zero hN htr hρt
  · exact ⟨1, 0, 0, one_pos, fun M _ r hr => absurd (hr.1.trans hr.2) (not_le.2 hT)⟩

example := (@movT_source_exp_uniform_proof' : type_of% @HRS.movT_source_exp_uniform)

end HRS
