import HRS.MS.TiltAux14
import HRS.MS.MovThermAux1
import HRS.MS.S21F_D00

/-!
# S21F, packet R26-T3.D02: reference data of a nonempty trajectory class

For `δ ≤ 1/2` and a `Trajectory p δ`: `0 < c₁`, `0 < C₁`, every `ρ t` (`t ≥ 0`) is a strictly positive probability density, and the
initial density `ρ 0 = (1+εψ)ρ_β` has `TcRef` data at every finite order.  Route: `mv0_rho_eq` (`ρ_β = thermalDensity`), the
`C_b` bound `|εψ| ≤ δ ≤ 1/2` (`s48_cbu_bound`, the oscillator part of the smallness is nonnegative), and `s47_hall` (merged).
Positivity of `C₁` and of `ρ t` comes from `C₁⁻¹ρ_β ≤ ρ t ≤ C₁ρ_β`, `ρ_β > 0`, and `∫ρ t = 1`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem r26t3_reference_data (p : Parameters) (δ : ℝ) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    0 < p.c₁ ∧ 0 < p.C₁ ∧
    (∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (R.ρ t) ∧ (∀ x, 0 < R.ρ t x)) ∧
    (∀ n : ℕ, ∃ M c S : ℝ, 0 < c ∧
      HRS.MS.TcDefs.TcRef p.d (R.ρ 0) M c S n) := by
  have hd := p.hd
  have hd0 : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
  have hsd : p.s < p.d := by have := p.hs; linarith
  have hρβ : R.ρβ = thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq hd p.hs0 hsd p.ha p.hβ R.thermal
  have hA := R.admissible
  have hRes := R.resulting
  have hosc : 0 ≤ oscNorm (102 * (p.d : ℝ) + 1020) (fun x => R.ε * Real.sqrt (R.ρβ x) * R.ψ x) :=
    Real.sqrt_nonneg _
  have hcb : cbNorm (100 * p.d + 1001) (fun x => R.ε * R.ψ x) ≤ δ := by
    have := hA.small
    linarith
  have hcb0 := HRS.MS.S48.s48_cbu_bound hA.smooth hA.compactSupport R.ε δ (100 * p.d + 1001) hcb 0
    (Nat.zero_le _)
  have htilt : IsTiltData p.d p.s p.a p.β R.ψ R.ε :=
    ⟨hA.smooth, hA.compactSupport, by rw [← hρβ]; exact hA.meanZero, fun x => by
      have := hcb0 x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      linarith⟩
  have hU0 : HRS.MS.S48.UnifRef p.d p.s p.a p.β δ (R.ρ 0) :=
    Or.inr ⟨R.ε, R.ψ, htilt, hcb, by rw [hRes.init, hρβ]⟩
  have hUβ : HRS.MS.S48.UnifRef p.d p.s p.a p.β δ R.ρβ := Or.inl hρβ
  obtain ⟨c, M₀, hc, hall⟩ := S47.s47_hall hd p.hs0 hsd p.ha p.hβ hU0
  obtain ⟨cβ, Mβ, hcβ, hallβ⟩ := S47.s47_hall hd p.hs0 hsd p.ha p.hβ hUβ
  obtain ⟨Sβ, hSβ⟩ := hallβ 0
  have hβpos : ∀ x, 0 < R.ρβ x := hSβ.pos
  have hdens : ∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (R.ρ t) := fun t ht =>
    (hRes.global t).density t ⟨ht, le_rfl⟩
  have hC : 0 < p.C₁ := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨S0, hS0⟩ := hall 0
    have h1 := (hRes.ratio 0 le_rfl 0).2
    have h2 := hS0.pos 0
    nlinarith [hβpos 0, mul_nonpos_of_nonpos_of_nonneg hneg (hβpos 0).le]
  have hpos : ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < R.ρ t x := fun t ht x =>
    lt_of_lt_of_le (mul_pos (inv_pos.2 hC) (hβpos x)) (hRes.ratio t ht x).1
  exact ⟨hRes.cpos, hC, fun t ht => ⟨hdens t ht, hpos t ht⟩, fun n => by
    obtain ⟨S, hS⟩ := hall n
    exact ⟨M₀, c, S, hc, hS⟩⟩

end HRS.MS.R26T3
