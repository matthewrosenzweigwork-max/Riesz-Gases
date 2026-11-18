import HRS.MS.Mov63EAux11

/-!
# S6.3, packet N6 (part 12): assembly with the mild existence theorem

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.  **`mov63_signed_solution`**: for the thermal data `H`, the rate `c` and every integer `m > d/2+3`, the
small mass-zero data of `mov63_mild_existence` give a mild solution `v` (`MneMild`), the bound `‖v_t‖ ≤ C‖x₀‖e^{-(c/2)t}`, the pointwise classical mean-field and `Q`
equations (signed), and, conditionally on `ρ_t ≥ 0` (N7), a member of `MovInSmallClass` (`r = C‖x₀‖`, `c₀ = c/2`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Final

/-- **N6 output (assembly with N5)**: for the thermal data `H` and every integer `m > d/2 + 3` the mild solutions of
`mov63_mild_existence` (small mass-zero data `x₀`) satisfy `MneMild`, and
(i) *if `ρ_t = ρ + √ρ V_t ≥ 0` for `t ≥ 0`* (the content of N7), the family `mneP` is a member of `MovInSmallClass`
with `r = C‖x₀‖`, `c₀ = c/2`, `f₀ = V_0/√ρ`; in particular a global weak solution of the mean-field equation in the sense of
`IsWholeMeanFieldSolution` (all `C_b²` tests);
(ii) unconditionally (signed): the pointwise classical mean-field equation in conservation form and the `Q`-equation. -/
theorem mov63_signed_solution (H : Mov2dTh d s β q ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (hm : (d : ℝ) / 2 + 3 < m), ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ x0 : OscSpace d (m : ℝ), MovMassZero ρ (mnd_m_nonneg hm) x0 → ‖x0‖ ≤ ε →
        ∃ v : ℝ → OscSpace d (m : ℝ), MneMild H hm v ∧ v 0 = x0 ∧
          (∀ t, 0 ≤ t → ‖v t‖ ≤ C * ‖x0‖ * Real.exp (-(c / 2) * t)) ∧
          ((∀ t, 0 ≤ t → ∀ x, 0 ≤ mneP d ρ hm v t x) →
            MovInSmallClass d s q β ρ m (C * ‖x0‖) (c / 2) (mneF0fun d ρ hm v) (mneP d ρ hm v)) ∧
          (∀ t, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => mneRho ρ hm (v τ) x)
            (movDiv (mneY d s q β ρ hm (v t)) x) (Ici 0) t) ∧
          (∀ t, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => mneQ ρ hm (v τ) x)
            (β⁻¹ * Laplacian.laplacian (mneQ ρ hm (v t)) x +
              inner ℝ (β⁻¹ • gradient (fun y => Real.log (ρ y)) x + mneFo d s ρ hm (v t) x)
                (gradient (mneQ ρ hm (v t)) x) +
              (movDiv (mneFo d s ρ hm (v t)) x +
                inner ℝ (gradient (fun y => Real.log (ρ y)) x) (mneFo d s ρ hm (v t) x)) *
                mneQ ρ hm (v t) x) (Ici 0) t) := by
  obtain ⟨c, hc, h⟩ := mov63_mild_existence H
  refine ⟨c, hc, fun m hm => ?_⟩
  obtain ⟨ε, C, hε, hC, h2⟩ := h (m : ℝ) hm
  refine ⟨ε, C, hε, hC, fun x0 hx0 hxε => ?_⟩
  obtain ⟨v, hvc, hv0, hmass, hbd, hmild⟩ := h2 x0 hx0 hxε
  have hM : MneMild H hm v := ⟨hvc, hmass, fun t ht => by
    obtain ⟨h1, h2⟩ := hmild t ht
    rw [hv0]
    exact ⟨h1, h2⟩⟩
  refine ⟨v, hM, hv0, fun t ht => (hbd t ht), fun hnn => ?_, fun t ht x => mne_hasDeriv hm H hM ht x,
    fun t ht x => mne_Q_hasDeriv hm H hM ht x⟩
  refine mne_class hm H hM hnn (C * ‖x0‖) (c / 2) (fun t ht => ?_)
  exact hbd t ht

end Final

end HRS.MS.Mov63

end

example := @HRS.MS.Mov63.mov63_signed_solution
