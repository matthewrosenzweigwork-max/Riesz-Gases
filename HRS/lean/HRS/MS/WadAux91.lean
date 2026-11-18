import HRS.MS.WadAux90

/-!
# S8.3, packet S8E-5, part 2: clause (2a) pointwise, sections of a doubly centered pair

For `t ≥ 1` and a centered `h ∈ C_M` with `Wt M C h`: `|U_t h(y)| ≤ C_d e^{-ct} C ⟨y⟩^M` (`s8e_2a_pt`).
For `R` doubly centered in `C_M^{pair}`, `x' ↦ U_t(R x')(y)` lies in `C_M` and `|U_t(R x')(y)| ≤ C_d e^{-ct} N_0 ⟨x'⟩^M ⟨y⟩^M`
(`s8e_G_cm`, `s8e_G_bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_2a_pt (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) :
    ∃ Cd c : ℝ, 0 ≤ Cd ∧ 0 < c ∧ ∀ {t : ℝ}, 1 ≤ t → ∀ {h : Euc d → ℝ} {C : ℝ}, MemCM M h → Wt M C h →
      ∀ y, |s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) h) y| ≤
        Cd * Real.exp (-c * t) * C * jbracket y ^ M := by
  obtain ⟨Cd, c, hc, h⟩ := s8d_clause2a_Ulim hd ha hβ hρ hMpos
  refine ⟨max Cd 0, c, le_max_right _ _, hc, fun {t} ht {h'} {C} hh hw y => ?_⟩
  have hC := hw.nonneg
  have h1 := h ht hh
  have h2 : weightedSupE 0 (-M) h' ≤ ENNReal.ofReal C := (s83_wsup0_le_iff hC h').2 hw
  have hCd : 0 ≤ max Cd 0 * Real.exp (-c * t) := mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
  have h3 : weightedSupE 0 (-M) (s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) h')) ≤
      ENNReal.ofReal (max Cd 0 * Real.exp (-c * t) * C) := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul hCd]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.exp_pos _).le)) h2
  have := (s83_wsup0_le_iff (mul_nonneg hCd hC) _).1 h3 y
  exact this

end HRS.MS.Wad
