import HRS.MS.SA12V3L

/-!
# S.A.12 C2 (SA12V3 worker), part M: the dilated cutoff `ζ(·/L)` is a uniform `H^m` multiplier for `L ≥ 1`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_zeta_mul (m : ℕ) {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ u : Euc d → ℝ,
      sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * u x) ≤ ENNReal.ofReal C * sobolevNormE (m : ℝ) u := by
  obtain ⟨C0, hC0, h⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d m
  have hb : ∀ j : ℕ, BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ j ζ x‖) := by
    intro j
    have hc : Continuous (iteratedFDeriv ℝ j ζ) := hζ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (hζc.iteratedFDeriv j)
    exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x⟩
  have hL : ∀ L : ℝ, 1 ≤ L → HRS.MemCb m (fun x : Euc d => ζ (L⁻¹ • x)) ∧
      HRS.cbNorm m (fun x : Euc d => ζ (L⁻¹ • x)) ≤ HRS.cbNorm m ζ := by
    intro L hL1
    have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
    have hscale : ∀ (j : ℕ) (x : Euc d), ‖iteratedFDeriv ℝ j (fun y : Euc d => ζ (L⁻¹ • y)) x‖ ≤
        ‖iteratedFDeriv ℝ j ζ (L⁻¹ • x)‖ := by
      intro j x
      rw [HRS.MS.Ker1.ker1_iteratedFDeriv_comp_smul ζ (inv_ne_zero hL0.ne') j x, norm_smul, norm_pow,
        Real.norm_eq_abs, abs_inv, abs_of_pos hL0]
      have : L⁻¹ ^ j ≤ 1 := pow_le_one₀ (inv_nonneg.2 hL0.le) (inv_le_one_of_one_le₀ hL1)
      calc L⁻¹ ^ j * ‖iteratedFDeriv ℝ j ζ (L⁻¹ • x)‖ ≤ 1 * ‖iteratedFDeriv ℝ j ζ (L⁻¹ • x)‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := one_mul _
    refine ⟨⟨(hζ.comp (contDiff_const_smul _)).of_le (by exact_mod_cast le_top), fun j _ => ?_⟩, ?_⟩
    · obtain ⟨B, hB⟩ := hb j
      exact ⟨B, by
        rintro _ ⟨x, rfl⟩
        exact (hscale j x).trans (hB ⟨L⁻¹ • x, rfl⟩)⟩
    · unfold HRS.cbNorm
      refine Finset.sum_le_sum fun j _ => ?_
      refine ciSup_le fun x => ?_
      exact (hscale j x).trans (le_ciSup (hb j) (L⁻¹ • x))
  have hcb0 : 0 ≤ HRS.cbNorm m ζ := HRS.MS.Ul.ul0_cbNorm_nonneg m ζ
  refine ⟨C0 * HRS.cbNorm m ζ, mul_nonneg hC0.le hcb0, fun L hL1 u => ?_⟩
  obtain ⟨hmem, hcbL⟩ := hL L hL1
  refine (h _ hmem u).trans ?_
  gcongr

end HRS.MH.AdjointRd.Phase2SA12V3
