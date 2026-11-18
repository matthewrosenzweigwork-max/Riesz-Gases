import Mathlib

/-!
# EQ-LZ packet ASM, part 1: the finite-time-set limit (abstract measure theory)

Abstract lemma `asm_finite`: if a family `G k` of bounded measurable statistics approximates `F ∈ L²(μ)` in `L²(μ)`
with convergent energy bounds, and the maximal inequality holds for each `G k` with constant `C`, then it holds for `F`
with the same constant `C` on every FINITE set `S` of times (all one-time marginals are `μ`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace HRS.MD.EQLZ.Asm

theorem asm_sq_le {ε : ℝ} (hε : 0 < ε) (b c : ℝ) :
    (b + c) ^ 2 ≤ (1 + ε) * b ^ 2 + (1 + 1 / ε) * c ^ 2 := by
  have h : 0 ≤ (ε * b - c) ^ 2 / ε := by positivity
  have : (1 + ε) * b ^ 2 + (1 + 1 / ε) * c ^ 2 - (b + c) ^ 2 = (ε * b - c) ^ 2 / ε := by
    field_simp; ring
  linarith

theorem asm_ofReal_sq_le {ε : ℝ} (hε : 0 < ε) (b c : ℝ) :
    ENNReal.ofReal ((b + c) ^ 2) ≤
      ENNReal.ofReal (1 + ε) * ENNReal.ofReal (b ^ 2) + ENNReal.ofReal (1 + 1 / ε) * ENNReal.ofReal (c ^ 2) := by
  have h1 : (0 : ℝ) ≤ 1 + ε := by linarith
  have h2 : (0 : ℝ) ≤ 1 + 1 / ε := by positivity
  calc ENNReal.ofReal ((b + c) ^ 2) ≤ ENNReal.ofReal ((1 + ε) * b ^ 2 + (1 + 1 / ε) * c ^ 2) :=
        ENNReal.ofReal_le_ofReal (asm_sq_le hε b c)
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul h1,
          ENNReal.ofReal_mul h2]

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- One comparison step on a finite set of times `S`: `u = b + c`. -/
theorem asm_step (P : Measure Ω) (μ : Measure α) (Y : ℝ → Ω → α) (S : Finset ℝ)
    (hY : ∀ t ∈ S, Measurable (Y t)) (hlaw : ∀ t ∈ S, P.map (Y t) = μ) (u b c : α → ℝ)
    (hb : Measurable b) (hc : Measurable c) (huc : ∀ x, u x = b x + c x) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ω, ⨆ t ∈ (S : Set ℝ), ENNReal.ofReal (u (Y t ω) ^ 2) ∂P ≤
      ENNReal.ofReal (1 + ε) * ∫⁻ ω, ⨆ t ∈ (S : Set ℝ), ENNReal.ofReal (b (Y t ω) ^ 2) ∂P +
        ENNReal.ofReal (1 + 1 / ε) * ((S.card : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (c x ^ 2) ∂μ) := by
  have hmeas_sup : Measurable fun ω => ⨆ t ∈ (S : Set ℝ), ENNReal.ofReal (b (Y t ω) ^ 2) := by
    refine Measurable.biSup (S : Set ℝ) S.countable_toSet fun t ht => ?_
    exact ENNReal.measurable_ofReal.comp (((hb.comp (hY t ht)).pow_const 2))
  have hmeas_c : ∀ t ∈ S, Measurable fun ω => ENNReal.ofReal (c (Y t ω) ^ 2) := fun t ht =>
    ENNReal.measurable_ofReal.comp ((hc.comp (hY t ht)).pow_const 2)
  have hpt : ∀ ω, ⨆ t ∈ (S : Set ℝ), ENNReal.ofReal (u (Y t ω) ^ 2) ≤
      ENNReal.ofReal (1 + ε) * (⨆ t ∈ (S : Set ℝ), ENNReal.ofReal (b (Y t ω) ^ 2)) +
        ENNReal.ofReal (1 + 1 / ε) * ∑ t ∈ S, ENNReal.ofReal (c (Y t ω) ^ 2) := by
    intro ω
    refine iSup₂_le fun t ht => ?_
    rw [huc]
    refine (asm_ofReal_sq_le hε _ _).trans (add_le_add ?_ ?_)
    · exact mul_le_mul_right (le_iSup₂ (f := fun t (_ : t ∈ (S : Set ℝ)) =>
        ENNReal.ofReal (b (Y t ω) ^ 2)) t ht) _
    · exact mul_le_mul_right (Finset.single_le_sum (f := fun t => ENNReal.ofReal (c (Y t ω) ^ 2))
        (fun _ _ => bot_le) (Finset.mem_coe.mp ht)) _
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left (hmeas_sup.const_mul _), lintegral_const_mul _ hmeas_sup,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finset_sum _ hmeas_c]
  refine add_le_add le_rfl (mul_le_mul_right ?_ _)
  have : ∀ t ∈ S, ∫⁻ ω, ENNReal.ofReal (c (Y t ω) ^ 2) ∂P = ∫⁻ x, ENNReal.ofReal (c x ^ 2) ∂μ := by
    intro t ht
    rw [← hlaw t ht]
    exact (lintegral_map (f := fun x => ENNReal.ofReal (c x ^ 2))
      (ENNReal.measurable_ofReal.comp (hc.pow_const 2)) (hY t ht)).symm
  rw [Finset.sum_congr rfl this]
  simp

end HRS.MD.EQLZ.Asm

end
