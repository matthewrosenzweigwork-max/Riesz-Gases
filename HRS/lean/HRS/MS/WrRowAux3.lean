import HRS.MS.WrRowAux2
import HRS.MS.WrKerAux1

/-!
# HRS.MS.WrRowAux3 -- real-valued row bounds with integrability, `δ_N` form, `EWeakKernel` packaging (WR-3, part 3)

Consumers of the row bounds of `WrRowAux2` (WR-4: `Abs.conv_abstract` needs the Bochner row hypotheses
`∫ (q x y - N)_+ dμ ≤ a₂`, `∫ min(q x y, N)² dμ ≤ b₁`; WR-1/WR-5 need an `EWeakKernel`):

* `wr3_row_bounds_real_integral`: the Bochner form of `wr3_row_bounds_real`, with **integrability** of the
  integrands (so the bounds are not satisfied by the Bochner junk value `0`); `q` is assumed measurable.
* `wr3_row_bounds_delta`: the `δ_N` form (port of `row_bounds`, level `N ≥ 2`):
  `∫ (q - N)_+ ≤ C_a δ_N`, `∫ min(q,N)² ≤ C_b N δ_N`, with integrability.
* `wr3_eWeakKernel_of_envelope`: a measurable symmetric nonnegative kernel dominated by
  `A W_s(x-y)` off the diagonal is an `EWeakKernel (ρ dx) a q` for some `a ≥ 0` depending only on
  `(d, s, A, M)` (the row integral `∫ q(x,y) dμ(y)` is bounded by `A ∫ W_s(x-y) dμ(y)`).
Helper lemmas carry the prefix `wr3_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ}

/-- Bochner form of the row bounds, with integrability of the integrands. -/
theorem wr3_row_bounds_real_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (A M : ℝ) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, Measurable (Function.uncurry q) → (∀ x y, 0 ≤ q x y) →
      (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) → ∀ x : Euc d,
        (∀ L : ℝ, 0 < L →
          Integrable (fun y => max (q x y - L) 0) (HRS.Whole.withDensityReal ρ) ∧
          ∫ y, max (q x y - L) 0 ∂(HRS.Whole.withDensityReal ρ)
            ≤ Ca * L ^ (1 - (d : ℝ) / HRS.WeakRef.sigmaOf d s)) ∧
        (∀ L : ℝ, 1 ≤ L →
          Integrable (fun y => (min (q x y) L) ^ 2) (HRS.Whole.withDensityReal ρ) ∧
          ∫ y, (min (q x y) L) ^ 2 ∂(HRS.Whole.withDensityReal ρ)
            ≤ Cb * HRS.WeakRef.psi2 d s L) := by
  obtain ⟨Ca, Cb, hCa, hCb, H⟩ := wr3_row_bounds_real hd hs0 hsd A M
  refine ⟨Ca, Cb, hCa, hCb, fun ρ hρ hM q hqm hq0 hqA x => ?_⟩
  obtain ⟨h1, h2⟩ := H ρ hρ hM q hq0 hqA x
  have hqx : Measurable (q x) := hqm.comp (measurable_const.prodMk measurable_id)
  refine ⟨fun L hL => ?_, fun L hL => ?_⟩
  · exact HRS.Whole.Q34.integrable_of_lintegral_le
      ((hqx.sub_const L).max measurable_const) (fun _ => le_max_right _ _)
      (mul_nonneg hCa (Real.rpow_nonneg hL.le _)) (h1 L hL)
  · have hψ := wr3_one_le_psi2 hd hs0 hL
    exact HRS.Whole.Q34.integrable_of_lintegral_le
      ((hqx.min measurable_const).pow_const 2) (fun _ => sq_nonneg _)
      (mul_nonneg hCb (by linarith)) (h2 L hL)

/-- The `δ_N` form of the row bounds (port of `row_bounds`): for `N ≥ 2`,
`∫ (q(x,y) - N)_+ dμ ≤ C_a δ_N` and `∫ min(q(x,y), N)² dμ ≤ C_b N δ_N`, both integrands integrable. -/
theorem wr3_row_bounds_delta (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (A M : ℝ) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, Measurable (Function.uncurry q) → (∀ x y, 0 ≤ q x y) →
      (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
        (Integrable (fun y => max (q x y - N) 0) (HRS.Whole.withDensityReal ρ) ∧
          ∫ y, max (q x y - N) 0 ∂(HRS.Whole.withDensityReal ρ) ≤ Ca * deltaN d s N) ∧
        (Integrable (fun y => (min (q x y) N) ^ 2) (HRS.Whole.withDensityReal ρ) ∧
          ∫ y, (min (q x y) N) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ Cb * (N * deltaN d s N)) := by
  obtain ⟨Ca, Cb, hCa, hCb, H⟩ := wr3_row_bounds_real_integral hd hs0 hsd A M
  refine ⟨Ca, Cb, hCa, hCb, fun ρ hρ hM q hqm hq0 hqA N hN x => ?_⟩
  obtain ⟨h1, h2⟩ := H ρ hρ hM q hqm hq0 hqA x
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨hi, hb⟩ := h1 N hNpos
    exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_left
      (HRS.WeakRef.rpow_le_deltaN hd hs0 hsd (N := N) (by omega)) hCa)⟩
  · obtain ⟨hi, hb⟩ := h2 N hN1
    refine ⟨hi, ?_⟩
    rw [HRS.WeakRef.mul_deltaN_eq_psi2 s (N := N) (by omega)]
    exact hb

/-- A measurable symmetric nonnegative kernel dominated by `A W_s(x-y)` off the diagonal is an
`EWeakKernel (ρ dx) a q`, with `a ≥ 0` depending only on `(d, s, A, M)` (`ρ` a probability density
with `ρ ≤ M`). -/
theorem wr3_eWeakKernel_of_envelope (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (A M : ℝ) :
    ∃ a : ℝ, 0 ≤ a ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
      (∀ x y, 0 ≤ q x y) →
      (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) →
        EWeakKernel (HRS.Whole.withDensityReal ρ) a q := by
  have hσ0 := HRS.WeakRef.sigmaOf_pos hd hs0
  have hσd := HRS.WeakRef.sigmaOf_lt hd hsd
  set σ := HRS.WeakRef.sigmaOf d s with hσ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set Ā : ℝ := max A 1 with hĀ
  have hĀ1 : 1 ≤ Ā := le_max_right _ _
  have hĀ0 : 0 < Ā := by linarith
  have hAĀ : A ≤ Ā := le_max_left _ _
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set B : ℝ := 1 + 4 / (d : ℝ) with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ 4 / (d : ℝ) := by positivity
    rw [hB]; linarith
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hdσ : 0 < (d : ℝ) - σ := by linarith
  set cW : ℝ := 1 + B * (M' * sphereArea d / ((d : ℝ) - σ) + 1) with hcW
  have hcW0 : 0 ≤ cW := by rw [hcW]; positivity
  refine ⟨Ā * cW, by positivity, fun ρ hρ hM q hqm hqs hq0 hqA => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hM' : ∀ y, ρ y ≤ M' := fun y => (hM y).trans (le_max_left _ _)
  refine ⟨hqm, hqs, hq0, fun x => ?_⟩
  have hae := wr3_ae_ne hd ρ x
  have hW1 : ∀ z : Euc d, 1 ≤ 1 + HRS.Whole.rieszWeight s z := fun z => by
    linarith [wr3_rieszWeight_nonneg (d := d) s z]
  calc ∫⁻ y, ENNReal.ofReal (q x y) ∂(HRS.Whole.withDensityReal ρ)
      ≤ ∫⁻ y, ENNReal.ofReal Ā * ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y))
          ∂(HRS.Whole.withDensityReal ρ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with y hy
        rw [← ENNReal.ofReal_mul hĀ0.le]
        refine ENNReal.ofReal_le_ofReal ?_
        exact (hqA x y (Ne.symm hy)).trans
          (mul_le_mul_of_nonneg_right hAĀ (by linarith [hW1 (x - y)]))
    _ = ENNReal.ofReal Ā *
          ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Ā * ENNReal.ofReal cW := by
        gcongr
        exact wr3_lintegral_W_row hd hs0 hsd hρ hM' x
    _ = ENNReal.ofReal (Ā * cW) := (ENNReal.ofReal_mul hĀ0.le).symm

end HRS.MS.Wr
