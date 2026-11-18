import Mathlib

/-!
# S11.3 Liouville (worker S11Q2), C2: volume of Lipschitz images and of preimages under lower Lipschitz maps

`s11q2_vol_lip`: `μ (f '' S) ≤ K^n μ S` for `f` `K`-Lipschitz on `S` (Haar measure `μ`, `n = finrank`).
`s11q2_vol_preimage`: if `F` is lower Lipschitz on `S` (`κ dist x x' ≤ dist (F x) (F x')`), then `μ (S ∩ F⁻¹ A) ≤ κ^{-n} μ A`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Measure Set
open scoped NNReal ENNReal

namespace HRS.MS.S11Q2

theorem s11q2_vol_lip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {K : ℝ≥0} {f : E → E} {S : Set E}
    (hf : LipschitzOnWith K f S) : μ (f '' S) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ E) * μ S := by
  set ν : Measure E := μH[(Module.finrank ℝ E : ℝ)] with hν
  have hc := isAddLeftInvariant_eq_smul ν μ
  have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  set c := addHaarScalarFactor ν μ with hcdef
  have h1 := hf.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
  rw [← hν, hc] at h1
  simp only [Measure.smul_apply, ENNReal.rpow_natCast, ENNReal.smul_def, smul_eq_mul] at h1
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpos.ne'
  have hct : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  refine (ENNReal.mul_le_mul_iff_right hc0 hct).1 ?_
  calc (c : ℝ≥0∞) * μ (f '' S) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ E) * ((c : ℝ≥0∞) * μ S) := h1
    _ = _ := by ring

theorem s11q2_vol_preimage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {κ : ℝ≥0} (hκ : 0 < κ) {F : E → E}
    {S : Set E} (hlow : ∀ x ∈ S, ∀ x' ∈ S, (κ : ℝ) * dist x x' ≤ dist (F x) (F x')) (A : Set E) :
    μ (S ∩ F ⁻¹' A) ≤ ((κ⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ E) * μ A := by
  have hinj : InjOn F S := fun x hx x' hx' h => by
    have := hlow x hx x' hx'
    rw [h, dist_self] at this
    have h0 : dist x x' ≤ 0 := by
      by_contra hne
      push_neg at hne
      have : 0 < (κ : ℝ) * dist x x' := mul_pos (by exact_mod_cast hκ) hne
      linarith
    exact dist_le_zero.1 h0
  set Ψ := Function.invFunOn F S with hΨ
  set T0 := F '' (S ∩ F ⁻¹' A) with hT0
  have hlip : LipschitzOnWith κ⁻¹ Ψ T0 := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨x', hx', rfl⟩ := hy'
    rw [hΨ, hinj.leftInvOn_invFunOn hx.1, hinj.leftInvOn_invFunOn hx'.1]
    have := hlow x hx.1 x' hx'.1
    have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ
    rw [NNReal.coe_inv, inv_mul_eq_div, le_div_iff₀ hκ']
    linarith
  have hsub : S ∩ F ⁻¹' A ⊆ Ψ '' T0 := fun x hx =>
    ⟨F x, ⟨x, hx, rfl⟩, hinj.leftInvOn_invFunOn hx.1⟩
  calc μ (S ∩ F ⁻¹' A) ≤ μ (Ψ '' T0) := measure_mono hsub
    _ ≤ ((κ⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ E) * μ T0 := s11q2_vol_lip μ hlip
    _ ≤ _ := by
        gcongr
        rintro _ ⟨x, hx, rfl⟩
        exact hx.2

end HRS.MS.S11Q2

end
