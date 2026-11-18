import HRS.ME.RetWeight

/-!
# Row 5.10, shifted burn-in, part C: transfer of the weight to the enlarged space

`w ω' = h (Xz (π ω'))`, where `Xz = X 0` is a.e. equal to the initial datum `X₀`.  Under a measure preserving `π` and a
joint law `(X₀ ∘ π, η')` equal to `law X₀ ⊗ ν₀`: `∫ w = 1`, `(w P₁) ∘ π⁻¹ = (h ∘ X₀) P`, `(w P₁) ∘ η'⁻¹ = ν₀`, `∫ w² = ∫ h(X₀)²`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

section WeightTransfer

variable {Ω Ω₁ E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [MeasurableSpace E] [MeasurableSpace F]

theorem rbs_w_lintegral {P : Measure Ω} {P₁ : Measure Ω₁} {π : Ω₁ → Ω} (hπ : MeasurePreserving π P₁ P)
    {X₀ Xz : Ω → E} (hXz : Measurable Xz) (hae : Xz =ᵐ[P] X₀) {h : E → ℝ≥0∞} (hh : Measurable h) (k : ℝ≥0∞ → ℝ≥0∞)
    (hk : Measurable k) :
    ∫⁻ ω', k (h (Xz (π ω'))) ∂P₁ = ∫⁻ ω, k (h (X₀ ω)) ∂P := by
  have h1 : ∫⁻ ω', (fun ω => k (h (Xz ω))) (π ω') ∂P₁ = ∫⁻ ω, k (h (Xz ω)) ∂P :=
    hπ.lintegral_comp (hk.comp (hh.comp hXz))
  refine h1.trans (lintegral_congr_ae ?_)
  filter_upwards [hae] with ω hω
  simp [hω]

theorem rbs_w_map_pi {P : Measure Ω} {P₁ : Measure Ω₁} {π : Ω₁ → Ω} (hπ : MeasurePreserving π P₁ P)
    {X₀ Xz : Ω → E} (hXz : Measurable Xz) (hae : Xz =ᵐ[P] X₀) {h : E → ℝ≥0∞} (hh : Measurable h) :
    (P₁.withDensity fun ω' => h (Xz (π ω'))).map π = P.withDensity fun ω => h (X₀ ω) := by
  have hwae : (P.withDensity fun ω => h (Xz ω)) = P.withDensity fun ω => h (X₀ ω) := by
    refine withDensity_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp [hω]
  rw [← hwae]
  ext A hA
  rw [Measure.map_apply hπ.measurable hA, withDensity_apply _ (hπ.measurable hA), withDensity_apply _ hA]
  exact hπ.setLIntegral_comp_preimage hA (hh.comp hXz)

theorem rbs_w_map_eta {P : Measure Ω} {P₁ : Measure Ω₁} {π : Ω₁ → Ω} (hπ : MeasurePreserving π P₁ P)
    {X₀ Xz : Ω → E} (hX₀ : Measurable X₀) (hXz : Measurable Xz) (hae : Xz =ᵐ[P] X₀) {h : E → ℝ≥0∞}
    (hh : Measurable h) (h1 : ∫⁻ ω, h (X₀ ω) ∂P = 1) {η' : Ω₁ → F} (hη' : Measurable η')
    {ν₀ : Measure F} [IsProbabilityMeasure ν₀]
    (hpair : P₁.map (fun ω' => (X₀ (π ω'), η' ω')) = (P.map X₀).prod ν₀) :
    (P₁.withDensity fun ω' => h (Xz (π ω'))).map η' = ν₀ := by
  have hX₀π : Measurable (fun ω' => X₀ (π ω')) := hX₀.comp hπ.measurable
  have hpm : Measurable (fun ω' => (X₀ (π ω'), η' ω')) := hX₀π.prodMk hη'
  have haeπ : ∀ᵐ ω' ∂P₁, Xz (π ω') = X₀ (π ω') := hπ.quasiMeasurePreserving.ae hae
  ext B hB
  rw [Measure.map_apply hη' hB, withDensity_apply _ (hη' hB)]
  set Fp : E × F → ℝ≥0∞ := fun p => h p.1 * B.indicator (fun _ => (1 : ℝ≥0∞)) p.2 with hFp
  have hFpm : Measurable Fp :=
    (hh.comp measurable_fst).mul (measurable_const.indicator hB |>.comp measurable_snd)
  have e1 : ∫⁻ ω' in η' ⁻¹' B, h (Xz (π ω')) ∂P₁ = ∫⁻ ω', Fp (X₀ (π ω'), η' ω') ∂P₁ := by
    rw [← lintegral_indicator (hη' hB)]
    refine lintegral_congr_ae ?_
    filter_upwards [haeπ] with ω' hω'
    by_cases hb : η' ω' ∈ B
    · simp [Set.indicator, hb, hFp, hω']
    · simp [Set.indicator, hb, hFp]
  rw [e1, ← lintegral_map hFpm hpm, hpair, lintegral_prod _ hFpm.aemeasurable]
  have e2 : ∀ x, ∫⁻ y, Fp (x, y) ∂ν₀ = h x * ν₀ B := by
    intro x
    simp only [hFp]
    rw [lintegral_const_mul _ (measurable_const.indicator hB), lintegral_indicator_const hB, one_mul]
  simp_rw [e2]
  rw [lintegral_mul_const _ hh, lintegral_map hh hX₀, h1, one_mul]

end WeightTransfer

theorem rbs_l2_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ≥0∞) {A : ℝ} (hA : 0 ≤ A)
    (h : ∫⁻ x, f x ^ 2 ∂μ ≤ ENNReal.ofReal A) :
    (∫⁻ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt A) := by
  calc (∫⁻ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal A) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt A) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num), ← Real.sqrt_eq_rpow]

/-- Hölder with the weight and a bound on the `L²` norm of the other factor. -/
theorem rbs_holder {α : Type*} [MeasurableSpace α] (μ : Measure α) {w F : α → ℝ≥0∞} (hw : AEMeasurable w μ)
    (hF : AEMeasurable F μ) {q : ℝ≥0∞} (hq : (∫⁻ x, F x ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ q) :
    ∫⁻ x, w x * F x ∂μ ≤ (∫⁻ x, w x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * q :=
  (lintegral_mul_le_L2 μ hw hF).trans (mul_le_mul' le_rfl hq)

end HRS.ME.Ret

end
