import HRS.MS.S111K4J02B

/-!
# S11.1 / J02, piece D (S111K4): pointwise slice bound of a bounded functional of `timeCoeffOf`

`k4j_slice_bound`: for every `y`, `‖L (timeCoeffOf H q y)‖ₑ ≤ ofReal β * ∫⁻_{(a,b]} ofReal(wt z) ‖q(z,y)‖ₑ dz`
whenever `‖L q'‖ ≤ β ∫_{(a,b]} wt ‖q'‖` for all `q'` (and `L` is a bounded linear map, so `L 0 = 0`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem k4j_ofReal_integral_le {μ : Measure ℝ} {f : ℝ → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ENNReal.ofReal (∫ z, f z ∂μ) ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf)]
  · rw [integral_undef hi]; simp

theorem k4j_slice_bound {Ω : Type*} [MeasurableSpace Ω] (H : ℝ) (q : ℝ × Ω → Coeff) (hqm : Measurable q)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (L : TimeCoeff H →L[ℝ] X)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ H) (wt : ℝ → ℝ) (hwt0 : ∀ v, 0 ≤ wt v) (β : ℝ) (hβ : 0 ≤ β)
    (hL : ∀ q' : TimeCoeff H, ‖L q'‖ ≤ β * ∫ z in Set.Ioc a b, wt z * ‖(q' : ℝ → Coeff) z‖) (y : Ω) :
    ‖L (timeCoeffOf H q y)‖ₑ ≤ ENNReal.ofReal β *
      ∫⁻ z in Set.Ioc a b, ENNReal.ofReal (wt z) * ‖q (z, y)‖ₑ := by
  by_cases hmem : MemLp (fun v => q (v, y)) 1 (volume.restrict (Set.Icc (0 : ℝ) H))
  · have htc : timeCoeffOf H q y = hmem.toLp (fun v => q (v, y)) := by
      unfold timeCoeffOf; rw [dif_pos hmem]
    have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) H := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
    have hae : ∀ᵐ z ∂(volume.restrict (Set.Ioc a b)),
        ((timeCoeffOf H q y : TimeCoeff H) : ℝ → Coeff) z = q (z, y) := by
      rw [htc]
      exact ae_restrict_of_ae_restrict_of_subset hsub hmem.coeFn_toLp
    have hint : ∫ z in Set.Ioc a b, wt z * ‖((timeCoeffOf H q y : TimeCoeff H) : ℝ → Coeff) z‖ =
        ∫ z in Set.Ioc a b, wt z * ‖q (z, y)‖ :=
      integral_congr_ae (hae.mono fun z hz => by simp only []; rw [hz])
    have h1 := hL (timeCoeffOf H q y)
    rw [hint] at h1
    rw [← ofReal_norm_eq_enorm]
    calc ENNReal.ofReal ‖L (timeCoeffOf H q y)‖ ≤ ENNReal.ofReal (β * ∫ z in Set.Ioc a b, wt z * ‖q (z, y)‖) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal β * ENNReal.ofReal (∫ z in Set.Ioc a b, wt z * ‖q (z, y)‖) :=
          ENNReal.ofReal_mul hβ
      _ ≤ ENNReal.ofReal β * ∫⁻ z in Set.Ioc a b, ENNReal.ofReal (wt z * ‖q (z, y)‖) :=
          mul_le_mul' le_rfl (k4j_ofReal_integral_le fun z => mul_nonneg (hwt0 z) (norm_nonneg _))
      _ = _ := by
          congr 1
          refine lintegral_congr fun z => ?_
          rw [ENNReal.ofReal_mul (hwt0 z), ofReal_norm_eq_enorm]
  · have htc : timeCoeffOf H q y = 0 := by
      unfold timeCoeffOf; rw [dif_neg hmem]
    rw [htc, map_zero]
    simp

end HRS.MS.S111K4J01
