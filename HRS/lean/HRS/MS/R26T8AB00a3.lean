import HRS.MS.R26T8AB00a2

/-!
# S8.2 observed-time layer, packet T8A.B00a (helper 3): the L² bound of a parameter integral

If `‖F · b‖_{L²(P)}² ≤ A²` for `ν`-a.e. `b`, then `‖∫⁻_ν F · b‖_{L²(P)} ≤ ν(univ) A`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00a3_sq_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) (A : ℝ)
    (hm : AEStronglyMeasurable f P) (hf : eLpNorm f 2 P ≤ ENNReal.ofReal A) :
    ∫⁻ w, ‖f w‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal A ^ (2 : ℝ) := by
  have h : eLpNorm f 2 P = (∫⁻ w, ‖f w‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
    have := eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (f := f) (μ := P) (by norm_num)
      (by norm_num) hm
    simpa using this
  have h3 : (∫⁻ w, ‖f w‖ₑ ^ (2 : ℝ) ∂P) = (eLpNorm f 2 P) ^ (2 : ℝ) := by
    rw [h, ← ENNReal.rpow_mul]; norm_num
  rw [h3]
  exact ENNReal.rpow_le_rpow hf (by norm_num)

theorem r26t8a_b00a3_L2 {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [SFinite P] (ν : Measure β) [SFinite ν]
    {F : Ω → β → ℝ≥0∞} (hF : AEMeasurable (Function.uncurry F) (P.prod ν)) (A : ℝ≥0∞)
    (hb : ∀ᵐ b ∂ν, ∫⁻ w, F w b ^ (2 : ℝ) ∂P ≤ A ^ (2 : ℝ)) :
    (∫⁻ w, (∫⁻ b, F w b ∂ν) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤ ν Set.univ * A := by
  have h1 := r26t8a_b00n1_mink_ae P ν hF
  have h2 : ∫⁻ b, ∫⁻ w, F w b ^ (2 : ℝ) ∂P ∂ν ≤ A ^ (2 : ℝ) * ν Set.univ := by
    calc _ ≤ ∫⁻ _b, A ^ (2 : ℝ) ∂ν := lintegral_mono_ae hb
      _ = _ := lintegral_const _
  have h3 : ∫⁻ w, (∫⁻ b, F w b ∂ν) ^ (2 : ℝ) ∂P ≤ (ν Set.univ * A) ^ (2 : ℝ) := by
    refine h1.trans ((mul_le_mul' le_rfl h2).trans (le_of_eq ?_))
    rw [ENNReal.rpow_two, ENNReal.rpow_two]; ring
  calc _ ≤ ((ν Set.univ * A) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h3 (by norm_num)
    _ = _ := by rw [← ENNReal.rpow_mul]; norm_num

end HRS.MS.R26T8A

end
