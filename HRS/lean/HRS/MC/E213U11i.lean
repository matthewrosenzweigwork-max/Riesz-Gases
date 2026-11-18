import HRS.MC.E213U11h

/-!
# Packet e213u11, file i: uniform moments of `D_a` (order 3), `J_a` and `Z_a` (order 2)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Moments2

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u11_D_moment3 (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      Integrable (fun ω => ‖gd.Dwin T a ω‖ ^ 3) gd.P₀ ∧ ∫ ω, ‖gd.Dwin T a ω‖ ^ 3 ∂gd.P₀ ≤ C := by
  obtain ⟨K, c, hK, hc, hpt⟩ := u11_D_pointwise hE gd T hT
  obtain ⟨A, hA0, hA⟩ := u11_weights_bound c T hc hT
  obtain ⟨CB, hCB0, hCB⟩ := u11_B_moment gd 1 one_pos 3 (by norm_num)
  refine ⟨K ^ 3 * (A ^ 3 * CB), by positivity, fun a ha => ?_⟩
  have hY := fun k : ℕ => hCB (k : ℝ) (Nat.cast_nonneg k)
  obtain ⟨hI, hM⟩ := u11_wsum_moment (P := gd.P₀) ⌈a + T⌉₊ (fun k => Real.exp (-c * (a - ((k : ℝ) + 1))))
    (fun k ω => ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖) (fun k => (Real.exp_pos _).le)
    (fun k ω => norm_nonneg _) (fun k => (hY k).1.norm) 3 (by norm_num) CB
    (fun k => by simpa [Real.rpow_ofNat] using (hY k).2.1)
    (fun k => by simpa [Real.rpow_ofNat] using (hY k).2.2)
  have hF0 : ∀ ω, 0 ≤ ∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) *
      ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖ := fun ω =>
    Finset.sum_nonneg fun k _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hDm : AEMeasurable (fun ω => ‖gd.Dwin T a ω‖ ^ 3) gd.P₀ :=
    (u11_Dwin_aesm gd T hT a ha).norm.aemeasurable.pow_const 3
  have hb : ∀ᵐ ω ∂gd.P₀, ‖gd.Dwin T a ω‖ ^ 3 ≤ K ^ 3 * (∑ k ∈ Finset.range ⌈a + T⌉₊,
      Real.exp (-c * (a - ((k : ℝ) + 1))) * ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖) ^ 3 := by
    filter_upwards [hpt a ha] with ω h
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 3
  refine ⟨(hI.const_mul (K ^ 3)).mono' hDm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hb] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact h
  · refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => pow_nonneg (norm_nonneg _) _)
      (hI.const_mul (K ^ 3)) hb).trans ?_
    rw [integral_const_mul]
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have : (∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1)))) ^ 3 * CB ≤ A ^ 3 * CB :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsum0 (hA a ha) 3) hCB0
    exact mul_le_mul_of_nonneg_left (hM.trans this) (by positivity)

theorem u11_sq_moment_of_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (J M F : Ω → ℝ)
    (hJm : AEMeasurable (fun ω => J ω ^ 2) P) (K₁ K₂ CM CF : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hJ0 : ∀ ω, 0 ≤ J ω)
    (hMi : Integrable (fun ω => M ω ^ 2) P) (hMb : ∫ ω, M ω ^ 2 ∂P ≤ CM)
    (hFi : Integrable (fun ω => F ω ^ 2) P) (hFb : ∫ ω, F ω ^ 2 ∂P ≤ CF)
    (hpt : ∀ᵐ ω ∂P, J ω ≤ K₁ * M ω + K₂ * F ω) :
    Integrable (fun ω => J ω ^ 2) P ∧ ∫ ω, J ω ^ 2 ∂P ≤ 2 * K₁ ^ 2 * CM + 2 * K₂ ^ 2 * CF := by
  have hb : ∀ᵐ ω ∂P, J ω ^ 2 ≤ 2 * K₁ ^ 2 * (M ω ^ 2) + 2 * K₂ ^ 2 * (F ω ^ 2) := by
    filter_upwards [hpt] with ω h
    have h2 := pow_le_pow_left₀ (hJ0 ω) h 2
    refine h2.trans ?_
    nlinarith [sq_nonneg (K₁ * M ω - K₂ * F ω)]
  have hIr : Integrable (fun ω => 2 * K₁ ^ 2 * (M ω ^ 2) + 2 * K₂ ^ 2 * (F ω ^ 2)) P :=
    (hMi.const_mul _).add (hFi.const_mul _)
  refine ⟨hIr.mono' hJm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hb] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hJ0 ω) _)]
    exact h
  · refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => pow_nonneg (hJ0 ω) _) hIr hb).trans ?_
    rw [integral_add (hMi.const_mul _) (hFi.const_mul _), integral_const_mul, integral_const_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hMb (by positivity))
      (mul_le_mul_of_nonneg_left hFb (by positivity))

theorem u11_J_moment2 (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      Integrable (fun ω => ‖gd.Jwin T a ω‖ ^ 2) gd.P₀ ∧ ∫ ω, ‖gd.Jwin T a ω‖ ^ 2 ∂gd.P₀ ≤ C := by
  obtain ⟨K₁, K₂, c, hK₁, hK₂, hc, hpt⟩ := u11_J_pointwise hE gd T hT
  obtain ⟨A, hA0, hA⟩ := u11_weights_bound c T hc hT
  obtain ⟨CM, hCM0, hCM⟩ := u11_eta_moment gd (T + 1) (by linarith) 2 (by norm_num)
  obtain ⟨CY, hCY0, hCY⟩ := u11_eta_moment gd 1 one_pos 2 (by norm_num)
  refine ⟨2 * K₁ ^ 2 * CM + 2 * K₂ ^ 2 * (A ^ 2 * CY), by positivity, fun a ha => ?_⟩
  have hb0 : 0 ≤ max (a - 1) 0 := le_max_right _ _
  obtain ⟨hMm, hMi, hMb⟩ := hCM _ hb0
  have hY := fun k : ℕ => hCY (k : ℝ) (Nat.cast_nonneg k)
  obtain ⟨hI, hM⟩ := u11_wsum_moment (P := gd.P₀) ⌈a + T⌉₊ (fun k => Real.exp (-c * (a - ((k : ℝ) + 1))))
    (fun k ω => ‖procWin (rLvl d) 1 (k : ℝ) gd.η ω‖) (fun k => (Real.exp_pos _).le)
    (fun k ω => norm_nonneg _) (fun k => (hY k).1.norm) 2 (by norm_num) CY
    (fun k => by simpa [Real.rpow_ofNat] using (hY k).2.1)
    (fun k => by simpa [Real.rpow_ofNat] using (hY k).2.2)
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) :=
    Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  have h1 : (∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1)))) ^ 2 * CY ≤ A ^ 2 * CY :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsum0 (hA a ha) 2) hCY0
  have e1 : AEMeasurable (fun ω => ‖gd.Jwin T a ω‖ ^ 2) gd.P₀ :=
    ((continuous_norm (E := TensorDual (PathSpace d m T) 2)).comp_aestronglyMeasurable
      (u11_Jwin_aesm_mem gd T hT a ha).1).aemeasurable.pow_const 2
  have e2 : Integrable (fun ω => ‖procWin (rLvl d) (T + 1) (max (a - 1) 0) gd.η ω‖ ^ 2) gd.P₀ := by
    simpa [Real.rpow_ofNat] using hMi
  have e3 : ∫ ω, ‖procWin (rLvl d) (T + 1) (max (a - 1) 0) gd.η ω‖ ^ 2 ∂gd.P₀ ≤ CM := by
    simpa [Real.rpow_ofNat] using hMb
  have e4 : Integrable (fun ω => (∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) *
      ‖procWin (rLvl d) 1 (k : ℝ) gd.η ω‖) ^ 2) gd.P₀ := hI
  have e5 : ∫ ω, (∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) *
      ‖procWin (rLvl d) 1 (k : ℝ) gd.η ω‖) ^ 2 ∂gd.P₀ ≤ A ^ 2 * CY := hM.trans h1
  have e6 := hpt a ha
  exact u11_sq_moment_of_bound (P := gd.P₀) (fun ω => ‖gd.Jwin T a ω‖)
    (fun ω => ‖procWin (rLvl d) (T + 1) (max (a - 1) 0) gd.η ω‖)
    (fun ω => ∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) *
      ‖procWin (rLvl d) 1 (k : ℝ) gd.η ω‖) e1 K₁ K₂ CM (A ^ 2 * CY) hK₁.le hK₂.le
    (fun ω => norm_nonneg (gd.Jwin T a ω)) e2 e3 e4 e5 e6

end Moments2

end HRS.MC.E213U11

end
