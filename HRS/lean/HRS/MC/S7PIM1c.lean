import HRS.MC.S7PIM1b
import HRS.MC.S7FCF5F6a

/-!
# Packet piM, part M1c: the first moment of `ℬ_N^t` in `E_m`, uniformly in `t ≥ 0`, for every `N ≥ 1` (prefix `S7PIM_`)

* `S7PIM_B_embed`: `quadFieldAt m = embedCLM (quadFieldAt r)` when the `E_r`-field is integrable;
* `S7PIM_integrable_tilde`: for `N ≥ 2` the field `ℬ̃_N^t` is integrable in `E_r` (from `fcf5_F6a_B_section_moment_proof`);
* `S7PIM_B_moment`: `∃ C, ∀ t ≥ 0, ∫⁻ ‖ℬ_N^t‖_{E_m} ≤ C` for `N ≥ 1` (`N ≥ 2` by FC-F6a, `N = 1` by boundedness).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIM

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

theorem S7PIM_B_embed (R : Regime d) {r m : ℝ} (hr : (d : ℝ) < 2 * (r - 2)) (hrm : r ≤ m) {N : ℕ}
    (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) {t : ℝ}
    (ht : 0 ≤ t)
    (hint : Integrable (fun ω => quadFieldTilde r R.D.s (withDensityReal (R.ρ t)) (X t.toNNReal ω)) P)
    (ω : Ω) :
    quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω =
      HRS.MD.EQInterp.embedCLM hrm (quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω) := by
  unfold quadFieldAt
  simp_rw [S7PIM_tilde_embed R hr hrm hN ht]
  rw [map_sub, ContinuousLinearMap.integral_comp_comm _ hint]

/-- Measurability of `ω ↦ ℬ̃_N^t(X_t ω)`. -/
theorem S7PIM_tilde_measurable (R : Regime d) (r : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ s : ℝ≥0, Measurable (X s)) {t : ℝ} (ht : 0 ≤ t) :
    Measurable fun ω => quadFieldTilde r R.D.s (withDensityReal (R.ρ t)) (X t.toNNReal ω) := by
  have h := (HRS.MC.Sec7.S7FCW12.s7fcw12_quadTilde_measurable R r (N := N)).comp
    ((measurable_const (a := t)).prodMk (hadapt t.toNNReal))
  have hμ : withDensityReal (R.ρ t) =
      withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (t, y) := by
    congr 1
    funext y
    rw [HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos_eq R ht y]
  rw [hμ]
  exact h

/-- For `N ≥ 2` the field `ℬ̃_N^t` is integrable in `E_{2d+6}`. -/
theorem S7PIM_integrable_tilde (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) {N : ℕ} (hN2 : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : FCPrepared R P X₀ W X) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => quadFieldTilde r R.D.s (withDensityReal (R.ρ t)) (X t.toNNReal ω)) P := by
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7FCF5F.fcf5_F6a_B_section_moment_proof R r hr 1 le_rfl
  have hmeas := S7PIM_tilde_measurable R r X (hreal.solution 0).adapted ht
  by_contra hni
  have h0 : ∫ ω', quadFieldTilde r R.D.s (withDensityReal (R.ρ t)) (X t.toNNReal ω') ∂P = 0 :=
    integral_undef hni
  have hB := hC N hN2 P X₀ W X hreal t ht
  simp only [quadFieldAt, h0, sub_zero, ENNReal.rpow_one] at hB
  exact hni ⟨hmeas.aestronglyMeasurable, lt_of_le_of_lt hB ENNReal.ofReal_lt_top⟩

/-- The first moment of `ℬ_N^t` in `E_m`, uniformly in `t ≥ 0`, for every `N ≥ 1`. -/
theorem S7PIM_B_moment (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : FCPrepared R P X₀ W X) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ∂P ≤ ENNReal.ofReal C := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr : (d : ℝ) < 2 * (2 * (d : ℝ) + 6 - 2) := by linarith
  have hrm : 2 * (d : ℝ) + 6 ≤ m := by linarith
  have hN0 : 0 < N := hN
  rcases Nat.lt_or_ge N 2 with h1 | h2
  · -- `N = 1`: the field is bounded
    have hN1 : N = 1 := by omega
    subst hN1
    obtain ⟨C1, hC1⟩ := S7PIM_tilde_bdd_one R (m := m) (by linarith)
    refine ⟨2 * C1, fun t ht => ?_⟩
    have hbd : ∀ ω, ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ ≤ 2 * C1 := by
      intro ω
      unfold quadFieldAt
      have h1 := hC1 t ht (X t.toNNReal ω)
      have h2 : ‖∫ ω', quadFieldTilde m R.D.s (withDensityReal (R.ρ t)) (X t.toNNReal ω') ∂P‖ ≤ C1 := by
        have := norm_integral_le_of_norm_le_const (μ := P) (C := C1)
          (f := fun ω' => quadFieldTilde m R.D.s (withDensityReal (R.ρ t)) (X t.toNNReal ω'))
          (Eventually.of_forall fun ω' => hC1 t ht (X t.toNNReal ω'))
        simpa using this
      calc _ ≤ _ := norm_sub_le _ _
        _ ≤ C1 + C1 := add_le_add h1 h2
        _ = 2 * C1 := by ring
    calc ∫⁻ ω, ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ∂P
        ≤ ∫⁻ _ω, ENNReal.ofReal (2 * C1) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hbd ω)
      _ = ENNReal.ofReal (2 * C1) := by simp
  · -- `N ≥ 2`: FC-F6a
    obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7FCF5F.fcf5_F6a_B_section_moment_proof R (2 * (d : ℝ) + 6) rfl 1 le_rfl
    refine ⟨C, fun t ht => ?_⟩
    have hint := S7PIM_integrable_tilde R _ rfl h2 P X₀ W X hreal ht
    have hB := hC N h2 P X₀ W X hreal t ht
    simp only [ENNReal.rpow_one] at hB
    refine le_trans (lintegral_mono fun ω => ?_) hB
    rw [S7PIM_B_embed R hr hrm hN0 P X ht hint ω]
    have := (HRS.MD.EQInterp.embedCLM (d := d) hrm).le_opNorm
      (quadFieldAt (2 * (d : ℝ) + 6) R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω)
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal (this.trans ?_)
    have hop : ‖(HRS.MD.EQInterp.embedCLM (d := d) hrm)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun F => by
        rw [HRS.MD.EQInterp.embedCLM_apply, one_mul]
        exact NegSobolev.norm_embed_le m hrm F
    exact mul_le_of_le_one_left (norm_nonneg _) hop

end HRS.MC.Sec7.S7PIM

end
