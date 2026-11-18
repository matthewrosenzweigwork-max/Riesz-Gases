import HRS.MC.S7FCF5RPath
import HRS.MC.S7FCF5MU

/-!
# Packet fcf5r, E3b = F5: proof of `fcf5_E3b_F5_zeta_moments` (`S7FCF5Plan.lean`)

Route (the five steps of the docstring of `fcf5_E3b_F5_zeta_moments`):

1. pointwise `‖windowFluc ω‖ₑ ≤ Ŝ(ω)` (`S7FCF5R_windowFluc_le`, every `ω`; the zero path is `0`);
2. pointwise `‖zetaWin ω‖ₑ ≤ Ŝ(ω) + β`, `β = ∫⁻ Ŝ dP` (`S7FCF5R_zetaWin_le`, from E3a);
3. `∫⁻ (Ŝ+β)^q ≤ 2^{q-1} (∫⁻ Ŝ^q + β^q)` and `β ≤ 1 + ∫⁻ Ŝ^q` (no Jensen, no measurability of `Ŝ` needed);
4. the moment `∫⁻ Ŝ^q ≤ ofReal Cd` from D2 (`fcf5_D2_Shat_moment_proof`, `S7FCF5OD2.lean`);
5. `Integrable` from `AEMeasurable` (E2, `fcf5_E2_window_aemeasurable_proof`) and the finite `lintegral`
   (`S7FCF5R_moment_of_enorm`).

Namespace `HRS.MC.Sec7.S7FCF5R`, `_proof` for the theorem.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5R

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- **E3b = F5 (moments of the path components), proof.**  Statement verbatim from `S7FCF5Plan.lean`. -/
theorem fcf5_E3b_F5_zeta_moments_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T) (q : ℝ)
    (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        (Integrable (fun ω => ‖zetaWin r T a P X ω‖ ^ q) P ∧ ∫ ω, ‖zetaWin r T a P X ω‖ ^ q ∂P ≤ C) ∧
        (Integrable (fun ω => ‖HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω‖ ^ q) P ∧
          ∫ ω, ‖HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω‖ ^ q ∂P ≤ C) := by
  have hd : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨Cd, hCd⟩ := HRS.MC.Sec7.S7FCF5O.fcf5_D2_Shat_moment_proof R r hr T hT q hq
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = max Cd 0 := ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by
    rw [hCb]
    exact le_max_right _ _
  have hCbd : Cd ≤ Cb := by
    rw [hCb]
    exact le_max_left _ _
  have hC2 : (0 : ℝ) ≤ 2 ^ (q - 1) := Real.rpow_nonneg (by norm_num) _
  have hC1 : (0 : ℝ) ≤ (1 + Cb) ^ q := Real.rpow_nonneg (by linarith) _
  have hCout : 0 ≤ Cb + 2 ^ (q - 1) * (Cb + (1 + Cb) ^ q) :=
    add_nonneg hCb0 (mul_nonneg hC2 (add_nonneg hCb0 hC1))
  refine ⟨Cb + 2 ^ (q - 1) * (Cb + (1 + Cb) ^ q), ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hprep
  have hN1 : 1 ≤ N := by omega
  have hX : ∀ t : ℝ≥0, Measurable (X t) := (hprep.solution 0).adapted
  -- (4) the moment of the window supremum, from D2
  have hM : ∫⁻ ω, fcf5Shat R r a T X ω ^ q ∂P ≤ ENNReal.ofReal Cb :=
    (hCd N hN P X₀ W X hprep a ha).trans (ENNReal.ofReal_le_ofReal hCbd)
  -- (3) the mean `β` of the supremum and its bound
  set β : ℝ≥0∞ := ∫⁻ ω', fcf5Shat R r a T X ω' ∂P with hβdef
  have hβ1 : β ≤ ENNReal.ofReal (1 + Cb) := by
    calc β ≤ ∫⁻ ω', (1 + fcf5Shat R r a T X ω' ^ q) ∂P :=
          lintegral_mono fun ω' => HRS.MC.Sec7.S7FCF5B.S7FCF5B_enorm_le_one_add_rpow hq _
      _ = 1 + ∫⁻ ω', fcf5Shat R r a T X ω' ^ q ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + ENNReal.ofReal Cb := add_le_add le_rfl hM
      _ = ENNReal.ofReal (1 + Cb) := by
          rw [ENNReal.ofReal_add zero_le_one hCb0, ENNReal.ofReal_one]
  have hβq : β ^ q ≤ ENNReal.ofReal ((1 + Cb) ^ q) := by
    calc β ^ q ≤ (ENNReal.ofReal (1 + Cb)) ^ q := ENNReal.rpow_le_rpow hβ1 hq0
      _ = ENNReal.ofReal ((1 + Cb) ^ q) := ENNReal.ofReal_rpow_of_nonneg (by linarith) hq0
  -- (2)-(3) the moment of the particle window `ζ`
  have hMζ : ∫⁻ ω, ‖zetaWin r T a P X ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (2 ^ (q - 1) * (Cb + (1 + Cb) ^ q)) := by
    calc ∫⁻ ω, ‖zetaWin r T a P X ω‖ₑ ^ q ∂P
        ≤ ∫⁻ ω, (fcf5Shat R r a T X ω + β) ^ q ∂P :=
          lintegral_mono fun ω =>
            ENNReal.rpow_le_rpow (S7FCF5R_zetaWin_le R r hd T hT hN1 P X hX a ha ω) hq0
      _ ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ (q - 1) * (fcf5Shat R r a T X ω ^ q + β ^ q) ∂P :=
          lintegral_mono fun ω => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
      _ = (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ ω, fcf5Shat R r a T X ω ^ q ∂P + β ^ q) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top),
            lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ (2 : ℝ≥0∞) ^ (q - 1) * (ENNReal.ofReal Cb + ENNReal.ofReal ((1 + Cb) ^ q)) :=
          mul_le_mul_of_nonneg_left (add_le_add hM hβq) bot_le
      _ = ENNReal.ofReal (2 ^ (q - 1) * (Cb + (1 + Cb) ^ q)) := by
          rw [HRS.MC.Sec7.S7FCF5M.S7FCF5M_two_rpow, ← ENNReal.ofReal_add hCb0 hC1,
            ← ENNReal.ofReal_mul hC2]
  -- (1) the moment of the `E_r`-window `η`
  have hMW : ∫⁻ ω, ‖HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal Cb :=
    calc ∫⁻ ω, ‖HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω‖ₑ ^ q ∂P
        ≤ ∫⁻ ω, fcf5Shat R r a T X ω ^ q ∂P :=
          lintegral_mono fun ω =>
            ENNReal.rpow_le_rpow (S7FCF5R_windowFluc_le R r T hT X a ha ω) hq0
      _ ≤ ENNReal.ofReal Cb := hM
  -- (5) measurability (E2) and the conclusion
  have hE2 := HRS.MC.Sec7.S7FCF5I.fcf5_E2_window_aemeasurable_proof R r hr T hT hN1 P X₀ W X hprep a ha
  have hζC : ∫⁻ ω, ‖zetaWin r T a P X ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (Cb + 2 ^ (q - 1) * (Cb + (1 + Cb) ^ q)) :=
    hMζ.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hCb0))
  have hWC : ∫⁻ ω, ‖HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (Cb + 2 ^ (q - 1) * (Cb + (1 + Cb) ^ q)) :=
    hMW.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (mul_nonneg hC2 (add_nonneg hCb0 hC1))))
  exact ⟨S7FCF5R_moment_of_enorm P (zetaWin r T a P X) hE2.2 q hq0 _ hCout hζC,
    S7FCF5R_moment_of_enorm P (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ) hE2.1 q hq0 _ hCout hWC⟩

end HRS.MC.Sec7.S7FCF5R

end
