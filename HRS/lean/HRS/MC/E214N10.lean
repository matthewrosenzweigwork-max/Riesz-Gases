import HRS.MC.E214N9

/-!
# E214N10: moment bounds for the two correction terms of the shift identity

`E[‖D_{a+h} - D^{(h)}_a‖ ‖Z‖²] ≤ K e^{-ca}` and `E[‖J_{a+h} - J^{(h)}_a‖ ‖Z‖] ≤ K e^{-ca}`, uniformly in `h ≥ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

theorem integrable_integral_le_of_ae_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F G : Ω → ℝ}
    (hF0 : ∀ ω, 0 ≤ F ω) (hFm : AEStronglyMeasurable F P) (hG : Integrable G P) (hFG : ∀ᵐ ω ∂P, F ω ≤ G ω) :
    Integrable F P ∧ ∫ ω, F ω ∂P ≤ ∫ ω, G ω ∂P := by
  refine ⟨hG.mono' hFm ?_, integral_mono_of_nonneg (Eventually.of_forall hF0) hG hFG⟩
  filter_upwards [hFG] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
  exact hω

section Terms

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)

theorem shift_D_term (gds : GaussData sd.Ss S.β sd.hEs) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (h : ℝ) (hh : 0 ≤ h) (a : ℝ), 0 ≤ a →
      Integrable (fun ω => ‖gds.Dwin T (a + h) ω - (shiftGD_proof sd gds h hh).Dwin T a ω‖ *
        ‖gds.Zwin T (a + h) ω‖ * ‖gds.Zwin T (a + h) ω‖) gds.P₀ ∧
      ∫ ω, ‖gds.Dwin T (a + h) ω - (shiftGD_proof sd gds h hh).Dwin T a ω‖ *
        ‖gds.Zwin T (a + h) ω‖ * ‖gds.Zwin T (a + h) ω‖ ∂gds.P₀ ≤ K * Real.exp (-c * a) := by
  obtain ⟨K, c, hK, hc, hpt⟩ := shift_D_bound sd gds T hT
  obtain ⟨A, hA0, hA⟩ := HRS.MC.E213U11.u11_weights_bound c T hc hT
  obtain ⟨CB, hCB0, hCB⟩ := HRS.MC.E213U11.u11_B_moment gds 1 one_pos 3 (by norm_num)
  obtain ⟨CZ, hCZ0, hCZ⟩ := HRS.MC.E213U11.u11_Z_moment gds T hT 3 (by norm_num)
  refine ⟨K * ((A ^ 3 * CB + 2 * CZ) / 3 + 1), c, by positivity, hc, fun h hh a ha => ?_⟩
  have ha' : 0 ≤ a + h := add_nonneg ha hh
  have hY := fun k : ℕ => hCB (k : ℝ) (Nat.cast_nonneg k)
  obtain ⟨hI, hM⟩ := HRS.MC.E213U11.u11_wsum_moment (P := gds.P₀) ⌈h + T⌉₊
    (fun k => Real.exp (-c * (h - ((k : ℝ) + 1))))
    (fun k ω => ‖toL2 (rLvl d) 1 (fun t => gds.B ((k : ℝ) + t) ω)‖) (fun k => (Real.exp_pos _).le)
    (fun k ω => norm_nonneg _) (fun k => (hY k).1.norm) 3 (by norm_num) CB
    (fun k => by simpa [Real.rpow_ofNat] using (hY k).2.1)
    (fun k => by simpa [Real.rpow_ofNat] using (hY k).2.2)
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range ⌈h + T⌉₊, Real.exp (-c * (h - ((k : ℝ) + 1))) :=
    Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  have hMb : ∫ ω, (∑ k ∈ Finset.range ⌈h + T⌉₊, Real.exp (-c * (h - ((k : ℝ) + 1))) *
      ‖toL2 (rLvl d) 1 (fun t => gds.B ((k : ℝ) + t) ω)‖) ^ 3 ∂gds.P₀ ≤ A ^ 3 * CB :=
    hM.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsum0 (hA h hh) 3) hCB0)
  set Sx : gds.Ω₀ → ℝ := fun ω => ∑ k ∈ Finset.range ⌈h + T⌉₊, Real.exp (-c * (h - ((k : ℝ) + 1))) *
      ‖toL2 (rLvl d) 1 (fun t => gds.B ((k : ℝ) + t) ω)‖ with hSx
  have hSm : AEStronglyMeasurable Sx gds.P₀ :=
    (Finset.aemeasurable_fun_sum _ fun k _ => (hY k).1.norm.const_mul _).aestronglyMeasurable
  have hSx0 : ∀ ω, 0 ≤ Sx ω := fun ω =>
    Finset.sum_nonneg fun k _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  obtain ⟨hZm, hZ3i, hZ3b⟩ := hCZ (a + h) ha'
  have hZ3i' : Integrable (fun ω => ‖gds.Zwin T (a + h) ω‖ ^ 3) gds.P₀ := by simpa [Real.rpow_ofNat] using hZ3i
  have hZ3b' : ∫ ω, ‖gds.Zwin T (a + h) ω‖ ^ 3 ∂gds.P₀ ≤ CZ := by simpa [Real.rpow_ofNat] using hZ3b
  obtain ⟨y1, y2⟩ := HRS.MC.E213U11.u11_young3 (P := gds.P₀) Sx (fun ω => ‖gds.Zwin T (a + h) ω‖) hSx0
    (fun ω => norm_nonneg _) hSm hZm.norm hI hZ3i' (A ^ 3 * CB) CZ hMb hZ3b'
  have hΔ : AEStronglyMeasurable (fun ω => gds.Dwin T (a + h) ω - (shiftGD_proof sd gds h hh).Dwin T a ω) gds.P₀ :=
    (HRS.MC.E213U11.u11_Dwin_aesm gds T hT (a + h) ha').sub
      (HRS.MC.E213U11.u11_Dwin_aesm (shiftGD_proof sd gds h hh) T hT a ha)
  have hmeas : AEStronglyMeasurable (fun ω => ‖gds.Dwin T (a + h) ω - (shiftGD_proof sd gds h hh).Dwin T a ω‖ *
        ‖gds.Zwin T (a + h) ω‖ * ‖gds.Zwin T (a + h) ω‖) gds.P₀ :=
    (hΔ.norm.mul hZm.norm).mul hZm.norm
  have hb : ∀ᵐ ω ∂gds.P₀, ‖gds.Dwin T (a + h) ω - (shiftGD_proof sd gds h hh).Dwin T a ω‖ *
        ‖gds.Zwin T (a + h) ω‖ * ‖gds.Zwin T (a + h) ω‖ ≤
      (K * Real.exp (-c * a)) * (Sx ω * ‖gds.Zwin T (a + h) ω‖ * ‖gds.Zwin T (a + h) ω‖) := by
    filter_upwards [hpt h hh a ha] with ω hω
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hω (norm_nonneg (gds.Zwin T (a + h) ω)))
      (norm_nonneg (gds.Zwin T (a + h) ω))
    refine h1.trans (le_of_eq ?_)
    simp only [hSx]
    ring
  have hIr : Integrable (fun ω => (K * Real.exp (-c * a)) *
      (Sx ω * ‖gds.Zwin T (a + h) ω‖ * ‖gds.Zwin T (a + h) ω‖)) gds.P₀ := y1.const_mul _
  refine ⟨hIr.mono' hmeas ?_, ?_⟩
  · filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))]
    exact hω
  · refine (integral_mono_of_nonneg (Eventually.of_forall fun ω =>
      mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) hIr hb).trans ?_
    rw [integral_const_mul]
    have hKe : 0 ≤ K * Real.exp (-c * a) := mul_nonneg hK.le (Real.exp_pos _).le
    calc K * Real.exp (-c * a) * ∫ ω, Sx ω * ‖gds.Zwin T (a + h) ω‖ * ‖gds.Zwin T (a + h) ω‖ ∂gds.P₀
        ≤ K * Real.exp (-c * a) * ((A ^ 3 * CB + 2 * CZ) / 3) := mul_le_mul_of_nonneg_left y2 hKe
      _ ≤ _ := by nlinarith [hKe]

theorem shift_J_term (gds : GaussData sd.Ss S.β sd.hEs) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (h : ℝ) (hh : 0 ≤ h) (a : ℝ), 0 ≤ a →
      Integrable (fun ω => ‖gds.Jwin T (a + h) ω - (shiftGD_proof sd gds h hh).Jwin T a ω‖ *
        ‖gds.Zwin T (a + h) ω‖) gds.P₀ ∧
      ∫ ω, ‖gds.Jwin T (a + h) ω - (shiftGD_proof sd gds h hh).Jwin T a ω‖ *
        ‖gds.Zwin T (a + h) ω‖ ∂gds.P₀ ≤ K * Real.exp (-c * a) := by
  obtain ⟨K, c, hK, hc, hpt⟩ := shift_J_bound sd gds T hT
  obtain ⟨A, hA0, hA⟩ := HRS.MC.E213U11.u11_weights_bound c T hc hT
  obtain ⟨CY, hCY0, hCY⟩ := HRS.MC.E213U11.u11_eta_moment gds 1 one_pos 2 (by norm_num)
  obtain ⟨CZ, hCZ0, hCZ⟩ := HRS.MC.E213U11.u11_Z_moment gds T hT 2 (by norm_num)
  refine ⟨K * ((A ^ 2 * CY + CZ) / 2 + 1), c, by positivity, hc, fun h hh a ha => ?_⟩
  have ha' : 0 ≤ a + h := add_nonneg ha hh
  have hY := fun k : ℕ => hCY (k : ℝ) (Nat.cast_nonneg k)
  obtain ⟨hI, hM⟩ := HRS.MC.E213U11.u11_wsum_moment (P := gds.P₀) ⌈h + T⌉₊
    (fun k => Real.exp (-c * (h - ((k : ℝ) + 1))))
    (fun k ω => ‖procWin (rLvl d) 1 (k : ℝ) gds.η ω‖) (fun k => (Real.exp_pos _).le)
    (fun k ω => norm_nonneg _) (fun k => (hY k).1.norm) 2 (by norm_num) CY
    (fun k => by simpa [Real.rpow_ofNat] using (hY k).2.1)
    (fun k => by simpa [Real.rpow_ofNat] using (hY k).2.2)
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range ⌈h + T⌉₊, Real.exp (-c * (h - ((k : ℝ) + 1))) :=
    Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  have hMb : ∫ ω, (∑ k ∈ Finset.range ⌈h + T⌉₊, Real.exp (-c * (h - ((k : ℝ) + 1))) *
      ‖procWin (rLvl d) 1 (k : ℝ) gds.η ω‖) ^ 2 ∂gds.P₀ ≤ A ^ 2 * CY :=
    hM.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsum0 (hA h hh) 2) hCY0)
  set Sx : gds.Ω₀ → ℝ := fun ω => ∑ k ∈ Finset.range ⌈h + T⌉₊, Real.exp (-c * (h - ((k : ℝ) + 1))) *
      ‖procWin (rLvl d) 1 (k : ℝ) gds.η ω‖ with hSx
  have hSm : AEStronglyMeasurable Sx gds.P₀ :=
    (Finset.aemeasurable_fun_sum _ fun k _ => (hY k).1.norm.const_mul _).aestronglyMeasurable
  have hSx0 : ∀ ω, 0 ≤ Sx ω := fun ω =>
    Finset.sum_nonneg fun k _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  obtain ⟨hZm, hZ2i, hZ2b⟩ := hCZ (a + h) ha'
  have hZ2i' : Integrable (fun ω => ‖gds.Zwin T (a + h) ω‖ ^ 2) gds.P₀ := by simpa [Real.rpow_ofNat] using hZ2i
  have hZ2b' : ∫ ω, ‖gds.Zwin T (a + h) ω‖ ^ 2 ∂gds.P₀ ≤ CZ := by simpa [Real.rpow_ofNat] using hZ2b
  obtain ⟨y1, y2⟩ := HRS.MC.E213U11.u11_young2 (P := gds.P₀) Sx (fun ω => ‖gds.Zwin T (a + h) ω‖) hSx0
    (fun ω => norm_nonneg _) hSm hZm.norm hI hZ2i' (A ^ 2 * CY) CZ hMb hZ2b'
  have hΔ : AEStronglyMeasurable (fun ω => gds.Jwin T (a + h) ω - (shiftGD_proof sd gds h hh).Jwin T a ω) gds.P₀ :=
    (HRS.MC.E213U11.u11_Jwin_aesm_mem gds T hT (a + h) ha').1.sub
      (HRS.MC.E213U11.u11_Jwin_aesm_mem (shiftGD_proof sd gds h hh) T hT a ha).1
  have hn : AEStronglyMeasurable (fun ω => ‖gds.Jwin T (a + h) ω - (shiftGD_proof sd gds h hh).Jwin T a ω‖) gds.P₀ :=
    (continuous_norm (E := TensorDual (PathSpace d m T) 2)).comp_aestronglyMeasurable hΔ
  have hmeas : AEStronglyMeasurable (fun ω => ‖gds.Jwin T (a + h) ω - (shiftGD_proof sd gds h hh).Jwin T a ω‖ *
        ‖gds.Zwin T (a + h) ω‖) gds.P₀ := hn.mul hZm.norm
  have hb : ∀ᵐ ω ∂gds.P₀, ‖gds.Jwin T (a + h) ω - (shiftGD_proof sd gds h hh).Jwin T a ω‖ *
        ‖gds.Zwin T (a + h) ω‖ ≤ (K * Real.exp (-c * a)) * (Sx ω * ‖gds.Zwin T (a + h) ω‖) := by
    filter_upwards [hpt h hh a ha] with ω hω
    have h1 := mul_le_mul_of_nonneg_right hω (norm_nonneg (gds.Zwin T (a + h) ω))
    refine h1.trans (le_of_eq ?_)
    simp only [hSx]
    ring
  have hIr : Integrable (fun ω => (K * Real.exp (-c * a)) * (Sx ω * ‖gds.Zwin T (a + h) ω‖)) gds.P₀ :=
    y1.const_mul _
  have key := integrable_integral_le_of_ae_le
    (F := fun ω : gds.Ω₀ => ‖gds.Jwin T (a + h) ω - (shiftGD_proof sd gds h hh).Jwin T a ω‖ *
        ‖gds.Zwin T (a + h) ω‖)
    (G := fun ω => (K * Real.exp (-c * a)) * (Sx ω * ‖gds.Zwin T (a + h) ω‖))
    (fun ω => mul_nonneg (norm_nonneg (gds.Jwin T (a + h) ω - (shiftGD_proof sd gds h hh).Jwin T a ω))
      (norm_nonneg _)) hmeas hIr hb
  refine ⟨key.1, key.2.trans ?_⟩
  rw [integral_const_mul]
  have hKe : 0 ≤ K * Real.exp (-c * a) := mul_nonneg hK.le (Real.exp_pos _).le
  calc K * Real.exp (-c * a) * ∫ ω, Sx ω * ‖gds.Zwin T (a + h) ω‖ ∂gds.P₀
      ≤ K * Real.exp (-c * a) * ((A ^ 2 * CY + CZ) / 2) := mul_le_mul_of_nonneg_left y2 hKe
    _ ≤ _ := by nlinarith [hKe]

end Terms

end HRS.MC.E214N

end
