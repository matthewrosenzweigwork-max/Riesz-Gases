import HRS.MS.UlocCutAux1
import HRS.Whole.AppendixA

/-!
# MS-ULOC-CUT, part 2: the key lemma (comparison of two cutoffs through a finite net)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UlocCut
open HRS.Whole.AppendixA

variable {d : ℕ}

/-- a smooth compactly supported inverse of `p ↦ ∑_{y∈Y} χ'(p - y)` on `closedBall 0 R` -/
theorem uc_exists_R (χ' : Euc d → ℝ) (hχ' : IsUlocCutoff χ') (Y : Finset (Euc d)) (R : ℝ)
    (hR : 0 < R) (hY : ∀ p : Euc d, ‖p‖ ≤ R → ∃ y ∈ Y, ‖p - y‖ ≤ 1) :
    ∃ ρ : Euc d → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      ∀ p : Euc d, ‖p‖ ≤ R → ρ p * ∑ y ∈ Y, χ' (p - y) = 1 := by
  set Sg : Euc d → ℝ := fun p => ∑ y ∈ Y, χ' (p - y) with hSg
  have hS : ContDiff ℝ ∞ Sg :=
    ContDiff.sum fun y _ => hχ'.1.comp (contDiff_id.sub contDiff_const)
  have hge : ∀ p : Euc d, ‖p‖ ≤ R → 1 ≤ Sg p := by
    intro p hp
    obtain ⟨y, hy, hpy⟩ := hY p hp
    have h1 : χ' (p - y) = 1 := hχ'.2.2.2.2 _ (by simpa using hpy)
    calc (1 : ℝ) = χ' (p - y) := h1.symm
      _ ≤ Sg p := Finset.single_le_sum (f := fun y => χ' (p - y))
          (fun y _ => (hχ'.2.2.2.1 _).1) hy
  have hU : IsOpen {p : Euc d | 1 / 2 < Sg p} := isOpen_lt continuous_const hS.continuous
  have hKU : Metric.closedBall (0 : Euc d) R ⊆ {p : Euc d | 1 / 2 < Sg p} := fun p hp => by
    have := hge p (by simpa using hp)
    show 1 / 2 < Sg p
    linarith
  obtain ⟨δ, hδ, hth⟩ := (isCompact_closedBall (0 : Euc d) R).exists_thickening_subset_open hU hKU
  let f : ContDiffBump (0 : Euc d) := ⟨R, R + δ / 2, hR, by linarith⟩
  have hts : tsupport f ⊆ {p : Euc d | 1 / 2 < Sg p} := by
    rw [f.tsupport_eq]
    intro p hp
    apply hth
    rw [thickening_closedBall hδ hR.le]
    have : ‖p‖ ≤ R + δ / 2 := by simpa [f] using hp
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  refine ⟨fun p => f p / Sg p, ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : Sg x = 0
    · have hxn : x ∉ tsupport f := fun h => by
        have := hts h
        simp only [Set.mem_ofPred_eq] at this
        linarith
      have hev := notMem_tsupport_iff_eventuallyEq.1 hxn
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      simp [hy]
    · exact (f.contDiff.contDiffAt).div (hS.contDiffAt) hx
  · refine f.hasCompactSupport.mono' ?_
    intro y hy
    refine subset_tsupport _ ?_
    intro h0
    exact hy (by simp [h0])
  · intro p hp
    have h1 : f p = 1 := f.one_of_mem_closedBall (by simpa [f] using hp)
    have h2 := hge p hp
    show f p / Sg p * Sg p = 1
    rw [h1]; field_simp

theorem uc_key (m : ℕ) (χ χ' : Euc d → ℝ) (hχ : IsUlocCutoff χ) (hχ' : IsUlocCutoff χ')
    (Y : Finset (Euc d)) (R1 : ℝ) (hR1 : 0 ≤ R1)
    (hY : ∀ p : Euc d, ‖p‖ ≤ 2 + R1 → ∃ y ∈ Y, ‖p - y‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z w : Euc d, ‖z - w‖ ≤ R1 → ∀ u : Euc d → ℝ,
      HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - z) * u x) ≤
        ENNReal.ofReal C * ∑ y ∈ Y, HRS.Whole.sobolevNormE (m : ℝ)
          (fun x => χ' (x - (w + y)) * u x) := by
  obtain ⟨ρ, hρ, hρc, hρ1⟩ := uc_exists_R χ' hχ' Y (2 + R1) (by linarith) hY
  obtain ⟨C1, hC1, h1⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ)
    (Nat.cast_nonneg m) χ hχ.1 hχ.2.1
  obtain ⟨C2, hC2, h2⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ)
    (Nat.cast_nonneg m) ρ hρ hρc
  refine ⟨C1 * C2, mul_pos hC1 hC2, fun z w hzw u => ?_⟩
  have hpt : (fun x => χ (x - z) * u x) =
      fun x => χ (x - z) * (ρ (x - w) * ∑ y ∈ Y, (χ' (x - (w + y)) * u x)) := by
    funext x
    by_cases hx : χ (x - z) = 0
    · simp [hx]
    · have hsup : x - z ∈ Metric.ball (0 : Euc d) 2 :=
        hχ.2.2.1 (subset_tsupport _ (Function.mem_support.2 hx))
      have hn : ‖x - z‖ < 2 := by simpa using hsup
      have hxw : ‖x - w‖ ≤ 2 + R1 := by
        calc ‖x - w‖ = ‖(x - z) + (z - w)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖x - z‖ + ‖z - w‖ := norm_add_le _ _
          _ ≤ 2 + R1 := by linarith
      have := hρ1 (x - w) hxw
      rw [← Finset.sum_mul]
      have e : ∑ y ∈ Y, χ' (x - (w + y)) = ∑ y ∈ Y, χ' (x - w - y) :=
        Finset.sum_congr rfl fun y _ => by rw [sub_sub]
      rw [e, ← mul_assoc (ρ (x - w)), this, one_mul]
  rw [hpt]
  calc HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - z) *
        (ρ (x - w) * ∑ y ∈ Y, (χ' (x - (w + y)) * u x)))
      ≤ ENNReal.ofReal C1 * HRS.Whole.sobolevNormE (m : ℝ)
          (fun x => ρ (x - w) * ∑ y ∈ Y, (χ' (x - (w + y)) * u x)) :=
        h1 z _
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal C2 * HRS.Whole.sobolevNormE (m : ℝ)
          (fun x => ∑ y ∈ Y, (χ' (x - (w + y)) * u x))) := by
        gcongr
        exact h2 w _
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal C2 * ∑ y ∈ Y, HRS.Whole.sobolevNormE (m : ℝ)
          (fun x => χ' (x - (w + y)) * u x)) := by
        gcongr
        exact uc_sum_le (m : ℝ) Y (fun y x => χ' (x - (w + y)) * u x)
    _ = ENNReal.ofReal (C1 * C2) * ∑ y ∈ Y, HRS.Whole.sobolevNormE (m : ℝ)
          (fun x => χ' (x - (w + y)) * u x) := by
        rw [ENNReal.ofReal_mul hC1.le, mul_assoc]

end HRS.MS.UlocCut
