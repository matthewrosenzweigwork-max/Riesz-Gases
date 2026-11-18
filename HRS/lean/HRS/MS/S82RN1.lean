import HRS.MS.WrRowAux3
import HRS.MS.S82P2Sum3

/-!
# S8.2 R02 (S82R), N1: the level-set row bounds for a `ShortRangePole` at `s = d/2`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

lemma s82r_crit_ne (hd : 1 ≤ d) : criticalS d ≠ 0 := by
  unfold criticalS
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  intro h; linarith

/-- `q(w) ≤ A (1 + |w|^{-s})` off the origin. -/
lemma s82r_q_envelope (hd : 1 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : Euc d, w ≠ 0 → q w ≤ A * (1 + HRS.Whole.rieszWeight (criticalS d) w) := by
  obtain ⟨K1, hK1, hqK⟩ := HRS.MS.S82P2.s82p2_q_le hq
  refine ⟨2 * K1, by positivity, fun w hw => ?_⟩
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hrw : HRS.Whole.rieszWeight (criticalS d) w = ‖w‖ ^ (-criticalS d) := by
    unfold HRS.Whole.rieszWeight; rw [if_neg (s82r_crit_ne hd)]
  rw [hrw]
  have h1 := hqK w hw
  have hp : 0 ≤ ‖w‖ ^ (-criticalS d) := Real.rpow_nonneg hn.le _
  by_cases h : ‖w‖ < 1
  · rw [min_eq_right h.le] at h1
    nlinarith
  · push Not at h
    rw [min_eq_left h, Real.one_rpow] at h1
    nlinarith

/-- The level-set row bounds at `s = d/2`. -/
lemma s82r_rows (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ x : Euc d,
        (∀ L : ℝ, 0 < L →
          Integrable (fun y => max (q (x - y) - L) 0) (HRS.Whole.withDensityReal ρ) ∧
          ∫ y, max (q (x - y) - L) 0 ∂(HRS.Whole.withDensityReal ρ) ≤ Ca / L) ∧
        (∀ L : ℝ, 1 ≤ L →
          Integrable (fun y => (min (q (x - y)) L) ^ 2) (HRS.Whole.withDensityReal ρ) ∧
          ∫ y, (min (q (x - y)) L) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
            Cb * Real.log (Real.exp 1 * L)) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨A, hA0, hA⟩ := s82r_q_envelope hd1 hq
  obtain ⟨Ca, Cb, hCa, hCb, H⟩ := HRS.MS.Wr.wr3_row_bounds_real_integral hd1 hs0 hsd A M
  refine ⟨Ca, Cb, hCa, hCb, fun ρ hρ hM x => ?_⟩
  have hmeas : Measurable (Function.uncurry fun x y : Euc d => q (x - y)) :=
    hq.measurable.comp (measurable_fst.sub measurable_snd)
  have h := H ρ hρ hM (fun x y => q (x - y)) hmeas (fun x y => hq.nonneg _)
    (fun x y hxy => hA _ (sub_ne_zero.2 hxy)) x
  have hs : criticalS d ≠ 0 := s82r_crit_ne hd1
  have hσ : HRS.WeakRef.sigmaOf d (criticalS d) = criticalS d := by
    unfold HRS.WeakRef.sigmaOf; rw [if_neg hs]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hexp : 1 - (d : ℝ) / HRS.WeakRef.sigmaOf d (criticalS d) = -1 := by
    rw [hσ]; unfold criticalS; field_simp; norm_num
  have hψ : ∀ L : ℝ, HRS.WeakRef.psi2 d (criticalS d) L = Real.log (Real.exp 1 * L) := by
    intro L
    unfold HRS.WeakRef.psi2
    rw [if_neg (by unfold criticalS; exact lt_irrefl _), if_pos (by unfold criticalS; rfl)]
  refine ⟨fun L hL => ?_, fun L hL => ?_⟩
  · obtain ⟨hi, hb⟩ := h.1 L hL
    refine ⟨hi, hb.trans ?_⟩
    rw [hexp, Real.rpow_neg_one, div_eq_mul_inv, mul_comm]
  · obtain ⟨hi, hb⟩ := h.2 L hL
    exact ⟨hi, by rw [hψ] at hb; exact hb⟩

end HRS.MS.S82R

end
