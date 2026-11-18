import HRS.MS.R26T8AP00
import HRS.MS.Ker1Aux4

/-!
# S8.2 local Newton layer, packet T8A.P01 (part a): the dyadic annulus cutoff
`annulus chi R z = chi (z/R) - chi (2 z/R)` vanishes for `|z| <= R/2` and `|z| >= 2R`, is smooth, and has jets `<= Kc R^{-i}`
(scaling lemma `ker1_iteratedFDeriv_comp_smul`).  `psiCut chi R w = 1 - chi (8 w/R)` is `1` for `|w| >= R/4` and `0` for `|w| <= R/8`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_annulus_zero_small {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R) {z : Euc d}
    (hz : ‖z‖ ≤ R / 2) : r26t8a_annulus chi R z = 0 := by
  unfold r26t8a_annulus
  have h1 : ‖R⁻¹ • z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), inv_mul_le_iff₀ hR]; linarith
  have h2 : ‖(2 / R) • z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_eq_mul_div, div_le_one hR]; linarith
  rw [hchi.2.2.2.1 _ h1, hchi.2.2.2.1 _ h2]; ring

theorem r26t8a_annulus_zero_large {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R) {z : Euc d}
    (hz : 2 * R ≤ ‖z‖) : r26t8a_annulus chi R z = 0 := by
  unfold r26t8a_annulus
  have h1 : 2 ≤ ‖R⁻¹ • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), le_inv_mul_iff₀ hR]; linarith
  have h2 : 2 ≤ ‖(2 / R) • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_eq_mul_div, le_div_iff₀ hR]; linarith
  rw [hchi.2.2.2.2 _ h1, hchi.2.2.2.2 _ h2]; ring

theorem r26t8a_annulus_tsupport {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R) :
    tsupport (r26t8a_annulus chi R) ⊆ {z | R / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * R} := by
  refine closure_minimal (fun z hz => ?_) ?_
  · by_contra hn
    simp only [Set.mem_setOf_eq, not_and_or, not_le] at hn
    apply hz
    rcases hn with h | h
    · exact r26t8a_annulus_zero_small hchi hR h.le
    · exact r26t8a_annulus_zero_large hchi hR h.le
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

theorem r26t8a_annulus_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (r26t8a_annulus chi R) := by
  unfold r26t8a_annulus
  exact (hchi.1.comp (contDiff_const_smul _)).sub (hchi.1.comp (contDiff_const_smul _))

theorem r26t8a_chi_hasCompactSupport {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) : HasCompactSupport chi := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall (0 : Euc d) 2)
    (isCompact_closedBall _ _) (fun z hz => ?_)
  by_contra h
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at h
  exact hz (hchi.2.2.2.2 z h.le)

theorem r26t8a_chi_jets {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i chi x‖ ≤ B := by
  have hC : ∀ i : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ i chi y‖ ≤ C := fun i =>
    (hchi.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      ((r26t8a_chi_hasCompactSupport hchi).iteratedFDeriv i)
  choose C hC using hC
  refine ⟨∑ i ∈ Finset.range (k + 1), max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun i hi y => ?_⟩
  have h1 : C i ≤ ∑ i ∈ Finset.range (k + 1), max (C i) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (C i) 0)
      (fun i _ => le_max_right _ _) (Finset.mem_range.2 (by omega)))
  exact (hC i y).trans h1

/-- Jets of `chi (c . )` scale like `c^i`. -/
theorem r26t8a_scaled_jet {chi : Euc d → ℝ} {c : ℝ} (hc : 0 < c) (i : ℕ) (w : Euc d) {B : ℝ}
    (hB : ∀ x, ‖iteratedFDeriv ℝ i chi x‖ ≤ B) :
    ‖iteratedFDeriv ℝ i (fun y => chi (c • y)) w‖ ≤ c ^ i * B := by
  rw [HRS.MS.Ker1.ker1_iteratedFDeriv_comp_smul chi hc.ne' i w, norm_smul, norm_pow, Real.norm_eq_abs,
    abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

theorem r26t8a_annulus_jets {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k : ℕ) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ i ≤ k, ∀ w : Euc d,
      ‖iteratedFDeriv ℝ i (r26t8a_annulus chi R) w‖ ≤ Kc * R ^ (-(i : ℝ)) := by
  obtain ⟨B, hB0, hB⟩ := r26t8a_chi_jets hchi k
  refine ⟨(1 + 2 ^ k) * B, by positivity, fun R hR hR1 i hi w => ?_⟩
  have hcs : ∀ c : ℝ, ContDiff ℝ ∞ (fun y : Euc d => chi (c • y)) := fun c => hchi.1.comp (contDiff_const_smul _)
  unfold r26t8a_annulus
  have hsub : iteratedFDeriv ℝ i (fun y => chi (R⁻¹ • y) - chi ((2 / R) • y)) w =
      iteratedFDeriv ℝ i (fun y => chi (R⁻¹ • y)) w - iteratedFDeriv ℝ i (fun y => chi ((2 / R) • y)) w :=
    iteratedFDeriv_sub_apply (((hcs _).of_le (by exact_mod_cast le_top)).contDiffAt) (((hcs _).of_le (by exact_mod_cast le_top)).contDiffAt)
  rw [hsub]
  refine (norm_sub_le _ _).trans ?_
  have h1 := r26t8a_scaled_jet (chi := chi) (inv_pos.2 hR) i w (hB i hi)
  have h2 := r26t8a_scaled_jet (chi := chi) (show 0 < 2 / R by positivity) i w (hB i hi)
  have hRi : R ^ (-(i : ℝ)) = (R⁻¹) ^ i := by rw [Real.rpow_neg hR.le, Real.rpow_natCast, inv_pow]
  have e2 : (2 / R) ^ i = 2 ^ i * R⁻¹ ^ i := by rw [div_eq_mul_inv, mul_pow]
  have h2i : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi
  have hpos : 0 ≤ R⁻¹ ^ i * B := by positivity
  calc _ ≤ R⁻¹ ^ i * B + (2 / R) ^ i * B := add_le_add h1 h2
    _ = (1 + 2 ^ i) * B * R⁻¹ ^ i := by rw [e2]; ring
    _ ≤ (1 + 2 ^ k) * B * R ^ (-(i : ℝ)) := by
        rw [hRi]
        have : (1 + 2 ^ i : ℝ) ≤ 1 + 2 ^ k := by linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hB0) (by positivity)

/-- Smooth cutoff vanishing near `0` and equal to `1` for `|w| >= R/4`. -/
def r26t8a_psiCut {d : ℕ} (chi : Euc d → ℝ) (R : ℝ) (w : Euc d) : ℝ := 1 - chi ((8 / R) • w)

theorem r26t8a_psiCut_one {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R) {w : Euc d}
    (hw : R / 4 ≤ ‖w‖) : r26t8a_psiCut chi R w = 1 := by
  unfold r26t8a_psiCut
  have : 2 ≤ ‖(8 / R) • w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_eq_mul_div, le_div_iff₀ hR]; linarith
  rw [hchi.2.2.2.2 _ this]; ring

theorem r26t8a_psiCut_zero {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R) {w : Euc d}
    (hw : ‖w‖ ≤ R / 8) : r26t8a_psiCut chi R w = 0 := by
  unfold r26t8a_psiCut
  have : ‖(8 / R) • w‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_eq_mul_div, div_le_one hR]; linarith
  rw [hchi.2.2.2.1 _ this]; ring

theorem r26t8a_psiCut_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (R : ℝ) :
    ContDiff ℝ ∞ (r26t8a_psiCut chi R) := by
  unfold r26t8a_psiCut
  exact contDiff_const.sub (hchi.1.comp (contDiff_const_smul _))

end HRS.MS.R26T8A
