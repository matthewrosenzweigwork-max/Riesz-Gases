import HRS.MS.SA16QMorrey1

/-!
# S.A.16 (SA16Q), E11 part 2: scaling and Holder on the annulus

`sa16q_A d = {1 < |z| < 2}` (open, positive finite measure).  Facts:

* `sa16q_scale`: `∫⁻ z, ph (x + t • z) = ofReal (t^(-d)) * ∫⁻ y, ph y` for `t > 0`;
* `sa16q_annulus_holder`: `∫⁻_A ph (x + t z) dz ≤ vol(A)^{1/q} t^{-d/p} ‖ph‖_{L^p}`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Nat

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Scale
variable {d : ℕ}

/-- the open annulus `1 < |z| < 2` -/
def sa16q_A (d : ℕ) : Set (Euc d) := Metric.ball (0 : Euc d) 2 \ Metric.closedBall 0 1

lemma sa16q_A_meas (d : ℕ) : MeasurableSet (sa16q_A d) :=
  Metric.isOpen_ball.measurableSet.diff Metric.isClosed_closedBall.measurableSet

lemma sa16q_A_mem {z : Euc d} (hz : z ∈ sa16q_A d) : 1 < ‖z‖ ∧ ‖z‖ < 2 := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨?_, by simpa using h1⟩
  by_contra h
  exact h2 (by simpa using not_lt.1 h)

lemma sa16q_A_pos (hd : 1 ≤ d) : 0 < volume (sa16q_A d) := by
  have hopen : IsOpen (sa16q_A d) :=
    Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hn : ‖(3 / 2 : ℝ) • (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Euc d)‖ = 3 / 2 := by
    rw [norm_smul, EuclideanSpace.norm_single]; norm_num
  refine hopen.measure_pos volume ⟨(3 / 2 : ℝ) • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), ?_⟩
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, hn]; norm_num
  · rw [mem_closedBall_zero_iff, hn]; norm_num

lemma sa16q_A_fin (d : ℕ) : volume (sa16q_A d) < ⊤ :=
  lt_of_le_of_lt (measure_mono Set.diff_subset) measure_ball_lt_top

/-- change of variables `z ↦ x + t z` in the lower integral -/
lemma sa16q_scale {t : ℝ} (ht : 0 < t) (x : Euc d) {ph : Euc d → ℝ≥0∞} (hph : Measurable ph) :
    ∫⁻ z, ph (x + t • z) = ENNReal.ofReal ((t ^ d)⁻¹) * ∫⁻ y, ph y := by
  have hψ : Measurable (fun y : Euc d => ph (x + y)) := hph.comp (measurable_const_add x)
  have hsm : Measurable (fun z : Euc d => t • z) := measurable_const_smul t
  have h1 : ∫⁻ z, ph (x + t • z) = ∫⁻ y, ph (x + y) ∂(Measure.map (fun z : Euc d => t • z) volume) := by
    rw [lintegral_map hψ hsm]
  rw [h1, Measure.map_addHaar_smul (volume : Measure (Euc d)) ht.ne', lintegral_smul_measure,
    lintegral_add_left_eq_self (fun y => ph y) x]
  simp [finrank_euclideanSpace, abs_of_pos (inv_pos.2 (pow_pos ht d))]

/-- Holder on the annulus for the rescaled integrand -/
lemma sa16q_annulus_holder (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) {t : ℝ} (ht : 0 < t) (x : Euc d)
    {ph : Euc d → ℝ≥0∞} (hph : Measurable ph) :
    ∫⁻ z in sa16q_A d, ph (x + t • z) ≤
      volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
        (ENNReal.ofReal (((t ^ d)⁻¹) ^ (1 / p)) * (∫⁻ y, ph y ^ p) ^ (1 / p)) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  set q := Real.conjExponent p with hq
  have hp0 : 0 ≤ 1 / p := one_div_nonneg.2 (by linarith)
  have hmeasf : Measurable (fun z : Euc d => ph (x + t • z)) :=
    hph.comp ((measurable_const_add x).comp (measurable_const_smul t))
  have h1 : ∫⁻ z in sa16q_A d, ph (x + t • z) =
      ∫⁻ z, ((fun z => ph (x + t • z)) * (sa16q_A d).indicator (1 : Euc d → ℝ≥0∞)) z := by
    rw [← lintegral_indicator (sa16q_A_meas d)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ sa16q_A d <;> simp [hz]
  rw [h1]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hmeasf.aemeasurable
    ((measurable_one.indicator (sa16q_A_meas d)).aemeasurable)).trans ?_
  have h2 : ∫⁻ z, ((sa16q_A d).indicator (1 : Euc d → ℝ≥0∞) z) ^ q = volume (sa16q_A d) := by
    have : (fun z : Euc d => ((sa16q_A d).indicator (1 : Euc d → ℝ≥0∞) z) ^ q) =
        (sa16q_A d).indicator 1 := by
      funext z
      by_cases hz : z ∈ sa16q_A d
      · simp [hz]
      · simp [hz, ENNReal.zero_rpow_of_pos hpq.symm.pos]
    rw [this, lintegral_indicator (sa16q_A_meas d)]
    simp
  have h3 : ∫⁻ z, ph (x + t • z) ^ p = ENNReal.ofReal ((t ^ d)⁻¹) * ∫⁻ y, ph y ^ p :=
    sa16q_scale ht x (ph := fun y => ph y ^ p) (hph.pow_const p)
  try simp only [Pi.mul_apply]
  rw [h2, h3, ENNReal.mul_rpow_of_nonneg _ _ hp0,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0]
  rw [mul_comm]

end Scale

end HRS.Whole.AppendixA.Phase2SA16Q
