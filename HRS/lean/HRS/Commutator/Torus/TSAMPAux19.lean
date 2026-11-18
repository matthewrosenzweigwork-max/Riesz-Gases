import HRS.Commutator.Torus.TSAMPAux18

/-!
# T-SAMP helpers, part 19: the abstract sampling inequality
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- The closed `tdist`-ball. -/
def tsampBall (R : ℝ) (x : Torus d) : Set (Torus d) := {y | KernelGrad.tdist x y ≤ R}

lemma tsamp_measurableSet_ball (R : ℝ) : MeasurableSet {z : Torus d | KernelGrad.tdist z 0 ≤ R} :=
  measurableSet_le (tsamp_measurable_tdist 0) measurable_const

lemma tsamp_ball_eq (R : ℝ) (y : Torus d) :
    {x : Torus d | KernelGrad.tdist x y ≤ R} = (fun x => x - y) ⁻¹' {z | KernelGrad.tdist z 0 ≤ R} := by
  ext x
  simp [KernelGrad.tdist_eq_sub_zero x y]

lemma tsamp_ball_volume_translate (R : ℝ) (y : Torus d) :
    volume {x : Torus d | KernelGrad.tdist x y ≤ R} = volume {z : Torus d | KernelGrad.tdist z 0 ≤ R} := by
  rw [tsamp_ball_eq]
  exact (measurePreserving_sub_right (volume : Measure (Torus d)) y).measure_preimage
    (tsamp_measurableSet_ball R).nullMeasurableSet

lemma tsamp_ball_lintegral (R : ℝ) {G : Torus d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, ∫⁻ y in tsampBall R x, G y =
      volume {z : Torus d | KernelGrad.tdist z 0 ≤ R} * ∫⁻ y, G y := by
  have hset : MeasurableSet {q : Torus d × Torus d | KernelGrad.tdist q.1 q.2 ≤ R} :=
    measurableSet_le (by
      have : Continuous fun q : Torus d × Torus d => KernelGrad.tdist q.1 q.2 := by
        simp_rw [CoercAux.tdist_eq_sqrt]; fun_prop
      exact this.measurable) measurable_const
  have h1 : ∀ x, ∫⁻ y in tsampBall R x, G y =
      ∫⁻ y, {q : Torus d × Torus d | KernelGrad.tdist q.1 q.2 ≤ R}.indicator (fun q => G q.2) (x, y) := by
    intro x
    have hBx : MeasurableSet (tsampBall (d := d) R x) := measurableSet_le (by
      have : Continuous fun y : Torus d => KernelGrad.tdist x y := by
        simp_rw [CoercAux.tdist_eq_sqrt]; fun_prop
      exact this.measurable) measurable_const
    rw [← lintegral_indicator hBx]
    refine lintegral_congr fun y => ?_
    by_cases hh : KernelGrad.tdist x y ≤ R <;> simp [Set.indicator, tsampBall, hh]
  simp_rw [h1]
  rw [lintegral_lintegral_swap]
  · have h2 : ∀ y, ∫⁻ x, {q : Torus d × Torus d | KernelGrad.tdist q.1 q.2 ≤ R}.indicator
        (fun q => G q.2) (x, y) = G y * volume {z : Torus d | KernelGrad.tdist z 0 ≤ R} := by
      intro y
      have : (fun x => {q : Torus d × Torus d | KernelGrad.tdist q.1 q.2 ≤ R}.indicator
          (fun q => G q.2) (x, y)) = {x : Torus d | KernelGrad.tdist x y ≤ R}.indicator (fun _ => G y) := by
        funext x; simp [Set.indicator]
      rw [this, lintegral_indicator_const (by
        rw [tsamp_ball_eq]; exact (tsamp_measurableSet_ball R).preimage (measurable_id.sub_const y)),
        tsamp_ball_volume_translate]
    simp_rw [h2]
    rw [lintegral_mul_const _ hG, mul_comm]
  · exact (Measurable.indicator (hG.comp measurable_snd) hset).aemeasurable

/-- Hölder on a ball: the near part. -/
lemma tsamp_near_holder {p q : ℝ} (hpq : p.HolderConjugate q) {kn g : Torus d → ℝ≥0∞}
    (hkn : Measurable kn) (hg : Measurable g) {x x' : Torus d} {r R : ℝ}
    (hsupp : ∀ z, kn z ≠ 0 → KernelGrad.tdist z 0 < r)
    (hxx : KernelGrad.tdist x x' ≤ R - r) :
    ∫⁻ y, kn (x - y) * g y ≤
      (∫⁻ z, kn z ^ q) ^ (1 / q) * (∫⁻ y in tsampBall R x', g y ^ p) ^ (1 / p) := by
  have hB : MeasurableSet (tsampBall (d := d) R x') := measurableSet_le (by
    have : Continuous fun y : Torus d => KernelGrad.tdist x' y := by
      simp_rw [CoercAux.tdist_eq_sqrt]; fun_prop
    exact this.measurable) measurable_const
  have h1 : ∀ y, kn (x - y) * g y ≤ kn (x - y) * (tsampBall R x').indicator g y := by
    intro y
    by_cases hk : kn (x - y) = 0
    · simp [hk]
    · have h2 := hsupp _ hk
      have hy : y ∈ tsampBall R x' := by
        show KernelGrad.tdist x' y ≤ R
        have t1 := tsamp_tdist_triangle x' x y
        have t2 : KernelGrad.tdist x y = KernelGrad.tdist (x - y) 0 := KernelGrad.tdist_eq_sub_zero x y
        rw [tsamp_tdist_symm x' x] at t1
        linarith
      simp [Set.indicator_of_mem hy]
  calc ∫⁻ y, kn (x - y) * g y ≤ ∫⁻ y, kn (x - y) * (tsampBall R x').indicator g y := lintegral_mono h1
    _ ≤ (∫⁻ y, kn (x - y) ^ q) ^ (1 / q) * (∫⁻ y, ((tsampBall R x').indicator g y) ^ p) ^ (1 / p) := by
        have := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (volume : Measure (Torus d))) hpq.symm
          (f := fun y => kn (x - y)) (g := fun y => (tsampBall R x').indicator g y)
          (hkn.comp (measurable_const.sub measurable_id)).aemeasurable
          (hg.indicator hB).aemeasurable
        simpa [Pi.mul_apply] using this
    _ = (∫⁻ z, kn z ^ q) ^ (1 / q) * (∫⁻ y in tsampBall R x', g y ^ p) ^ (1 / p) := by
        have e1 : ∫⁻ y, kn (x - y) ^ q = ∫⁻ z, kn z ^ q :=
          ((volume : Measure (Torus d)).measurePreserving_sub_left x).lintegral_comp
            (hkn.pow_const q)
        have e2 : ∫⁻ y, ((tsampBall R x').indicator g y) ^ p = ∫⁻ y in tsampBall R x', g y ^ p := by
          rw [← lintegral_indicator hB]
          refine lintegral_congr fun y => ?_
          by_cases hy : y ∈ tsampBall R x'
          · simp [Set.indicator_of_mem hy]
          · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hpq.pos]
        rw [e1, e2]

end HRS.Commutator.TorusNote
