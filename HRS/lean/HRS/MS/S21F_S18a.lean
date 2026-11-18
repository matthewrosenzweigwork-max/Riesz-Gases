import HRS.MS.S21F_S19

/-!
# S21F, packet R26-T3.S18 (part a): the measure of a pair collision neighbourhood

For `μ = ρ dx` with `ρ ≤ M` and `i ≠ j`: `μ^{⊗N}{‖X_i - X_j‖ ≤ 2η} ≤ M (2η)^d |B_1|` (independence of the coordinates gives the pair law `μ ⊗ μ`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_pair_ball {d N : ℕ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) (i j : Fin N) (hij : i ≠ j) {η : ℝ} (hη : 0 ≤ η) :
    (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) {X : EucConfig d N | ‖X i - X j‖ ≤ 2 * η} ≤
      ENNReal.ofReal M * (ENNReal.ofReal ((2 * η) ^ d) * volume (ball (0 : Euc d) 1)) := by
  have hP := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hν
  have hind : IndepFun (fun X : EucConfig d N => X i) (fun X : EucConfig d N => X j) ν :=
    (iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)).indepFun hij
  have hmap : ν.map (fun X => (X i, X j)) = μ.prod μ := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable).1 hind, (measurePreserving_eval _ i).map_eq,
      (measurePreserving_eval _ j).map_eq]
  have hS : MeasurableSet {p : Euc d × Euc d | ‖p.1 - p.2‖ ≤ 2 * η} :=
    measurableSet_le (measurable_fst.sub measurable_snd).norm measurable_const
  have hpre : {X : EucConfig d N | ‖X i - X j‖ ≤ 2 * η} =
      (fun X : EucConfig d N => (X i, X j)) ⁻¹' {p : Euc d × Euc d | ‖p.1 - p.2‖ ≤ 2 * η} := rfl
  rw [hpre, ← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hS, hmap,
    Measure.prod_apply hS]
  have hslice : ∀ x : Euc d, μ (Prod.mk x ⁻¹' {p : Euc d × Euc d | ‖p.1 - p.2‖ ≤ 2 * η}) ≤
      ENNReal.ofReal M * (ENNReal.ofReal ((2 * η) ^ d) * volume (ball (0 : Euc d) 1)) := fun x => by
    have : Prod.mk x ⁻¹' {p : Euc d × Euc d | ‖p.1 - p.2‖ ≤ 2 * η} = closedBall x (2 * η) := by
      ext y; simp [dist_eq_norm, norm_sub_rev y x]
    rw [this, hμ, HRS.Whole.withDensityReal, withDensity_apply _ measurableSet_closedBall]
    calc ∫⁻ y in closedBall x (2 * η), ENNReal.ofReal (ρ y) ≤ ∫⁻ y in closedBall x (2 * η), ENNReal.ofReal M :=
          lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hM y)
      _ = ENNReal.ofReal M * volume (closedBall x (2 * η)) := by rw [setLIntegral_const, mul_comm]
      _ = _ := by
          rw [Measure.addHaar_closedBall _ x (by positivity)]
          simp
  calc ∫⁻ x, μ (Prod.mk x ⁻¹' {p : Euc d × Euc d | ‖p.1 - p.2‖ ≤ 2 * η}) ∂μ
      ≤ ∫⁻ _x, ENNReal.ofReal M * (ENNReal.ofReal ((2 * η) ^ d) * volume (ball (0 : Euc d) 1)) ∂μ :=
        lintegral_mono hslice
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end HRS.MS.R26T3
