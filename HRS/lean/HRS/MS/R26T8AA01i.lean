import HRS.MS.R26T8AA01h

/-!
# S8.2 T8A A01 (part i): principal value of `φ ⋆ (∇g)_j` along a punctured exterior region
For `φ` integrable, locally Lipschitz at `u`, and `v ≠ u`:
`∫_{ε<‖u-z‖, ε<‖v-z‖} φ(z) (∇g)_j(u-z) dz → (convGradConvW (∇g) φ u)_j` as `ε → 0+`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_pv_coord (hd : 2 ≤ d) (j : Fin d) {u v : Euc d} (huv : u ≠ v)
    {φ : Euc d → ℝ} (hφm : AEStronglyMeasurable φ volume) (hφi : Integrable φ)
    {r1 : ℝ} (hr1 : 0 < r1) (hr14 : r1 ≤ 1 / 4) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z : Euc d, ‖z - u‖ < r1 → |φ z - φ u| ≤ L * ‖z - u‖) :
    Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => φ z * r26t8a_a01_kappa d j (u - z)) z) (𝓝[>] 0)
      (𝓝 ((convGradConvW (rieszKernelGrad d (criticalS d)) φ u) j)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  have hun : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 huv)
  obtain ⟨B, hB⟩ := r26t8a_a01_kappa_far hs0 j (‖u - v‖ / 2) (by positivity)
  have hvint : IntegrableOn (fun z => φ z * r26t8a_a01_kappa d j (u - z)) (ball v (‖u - v‖ / 2)) := by
    have hk : AEStronglyMeasurable (fun z => r26t8a_a01_kappa d j (u - z)) volume :=
      ((r26t8a_a01_kappa_meas j).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    refine Integrable.mono' (g := fun z => |B| * ‖φ z‖) ((hφi.norm.const_mul |B|).integrableOn)
      (hφm.mul hk).restrict ?_
    refine (ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall fun z hz => ?_)
    have hz' : ‖u - v‖ / 2 ≤ ‖u - z‖ := by
      rw [mem_ball, dist_eq_norm] at hz
      have := norm_sub_le_norm_sub_add_norm_sub u z v
      have h2 : ‖z - v‖ = ‖z - v‖ := rfl
      linarith
    rw [norm_mul, Real.norm_eq_abs]
    have := hB (u - z) hz'
    calc ‖φ z‖ * |r26t8a_a01_kappa d j (u - z)| ≤ ‖φ z‖ * |B| :=
          mul_le_mul_of_nonneg_left (this.trans (le_abs_self B)) (norm_nonneg _)
      _ = |B| * ‖φ z‖ := mul_comm _ _
  have hI := r26t8a_a01_canon_int hd hsd hs0 hφm hφi hr1 hr14 hL hlip
  have hIc := r26t8a_a01_canon_int_coord hd hsd hs0 j hφm hφi hr1 hr14 hL hlip
  have hpv := r26t8a_a01_pv huv (r26t8a_a01_kappa_meas j) (r26t8a_a01_kappa_odd j)
    (r26t8a_a01_kappa_far hs0 j) hφm hIc (r := ‖u - v‖ / 2) (by positivity) hvint
  have hcoord : (convGradConvW (rieszKernelGrad d (criticalS d)) φ u) j =
      ∫ z, if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) * r26t8a_a01_kappa d j (u - z)
        else φ z * r26t8a_a01_kappa d j (u - z) := by
    have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integral_comp_comm hI
    unfold convGradConvW
    rw [show ((∫ z, if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) • rieszKernelGrad d (criticalS d) (u - z)
        else φ z • rieszKernelGrad d (criticalS d) (u - z)) j) = (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) (∫ z, if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) • rieszKernelGrad d (criticalS d) (u - z)
        else φ z • rieszKernelGrad d (criticalS d) (u - z)) from rfl, ← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hc : ‖u - z‖ ≤ 1 / 4
    · simp only [hc, if_true, r26t8a_a01_kappa]; simp
    · simp only [hc, if_false, r26t8a_a01_kappa]; simp
  rw [hcoord]
  exact hpv

end HRS.MS.R26T8A
