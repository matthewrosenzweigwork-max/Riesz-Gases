import HRS.MS.ToriCoefBAux4

/-!
# MS-TORI-COEFB, helper file 5: `convGradConvL` as the vector of the scalar operators `T_{k_i}`

`convGradConvL L G μ x = ∫_{Q_L} (if |z| ≤ 1/4 then (μ(x-z) - μ(x)) • G(z) else μ(x-z) • G(z)) dz`
(change of variables `y = x - z`), whose `i`-th coordinate is `tcb_T L (fun z => G z i) μ x`; and the
resulting regularity / bound transfer to the vector `F = ∑_i (T_i μ) • e_i`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefB

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA

variable {d : ℕ}

theorem tcb_conv_eq (L : ℝ) (G : Euc d → Euc d) (μ : Euc d → ℝ) (x : Euc d) :
    convGradConvL L G μ x = ∫ z in tcb_Q d L,
      (if ‖z‖ ≤ 1 / 4 then (μ (x - z) - μ x) • G z else μ (x - z) • G z) := by
  unfold convGradConvL
  have hmp : MeasurePreserving (fun y : Euc d => x - y) volume volume :=
    (volume : Measure (Euc d)).measurePreserving_sub_left x
  have hemb : MeasurableEmbedding (fun y : Euc d => x - y) := measurableEmbedding_subLeft x
  have key := hmp.setIntegral_preimage_emb hemb
    (fun z => if ‖z‖ ≤ 1 / 4 then (μ (x - z) - μ x) • G z else μ (x - z) • G z) (tcb_Q d L)
  rw [← key]
  have e : {y : Euc d | ∀ i, -(L / 2) ≤ (x - y) i ∧ (x - y) i < L / 2} =
      (fun y : Euc d => x - y) ⁻¹' tcb_Q d L := rfl
  rw [e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel]

/-- Coordinates of the integrand. -/
theorem tcb_integrand_coord (G : Euc d → Euc d) (μ : Euc d → ℝ) (x z : Euc d) (b : Fin d) :
    (if ‖z‖ ≤ 1 / 4 then (μ (x - z) - μ x) • G z else μ (x - z) • G z) b =
      tcb_F (fun z => G z b) μ x z := by
  unfold tcb_F
  by_cases h : ‖z‖ ≤ 1 / 4
  · have hz : z ∈ tcb_N d := by simpa [tcb_N] using h
    simp only [h, if_true, Set.indicator_of_mem hz, PiLp.smul_apply, smul_eq_mul]
    ring
  · have hz : z ∉ tcb_N d := by simpa [tcb_N] using h
    simp only [h, if_false, Set.indicator_of_notMem hz, PiLp.smul_apply, smul_eq_mul]
    ring

/-- The coordinates of `convGradConvL` are the scalar operators `T_{k_i}`. -/
theorem tcb_conv_coord {L Kf : ℝ} (G : Euc d → Euc d) (hk : ∀ i, tcb_Kern L (fun z => G z i) Kf)
    (μ : Euc d → ℝ) (hμ : ContDiff ℝ 1 μ) (B0 B1 : ℝ) (h0 : ∀ y, ‖μ y‖ ≤ B0)
    (h1 : ∀ y, ‖fderiv ℝ μ y‖ ≤ B1) (x : Euc d) (i : Fin d) :
    convGradConvL L G μ x i = tcb_T L (fun z => G z i) μ x := by
  have hd : Differentiable ℝ μ := hμ.differentiable (by norm_num)
  have hΦ : Integrable (fun z => if ‖z‖ ≤ 1 / 4 then (μ (x - z) - μ x) • G z
      else μ (x - z) • G z) (volume.restrict (tcb_Q d L)) := by
    have e : (fun z => if ‖z‖ ≤ 1 / 4 then (μ (x - z) - μ x) • G z else μ (x - z) • G z) =
        fun z => ∑ j : Fin d, (tcb_F (fun z => G z j) μ x z) • EuclideanSpace.single j (1 : ℝ) := by
      funext z
      ext b
      rw [tcb_integrand_coord G μ x z b]
      simp [Pi.single_apply]
    rw [e]
    exact integrable_finsetSum _ fun j _ =>
      (tcb_F_integrable (hk j) μ hd B0 B1 h0 h1 x).smul_const _
  rw [tcb_conv_eq]
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hΦ
  have e2 : (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)
      (∫ z in tcb_Q d L, if ‖z‖ ≤ 1 / 4 then (μ (x - z) - μ x) • G z else μ (x - z) • G z) =
      (∫ z in tcb_Q d L, if ‖z‖ ≤ 1 / 4 then (μ (x - z) - μ x) • G z else μ (x - z) • G z) i := rfl
  rw [← e2, ← this]
  unfold tcb_T
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact tcb_integrand_coord G μ x z i

end HRS.MS.ToriCoefB
