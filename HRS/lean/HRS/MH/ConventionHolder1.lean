import HRS.PDE.ConventionHolder
import HRS.Kernel.GradOp

/-!
# `convGradConv_eq_convGradHolder`: cube convention versus Euclidean-ball convention

Relocation of `HRS.convGradConv_eq_convGradHolder` (`HRS/PDE/ConventionHolder.lean`).  The two
integrands differ only on the region `{‖x-y‖ ≤ 1/4 < tdist x y}` (cube minus ball), where the cube
form subtracts `ρ x • G (x-y)`; this region is symmetric under `y ↦ 2x - y`-type reflection
(`z ↦ -z` in the variable `z = x - y`) and `G` is odd, so the subtracted piece integrates to zero.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.ConventionHolder

variable {d : ℕ} {s C : ℝ} {G : Torus d → Euc d}

theorem ch_tdist_eq (x y : Torus d) : Torus.tdist x y = KernelGrad.tdist x y := rfl

/-- On the far field `tdist z 0 > 1/4` a good kernel is bounded. -/
theorem ch_far_bound (hG : KernelGrad.GoodKernel d s C G) {z : Torus d}
    (hz : 1 / 4 < KernelGrad.tdist z 0) :
    ‖G z‖ ≤ C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h0 : Torus.mk (0 : Euc d) = 0 := by funext i; simp [Torus.mk]
    have := KernelGrad.tdist_mk (d := d) (y := 0) (fun i => by simp)
    rw [h0] at this
    simp at this
    linarith
  refine (hG.bound z hz0).trans ?_
  have h1 : KernelGrad.tdist z 0 ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hz.le (by have := hG.hs0; linarith)
  have := hG.hC0
  gcongr

theorem ch_integral_odd {Q : Torus d → Euc d} (hQ : ∀ z, Q (-z) = - Q z) :
    ∫ z, Q z = 0 := by
  have h1 : ∫ z, Q (-z) = ∫ z, Q z := integral_neg_eq_self Q volume
  simp_rw [hQ] at h1
  rw [integral_neg] at h1
  have h2 : (-(∫ z, Q z)) = ∫ z, Q z := h1
  have h3 : (2 : ℝ) • ∫ z, Q z = 0 := by rw [two_smul]; nth_rewrite 1 [← h2]; simp
  simpa using h3

theorem ch_measurable_rep_coord (i : Fin d) : Measurable fun z : Torus d => Torus.rep z i := by
  have h1 : Measurable fun t : UnitAddCircle =>
      ((AddCircle.equivIco (1 : ℝ) 0 t : Set.Ico (0 : ℝ) (0 + 1)) : ℝ) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  exact h1.comp (measurable_pi_apply i)

theorem ch_measurable_tdist : Measurable fun z : Torus d => KernelGrad.tdist z 0 := by
  have : (fun z : Torus d => KernelGrad.tdist z 0) = fun z =>
      Real.sqrt (∑ i, (if Torus.rep z i ≤ 1 / 2 then Torus.rep z i else Torus.rep z i - 1) ^ 2) := by
    funext z
    unfold KernelGrad.tdist KernelGrad.centeredRep
    rw [sub_zero, EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [this]
  refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => ?_)
  refine Measurable.pow_const ?_ 2
  exact Measurable.ite (measurableSet_le (ch_measurable_rep_coord i) measurable_const)
    (ch_measurable_rep_coord i) ((ch_measurable_rep_coord i).sub_const 1)

/-- The bounded kernel on the cube minus the ball, as a function of `z = x - y`. -/
def chRing (G : Torus d → Euc d) (z : Torus d) : Euc d :=
  if ‖z‖ ≤ 1 / 4 ∧ 1 / 4 < KernelGrad.tdist z 0 then G z else 0

theorem ch_ring_odd (hG : KernelGrad.GoodKernel d s C G) (z : Torus d) :
    chRing G (-z) = - chRing G z := by
  unfold chRing
  simp only [norm_neg, KernelGrad.tdist_neg, hG.odd z]
  split_ifs <;> simp

theorem ch_ring_bound (hG : KernelGrad.GoodKernel d s C G) (z : Torus d) :
    ‖chRing G z‖ ≤ C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by
  unfold chRing
  split_ifs with h
  · exact ch_far_bound hG h.2
  · have := hG.hC0
    have : 0 ≤ C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (-s - 1)
      positivity
    simpa using this

theorem ch_measurable_ring (hG : KernelGrad.GoodKernel d s C G) : Measurable (chRing G) := by
  unfold chRing
  refine Measurable.ite ?_ hG.meas measurable_const
  exact (measurableSet_le measurable_norm measurable_const).inter
    (measurableSet_lt measurable_const ch_measurable_tdist)

theorem ch_measurable_tdist_sub (x : Torus d) :
    Measurable fun y : Torus d => KernelGrad.tdist x y := by
  have : (fun y : Torus d => KernelGrad.tdist x y) = fun y => KernelGrad.tdist (x - y) 0 := by
    funext y; exact KernelGrad.tdist_eq_sub_zero x y
  rw [this]
  exact ch_measurable_tdist.comp (measurable_const.sub measurable_id)

/-- The far-field integrand is integrable (bounded measurable function on a probability space). -/
theorem ch_integrable_far (hG : KernelGrad.GoodKernel d s C G) {ρ : Torus d → ℝ}
    (hρm : Measurable ρ) {B : ℝ} (hB : ∀ y, |ρ y| ≤ B) (x : Torus d) :
    Integrable (fun y => if 1 / 4 < Torus.tdist x y then ρ y • G (x - y) else 0) := by
  have hm : Measurable fun y : Torus d => if 1 / 4 < Torus.tdist x y then ρ y • G (x - y) else 0 :=
    Measurable.ite (measurableSet_lt measurable_const (ch_measurable_tdist_sub x))
      (hρm.smul (hG.meas.comp (measurable_const.sub measurable_id))) measurable_const
  refine Integrable.of_bound hm.aestronglyMeasurable (B * (C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)))
    (Eventually.of_forall fun y => ?_)
  by_cases h : 1 / 4 < Torus.tdist x y
  · rw [if_pos h, norm_smul, Real.norm_eq_abs]
    have h' : 1 / 4 < KernelGrad.tdist (x - y) 0 := by
      rw [← KernelGrad.tdist_eq_sub_zero]; exact h
    exact mul_le_mul (hB y) (ch_far_bound hG h') (norm_nonneg _) ((abs_nonneg _).trans (hB y))
  · rw [if_neg h]
    have := hG.hC0
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (-s - 1)
    simp only [norm_zero]
    positivity

theorem ch_integrable_ring (hG : KernelGrad.GoodKernel d s C G) (x : Torus d) :
    Integrable (fun y => chRing G (x - y)) := by
  refine Integrable.of_bound ((ch_measurable_ring hG).comp
    (measurable_const.sub measurable_id)).aestronglyMeasurable _
    (Eventually.of_forall fun y => ch_ring_bound hG (x - y))

theorem ch_pointwise (_hG : KernelGrad.GoodKernel d s C G) (ρ : Torus d → ℝ) (x y : Torus d) :
    (if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else ρ y • G (x - y)) =
      (if Torus.tdist x y ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else 0) +
      (if 1 / 4 < Torus.tdist x y then ρ y • G (x - y) else 0) - ρ x • chRing G (x - y) := by
  have hle : Torus.tdist x y ≤ 1 / 4 → ‖x - y‖ ≤ 1 / 4 := fun h =>
    (KernelGrad.norm_le_tdist (x - y)).trans (by
      have h' := h
      rwa [ch_tdist_eq, KernelGrad.tdist_eq_sub_zero] at h')
  have e : Torus.tdist x y = KernelGrad.tdist (x - y) 0 := by
    rw [ch_tdist_eq, KernelGrad.tdist_eq_sub_zero]
  have hn : ‖x - y‖ ≤ KernelGrad.tdist (x - y) 0 := KernelGrad.norm_le_tdist _
  unfold chRing
  rw [← e] at *
  split_ifs <;> first
    | (exfalso; linarith)
    | (exfalso; simp_all; done)
    | (simp [sub_smul]; done)
    | (simp_all [sub_smul]; done)

theorem convGradConv_eq_convGradHolder_proof :
    type_of% @HRS.convGradConv_eq_convGradHolder := by
  intro d s C G hG ρ hρm hρb x hint
  obtain ⟨B, hB⟩ := hρb
  have hf2 := ch_integrable_far hG hρm hB x
  have hc := ch_integrable_ring hG x
  have hc0 : ∫ y, chRing G (x - y) = 0 := by
    rw [integral_sub_left_eq_self (fun z => chRing G z) volume x]
    exact ch_integral_odd (ch_ring_odd hG)
  unfold convGradConv convGradHolder
  simp_rw [ch_pointwise hG ρ x]
  have h1 : ∫ y, ((if Torus.tdist x y ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else 0) +
      (if 1 / 4 < Torus.tdist x y then ρ y • G (x - y) else 0) - ρ x • chRing G (x - y)) =
      (∫ y, ((if Torus.tdist x y ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else 0) +
      (if 1 / 4 < Torus.tdist x y then ρ y • G (x - y) else 0))) -
      ∫ y, ρ x • chRing G (x - y) := integral_sub (hint.add hf2) (hc.smul (ρ x))
  have h2 : ∫ y, ((if Torus.tdist x y ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else 0) +
      (if 1 / 4 < Torus.tdist x y then ρ y • G (x - y) else 0)) =
      (∫ y, if Torus.tdist x y ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else 0) +
      ∫ y, if 1 / 4 < Torus.tdist x y then ρ y • G (x - y) else 0 := integral_add hint hf2
  rw [h1, h2, integral_smul, hc0]
  simp

end HRS.MH.ConventionHolder
