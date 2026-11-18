import HRS.MS.SA12W2K
import HRS.Kernel.GradOp

/-!
# S.A.12 C5 (SA12W2 worker), part L: centred-cube dictionary for the cancellation convolution

The centred half-open cube `[-1/2,1/2)^d` and its relation to the torus measure, to the period box `[-L/2,L/2)^d`, and the
torus norm of `mk w`; the change of variables `y = x - z` in `convGradConvL`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

/-- The centred half-open cube `[-1/2,1/2)^d`. -/
def sa12w2_cubeC (d : ℕ) : Set (Euc d) := {w | ∀ i, w i ∈ Ico (-1 / 2 : ℝ) (1 / 2)}

theorem sa12w2_measurableSet_cubeC : MeasurableSet (sa12w2_cubeC d) := by
  have : sa12w2_cubeC d = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ico (-1 / 2 : ℝ) (1 / 2)) := by
    ext w; simp [sa12w2_cubeC]
  rw [this]
  exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

theorem sa12w2_mk_mp_cubeC :
    MeasurePreserving (Torus.mk : Euc d → Torus d) (volume.restrict (sa12w2_cubeC d)) volume := by
  have hIco : (volume : Measure ℝ).restrict (Ico (-1 / 2 : ℝ) (1 / 2)) =
      (volume : Measure ℝ).restrict (Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) := by
    have : (-1 / 2 + 1 : ℝ) = 1 / 2 := by norm_num
    rw [this]; exact Measure.restrict_congr_set Ico_ae_eq_Ioc
  have h1 := measurePreserving_pi (fun _ : Fin d => (volume : Measure ℝ).restrict (Ico (-1 / 2 : ℝ) (1 / 2)))
    (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) (fun _ => by
      rw [hIco]; exact UnitAddCircle.measurePreserving_mk (-1 / 2))
  rw [← Measure.restrict_pi_pi] at h1
  have h2 := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (s := Set.pi univ fun _ : Fin d => Ico (-1 / 2 : ℝ) (1 / 2))
    (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico)
  have hc : (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ico (-1 / 2 : ℝ) (1 / 2)) =
      sa12w2_cubeC d := by
    ext w; simp [sa12w2_cubeC]
  rw [hc] at h2
  exact h1.comp h2

theorem sa12w2_torus_int_cubeC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Torus d → E)
    (hF : AEStronglyMeasurable F volume) :
    ∫ x, F x = ∫ w in sa12w2_cubeC d, F (Torus.mk w) := by
  have h := sa12w2_mk_mp_cubeC (d := d)
  conv_lhs => rw [← h.map_eq]
  exact integral_map h.measurable.aemeasurable (by rw [h.map_eq]; exact hF)

theorem sa12w2_cb_preimage {L : ℝ} (hL : 0 < L) :
    (fun w : Euc d => L • w) ⁻¹' centeredBox d L = sa12w2_cubeC d := by
  ext w
  simp only [mem_preimage, centeredBox, sa12w2_cubeC, mem_setOf_eq, mem_Ico]
  refine forall_congr' fun i => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

theorem sa12w2_measurableSet_cb (L : ℝ) : MeasurableSet (centeredBox d L) := sa12v_centered_meas L

/-- Scaling of an integral over a set. -/
theorem sa12w2_set_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ} (hL : 0 < L)
    {S : Set (Euc d)} (hS : MeasurableSet S) (g : Euc d → E) :
    ∫ w in (fun w : Euc d => L • w) ⁻¹' S, g (L • w) = (L ^ d)⁻¹ • ∫ x in S, g x := by
  rw [← integral_indicator (hS.preimage (measurable_const_smul L)), ← integral_indicator hS]
  have e : (fun w : Euc d => ((fun w : Euc d => L • w) ⁻¹' S).indicator (fun w => g (L • w)) w) =
      fun w => S.indicator g (L • w) := by
    funext w
    by_cases hw : L • w ∈ S <;> simp [Set.indicator, hw]
  rw [e, Measure.integral_comp_smul (μ := (volume : Measure (Euc d))) (S.indicator g) L]
  simp [finrank_euclideanSpace, abs_of_pos (pow_pos hL d)]

/-- Torus norm of `mk w` for `w` in the centred cube. -/
theorem sa12w2_norm_mk_le {w : Euc d} (hw : ∀ i, |w i| ≤ 1 / 2) {c : ℝ} (hc : 0 ≤ c) :
    ‖(Torus.mk w : Torus d)‖ ≤ c ↔ ∀ i, |w i| ≤ c := by
  have hn : ∀ i, ‖((w i : ℝ) : UnitAddCircle)‖ = |w i| := fun i => by
    rw [AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero]
    simpa using hw i
  rw [pi_norm_le_iff_of_nonneg hc]
  refine forall_congr' fun i => ?_
  exact (show ‖(Torus.mk w : Torus d) i‖ = |w i| from hn i) ▸ Iff.rfl

end HRS.PDE.SA12W2
