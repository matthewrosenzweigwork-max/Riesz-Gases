import HRS.MC.S7FCBFin

/-!
# FC-B, part 11: null diagonal, `L^p` membership of the envelope, pointwise bound of `fcbT`, measure comparison
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

local instance fcb_borel_prod2b : BorelSpace (Torus d × Torus d) := Prod.borelSpace
local instance fcb_open_prod4b : OpensMeasurableSpace ((Torus d × Torus d) × Torus d × Torus d) :=
  Prod.opensMeasurableSpace

theorem fcb_circle_singleton (x : AddCircle (1:ℝ)) : (volume : Measure (AddCircle (1:ℝ))) {x} = 0 := by
  refine le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have h1 : (volume : Measure (AddCircle (1:ℝ))) {x} ≤ volume (Metric.closedBall x ((η : ℝ) / 2)) :=
    measure_mono (by intro y hy; rw [Set.mem_singleton_iff.1 hy]; exact Metric.mem_closedBall_self (by positivity))
  rw [AddCircle.volume_closedBall] at h1
  refine h1.trans ?_
  rw [zero_add]
  have : min (1:ℝ) (2 * ((η:ℝ) / 2)) ≤ η := by
    refine (min_le_right _ _).trans (by linarith)
  calc ENNReal.ofReal (min 1 (2 * ((η:ℝ) / 2))) ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal this
    _ = η := by simp

theorem fcb_torus_singleton (hd : 0 < d) (x : Torus d) : (volume : Measure (Torus d)) {x} = 0 := by
  have e : ({x} : Set (Torus d)) = Set.pi Set.univ (fun i => ({x i} : Set (AddCircle (1:ℝ)))) := by
    ext y; simp [funext_iff]
  have hv : (volume : Measure (Torus d)) = Measure.pi (fun _ : Fin d => (volume : Measure (AddCircle (1:ℝ)))) := rfl
  rw [e, hv, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hd⟩ : Fin d)) (fcb_circle_singleton _)

theorem fcb_ae_ne (hd : 0 < d) : ∀ᵐ q ∂(volume.prod volume : Measure (Torus d × Torus d)), q.1 ≠ q.2 := by
  have hm : MeasurableSet {q : Torus d × Torus d | q.1 ≠ q.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  refine (Measure.ae_prod_mem_iff_ae_ae_mem (μ := (volume : Measure (Torus d)))
    (ν := (volume : Measure (Torus d))) hm).2 (Filter.Eventually.of_forall fun x => ?_)
  have : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
    rw [ae_iff]; simpa using fcb_torus_singleton hd x
  filter_upwards [this] with y hy
  exact fun h => hy h.symm

theorem fcb_memLp_Phi (hd : 0 < d) {s p : ℝ} (hs0 : 0 ≤ s) (hp : 0 < p) (hps : p * s < d) :
    MemLp (fun q : Torus d × Torus d => fcbPhi s ‖q.1 - q.2‖) (ENNReal.ofReal p) (volume.prod volume) := by
  have hm : Measurable (fun q : Torus d × Torus d => fcbPhi s ‖q.1 - q.2‖) :=
    (fcb_measurable_Phi_norm s).comp (measurable_fst.sub measurable_snd)
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  have hE : ∀ q : Torus d × Torus d, ‖fcbPhi s ‖q.1 - q.2‖‖ₑ ^ p =
      ENNReal.ofReal (fcbPhi s ‖q.1 - q.2‖) ^ p := fun q => by
    rw [Real.enorm_of_nonneg (fcb_Phi_nonneg hs0 (norm_nonneg _))]
  simp_rw [hE]
  have hfm : Measurable fun v : Torus d => ENNReal.ofReal (fcbPhi s ‖v‖) ^ p :=
    (ENNReal.measurable_ofReal.comp (fcb_measurable_Phi_norm s)).pow_const p
  have hmeas : AEMeasurable (fun q : Torus d × Torus d => ENNReal.ofReal (fcbPhi s ‖q.1 - q.2‖) ^ p)
      (volume.prod volume) := (hfm.comp (measurable_fst.sub measurable_snd)).aemeasurable
  rw [lintegral_prod _ hmeas]
  have hin : ∀ q1 : Torus d, ∫⁻ q2 : Torus d, ENNReal.ofReal (fcbPhi s ‖q1 - q2‖) ^ p =
      ∫⁻ v : Torus d, ENNReal.ofReal (fcbPhi s ‖v‖) ^ p := fun q1 =>
    (Measure.measurePreserving_sub_left volume q1).lintegral_comp
      (f := fun v : Torus d => ENNReal.ofReal (fcbPhi s ‖v‖) ^ p) hfm
  simp_rw [hin]
  rw [lintegral_const, measure_univ, mul_one]
  exact (fcb_lintegral_Phi_rpow hd hs0 hp hps).ne

end HRS.MC.Sec7.FCB
