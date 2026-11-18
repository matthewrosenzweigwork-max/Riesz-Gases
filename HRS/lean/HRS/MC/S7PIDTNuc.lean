import HRS.MC.S7PIDNMain
import HRS.MC.S7PIDDefs

/-!
# Packet PI-D, sub-packet T (part 6): `nuc` applied to a bounded bilinear form

For node families `w, w'` that are only a.e. strongly measurable on `(c,c']` (the causal kernel `V^{t,u}e` is only
known to be measurable in `u` on `[0,t]`) and a.e. bounded, `nuc … w w' M = ∫_{(c,c']} M[polyPath (w u), polyPath (w' u)] du`.
Route: replace `w` by a globally measurable, globally bounded modification `wmod` with the same values a.e. on `(c,c']`,
apply `s7_PID_nuc_mem_proof` to `wmod`, and commute the evaluation at `M` with the Bochner integral.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

/-- a globally measurable, globally bounded modification of a family of a.e. measurable, a.e. bounded node maps -/
theorem S7PIDT_modify (m : ℝ) (μ : Measure ℝ) (N : ℕ) (w : ℝ → ℕ → NegSobolev d m) (b : ℝ)
    (hw : ∀ i ≤ N, AEStronglyMeasurable (fun u => w u i) μ)
    (hb : ∀ i ≤ N, ∀ᵐ u ∂μ, ‖w u i‖ ≤ b) :
    ∃ wmod : ℝ → ℕ → NegSobolev d m, (∀ i, Measurable fun u => wmod u i) ∧ (∀ u i, ‖wmod u i‖ ≤ max b 0) ∧
      ∀ᵐ u ∂μ, ∀ i ≤ N, wmod u i = w u i := by
  classical
  let g : ∀ i : ℕ, ℝ → NegSobolev d m := fun i =>
    if h : i ≤ N then (hw i h).mk (fun u => w u i) else fun _ => 0
  have hgm : ∀ i, Measurable (g i) := by
    intro i
    by_cases h : i ≤ N
    · simp only [g, dif_pos h]
      exact (hw i h).stronglyMeasurable_mk.measurable
    · simp only [g, dif_neg h]
      exact measurable_const
  refine ⟨fun u i => if ‖g i u‖ ≤ b then g i u else 0, fun i => ?_, fun u i => ?_, ?_⟩
  · exact Measurable.ite (measurableSet_le (hgm i).norm measurable_const) (hgm i) measurable_const
  · by_cases h : ‖g i u‖ ≤ b
    · simp only [h, if_true]; exact h.trans (le_max_left _ _)
    · simp only [h, if_false, norm_zero]; exact le_max_right _ _
  · have key : ∀ i : ℕ, ∀ᵐ u ∂μ, i ≤ N → (if ‖g i u‖ ≤ b then g i u else 0) = w u i := by
     intro i
     by_cases hi : i ≤ N
     · have h1 := (hw i hi).ae_eq_mk
       have h2 := hb i hi
       filter_upwards [h1, h2] with u hu1 hu2
       intro _
       have : g i u = w u i := by simp only [g, dif_pos hi]; exact hu1.symm
       have hh : ‖g i u‖ ≤ b := by rw [this]; exact hu2
       rw [if_pos hh, this]
     · exact Filter.Eventually.of_forall fun u h => absurd h hi
    filter_upwards [ae_all_iff.2 key] with u hu i hi using hu i hi

theorem S7PIDT_nuc_apply (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (c c' : ℝ) (hc : 0 ≤ c) (hcc : c ≤ c') (hc' : c' ≤ T) (n : ℕ) (w w' : ℝ → ℕ → NegSobolev d m) (b : ℝ)
    (hw : ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => w u i) (volume.restrict (Set.Ioc c c')))
    (hw' : ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => w' u i) (volume.restrict (Set.Ioc c c')))
    (hb : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖w u i‖ ≤ b)
    (hb' : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖w' u i‖ ≤ b)
    (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    nuc R.D R.ρ m T c c' n w w' M =
      ∫ u in Set.Ioc c c', M ![polyPath R.D R.ρ m T c c' n (w u), polyPath R.D R.ρ m T c c' n (w' u)] := by
  obtain ⟨wt, hwt1, hwt2, hwt3⟩ := S7PIDT_modify m _ (2 ^ n) w b hw hb
  obtain ⟨wt', hwt1', hwt2', hwt3'⟩ := S7PIDT_modify m _ (2 ^ n) w' b hw' hb'
  obtain ⟨hint, -⟩ := HRS.MC.Sec7.S7PIDN.s7_PID_nuc_mem_proof R m hm T hT c c' hc hcc hc' n wt wt' hwt1 hwt1'
    (max b 0) hwt2 hwt2'
  have hcongr : ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')),
      (elemTensor ![polyPath R.D R.ρ m T c c' n (wt u), polyPath R.D R.ρ m T c c' n (wt' u)] :
        TensorDual (PathSpace d m T) 2) =
      elemTensor ![polyPath R.D R.ρ m T c c' n (w u), polyPath R.D R.ρ m T c c' n (w' u)] := by
    filter_upwards [hwt3, hwt3'] with u h1 h2
    rw [HRS.MC.Sec7.S7PIDN.S7PIDN_polyPath_congr R.D R.ρ m T c c' n (wt u) (w u) h1,
      HRS.MC.Sec7.S7PIDN.S7PIDN_polyPath_congr R.D R.ρ m T c c' n (wt' u) (w' u) h2]
  have e1 : nuc R.D R.ρ m T c c' n w w' = nuc R.D R.ρ m T c c' n wt wt' := by
    unfold nuc
    exact (integral_congr_ae hcongr).symm
  rw [e1]
  unfold nuc
  rw [ContinuousLinearMap.integral_apply hint M]
  refine integral_congr_ae ?_
  filter_upwards [hcongr] with u hu
  rw [hu]
  rfl

end HRS.MC.Sec7.S7PIDT

end
