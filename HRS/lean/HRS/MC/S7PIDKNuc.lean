import HRS.MC.S7PIDTNuc
import HRS.MC.S7PIDTPhi
import HRS.MC.S7PIDTFam
import HRS.MC.S7PIDNMain

/-!
# Packet PI-D, sub-packet K (part 6): `nuc` against a product form, as an integral of evaluations

For `l₁, l₂ ∈ 𝒳*`: `nuc_n (prodForm l₁ l₂) = ∫_{(c,c']} l₁(polyPath(w u)) l₂(polyPath(w' u)) du`, and the integrand is
a.e. strongly measurable (it is a continuous function of the finitely many node vectors).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDK

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

theorem S7PIDK_prodForm_apply {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] (l₁ l₂ : StrongDual ℝ B) (a b : B) :
    prodForm l₁ l₂ ![a, b] = l₁ a * l₂ b := by
  simp [prodForm, Fin.prod_univ_two]

set_option maxSynthPendingDepth 3 in
theorem S7PIDK_nuc_prodForm (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (c c' : ℝ) (hc : 0 ≤ c) (hcc : c < c') (hc' : c' ≤ T) (n : ℕ) (w w' : ℝ → ℕ → NegSobolev d m) (b : ℝ)
    (hw : ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => w u i) (volume.restrict (Set.Ioc c c')))
    (hw' : ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => w' u i) (volume.restrict (Set.Ioc c c')))
    (hb : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖w u i‖ ≤ b)
    (hb' : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖w' u i‖ ≤ b)
    (l₁ l₂ : StrongDual ℝ (PathSpace d m T)) :
    nuc R.D R.ρ m T c c' n w w' (prodForm l₁ l₂) =
        ∫ u in Set.Ioc c c', l₁ (polyPath R.D R.ρ m T c c' n (w u)) * l₂ (polyPath R.D R.ρ m T c c' n (w' u)) ∧
      AEStronglyMeasurable (fun u => l₁ (polyPath R.D R.ρ m T c c' n (w u)) *
        l₂ (polyPath R.D R.ρ m T c c' n (w' u))) (volume.restrict (Set.Ioc c c')) := by
  refine ⟨?_, ?_⟩
  · rw [HRS.MC.Sec7.S7PIDT.S7PIDT_nuc_apply R m hm T hT c c' hc hcc.le hc' n w w' b hw hw' hb hb']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact S7PIDK_prodForm_apply l₁ l₂ _ _
  · obtain ⟨Φ, hΦ⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_Phi R m hm T hT c c' hc hcc hc' n
    have hA : ∀ f : ℝ → ℕ → NegSobolev d m,
        (∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => f u i) (volume.restrict (Set.Ioc c c'))) →
        AEStronglyMeasurable (fun u => (fun j : Fin (2 ^ n + 1) => f u j.1)) (volume.restrict (Set.Ioc c c')) := by
      intro f hf
      refine AEMeasurable.aestronglyMeasurable ?_
      refine aemeasurable_pi_iff.2 fun j => ?_
      exact (hf j.1 (Nat.lt_succ_iff.1 j.2)).aemeasurable
    have h1 := (l₁.continuous.comp Φ.continuous).comp_aestronglyMeasurable (hA w hw)
    have h2 := (l₂.continuous.comp Φ.continuous).comp_aestronglyMeasurable (hA w' hw')
    refine (h1.mul h2).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp, hΦ]
    rfl

theorem S7PIDK_nodes (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (p : ℝ → ℝ) (B : ℝ), Measurable p → (∀ u, |p u| ≤ B) →
      ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → ∀ (e : NegSobolev d m) (n : ℕ),
        (∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => kernelNodes R.D R.ρ m c c' n p e u i)
            (volume.restrict (Set.Ioc c c'))) ∧
        (∀ i ≤ 2 ^ n, ∀ u ∈ Set.Ioc c c', ‖kernelNodes R.D R.ρ m c c' n p e u i‖ ≤ B * (Cb * ‖e‖)) := by
  obtain ⟨Cb, hCb0, hker⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_ker R m hm T hT
  refine ⟨Cb, hCb0, fun p B hp hpB c c' hc hcc hc' e n => ⟨fun i hi => ?_, fun i hi u hu => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_grid_mem c c' hcc n i hi
    exact hp.aestronglyMeasurable.smul (hker c c' hc hcc hc' e _ h1 h2).1
  · obtain ⟨h1, h2⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_grid_mem c c' hcc n i hi
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hpB 0)
    unfold kernelNodes
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hpB u) ((hker c c' hc hcc hc' e _ h1 h2).2 u hu) (norm_nonneg _) hB0

set_option maxSynthPendingDepth 3 in
/-- `nuc` of a.e. measurable, a.e. bounded node families lies in `projTensor` -/
theorem S7PIDK_nuc_mem (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (c c' : ℝ) (hc : 0 ≤ c) (hcc : c ≤ c') (hc' : c' ≤ T) (n : ℕ) (w w' : ℝ → ℕ → NegSobolev d m) (b : ℝ)
    (hw : ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => w u i) (volume.restrict (Set.Ioc c c')))
    (hw' : ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => w' u i) (volume.restrict (Set.Ioc c c')))
    (hb : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖w u i‖ ≤ b)
    (hb' : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖w' u i‖ ≤ b) :
    nuc R.D R.ρ m T c c' n w w' ∈ projTensor (PathSpace d m T) 2 := by
  obtain ⟨wt, hwt1, hwt2, hwt3⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_modify m _ (2 ^ n) w b hw hb
  obtain ⟨wt', hwt1', hwt2', hwt3'⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_modify m _ (2 ^ n) w' b hw' hb'
  obtain ⟨-, hmem⟩ := HRS.MC.Sec7.S7PIDN.s7_PID_nuc_mem_proof R m hm T hT c c' hc hcc hc' n wt wt' hwt1 hwt1'
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
  exact hmem

end HRS.MC.Sec7.S7PIDK

end
