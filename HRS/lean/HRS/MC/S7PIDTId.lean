import HRS.MC.S7PIDNMain
import HRS.MC.S7PIDDefs

/-!
# Packet PI-D, sub-packet T (part 5): the Gaussian representation of `∫ M(Φ w, Φ' w')`

For a bounded bilinear form `M` on `X` and continuous linear maps `Φ, Φ' : (ι → ℝ^r) →L X`, the integral
`∫_I M(Φ (w u), Φ' (w' u)) du` equals the Gaussian expectation `E M(Φ Y, Φ' Y')` as soon as the pair of finite
Gaussian families `(Y, Y')` has the cross covariances `∫_I B(w_i, w'_j)` (expansion over the finitely many
indices).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID

section Bil

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- the bounded bilinear form `(a, b) ↦ M[A a, A' b]` -/
def S7PIDT_bil (M : X [×2]→L[ℝ] ℝ) (A A' : W →L[ℝ] X) : W →L[ℝ] W →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun a b => M ![A a, A' b])
      (fun a a' b => by simp only [map_add]; exact HRS.MC.Sec7.S7PIDN.S7PIDN_elem_add_left M _ _ _)
      (fun r a b => by simp only [map_smul]; exact HRS.MC.Sec7.S7PIDN.S7PIDN_elem_smul_left M _ _ _)
      (fun a b b' => by simp only [map_add]; exact HRS.MC.Sec7.S7PIDN.S7PIDN_elem_add_right M _ _ _)
      (fun r a b => by simp only [map_smul]; exact HRS.MC.Sec7.S7PIDN.S7PIDN_elem_smul_right M _ _ _))
    (‖M‖ * ‖A‖ * ‖A'‖)
    (fun a b => by
      show ‖M ![A a, A' b]‖ ≤ ‖M‖ * ‖A‖ * ‖A'‖ * ‖a‖ * ‖b‖
      calc ‖M ![A a, A' b]‖ ≤ ‖M‖ * ∏ i, ‖(![A a, A' b] : Fin 2 → X) i‖ := M.le_opNorm _
        _ = ‖M‖ * (‖A a‖ * ‖A' b‖) := by simp [Fin.prod_univ_two]
        _ ≤ ‖M‖ * ((‖A‖ * ‖a‖) * (‖A'‖ * ‖b‖)) := by
            gcongr
            · exact A.le_opNorm a
            · exact A'.le_opNorm b
        _ = _ := by ring)

lemma S7PIDT_bil_apply (M : X [×2]→L[ℝ] ℝ) (A A' : W →L[ℝ] X) (a b : W) :
    S7PIDT_bil M A A' a b = M ![A a, A' b] := rfl

end Bil

section Expand

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- finite expansion of `M[Φ x, Φ' x']` into the bilinear forms `B i j` on `ℝ^r` -/
theorem S7PIDT_expand (M : X [×2]→L[ℝ] ℝ) (Φ Φ' : (ι → EuclideanSpace ℝ (Fin r)) →L[ℝ] X) :
    ∃ B : ι → ι → EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ,
      ∀ x x' : ι → EuclideanSpace ℝ (Fin r), M ![Φ x, Φ' x'] = ∑ i, ∑ j, B i j (x i) (x' j) := by
  let Mb : X →L[ℝ] X →L[ℝ] ℝ := S7PIDT_bil M (ContinuousLinearMap.id ℝ X) (ContinuousLinearMap.id ℝ X)
  let sg : ι → EuclideanSpace ℝ (Fin r) →L[ℝ] (ι → EuclideanSpace ℝ (Fin r)) := fun i =>
    (LinearMap.single ℝ (fun _ : ι => EuclideanSpace ℝ (Fin r)) i).toContinuousLinearMap
  refine ⟨fun i j => Mb.bilinearComp (Φ.comp (sg i)) (Φ'.comp (sg j)), fun x x' => ?_⟩
  have hx : ∀ y : ι → EuclideanSpace ℝ (Fin r), y = ∑ i, sg i (y i) := fun y => by
    ext i a
    simp [sg, Finset.sum_apply, Pi.single_apply]
  have hM : M ![Φ x, Φ' x'] = Mb (Φ x) (Φ' x') := rfl
  rw [hM]
  conv_lhs => rw [hx x, hx x']
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rfl

end Expand

section Integrable

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {r : ℕ}

theorem S7PIDT_int_bilin (B : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ)
    {f g : α → EuclideanSpace ℝ (Fin r)} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun a => B (f a) (g a)) μ := by
  have h1 : Integrable (fun a => ‖f a‖ * ‖g a‖) μ := hf.norm.integrable_mul hg.norm
  refine (h1.const_mul ‖B‖).mono' (B.continuous₂.comp_aestronglyMeasurable (hf.aestronglyMeasurable.prodMk hg.aestronglyMeasurable)) ?_
  refine Filter.Eventually.of_forall fun a => ?_
  calc ‖B (f a) (g a)‖ ≤ ‖B (f a)‖ * ‖g a‖ := (B (f a)).le_opNorm _
    _ ≤ (‖B‖ * ‖f a‖) * ‖g a‖ := by gcongr; exact B.le_opNorm _
    _ = ‖B‖ * (‖f a‖ * ‖g a‖) := by ring

end Integrable

section Main

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem S7PIDT_id (I : Set ℝ) (w w' : ι → ℝ → EuclideanSpace ℝ (Fin r))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict I)) (hw' : ∀ i, MemLp (w' i) 2 (volume.restrict I))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Y' : ι → Ω → EuclideanSpace ℝ (Fin r)) (hY : ∀ i, MemLp (Y i) 2 P) (hY' : ∀ i, MemLp (Y' i) 2 P)
    (hcross : ∀ (B : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ) (i j : ι),
      ∫ ω, B (Y i ω) (Y' j ω) ∂P = ∫ u in I, B (w i u) (w' j u))
    (Φ Φ' : (ι → EuclideanSpace ℝ (Fin r)) →L[ℝ] X) (M : X [×2]→L[ℝ] ℝ) :
    Integrable (fun ω => M ![Φ (fun i => Y i ω), Φ' (fun i => Y' i ω)]) P ∧
      Integrable (fun u => M ![Φ (fun i => w i u), Φ' (fun i => w' i u)]) (volume.restrict I) ∧
      ∫ u in I, M ![Φ (fun i => w i u), Φ' (fun i => w' i u)] =
        ∫ ω, M ![Φ (fun i => Y i ω), Φ' (fun i => Y' i ω)] ∂P := by
  obtain ⟨B, hB⟩ := S7PIDT_expand M Φ Φ'
  simp_rw [hB]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => S7PIDT_int_bilin _ (hY i) (hY' j),
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => S7PIDT_int_bilin _ (hw i) (hw' j), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => S7PIDT_int_bilin _ (hw i) (hw' j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => S7PIDT_int_bilin _ (hY i) (hY' j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => S7PIDT_int_bilin _ (hw i) (hw' j)),
    integral_finsetSum _ (fun j _ => S7PIDT_int_bilin _ (hY i) (hY' j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (hcross (B i j) i j).symm

end Main

end HRS.MC.Sec7.S7PIDT

end
