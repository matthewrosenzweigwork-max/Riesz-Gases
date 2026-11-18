import HRS.MC.E213TElem

/-!
# Packet e213c, file 2: the tensor cons `J ⊗ g` and its Bochner integral

For `J : TensorDual B 2` and `g : B`, `J ⊗ g : TensorDual B 3` is `M ↦ J (lastSlot M g)`
(`lastSlot M g = ((a,b) ↦ M[a,b,g])`, so `elemTensor ![a,b] ⊗ g = elemTensor ![a,b,g]`).
It is bounded bilinear with `‖J ⊗ g‖ ≤ ‖J‖‖g‖`, and maps `projTensor B 2 × B` into `projTensor B 3`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option maxSynthPendingDepth 3

namespace HRS.MC.E213T

open HRS HRS.Contr

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem e213t_lastSlot_add_left (M M' : B [×3]→L[ℝ] ℝ) (g : B) :
    lastSlot (M + M') g = lastSlot M g + lastSlot M' g := by
  ext m
  have hm : m = ![m 0, m 1] := by ext k; fin_cases k <;> rfl
  rw [hm]
  simp [lastSlot_apply]

theorem e213t_lastSlot_smul_left (c : ℝ) (M : B [×3]→L[ℝ] ℝ) (g : B) :
    lastSlot (c • M) g = c • lastSlot M g := by
  ext m
  have hm : m = ![m 0, m 1] := by ext k; fin_cases k <;> rfl
  rw [hm]
  simp [lastSlot_apply]

theorem e213t_lastSlot_add_right (M : B [×3]→L[ℝ] ℝ) (g g' : B) :
    lastSlot M (g + g') = lastSlot M g + lastSlot M g' := by
  have h := lastSlot_sub_right M g (-g')
  have h2 := lastSlot_sub_right M g' g'
  have h3 : lastSlot M (0 : B) = 0 := by
    have := lastSlot_sub_right M 0 0
    simpa using this
  have h4 : lastSlot M (-g') = - lastSlot M g' := by
    have := lastSlot_sub_right M 0 g'
    simpa [h3] using this
  simpa [sub_eq_add_neg, h4] using h

theorem e213t_lastSlot_smul_right (c : ℝ) (M : B [×3]→L[ℝ] ℝ) (g : B) :
    lastSlot M (c • g) = c • lastSlot M g := by
  ext m
  have hm : m = ![m 0, m 1] := by ext k; fin_cases k <;> rfl
  rw [hm]
  have h1 : (![m 0, m 1, c • g] : Fin 3 → B) = Function.update ![m 0, m 1, g] 2 (c • g) := by
    ext i; fin_cases i <;> simp [Function.update]
  have h0 : Function.update (![m 0, m 1, g] : Fin 3 → B) 2 g = ![m 0, m 1, g] := by
    ext i; fin_cases i <;> simp [Function.update]
  simp only [lastSlot_apply, smul_apply, smul_eq_mul]
  rw [h1, M.map_update_smul, h0, smul_eq_mul]

/-- `lastSlot · g` as a continuous linear map `(B [×3]→L ℝ) →L (B [×2]→L ℝ)`. -/
def lastSlotCLM (g : B) : (B [×3]→L[ℝ] ℝ) →L[ℝ] (B [×2]→L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun M => lastSlot M g
      map_add' := fun M M' => e213t_lastSlot_add_left M M' g
      map_smul' := fun c M => e213t_lastSlot_smul_left c M g }
    ‖g‖ (fun M => by simpa [mul_comm] using norm_lastSlot_le M g)

@[simp] theorem lastSlotCLM_apply (g : B) (M : B [×3]→L[ℝ] ℝ) : lastSlotCLM g M = lastSlot M g :=
  rfl

/-- (3) The tensor cons `J ⊗ g := (M ↦ J (lastSlot M g)) : TensorDual B 3`. -/
def tensorCons (J : TensorDual B 2) (g : B) : TensorDual B 3 :=
  J.comp (lastSlotCLM g)

/-- (3) Evaluation: `(J ⊗ g) M = J (lastSlot M g)`. -/
@[simp] theorem tensorCons_apply (J : TensorDual B 2) (g : B) (M : B [×3]→L[ℝ] ℝ) :
    tensorCons J g M = J (lastSlot M g) := rfl

/-- (3) Norm bound `‖J ⊗ g‖ ≤ ‖J‖ ‖g‖`. -/
theorem norm_tensorCons_le (J : TensorDual B 2) (g : B) : ‖tensorCons J g‖ ≤ ‖J‖ * ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun M => ?_
  rw [tensorCons_apply]
  calc ‖J (lastSlot M g)‖ ≤ ‖J‖ * ‖lastSlot M g‖ := J.le_opNorm _
    _ ≤ ‖J‖ * (‖M‖ * ‖g‖) := by gcongr; exact norm_lastSlot_le M g
    _ = ‖J‖ * ‖g‖ * ‖M‖ := by ring

theorem tensorCons_add_left (J J' : TensorDual B 2) (g : B) :
    tensorCons (J + J') g = tensorCons J g + tensorCons J' g := by
  ext M; simp

theorem tensorCons_smul_left (c : ℝ) (J : TensorDual B 2) (g : B) :
    tensorCons (c • J) g = c • tensorCons J g := by
  ext M; simp

theorem tensorCons_add_right (J : TensorDual B 2) (g g' : B) :
    tensorCons J (g + g') = tensorCons J g + tensorCons J g' := by
  ext M; simp [e213t_lastSlot_add_right]

theorem tensorCons_smul_right (c : ℝ) (J : TensorDual B 2) (g : B) :
    tensorCons J (c • g) = c • tensorCons J g := by
  ext M; simp [e213t_lastSlot_smul_right]

/-- (3) `tensorCons` as a continuous bilinear map `TensorDual B 2 →L B →L TensorDual B 3`. -/
def tensorConsL : TensorDual B 2 →L[ℝ] B →L[ℝ] TensorDual B 3 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun J g => tensorCons J g) tensorCons_add_left tensorCons_smul_left
      tensorCons_add_right tensorCons_smul_right)
    1 (fun J g => by simpa using norm_tensorCons_le J g)

@[simp] theorem tensorConsL_apply (J : TensorDual B 2) (g : B) :
    (tensorConsL (B := B)) J g = tensorCons J g :=
  rfl

/-- (3) `(J, g) ↦ J ⊗ g` is continuous. -/
theorem continuous_tensorCons :
    Continuous fun p : TensorDual B 2 × B => tensorCons p.1 p.2 :=
  (tensorConsL (B := B)).isBoundedBilinearMap.continuous

/-- (3) Elementary tensors map to elementary tensors: `elemTensor v ⊗ g = elemTensor ![v 0, v 1, g]`. -/
theorem tensorCons_elemTensor (v : Fin 2 → B) (g : B) :
    tensorCons (elemTensor v) g = elemTensor ![v 0, v 1, g] := by
  ext M
  have hv : v = ![v 0, v 1] := by ext k; fin_cases k <;> rfl
  rw [tensorCons_apply, elemTensor_apply, elemTensor_apply]
  conv_lhs => rw [hv]
  exact lastSlot_apply M g (v 0) (v 1)

/-- (3) `projTensor B 2 × B → projTensor B 3`: `J ⊗ g ∈ projTensor B 3` for `J ∈ projTensor B 2`. -/
theorem tensorCons_mem {J : TensorDual B 2} (hJ : J ∈ projTensor B 2) (g : B) :
    tensorCons J g ∈ projTensor B 3 := by
  have := e213t_map_projTensor_le (E := B) (k := 2) (k' := 3)
    ((ContinuousLinearMap.apply ℝ (TensorDual B 3) g).comp tensorConsL)
    (fun v => by
      simpa [tensorCons_elemTensor] using elemTensor_mem_projTensor (B := B) ![v 0, v 1, g]) J hJ
  simpa using this

section Bochner

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable (P) in
/-- (3) The Bochner tensor `E[J ⊗ g] := ∫ ω, J ω ⊗ g ω ∂P ∈ TensorDual B 3`. -/
def bochTensor21 (J : Ω → TensorDual B 2) (g : Ω → B) : TensorDual B 3 :=
  ∫ ω, tensorCons (J ω) (g ω) ∂P

/-- (3) Measurability of the integrand of `bochTensor21`. -/
theorem bochTensor21_aestronglyMeasurable {J : Ω → TensorDual B 2} {g : Ω → B}
    (hJ : AEStronglyMeasurable J P) (hg : AEStronglyMeasurable g P) :
    AEStronglyMeasurable (fun ω => tensorCons (J ω) (g ω)) P :=
  continuous_tensorCons.comp_aestronglyMeasurable (hJ.prodMk hg)

/-- (3) Integrability of the integrand of `bochTensor21` when `‖J‖‖g‖` is integrable. -/
theorem bochTensor21_integrable {J : Ω → TensorDual B 2} {g : Ω → B}
    (hJ : AEStronglyMeasurable J P) (hg : AEStronglyMeasurable g P)
    (hint : Integrable (fun ω => ‖J ω‖ * ‖g ω‖) P) :
    Integrable (fun ω => tensorCons (J ω) (g ω)) P :=
  Integrable.mono' hint (bochTensor21_aestronglyMeasurable hJ hg)
    (ae_of_all _ fun ω => norm_tensorCons_le _ _)

/-- (3) `bochTensor21 P J g ∈ projTensor B 3` when `J ω ∈ projTensor B 2` a.e. -/
theorem bochTensor21_mem {J : Ω → TensorDual B 2} {g : Ω → B}
    (hJ : AEStronglyMeasurable J P) (hg : AEStronglyMeasurable g P)
    (hint : Integrable (fun ω => ‖J ω‖ * ‖g ω‖) P)
    (hmem : ∀ᵐ ω ∂P, J ω ∈ projTensor B 2) :
    bochTensor21 P J g ∈ projTensor B 3 :=
  e213t_integral_mem _ (Submodule.isClosed_topologicalClosure _)
    (bochTensor21_integrable hJ hg hint) (hmem.mono fun ω h => tensorCons_mem h _)

/-- (3) Evaluation: `bochTensor21 P J g M = ∫ J ω (lastSlot M (g ω)) ∂P`. -/
theorem bochTensor21_apply {J : Ω → TensorDual B 2} {g : Ω → B}
    (hJ : AEStronglyMeasurable J P) (hg : AEStronglyMeasurable g P)
    (hint : Integrable (fun ω => ‖J ω‖ * ‖g ω‖) P) (M : B [×3]→L[ℝ] ℝ) :
    bochTensor21 P J g M = ∫ ω, J ω (lastSlot M (g ω)) ∂P := by
  unfold bochTensor21
  rw [ContinuousLinearMap.integral_apply (bochTensor21_integrable hJ hg hint)]
  simp only [tensorCons_apply]

/-- (3) Norm bound: `‖bochTensor21 P J g‖ ≤ ∫ ‖J ω‖ ‖g ω‖ ∂P`. -/
theorem norm_bochTensor21_le {J : Ω → TensorDual B 2} {g : Ω → B}
    (hJ : AEStronglyMeasurable J P) (hg : AEStronglyMeasurable g P)
    (hint : Integrable (fun ω => ‖J ω‖ * ‖g ω‖) P) :
    ‖bochTensor21 P J g‖ ≤ ∫ ω, ‖J ω‖ * ‖g ω‖ ∂P := by
  unfold bochTensor21
  refine (norm_integral_le_integral_norm _).trans ?_
  exact integral_mono (bochTensor21_integrable hJ hg hint).norm hint
    fun ω => norm_tensorCons_le _ _

/-- (3) Version for `J : Ω → projTensor B 2` (subtype-valued): membership in `projTensor B 3`. -/
theorem bochTensor21_mem_subtype {J : Ω → projTensor B 2} {g : Ω → B}
    (hJ : AEStronglyMeasurable (fun ω => (J ω : TensorDual B 2)) P)
    (hg : AEStronglyMeasurable g P)
    (hint : Integrable (fun ω => ‖J ω‖ * ‖g ω‖) P) :
    bochTensor21 P (fun ω => (J ω : TensorDual B 2)) g ∈ projTensor B 3 :=
  bochTensor21_mem hJ hg hint (ae_of_all _ fun ω => (J ω).2)

end Bochner

end HRS.MC.E213T
end
