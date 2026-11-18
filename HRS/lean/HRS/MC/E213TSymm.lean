import HRS.MC.E213TCons

/-!
# Packet e213c, file 3: the symmetrisation `symm3` and the pushforward `pushforward3`

`symm3` is the average over `Equiv.Perm (Fin 3)` of `u ↦ (M ↦ u (M.domDomCongr σ))`;
`pushforward3 I` is `u ↦ (M ↦ u (M.compContinuousLinearMap fun _ => I))`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option maxSynthPendingDepth 3

namespace HRS.MC.E213T

open HRS

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

section Symm

/-- The permutation `σ` acting on the trilinear forms, as a continuous linear map. -/
def permForms (σ : Equiv.Perm (Fin 3)) : (B [×3]→L[ℝ] ℝ) →L[ℝ] (B [×3]→L[ℝ] ℝ) :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ B ℝ σ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem permForms_apply (σ : Equiv.Perm (Fin 3)) (M : B [×3]→L[ℝ] ℝ) :
    permForms σ M = M.domDomCongr σ := rfl

theorem norm_permForms_apply (σ : Equiv.Perm (Fin 3)) (M : B [×3]→L[ℝ] ℝ) :
    ‖permForms σ M‖ = ‖M‖ := by
  simp [permForms_apply]

/-- `u ↦ (M ↦ u (M.domDomCongr σ))` as a continuous linear map of norm `≤ 1`. -/
def permTensor (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] (σ : Equiv.Perm (Fin 3)) :
    TensorDual B 3 →L[ℝ] TensorDual B 3 :=
  LinearMap.mkContinuous
    { toFun := fun u => u.comp (permForms σ)
      map_add' := fun u u' => by ext M; simp
      map_smul' := fun c u => by ext M; simp }
    1 (fun u => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun M => ?_
      show ‖u (permForms σ M)‖ ≤ 1 * ‖u‖ * ‖M‖
      calc ‖u (permForms σ M)‖ ≤ ‖u‖ * ‖permForms σ M‖ := u.le_opNorm _
        _ = 1 * ‖u‖ * ‖M‖ := by rw [norm_permForms_apply]; ring)

@[simp] theorem permTensor_apply (σ : Equiv.Perm (Fin 3)) (u : TensorDual B 3)
    (M : B [×3]→L[ℝ] ℝ) : permTensor B σ u M = u (M.domDomCongr σ) := rfl

theorem norm_permTensor_le (σ : Equiv.Perm (Fin 3)) : ‖permTensor B σ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The permutation average `(1/6) ∑_σ`, written with `Fintype.card (Equiv.Perm (Fin 3)) = 6`. -/
def symmCoeff : ℝ := ((Fintype.card (Equiv.Perm (Fin 3)) : ℕ) : ℝ)⁻¹

theorem symmCoeff_eq : symmCoeff = 1 / 6 := by
  have : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Fintype.card_perm]; simp [Nat.factorial]
  simp [symmCoeff, this]

/-- (4) `symm3 : TensorDual B 3 →L TensorDual B 3`, the average over `Equiv.Perm (Fin 3)` of
`u ↦ (M ↦ u (M.domDomCongr σ))`. -/
def symm3 (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] :
    TensorDual B 3 →L[ℝ] TensorDual B 3 :=
  symmCoeff • ∑ σ : Equiv.Perm (Fin 3), permTensor B σ

/-- (4) Evaluation formula `symm3 B u M = (1/6) ∑_σ u (M.domDomCongr σ)`. -/
theorem symm3_apply (u : TensorDual B 3) (M : B [×3]→L[ℝ] ℝ) :
    symm3 B u M = (1 / 6 : ℝ) * ∑ σ : Equiv.Perm (Fin 3), u (M.domDomCongr σ) := by
  simp [symm3, symmCoeff_eq]

/-- (4) `‖symm3‖ ≤ 1`. -/
theorem norm_symm3_le (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] : ‖symm3 B‖ ≤ 1 := by
  unfold symm3
  have hcard : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  calc ‖symmCoeff • ∑ σ : Equiv.Perm (Fin 3), (permTensor B σ)‖
      ≤ ‖symmCoeff‖ * ‖∑ σ : Equiv.Perm (Fin 3), (permTensor B σ)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖symmCoeff‖ * ∑ σ : Equiv.Perm (Fin 3), ‖(permTensor B σ)‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ ‖symmCoeff‖ * ∑ σ : Equiv.Perm (Fin 3), (1 : ℝ) := by
        gcongr with σ; exact norm_permTensor_le σ
    _ = 1 := by
        simp only [symmCoeff, norm_inv, Real.norm_natCast, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]
        exact inv_mul_cancel₀ hcard.ne'

theorem domDomCongr_domDomCongr (M : B [×3]→L[ℝ] ℝ) (σ τ : Equiv.Perm (Fin 3)) :
    (M.domDomCongr τ).domDomCongr σ = M.domDomCongr (σ * τ) := rfl

/-- (4) Symmetric output: `symm3 B u (M.domDomCongr τ) = symm3 B u M`. -/
theorem symm3_symmetric (u : TensorDual B 3) (M : B [×3]→L[ℝ] ℝ) (τ : Equiv.Perm (Fin 3)) :
    symm3 B u (M.domDomCongr τ) = symm3 B u M := by
  rw [symm3_apply, symm3_apply]
  congr 1
  simp only [domDomCongr_domDomCongr]
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun ρ => u (M.domDomCongr ρ))

/-- (4) `symm3` fixes symmetric elements. -/
theorem symm3_eq_of_symmetric {u : TensorDual B 3}
    (hu : ∀ (M : B [×3]→L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)), u (M.domDomCongr σ) = u M) :
    symm3 B u = u := by
  ext M
  rw [symm3_apply]
  simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) = 6 := by
    have : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Fintype.card_perm]; simp [Nat.factorial]
    exact_mod_cast this
  rw [this]; ring

/-- (4) `symm3 B (elemTensor v)` is the average of `elemTensor (v ∘ σ)`. -/
theorem symm3_elemTensor (v : Fin 3 → B) :
    symm3 B (elemTensor v : TensorDual B 3) =
      (1 / 6 : ℝ) • ∑ σ : Equiv.Perm (Fin 3), (elemTensor (fun i => v (σ i)) : TensorDual B 3) := by
  ext M
  rw [symm3_apply]
  simp [elemTensor_apply]

/-- (4) `symm3` maps `projTensor B 3` into itself. -/
theorem symm3_mem {u : TensorDual B 3} (hu : u ∈ projTensor B 3) : symm3 B u ∈ projTensor B 3 :=
  e213t_map_projTensor_le (E := B) (k := 3) (k' := 3) (symm3 B) (fun v => by
    rw [symm3_elemTensor]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => elemTensor_mem_projTensor _)) u hu

/-- (4) `symm3` restricted to `projTensor B 3`, as a continuous linear self-map of the subtype. -/
def symm3Proj (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] : projTensor B 3 →L[ℝ] projTensor B 3 :=
  (symm3 B).restrict (fun _ hu => symm3_mem hu)

@[simp] theorem coe_symm3Proj (u : projTensor B 3) :
    ((symm3Proj B u : projTensor B 3) : TensorDual B 3) = symm3 B (u : TensorDual B 3) := rfl

end Symm

section Push

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Precomposition of trilinear forms with `I` in each slot, as a continuous linear map. -/
def compForms (I : E →L[ℝ] B) : (B [×3]→L[ℝ] ℝ) →L[ℝ] (E [×3]→L[ℝ] ℝ) :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin 3 => I)

@[simp] theorem compForms_apply (I : E →L[ℝ] B) (M : B [×3]→L[ℝ] ℝ) :
    compForms I M = M.compContinuousLinearMap (fun _ : Fin 3 => I) := rfl

theorem norm_compForms_le (I : E →L[ℝ] B) : ‖compForms I‖ ≤ ‖I‖ ^ 3 := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le ℝ (fun _ : Fin 3 => I)).trans ?_
  simp

/-- (5) `pushforward3 I : TensorDual E 3 →L TensorDual B 3`,
`u ↦ (M ↦ u (M.compContinuousLinearMap fun _ => I))`. -/
def pushforward3 (I : E →L[ℝ] B) : TensorDual E 3 →L[ℝ] TensorDual B 3 :=
  LinearMap.mkContinuous
    { toFun := fun u => u.comp (compForms I)
      map_add' := fun u u' => by ext M; simp
      map_smul' := fun c u => by ext M; simp }
    (‖I‖ ^ 3) (fun u => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun M => ?_
      show ‖u (compForms I M)‖ ≤ ‖I‖ ^ 3 * ‖u‖ * ‖M‖
      calc ‖u (compForms I M)‖ ≤ ‖u‖ * ‖compForms I M‖ := u.le_opNorm _
        _ ≤ ‖u‖ * (‖I‖ ^ 3 * ‖M‖) := by
            gcongr; exact ((compForms I).le_opNorm M).trans (by gcongr; exact norm_compForms_le I)
        _ = ‖I‖ ^ 3 * ‖u‖ * ‖M‖ := by ring)

/-- (5) Evaluation formula. -/
@[simp] theorem pushforward3_apply (I : E →L[ℝ] B) (u : TensorDual E 3) (M : B [×3]→L[ℝ] ℝ) :
    pushforward3 I u M = u (M.compContinuousLinearMap (fun _ : Fin 3 => I)) := rfl

/-- (5) `‖pushforward3 I‖ ≤ ‖I‖ ^ 3`. -/
theorem norm_pushforward3_le (I : E →L[ℝ] B) : ‖pushforward3 I‖ ≤ ‖I‖ ^ 3 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- (5) `pushforward3 I (elemTensor v) = elemTensor (I ∘ v)`. -/
theorem pushforward3_elemTensor (I : E →L[ℝ] B) (v : Fin 3 → E) :
    pushforward3 I (elemTensor v) = elemTensor (fun i => I (v i)) := by
  ext M; rfl

/-- (5) `pushforward3 I (elemTensor ![x,y,z]) = elemTensor ![I x, I y, I z]`. -/
theorem pushforward3_elemTensor3 (I : E →L[ℝ] B) (x y z : E) :
    pushforward3 I (elemTensor ![x, y, z]) = elemTensor ![I x, I y, I z] := by
  rw [pushforward3_elemTensor]
  congr 1
  funext i; fin_cases i <;> rfl

/-- (5) `pushforward3 I` maps `projTensor E 3` into `projTensor B 3`. -/
theorem pushforward3_mem (I : E →L[ℝ] B) {u : TensorDual E 3} (hu : u ∈ projTensor E 3) :
    pushforward3 I u ∈ projTensor B 3 :=
  e213t_map_projTensor_le (E := E) (k := 3) (k' := 3) (pushforward3 I) (fun v => by
    rw [pushforward3_elemTensor]; exact elemTensor_mem_projTensor _) u hu

/-- (5) `pushforward3` commutes with `symm3`. -/
theorem pushforward3_symm3 (I : E →L[ℝ] B) (u : TensorDual E 3) :
    pushforward3 I (symm3 E u) = symm3 B (pushforward3 I u) := by
  ext M
  rw [pushforward3_apply, symm3_apply, symm3_apply]
  congr 1

/-- (5) `pushforward3` commutes with `bochTensor3`. -/
theorem pushforward3_bochTensor3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (I : E →L[ℝ] B) {x y z : Ω → E} (hx : AEStronglyMeasurable x P)
    (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P)
    (hint : Integrable (fun ω => ‖x ω‖ * ‖y ω‖ * ‖z ω‖) P) :
    pushforward3 I (bochTensor3 P x y z) =
      bochTensor3 P (fun ω => I (x ω)) (fun ω => I (y ω)) (fun ω => I (z ω)) := by
  unfold bochTensor3
  rw [← ContinuousLinearMap.integral_comp_comm _ (bochTensor3_integrable hx hy hz hint)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  exact pushforward3_elemTensor3 I _ _ _

end Push

end HRS.MC.E213T
end
