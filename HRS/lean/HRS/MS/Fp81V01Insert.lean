import HRS.MC.E213TSymm
import HRS.MC.E213U3C
import HRS.MS.S111TermAux1
import HRS.MS.R26T6CD03

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 64000

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111T HRS.MC.E213T

variable {d r : ℕ}
variable {s a β γ T u c B Pw : ℝ}
variable {ρ : Euc d → ℝ}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : r26t6_WeightedChart d r Pw}

local notation "X" => R2X d T
local notation "P2" => projTensor X 2
local notation "P3" => projTensor X 3

/-- The closed projective tensor subspace is complete as a subtype of `TensorDual`. -/
instance fp81v01_projTensorComplete (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) : CompleteSpace (projTensor Y k) :=
  (HRS.MC.E213U3.u3_isClosed_proj Y k).completeSpace_coe

private def fp81v01_cyclicPerm (j : Fin 3) : Equiv.Perm (Fin 3) :=
  if j = 0 then Equiv.refl (Fin 3)
  else if j = 1 then Equiv.swap 0 1 * Equiv.swap 0 2
  else Equiv.swap 1 2 * Equiv.swap 0 2

private theorem fp81v01_permTensor_norm_le (σ : Equiv.Perm (Fin 3))
    (u : TensorDual X 3) : ‖permTensor X σ u‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun M => ?_
  rw [permTensor_apply]
  calc
    ‖u (M.domDomCongr σ)‖ ≤ ‖u‖ * ‖M.domDomCongr σ‖ := u.le_opNorm _
    _ = ‖u‖ * ‖M‖ := by rw [← permForms_apply σ M, norm_permForms_apply]

private theorem fp81v01_cyclicPerm_slots (j : Fin 3) (v x y : X) :
    (fun k : Fin 3 => (![v, x, y] : Fin 3 → X) (fp81v01_cyclicPerm j k)) =
      fun k => if k = j then v else if k = j + 1 then x else y := by
  funext k
  fin_cases j <;> fin_cases k <;>
    simp [fp81v01_cyclicPerm, Equiv.swap_apply_def]

private def fp81v01_permProj (σ : Equiv.Perm (Fin 3)) : P3 →L[ℝ] P3 :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟨permTensor X σ (z : TensorDual X 3), by
        refine e213t_map_projTensor_le (E := X) (k := 3) (k' := 3)
          (permTensor X σ) ?_ z z.2
        intro w
        have he : permTensor X σ (elemTensor w) = elemTensor (fun i => w (σ i)) := by
          ext M
          simp [permTensor_apply, elemTensor_apply]
        rw [he]
        exact elemTensor_mem_projTensor _⟩
      map_add' := fun z z' => by
        apply Subtype.ext
        ext M
        simp [permTensor_apply]
      map_smul' := fun a z => by
        apply Subtype.ext
        ext M
        simp [permTensor_apply] }
    1 (fun z => by
      change ‖permTensor X σ (z : TensorDual X 3)‖ ≤ 1 * ‖(z : TensorDual X 3)‖
      calc
        ‖permTensor X σ (z : TensorDual X 3)‖ ≤ ‖(z : TensorDual X 3)‖ :=
          fp81v01_permTensor_norm_le σ _
        _ = 1 * ‖(z : TensorDual X 3)‖ := by ring)

private theorem fp81v01_permProj_norm (σ : Equiv.Perm (Fin 3)) (z : P3) :
    ‖fp81v01_permProj σ z‖ ≤ ‖z‖ := by
  change ‖permTensor X σ (z : TensorDual X 3)‖ ≤ ‖(z : TensorDual X 3)‖
  exact fp81v01_permTensor_norm_le σ _

@[simp] private theorem fp81v01_permProj_coe (σ : Equiv.Perm (Fin 3)) (z : P3) :
    ((fp81v01_permProj σ z : P3) : TensorDual X 3) = permTensor X σ z := rfl

private def fp81v01_elemCMM (σ : Equiv.Perm (Fin 3)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3 :=
  ((permTensor X σ).compContinuousMultilinearMap (elemTensorCMM X 3)).codRestrict P3
    (fun v => by
      change permTensor X σ (elemTensor v) ∈ P3
      have he : permTensor X σ (elemTensor v) = elemTensor (fun i => v (σ i)) := by
        ext M
        simp [permTensor_apply, elemTensor_apply]
      rw [he]
      exact elemTensor_mem_projTensor _)

private theorem fp81v01_update0 (x y z x' : X) :
    Function.update (![x, y, z] : Fin 3 → X) 0 x' = ![x', y, z] := by
  ext i
  fin_cases i <;> simp [Function.update]

private theorem fp81v01_update1 (x y z y' : X) :
    Function.update (![x, y, z] : Fin 3 → X) 1 y' = ![x, y', z] := by
  ext i
  fin_cases i <;> simp [Function.update]

private theorem fp81v01_update2 (x y z z' : X) :
    Function.update (![x, y, z] : Fin 3 → X) 2 z' = ![x, y, z'] := by
  ext i
  fin_cases i <;> simp [Function.update]

private theorem fp81v01_elem_add0 (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3)
    (x x' y z : X) : F ![x + x', y, z] = F ![x, y, z] + F ![x', y, z] := by
  change F.toMultilinearMap ![x + x', y, z] =
    F.toMultilinearMap ![x, y, z] + F.toMultilinearMap ![x', y, z]
  have h := F.toMultilinearMap.map_update_add (![x, y, z] : Fin 3 → X) 0 x x'
  simpa only [fp81v01_update0] using h

private theorem fp81v01_elem_smul0 (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3)
    (a : ℝ) (x y z : X) : F ![a • x, y, z] = a • F ![x, y, z] := by
  change F.toMultilinearMap ![a • x, y, z] = a • F.toMultilinearMap ![x, y, z]
  have h := F.toMultilinearMap.map_update_smul (![x, y, z] : Fin 3 → X) 0 a x
  simpa only [fp81v01_update0] using h

private theorem fp81v01_elem_add1 (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3)
    (x y y' z : X) : F ![x, y + y', z] = F ![x, y, z] + F ![x, y', z] := by
  change F.toMultilinearMap ![x, y + y', z] =
    F.toMultilinearMap ![x, y, z] + F.toMultilinearMap ![x, y', z]
  have h := F.toMultilinearMap.map_update_add (![x, y, z] : Fin 3 → X) 1 y y'
  simpa only [fp81v01_update1] using h

private theorem fp81v01_elem_smul1 (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3)
    (a : ℝ) (x y z : X) : F ![x, a • y, z] = a • F ![x, y, z] := by
  change F.toMultilinearMap ![x, a • y, z] = a • F.toMultilinearMap ![x, y, z]
  have h := F.toMultilinearMap.map_update_smul (![x, y, z] : Fin 3 → X) 1 a y
  simpa only [fp81v01_update1] using h

private theorem fp81v01_elem_add2 (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3)
    (x y z z' : X) : F ![x, y, z + z'] = F ![x, y, z] + F ![x, y, z'] := by
  change F.toMultilinearMap ![x, y, z + z'] =
    F.toMultilinearMap ![x, y, z] + F.toMultilinearMap ![x, y, z']
  have h := F.toMultilinearMap.map_update_add (![x, y, z] : Fin 3 → X) 2 z z'
  simpa only [fp81v01_update2] using h

private theorem fp81v01_elem_smul2 (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3)
    (a : ℝ) (x y z : X) : F ![x, y, a • z] = a • F ![x, y, z] := by
  change F.toMultilinearMap ![x, y, a • z] = a • F.toMultilinearMap ![x, y, z]
  have h := F.toMultilinearMap.map_update_smul (![x, y, z] : Fin 3 → X) 2 a z
  simpa only [fp81v01_update2] using h

private def fp81v01_curry3_inner
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3) (x y : X) : X →L[ℝ] P3 :=
  LinearMap.mkContinuous
    { toFun := fun z => F ![x, y, z]
      map_add' := fun z z' => fp81v01_elem_add2 F x y z z'
      map_smul' := fun a z => fp81v01_elem_smul2 F a x y z }
    (‖F‖ * ‖x‖ * ‖y‖) (fun z => by
      calc
        ‖F ![x, y, z]‖ ≤ ‖F‖ * (‖x‖ * ‖y‖ * ‖z‖) := by
          simpa [Fin.prod_univ_three, mul_assoc] using F.le_opNorm (![x, y, z] : Fin 3 → X)
        _ = (‖F‖ * ‖x‖ * ‖y‖) * ‖z‖ := by ring)

@[simp] private theorem fp81v01_curry3_inner_apply
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3) (x y z : X) :
    fp81v01_curry3_inner F x y z = F ![x, y, z] := rfl

private def fp81v01_curry3_mid
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3) (x : X) :
    X →L[ℝ] X →L[ℝ] P3 :=
  LinearMap.mkContinuous
    { toFun := fun y => fp81v01_curry3_inner F x y
      map_add' := fun y y' => by
        apply ContinuousLinearMap.ext
        intro z
        exact fp81v01_elem_add1 F x y y' z
      map_smul' := fun a y => by
        apply ContinuousLinearMap.ext
        intro z
        exact fp81v01_elem_smul1 F a x y z }
    (‖F‖ * ‖x‖) (fun y => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
      calc
        ‖fp81v01_curry3_inner F x y z‖ ≤ ‖F‖ * (‖x‖ * ‖y‖ * ‖z‖) := by
          simpa [Fin.prod_univ_three, mul_assoc] using F.le_opNorm (![x, y, z] : Fin 3 → X)
        _ = (‖F‖ * ‖x‖ * ‖y‖) * ‖z‖ := by ring)

@[simp] private theorem fp81v01_curry3_mid_apply
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3) (x y z : X) :
    fp81v01_curry3_mid F x y z = F ![x, y, z] := rfl

private def fp81v01_curry3 (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3) :
    X →L[ℝ] X →L[ℝ] X →L[ℝ] P3 :=
  LinearMap.mkContinuous
    { toFun := fun x => fp81v01_curry3_mid F x
      map_add' := fun x x' => by
        apply ContinuousLinearMap.ext
        intro y
        apply ContinuousLinearMap.ext
        intro z
        exact fp81v01_elem_add0 F x x' y z
      map_smul' := fun a x => by
        apply ContinuousLinearMap.ext
        intro y
        apply ContinuousLinearMap.ext
        intro z
        exact fp81v01_elem_smul0 F a x y z }
    ‖F‖ (fun x => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
      calc
        ‖fp81v01_curry3_mid F x y z‖ ≤ ‖F‖ * (‖x‖ * ‖y‖ * ‖z‖) := by
          simpa [Fin.prod_univ_three, mul_assoc] using F.le_opNorm (![x, y, z] : Fin 3 → X)
        _ = (‖F‖ * ‖x‖ * ‖y‖) * ‖z‖ := by ring)

@[simp] private theorem fp81v01_curry3_apply
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) P3) (x y z : X) :
    fp81v01_curry3 F x y z = F ![x, y, z] := rfl

-- The insertion definitions and Bochner interface follow below.

/-- Insert three vectors in cyclic slot order, with the first vector in slot `j`. -/
def Insert (j : Fin 3) : X →L[ℝ] X →L[ℝ] X →L[ℝ] P3 :=
  fp81v01_curry3 (fp81v01_elemCMM (fp81v01_cyclicPerm j))

/-- Insert a projective two tensor into the cyclic pair of slots beginning at `j`. -/
def PairInsert (j : Fin 3) : P2 →L[ℝ] X →L[ℝ] P3 := by
  let σ : Equiv.Perm (Fin 3) := fp81v01_cyclicPerm j
  let π : P3 →L[ℝ] P3 := fp81v01_permProj σ
  refine LinearMap.mkContinuous
    { toFun := fun Q => π.comp ((tensorConsL (B := X) (Q : TensorDual X 2)).codRestrict P3
        (fun y => tensorCons_mem Q.2 y))
      map_add' := fun Q Q' => by
        ext y M
        change (permTensor X σ (tensorCons
            ((Q : TensorDual X 2) + (Q' : TensorDual X 2)) y)) M =
          (permTensor X σ (tensorCons (Q : TensorDual X 2) y)) M +
            (permTensor X σ (tensorCons (Q' : TensorDual X 2) y)) M
        rw [tensorCons_add_left]
        simp [permTensor_apply]
      map_smul' := fun a Q => by
        ext y M
        change (permTensor X σ (tensorCons
            (a • (Q : TensorDual X 2)) y)) M =
          a * (permTensor X σ (tensorCons (Q : TensorDual X 2) y)) M
        rw [tensorCons_smul_left]
        simp [permTensor_apply] }
    1 (fun Q => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  calc
    ‖π.comp ((tensorConsL (B := X) (Q : TensorDual X 2)).codRestrict P3
        (fun z => tensorCons_mem Q.2 z)) y‖ ≤
      ‖((tensorConsL (B := X) (Q : TensorDual X 2)).codRestrict P3
        (fun z => tensorCons_mem Q.2 z)) y‖ := fp81v01_permProj_norm σ _
    _ = ‖tensorCons (Q : TensorDual X 2) y‖ := rfl
    _ ≤ 1 * ‖Q‖ * ‖y‖ := by
      have hQnorm : ‖(Q : TensorDual X 2)‖ = ‖Q‖ := rfl
      simpa [hQnorm] using norm_tensorCons_le (Q : TensorDual X 2) y

@[simp] private theorem fp81v01_PairInsert_apply (j : Fin 3) (Q : P2) (y : X) :
    PairInsert j Q y = fp81v01_permProj (fp81v01_cyclicPerm j)
      (((tensorConsL (B := X) (Q : TensorDual X 2)).codRestrict P3
        (fun z => tensorCons_mem Q.2 z)) y) := by
  rfl

/-- The insertion map is the elementary tensor with the stated cyclic slot arrangement. -/
theorem Insert_spec (j : Fin 3) (v x y : X) :
    ((Insert j v x y : P3) : TensorDual X 3) =
      elemTensor (fun k => if k = j then v else if k = j + 1 then x else y) := by
  change permTensor X (fp81v01_cyclicPerm j) (elemTensor ![v, x, y]) = _
  have hperm : permTensor X (fp81v01_cyclicPerm j) (elemTensor ![v, x, y]) =
      elemTensor (fun k => (![v, x, y] : Fin 3 → X) (fp81v01_cyclicPerm j k)) := by
    ext M
    simp [permTensor_apply, elemTensor_apply]
  rw [hperm, fp81v01_cyclicPerm_slots]

/-- Pair insertion agrees with elementary two tensor insertion. -/
theorem PairInsert_spec (j : Fin 3) (v x y : X) :
    ((PairInsert j
      ⟨elemTensor ![v, x], HRS.MC.E213T.elemTensor_mem_projTensor _⟩ y : P3) :
        TensorDual X 3) =
      elemTensor (fun k => if k = j then v else if k = j + 1 then x else y) := by
  rw [fp81v01_PairInsert_apply]
  change permTensor X (fp81v01_cyclicPerm j) (tensorCons (elemTensor ![v, x]) y) = _
  rw [tensorCons_elemTensor]
  have hv : (![![v, x] 0, ![v, x] 1, y] : Fin 3 → X) = ![v, x, y] := by
    ext k
    fin_cases k <;> simp
  rw [hv]
  have hperm : permTensor X (fp81v01_cyclicPerm j) (elemTensor ![v, x, y]) =
      elemTensor (fun k => (![v, x, y] : Fin 3 → X) (fp81v01_cyclicPerm j k)) := by
    ext M
    simp [permTensor_apply, elemTensor_apply]
  rw [hperm, fp81v01_cyclicPerm_slots]

/-- Projective norm bounds for both insertion maps. -/
theorem insertion_bounds (j : Fin 3) (v x y : X) (Q : P2) :
    ‖Insert j v x y‖ ≤ ‖v‖ * ‖x‖ * ‖y‖ ∧
    ‖PairInsert j Q y‖ ≤ ‖Q‖ * ‖y‖ := by
  constructor
  · change ‖((Insert j v x y : P3) : TensorDual X 3)‖ ≤ _
    rw [Insert_spec]
    calc
      ‖(elemTensor (fun k => if k = j then v else if k = j + 1 then x else y) : TensorDual X 3)‖ ≤
        ∏ k, ‖(fun k => if k = j then v else if k = j + 1 then x else y) k‖ :=
          e213t_norm_elemTensor_le _
      _ = ‖v‖ * ‖x‖ * ‖y‖ := by
        fin_cases j <;> simp [Fin.prod_univ_three, mul_assoc, mul_left_comm, mul_comm]
  · rw [fp81v01_PairInsert_apply]
    calc
      ‖fp81v01_permProj (fp81v01_cyclicPerm j)
          (((tensorConsL (B := X) (Q : TensorDual X 2)).codRestrict P3
            (fun z => tensorCons_mem Q.2 z)) y)‖ ≤
        ‖((tensorConsL (B := X) (Q : TensorDual X 2)).codRestrict P3
          (fun z => tensorCons_mem Q.2 z)) y‖ := fp81v01_permProj_norm _ _
      _ = ‖tensorCons (Q : TensorDual X 2) y‖ := rfl
      _ ≤ ‖Q‖ * ‖y‖ := by
        have hQnorm : ‖(Q : TensorDual X 2)‖ = ‖Q‖ := rfl
        simpa [hQnorm] using norm_tensorCons_le (Q : TensorDual X 2) y

/-- Cumulative drift tensor, with insertion in each cyclic slot. -/
noncomputable def D (P : Measure Ω)
    (O : r26t6_IntervalOperators E (r26t6_thermalCoeff d s a β ρ) T u c B)
    (q : ℝ × Ω → r26t6_Coeff) (Z : Ω → X) : ℝ → P3 :=
  fun v => ∑ j : Fin 3,
    ∫ w, Insert j (r26t6_randomDrift O q v w) (Z w) (Z w) ∂P

/-- Cumulative covariance tensor, with the paired insertion in each cyclic slot. -/
noncomputable def J (P : Measure Ω)
    (O : r26t6_IntervalOperators E (r26t6_thermalCoeff d s a β ρ) T u c B)
    (q : ℝ × Ω → r26t6_Coeff) (Z : Ω → X) : ℝ → P3 :=
  fun v => ∑ j : Fin 3,
    ∫ w, PairInsert j (r26t6_randomCovariance O q v w) (Z w) ∂P

/-- Hölder in the `(2,4,4)` regime makes the drift insertion Bochner integrable. -/
theorem Insert_integrable (P : Measure Ω)
    {A x y : Ω → X}
    (hA : MemLp A 2 P) (hx : MemLp x 4 P)
    (hy : MemLp y 4 P) (j : Fin 3) :
    Integrable (fun w => Insert j (A w) (x w) (y w)) P := by
  have hxy : MemLp (fun w => ‖x w‖ * ‖y w‖) 2 P :=
    hx.norm.mul hy.norm (r := 2)
  have hn : Integrable (fun w => ‖A w‖ * (‖x w‖ * ‖y w‖)) P :=
    hA.norm.integrable_mul hxy
  have htuple : Continuous (fun p : X × X × X =>
      (![p.1, p.2.1, p.2.2] : Fin 3 → X)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_fst
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd
  have helem : Continuous (fun p : X × X × X =>
      (⟨elemTensor ![p.1, p.2.1, p.2.2], elemTensor_mem_projTensor _⟩ : P3)) :=
    Continuous.subtype_mk
      ((e213t_continuous_elemTensor (B := X) 3).comp htuple)
      (fun p => elemTensor_mem_projTensor _)
  have hinsertCont : Continuous (fun p : X × X × X =>
      fp81v01_permProj (fp81v01_cyclicPerm j)
        (⟨elemTensor ![p.1, p.2.1, p.2.2], elemTensor_mem_projTensor _⟩ : P3)) :=
    (fp81v01_permProj (fp81v01_cyclicPerm j)).continuous.comp helem
  have hsmCMM : AEStronglyMeasurable
      (fun w => fp81v01_permProj (fp81v01_cyclicPerm j)
        (⟨elemTensor ![A w, x w, y w], elemTensor_mem_projTensor _⟩ : P3)) P :=
    hinsertCont.comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk (hx.aestronglyMeasurable.prodMk hy.aestronglyMeasurable))
  have hsm : AEStronglyMeasurable (fun w => Insert j (A w) (x w) (y w)) P := by
    apply hsmCMM.congr (Filter.Eventually.of_forall fun w => ?_)
    apply Subtype.ext
    rw [Insert_spec]
    have hperm : permTensor X (fp81v01_cyclicPerm j)
        (elemTensor ![A w, x w, y w]) =
          elemTensor (fun k => (![A w, x w, y w] : Fin 3 → X)
            (fp81v01_cyclicPerm j k)) := by
      ext M
      simp [permTensor_apply, elemTensor_apply]
    rw [fp81v01_permProj_coe]
    simpa only [fp81v01_cyclicPerm_slots] using hperm
  refine Integrable.mono' hn hsm (ae_of_all _ fun w => ?_)
  have hbound := (insertion_bounds j (A w) (x w) (y w) (0 : P2)).1
  simpa [mul_assoc] using hbound

/-- Hölder in the `(2,2)` regime makes the covariance insertion Bochner integrable. -/
theorem PairInsert_integrable (P : Measure Ω)
    {Q : Ω → P2} {x : Ω → X}
    (hQ : MemLp Q 2 P) (hx : MemLp x 2 P) (j : Fin 3) :
    Integrable (fun w => PairInsert j (Q w) (x w)) P := by
  have hn : Integrable (fun w => ‖Q w‖ * ‖x w‖) P := hQ.norm.integrable_mul hx.norm
  have hsource : Continuous (fun p : P2 × X => ((p.1 : TensorDual X 2), p.2)) :=
    (((projTensor X 2).subtypeL).continuous.comp continuous_fst).prodMk continuous_snd
  have hcons : Continuous (fun p : P2 × X =>
      (⟨tensorCons (p.1 : TensorDual X 2) p.2, tensorCons_mem p.1.2 p.2⟩ : P3)) :=
    Continuous.subtype_mk (continuous_tensorCons.comp hsource) (fun p => tensorCons_mem p.1.2 p.2)
  have hpair : Continuous (fun p : P2 × X =>
      fp81v01_permProj (fp81v01_cyclicPerm j)
        (⟨tensorCons (p.1 : TensorDual X 2) p.2, tensorCons_mem p.1.2 p.2⟩ : P3)) :=
    (fp81v01_permProj (fp81v01_cyclicPerm j)).continuous.comp hcons
  have hsm : AEStronglyMeasurable (fun w => PairInsert j (Q w) (x w)) P :=
    hpair.comp_aestronglyMeasurable (hQ.aestronglyMeasurable.prodMk hx.aestronglyMeasurable)
  refine Integrable.mono' hn hsm (ae_of_all _ fun w => ?_)
  have hbound := (insertion_bounds j (0 : X) (0 : X) (x w) (Q w)).2
  simpa using hbound

/-- Product-form evaluation of an inserted elementary tensor in cyclic order. -/
theorem Insert_product_eval (j : Fin 3) (v x y : X)
    (ell : Fin 3 → X →L[ℝ] ℝ) (M : X [×3]→L[ℝ] ℝ)
    (hM : ∀ w : Fin 3 → X, M w = ∏ i, ell i (w i)) :
    ((Insert j v x y : P3) : TensorDual X 3) M =
      ell j v * ell (j + 1) x * ell (j + 2) y := by
  rw [Insert_spec, elemTensor_apply, hM]
  fin_cases j <;> simp [Fin.prod_univ_three] <;> ring

/-- Evaluation by a bounded trilinear form commutes with the subtype-valued Bochner integral. -/
theorem Insert_integral_eval (P : Measure Ω) (j : Fin 3)
    {A x y : Ω → X} (hI : Integrable (fun w => Insert j (A w) (x w) (y w)) P)
    (M : X [×3]→L[ℝ] ℝ) :
    (((∫ w, Insert j (A w) (x w) (y w) ∂P : P3) : TensorDual X 3) M) =
      ∫ w, ((Insert j (A w) (x w) (y w) : P3) : TensorDual X 3) M ∂P := by
  let L : P3 →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ M).comp (projTensor X 3).subtypeL
  change L (∫ w, Insert j (A w) (x w) (y w) ∂P) =
    ∫ w, L (Insert j (A w) (x w) (y w)) ∂P
  exact (L.integral_comp_comm hI).symm

/- Axiom audit for this module's exported theorems. -/
#print axioms fp81v01_projTensorComplete
#print axioms Insert
#print axioms PairInsert
#print axioms Insert_spec
#print axioms PairInsert_spec
#print axioms insertion_bounds
#print axioms D
#print axioms J
#print axioms Insert_integrable
#print axioms PairInsert_integrable
#print axioms Insert_product_eval
#print axioms Insert_integral_eval

end HRS.Fp81.V01
end
