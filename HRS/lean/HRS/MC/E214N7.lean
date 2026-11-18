import HRS.MC.E214N6

/-!
# E214N7: difference of two window tensors with a common `Z` (generic algebra)

`‖Sym(X - 3E[D⊗Z⊗Z] + 3E[J⊗Z]) - Sym(X' - 3E[D'⊗Z⊗Z] + 3E[J'⊗Z])‖
  ≤ ‖X - X'‖ + 3 E[‖D-D'‖‖Z‖²] + 3 E[‖J-J'‖‖Z‖]`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {d : ℕ}

section Generic

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem elemTensor3_sub_left (x x' y z : B) :
    (elemTensor ![x - x', y, z] : TensorDual B 3) = elemTensor ![x, y, z] - elemTensor ![x', y, z] := by
  have e1 : (![x - x', y, z] : Fin 3 → B) = Function.update ![x, y, z] 0 (x - x') := by
    ext i; fin_cases i <;> simp
  have e2 : (![x', y, z] : Fin 3 → B) = Function.update ![x, y, z] 0 x' := by
    ext i; fin_cases i <;> simp
  ext M
  simp only [ContinuousLinearMap.sub_apply, elemTensor_apply]
  have := M.toMultilinearMap.map_update_sub (![x, y, z] : Fin 3 → B) 0 x x'
  have e3 : Function.update (![x, y, z] : Fin 3 → B) 0 x = ![x, y, z] := by
    ext i; fin_cases i <;> simp
  rw [e3] at this
  rw [e1, e2]
  exact this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem bochTensor3_sub_left {x x' y z : Ω → B} (hx : AEStronglyMeasurable x P)
    (hx' : AEStronglyMeasurable x' P) (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P)
    (h1 : Integrable (fun ω => ‖x ω‖ * ‖y ω‖ * ‖z ω‖) P)
    (h2 : Integrable (fun ω => ‖x' ω‖ * ‖y ω‖ * ‖z ω‖) P) :
    bochTensor3 P x y z - bochTensor3 P x' y z = bochTensor3 P (fun ω => x ω - x' ω) y z := by
  unfold bochTensor3
  rw [← integral_sub (bochTensor3_integrable hx hy hz h1) (bochTensor3_integrable hx' hy hz h2)]
  congr 1
  funext ω
  rw [elemTensor3_sub_left]

theorem norm_bochTensor3_sub_left_le {x x' y z : Ω → B} (hx : AEStronglyMeasurable x P)
    (hx' : AEStronglyMeasurable x' P) (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P)
    (h1 : Integrable (fun ω => ‖x ω‖ * ‖y ω‖ * ‖z ω‖) P)
    (h2 : Integrable (fun ω => ‖x' ω‖ * ‖y ω‖ * ‖z ω‖) P)
    (h3 : Integrable (fun ω => ‖x ω - x' ω‖ * ‖y ω‖ * ‖z ω‖) P) :
    ‖bochTensor3 P x y z - bochTensor3 P x' y z‖ ≤ ∫ ω, ‖x ω - x' ω‖ * ‖y ω‖ * ‖z ω‖ ∂P := by
  rw [bochTensor3_sub_left hx hx' hy hz h1 h2]
  exact norm_bochTensor3_le (hx.sub hx') hy hz h3

theorem bochTensor21_sub_left {J J' : Ω → TensorDual B 2} {g : Ω → B} (hJ : AEStronglyMeasurable J P)
    (hJ' : AEStronglyMeasurable J' P) (hg : AEStronglyMeasurable g P)
    (h1 : Integrable (fun ω => ‖J ω‖ * ‖g ω‖) P) (h2 : Integrable (fun ω => ‖J' ω‖ * ‖g ω‖) P) :
    bochTensor21 P J g - bochTensor21 P J' g = bochTensor21 P (fun ω => J ω - J' ω) g := by
  unfold bochTensor21
  rw [← integral_sub (bochTensor21_integrable hJ hg h1) (bochTensor21_integrable hJ' hg h2)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  ext M
  simp [tensorCons_apply]

theorem norm_bochTensor21_sub_left_le {J J' : Ω → TensorDual B 2} {g : Ω → B} (hJ : AEStronglyMeasurable J P)
    (hJ' : AEStronglyMeasurable J' P) (hg : AEStronglyMeasurable g P)
    (h1 : Integrable (fun ω => ‖J ω‖ * ‖g ω‖) P) (h2 : Integrable (fun ω => ‖J' ω‖ * ‖g ω‖) P)
    (h3 : Integrable (fun ω => ‖J ω - J' ω‖ * ‖g ω‖) P) :
    ‖bochTensor21 P J g - bochTensor21 P J' g‖ ≤ ∫ ω, ‖J ω - J' ω‖ * ‖g ω‖ ∂P := by
  rw [bochTensor21_sub_left hJ hJ' hg h1 h2]
  exact norm_bochTensor21_le (hJ.sub hJ') hg h3

/-- The combination `Sym(X - 3 E[D⊗Z⊗Z] + 3 E[J⊗Z])` for two sets of data with a common `Z`. -/
theorem comb_sub_le (X X' : TensorDual B 3) {D D' Z : Ω → B} {J J' : Ω → TensorDual B 2}
    (hD : AEStronglyMeasurable D P) (hD' : AEStronglyMeasurable D' P) (hZ : AEStronglyMeasurable Z P)
    (hJ : AEStronglyMeasurable J P) (hJ' : AEStronglyMeasurable J' P)
    (i1 : Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P)
    (i2 : Integrable (fun ω => ‖D' ω‖ * ‖Z ω‖ * ‖Z ω‖) P)
    (i3 : Integrable (fun ω => ‖D ω - D' ω‖ * ‖Z ω‖ * ‖Z ω‖) P)
    (j1 : Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P) (j2 : Integrable (fun ω => ‖J' ω‖ * ‖Z ω‖) P)
    (j3 : Integrable (fun ω => ‖J ω - J' ω‖ * ‖Z ω‖) P) :
    ‖symm3 B (X - (3 : ℝ) • bochTensor3 P D Z Z + (3 : ℝ) • bochTensor21 P J Z) -
        symm3 B (X' - (3 : ℝ) • bochTensor3 P D' Z Z + (3 : ℝ) • bochTensor21 P J' Z)‖ ≤
      ‖X - X'‖ + 3 * ∫ ω, ‖D ω - D' ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P + 3 * ∫ ω, ‖J ω - J' ω‖ * ‖Z ω‖ ∂P := by
  rw [← map_sub (symm3 B)]
  refine (HRS.MC.E213U11.u11_norm_symm3_apply_le _).trans ?_
  have e : X - (3 : ℝ) • bochTensor3 P D Z Z + (3 : ℝ) • bochTensor21 P J Z -
      (X' - (3 : ℝ) • bochTensor3 P D' Z Z + (3 : ℝ) • bochTensor21 P J' Z) =
      (X - X') - (3 : ℝ) • (bochTensor3 P D Z Z - bochTensor3 P D' Z Z) +
        (3 : ℝ) • (bochTensor21 P J Z - bochTensor21 P J' Z) := by
    ext M
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [e]
  have n3 := norm_bochTensor3_sub_left_le hD hD' hZ hZ i1 i2 i3
  have n21 := norm_bochTensor21_sub_left_le hJ hJ' hZ j1 j2 j3
  have s3 : ‖(3 : ℝ) • (bochTensor3 P D Z Z - bochTensor3 P D' Z Z)‖ ≤
      3 * ∫ ω, ‖D ω - D' ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P := by
    refine (ContinuousLinearMap.opNorm_smul_le (3 : ℝ) _).trans ?_
    rw [Real.norm_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left n3 (by norm_num)
  have s21 : ‖(3 : ℝ) • (bochTensor21 P J Z - bochTensor21 P J' Z)‖ ≤ 3 * ∫ ω, ‖J ω - J' ω‖ * ‖Z ω‖ ∂P := by
    refine (ContinuousLinearMap.opNorm_smul_le (3 : ℝ) _).trans ?_
    rw [Real.norm_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left n21 (by norm_num)
  set A : TensorDual B 3 := bochTensor3 P D Z Z - bochTensor3 P D' Z Z with hA
  set C : TensorDual B 3 := bochTensor21 P J Z - bochTensor21 P J' Z with hC
  calc ‖(X - X') - (3 : ℝ) • A + (3 : ℝ) • C‖
      ≤ ‖(X - X') - (3 : ℝ) • A‖ + ‖(3 : ℝ) • C‖ := norm_add_le ((X - X') - (3 : ℝ) • A) ((3 : ℝ) • C)
    _ ≤ (‖X - X'‖ + ‖(3 : ℝ) • A‖) + ‖(3 : ℝ) • C‖ := by gcongr; exact norm_sub_le (X - X') ((3 : ℝ) • A)
    _ ≤ (‖X - X'‖ + 3 * ∫ ω, ‖D ω - D' ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P) + 3 * ∫ ω, ‖J ω - J' ω‖ * ‖Z ω‖ ∂P := by
        gcongr
    _ = _ := by ring

end Generic

end HRS.MC.E214N

end
