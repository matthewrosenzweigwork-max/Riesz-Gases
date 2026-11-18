import HRS.Sections.QuenchAux26
import HRS.Sections.QuenchAux18

/-!
# Packet QUENCH (Q27), part 27: test forms `ℓ_j ⊗ ℓ_j` and summability of the mode tensors
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ} {m T : ℝ}

/-- The `j`-th weighted coordinate as a continuous linear functional on `E_m`. -/
def coordCLM (m : ℝ) (j : NonzeroLattice d) : NegSobolev d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => NegSobolev.coord F j
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl } 1 (fun F => by
      show ‖NegSobolev.coord F j‖ ≤ 1 * ‖F‖
      rw [Real.norm_eq_abs, one_mul]; exact abs_coord_le F j)

lemma coordCLM_apply (j : NonzeroLattice d) (F : NegSobolev d m) : coordCLM m j F = NegSobolev.coord F j := rfl

/-- The coordinate `j` of the time-zero value of a path. -/
def ell (hT : 0 < T) (j : NonzeroLattice d) : PathSpace d m T →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun w => NegSobolev.coord (w.at' ⟨0, le_rfl, hT.le⟩) j
      map_add' := fun w w' => rfl
      map_smul' := fun c w => rfl } 1 (fun w => by
        have h1 := abs_coord_le (w.at' ⟨0, le_rfl, hT.le⟩) j
        have h2 : ‖w.at' ⟨0, le_rfl, hT.le⟩‖ ≤ ‖w‖ :=
          ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) ⟨0, le_rfl, hT.le⟩
        show ‖NegSobolev.coord (w.at' ⟨0, le_rfl, hT.le⟩) j‖ ≤ 1 * ‖w‖
        rw [Real.norm_eq_abs, one_mul]; exact h1.trans h2)

lemma ell_apply (hT : 0 < T) (j : NonzeroLattice d) (w : PathSpace d m T) :
    ell hT j w = NegSobolev.coord (w.at' ⟨0, le_rfl, hT.le⟩) j := rfl

lemma norm_ell_le (hT : 0 < T) (j : NonzeroLattice d) : ‖(ell hT j : PathSpace d m T →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [ell_apply, Real.norm_eq_abs, one_mul]
  have h1 := abs_coord_le (w.at' ⟨0, le_rfl, hT.le⟩) j
  have h2 : ‖w.at' ⟨0, le_rfl, hT.le⟩‖ ≤ ‖w‖ :=
    ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) ⟨0, le_rfl, hT.le⟩
  exact h1.trans h2

/-- The product form `(x,y) ↦ ℓ x ℓ y`. -/
def M0of (ℓ : PathSpace d m T →L[ℝ] ℝ) : PathSpace d m T [×2]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 2 ℝ).compContinuousLinearMap (fun _ => ℓ)

lemma M0of_apply (ℓ : PathSpace d m T →L[ℝ] ℝ) (x y : PathSpace d m T) : M0of ℓ ![x, y] = ℓ x * ℓ y := by
  simp [M0of, ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ]

lemma norm_M0of (ℓ : PathSpace d m T →L[ℝ] ℝ) (h : ‖ℓ‖ ≤ 1) : ‖M0of ℓ‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v => ?_
  have e : M0of ℓ v = ℓ (v 0) * ℓ (v 1) := by
    have := M0of_apply ℓ (v 0) (v 1)
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv]; simpa using this
  rw [e, Fin.prod_univ_two, Real.norm_eq_abs, abs_mul, one_mul]
  have hb : ∀ x, |ℓ x| ≤ ‖x‖ := fun x =>
    (ℓ.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right h (norm_nonneg x))
  exact mul_le_mul (hb _) (hb _) (abs_nonneg _) (norm_nonneg _)

variable {s β : ℝ}

lemma ell_mp (hT : 0 < T) (j0 : NonzeroLattice d) (k : PosHalf d) (b : Bool) :
    ell hT j0 (modePath m T (lamMode d s β k.1) (modeFn k.1 b)) =
      sgn b * Lattice.jp k.1 ^ (-m) * (if j0 = idx k b then 1 else 0) := by
  rw [modePath_eq (T := T) (s := s) (β := β) k b _ rfl, ell_apply]
  show NegSobolev.coord ((sgn b * Lattice.jp k.1 ^ (-m)) •
    ((pathOf (m := m) (fexp (lamMode d s β k.1) T) (idx k b) : PathSpace d m T).at' ⟨0, le_rfl, hT.le⟩)) j0 = _
  rw [show (pathOf (m := m) (fexp (lamMode d s β k.1) T) (idx k b) : PathSpace d m T).at' ⟨0, le_rfl, hT.le⟩ =
    fexp (lamMode d s β k.1) T ⟨0, le_rfl, hT.le⟩ • esingle m (idx k b) from rfl, smul_smul, coord_smul_esingle,
    fexp_apply]
  simp

end Qch

end HRS
