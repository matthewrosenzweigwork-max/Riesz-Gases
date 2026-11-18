import HRS.MS.TransOpAux9

/-!
# S611 packet P2c: the dual operator `Λ_c` on `B_m = OscDual d m`

`s611_Lam m hm c : OscDual d m →L[ℝ] OscDual d m`, the dual of `φ ↦ φ(· + c)`: `eval (Λ_c u) φ = eval u φ(· + c)` for `φ ∈ Σ^m`
(`s611_eval_Lam`), `‖Λ_c‖ ≤ s611_K m c`, `Λ_c Λ_{c'} = Λ_{c+c'}`, `Λ_0 = id`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_O_ofFun' (m : ℕ) (hm : 1 ≤ m) (c : Euc d) {φ : Euc d → ℝ} (hφ : MemOsc (m : ℝ) φ) :
    s611_O m hm c (OscSpace.ofFun (m : ℝ) φ) = OscSpace.ofFun (m : ℝ) (fun x => φ (x + c)) :=
  s611_O_ofFun m hm c hφ (s611_memOsc_translate m hm c hφ).1

/-- The dual operator `Λ_c` of `φ ↦ φ(· + c)` on `B_m`. -/
def s611_LamLin (m : ℕ) (hm : 1 ≤ m) (c : Euc d) : OscDual d (m : ℝ) →ₗ[ℝ] OscDual d (m : ℝ) where
  toFun u := OscDual.toDual.symm ((OscDual.toDual u).comp (s611_O m hm c))
  map_add' u v := by
    rw [map_add, ContinuousLinearMap.add_comp, map_add]
  map_smul' a u := by
    rw [map_smul, ContinuousLinearMap.smul_comp, map_smul]
    rfl

theorem s611_norm_LamLin_le (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (u : OscDual d (m : ℝ)) :
    ‖s611_LamLin m hm c u‖ ≤ s611_K m c * ‖u‖ := by
  show ‖OscDual.toDual.symm ((OscDual.toDual u).comp (s611_O m hm c))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc ‖(OscDual.toDual u).comp (s611_O m hm c)‖ ≤ ‖OscDual.toDual u‖ * ‖s611_O m hm c‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖u‖ * s611_K m c := by
        rw [LinearIsometryEquiv.norm_map]
        exact mul_le_mul_of_nonneg_left (s611_norm_O_le m hm c) (norm_nonneg _)
    _ = s611_K m c * ‖u‖ := mul_comm _ _

/-- The translation operator `Λ_c` on `B_m` (`m ≥ 1`). -/
def s611_Lam (m : ℕ) (hm : 1 ≤ m) (c : Euc d) : OscDual d (m : ℝ) →L[ℝ] OscDual d (m : ℝ) :=
  LinearMap.mkContinuous (s611_LamLin m hm c) (s611_K m c) (s611_norm_LamLin_le m hm c)

theorem s611_norm_Lam_le (m : ℕ) (hm : 1 ≤ m) (c : Euc d) : ‖s611_Lam m hm c‖ ≤ s611_K m c :=
  LinearMap.mkContinuous_norm_le _ (s611_K_pos m c).le _

theorem s611_eval_Lam (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (u : OscDual d (m : ℝ)) {φ : Euc d → ℝ}
    (hφ : MemOsc (m : ℝ) φ) :
    OscDual.eval (s611_Lam m hm c u) φ = OscDual.eval u (fun x => φ (x + c)) := by
  have hφc := (s611_memOsc_translate m hm c hφ).1
  rw [← OscDual.toDual_ofFun _ φ hφ, ← OscDual.toDual_ofFun u _ hφc, ← s611_O_ofFun' m hm c hφ]
  show OscDual.toDual (OscDual.toDual.symm ((OscDual.toDual u).comp (s611_O m hm c)))
    (OscSpace.ofFun (m : ℝ) φ) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem s611_memOsc_herm (m : ℕ) (α : MultiIndex d) : MemOsc (m : ℝ) (hermiteFunD α) := by
  refine ⟨memLp_hermiteFunD α, ?_⟩
  refine summable_of_ne_finset_zero (s := {α}) fun β hβ => ?_
  have : hermiteCoeff (hermiteFunD α) β = 0 := by
    unfold hermiteCoeff
    rw [show (fun x => hermiteFunD α x * hermiteFunD β x) = fun x => hermiteFunD α x * hermiteFunD β x from rfl,
      hermiteFunD_orthonormal]
    have : α ≠ β := fun h => hβ (by simp [h])
    simp [this]
  rw [this]; simp

theorem s611_eval_herm (m : ℕ) (hm : 1 ≤ m) (v : OscDual d (m : ℝ)) (α : MultiIndex d) :
    OscDual.eval v (hermiteFunD α) = OscDual.hermiteCoeff v α := by
  unfold OscDual.eval
  rw [tsum_eq_single α]
  · have : hermiteCoeff (hermiteFunD α) α = 1 := by
      unfold hermiteCoeff
      rw [hermiteFunD_orthonormal]; simp
    rw [this, mul_one]
  · intro β hβ
    have : hermiteCoeff (hermiteFunD α) β = 0 := by
      unfold hermiteCoeff
      rw [hermiteFunD_orthonormal]
      simp [hβ.symm]
    rw [this, mul_zero]

theorem s611_hermiteCoeff_Lam (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (u : OscDual d (m : ℝ)) (α : MultiIndex d) :
    OscDual.hermiteCoeff (s611_Lam m hm c u) α = OscDual.eval u (fun x => hermiteFunD α (x + c)) := by
  rw [← s611_eval_herm m hm, s611_eval_Lam m hm c u (s611_memOsc_herm m α)]

theorem s611_Lam_add (m : ℕ) (hm : 1 ≤ m) (c c' : Euc d) (u : OscDual d (m : ℝ)) :
    s611_Lam m hm c (s611_Lam m hm c' u) = s611_Lam m hm (c' + c) u := by
  refine OscDual.ext_hermiteCoeff fun α => ?_
  rw [s611_hermiteCoeff_Lam, s611_hermiteCoeff_Lam]
  have h1 := s611_memOsc_translate m hm c (s611_memOsc_herm m α)
  rw [s611_eval_Lam m hm c' u h1.1]
  congr 1
  funext x
  simp only [add_assoc, add_comm c c']

theorem s611_Lam_zero (m : ℕ) (hm : 1 ≤ m) (u : OscDual d (m : ℝ)) :
    s611_Lam m hm (0 : Euc d) u = u := by
  refine OscDual.ext_hermiteCoeff fun α => ?_
  rw [s611_hermiteCoeff_Lam]
  simp only [add_zero]
  exact s611_eval_herm m hm u α

theorem s611_Lam_neg (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (u : OscDual d (m : ℝ)) :
    s611_Lam m hm (-c) (s611_Lam m hm c u) = u := by
  rw [s611_Lam_add, add_neg_cancel, s611_Lam_zero]

end HRS.MS.TransOp

end
