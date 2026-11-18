import HRS.Energy.Modulated
import HRS.Torus.Sobolev
import HRS.Prob.Gaussian
import HRS.MC.E213TElem

/-!
# Proofs of three small lemmas of the small main rows (packet SM3)

Statements copied verbatim from `HRS/MC/SmallRowsSpec.lean` (sorried spec, not imported):
`cbNorm_max_bridge` (clause U4), `projTensor_pairing_le` and `norm_elemTensor_eq` (clause C8).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

set_option maxSynthPendingDepth 3

namespace HRS.MC.SmallRows

open HRS

/-- Abstract form of the bridge: for nonnegative terms the maximum over `Fin (k+1)` is at most the
sum over `range (k+1)`, which is at most `(k+1)` times the maximum. -/
theorem p_sm3_bridge_abstract (k : ℕ) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (⨆ j : Fin (k + 1), f j) ≤ ∑ j ∈ Finset.range (k + 1), f j ∧
      ∑ j ∈ Finset.range (k + 1), f j ≤ ((k : ℝ) + 1) * ⨆ j : Fin (k + 1), f j := by
  constructor
  · apply ciSup_le
    intro j
    exact Finset.single_le_sum (f := f) (fun i _ => hf i) (Finset.mem_range.2 j.isLt)
  · have hle : ∀ j ∈ Finset.range (k + 1), f j ≤ ⨆ i : Fin (k + 1), f i := by
      intro j hj
      exact le_ciSup (Set.finite_range fun i : Fin (k + 1) => f i).bddAbove ⟨j, Finset.mem_range.1 hj⟩
    have h := Finset.sum_le_card_nsmul (Finset.range (k + 1)) f _ hle
    rw [Finset.card_range, nsmul_eq_mul] at h
    push_cast at h
    exact h

/-- Clause U4 (TeX M L10064-10065): the printed max norm `M` and the Lean sum norm
`Torus.cbNorm k φ` satisfy `M ≤ cbNorm k φ ≤ (k+1) M`, with no boundedness hypothesis. -/
theorem cbNorm_max_bridge {d : ℕ} (k : ℕ) (φ : Torus d → ℝ) :
    (⨆ j : Fin (k + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ (j : ℕ) (Torus.lift φ) x‖) ≤
        Torus.cbNorm k φ ∧
      Torus.cbNorm k φ ≤
        ((k : ℝ) + 1) * ⨆ j : Fin (k + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ (j : ℕ) (Torus.lift φ) x‖ := by
  unfold Torus.cbNorm
  exact p_sm3_bridge_abstract k
    (fun j => ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖)
    (fun j => Real.iSup_nonneg fun x => norm_nonneg _)

/-- Clause C8 (TeX M L1267-1270): `|⟨M, u⟩| ≤ ‖u‖ ‖M‖` for `u ∈ projTensor B 3`. -/
theorem projTensor_pairing_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (u : projTensor B 3) (M : B [×3]→L[ℝ] ℝ) :
    |((u : TensorDual B 3)) M| ≤ ‖u‖ * ‖M‖ := by
  have h := (u : TensorDual B 3).le_opNorm M
  have hu : ‖(u : TensorDual B 3)‖ = ‖u‖ := rfl
  rw [hu, Real.norm_eq_abs] at h
  exact h

/-- Clause C8 (optional): `‖x₁ ⊗ x₂ ⊗ x₃‖ = ∏ ‖xᵢ‖` for elementary tensors. -/
theorem norm_elemTensor_eq {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (v : Fin 3 → B) :
    ‖(elemTensor v : TensorDual B 3)‖ = ∏ i, ‖v i‖ := by
  refine le_antisymm (HRS.MC.E213T.e213t_norm_elemTensor_le v) ?_
  choose g hg1 hgv using fun i : Fin 3 => exists_dual_vector'' ℝ (v i)
  have hex : ∃ M : B [×3]→L[ℝ] ℝ, M v = ∏ i, ‖v i‖ ∧ ‖M‖ ≤ 1 := by
    refine ⟨(ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ).compContinuousLinearMap
      (fun i => (g i : B →L[ℝ] ℝ)), ?_, ?_⟩
    · simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebraFin_apply, hgv, Fin.prod_univ_three, mul_assoc]
    · have hP : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ‖ ≤ 1 := by simp
      have hprod : ∏ i, ‖(g i : B →L[ℝ] ℝ)‖ ≤ 1 :=
        Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hg1 i)
      refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
      exact le_trans (mul_le_mul hP hprod (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one)
        (by norm_num)
  obtain ⟨M, hMv, hM1⟩ := hex
  have key := (elemTensor v : TensorDual B 3).le_opNorm M
  have hev : (elemTensor v : TensorDual B 3) M = M v := rfl
  rw [hev, hMv, Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)] at key
  have h2 : ‖(elemTensor v : TensorDual B 3)‖ * ‖M‖ ≤ ‖(elemTensor v : TensorDual B 3)‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hM1
  linarith

end HRS.MC.SmallRows
