import HRS.MH.PairingRdDefs
import HRS.MH.DualityRdB1Aux
import HRS.MH.DualityRdC1a

/-!
# PairingRd packets PR1, PR2, PR3 (Hölder data and `C_b²` components on `ℝ^d`)

Statements copied verbatim from `HRS/MH/PairingRdSpec.lean`; the spec file is imported only for its vocabulary.
Proofs use the `db1_*` / `dc1a_*` helpers (`HRS/MH/DualityRdB1Aux.lean`, `HRS/MH/DualityRdC1a.lean`) and the
torus templates `holder_abs_le`, `holder_mul_kern`, `vcomp_lip` of `HRS/Duality/PairingExpansion.lean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- Real form of the Hölder condition on `ℝ^d` (port of `HRS.Duality.holder_abs_le`). -/
theorem holder_abs_le_euc {ρ : Euc d → ℝ} {C α : NNReal} (hH : HolderWith C α ρ) (x y : Euc d) :
    |ρ x - ρ y| ≤ (C : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
  have h := hH x y
  rw [edist_dist, edist_dist, Real.dist_eq, dist_eq_norm x y] at h
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (x - y)) (NNReal.coe_nonneg α),
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- **PR1** `holder_near_rd` (proof). -/
theorem holder_near_rd {ρ : Euc d → ℝ} {C α : NNReal} (hα0 : 0 < (α : ℝ)) (hH : HolderWith C α ρ) :
    Continuous ρ ∧ ∀ x z : Euc d, ‖z‖ ≤ 1 / 4 → |ρ (x - z) - ρ x| ≤ (C : ℝ) * ‖z‖ ^ (α : ℝ) := by
  refine ⟨hH.continuous hα0, fun x z _ => ?_⟩
  have h := holder_abs_le_euc hH (x - z) x
  rw [sub_sub_cancel_left, norm_neg] at h
  exact h

/-- **PR2** `holder_mul_near_rd` (proof). -/
theorem holder_mul_near_rd {ρ v : Euc d → ℝ} {Cρ β Lv Bρ Bv : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hCρ : 0 ≤ Cρ) (hLv : 0 ≤ Lv)
    (hBρ : ∀ x, |ρ x| ≤ Bρ) (hBv : ∀ x, |v x| ≤ Bv)
    (hρH : ∀ x z : Euc d, ‖z‖ ≤ 1 / 4 → |ρ (x - z) - ρ x| ≤ Cρ * ‖z‖ ^ β)
    (hvL : ∀ x y : Euc d, |v x - v y| ≤ Lv * ‖x - y‖) (x z : Euc d) (hz : ‖z‖ ≤ 1 / 4) :
    |ρ (x - z) * v (x - z) - ρ x * v x| ≤ (Cρ * Bv + Bρ * Lv) * ‖z‖ ^ β := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hz1 : ‖z‖ ≤ 1 := hz.trans (by norm_num)
  have hzβ : ‖z‖ ≤ ‖z‖ ^ β := by
    have h := Real.rpow_le_rpow_of_exponent_ge' hz0 hz1 hβ0 hβ1
    rwa [Real.rpow_one] at h
  have hBρ0 : 0 ≤ Bρ := (abs_nonneg _).trans (hBρ 0)
  have e : ρ (x - z) * v (x - z) - ρ x * v x
      = (ρ (x - z) - ρ x) * v (x - z) + ρ x * (v (x - z) - v x) := by ring
  have h1 : |(ρ (x - z) - ρ x) * v (x - z)| ≤ Cρ * ‖z‖ ^ β * Bv := by
    rw [abs_mul]
    exact mul_le_mul (hρH x z hz) (hBv _) (abs_nonneg _) (mul_nonneg hCρ (Real.rpow_nonneg hz0 _))
  have h2 : |ρ x * (v (x - z) - v x)| ≤ Bρ * (Lv * ‖z‖) := by
    rw [abs_mul]
    have h := hvL (x - z) x
    rw [sub_sub_cancel_left, norm_neg] at h
    exact mul_le_mul (hBρ x) h (abs_nonneg _) hBρ0
  rw [e]
  calc |(ρ (x - z) - ρ x) * v (x - z) + ρ x * (v (x - z) - v x)|
      ≤ |(ρ (x - z) - ρ x) * v (x - z)| + |ρ x * (v (x - z) - v x)| := abs_add_le _ _
    _ ≤ Cρ * ‖z‖ ^ β * Bv + Bρ * (Lv * ‖z‖) := add_le_add h1 h2
    _ ≤ (Cρ * Bv + Bρ * Lv) * ‖z‖ ^ β := by
        nlinarith [mul_le_mul_of_nonneg_left hzβ (mul_nonneg hBρ0 hLv)]

/-- **PR3** `vcomp_facts_rd` (proof). -/
theorem vcomp_facts_rd (M : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} (hf : MemCb 2 f) (a : Fin d) :
    ∃ Bv Lv : ℝ, 0 ≤ Bv ∧ 0 ≤ Lv ∧ Continuous (fun y => Torus.matVec M.transpose (gradient f y) a) ∧
      (∀ y, |Torus.matVec M.transpose (gradient f y) a| ≤ Bv) ∧
      (∀ x y : Euc d, |Torus.matVec M.transpose (gradient f x) a - Torus.matVec M.transpose (gradient f y) a|
        ≤ Lv * ‖x - y‖) := by
  obtain ⟨CM, hCM0, hCM⟩ := HRS.MH.DualityRd.db1_matVec_bound M.transpose
  obtain ⟨A, hA0, hA⟩ := HRS.MH.DualityRd.db1_grad_bound hf
  obtain ⟨L, hL0, hL⟩ := HRS.MH.DualityRd.db1_grad_lip hf
  have hcomp : ∀ v : Euc d, |Torus.matVec M.transpose v a| ≤ CM * ‖v‖ := fun v => by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ a).trans (hCM v)
  have hLip : ∀ x y : Euc d,
      |Torus.matVec M.transpose (gradient f x) a - Torus.matVec M.transpose (gradient f y) a|
        ≤ (CM * L) * ‖x - y‖ := fun x y => by
    have e : Torus.matVec M.transpose (gradient f x) a - Torus.matVec M.transpose (gradient f y) a
        = Torus.matVec M.transpose (gradient f x - gradient f y) a := by
      rw [HRS.MH.DualityRd.dc1a_matVec_sub]; rfl
    rw [e]
    refine (hcomp _).trans ?_
    calc CM * ‖gradient f x - gradient f y‖ ≤ CM * (L * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (hL x y) hCM0
      _ = CM * L * ‖x - y‖ := by ring
  refine ⟨CM * A, CM * L, mul_nonneg hCM0 hA0, mul_nonneg hCM0 hL0, ?_, fun y => ?_, hLip⟩
  · have hK : LipschitzWith (Real.toNNReal (CM * L))
        (fun y => Torus.matVec M.transpose (gradient f y) a) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hCM0 hL0)]
      exact hLip x y
    exact hK.continuous
  · exact (hcomp _).trans (mul_le_mul_of_nonneg_left (hA y) hCM0)

end HRS.MH.PairingRdP
