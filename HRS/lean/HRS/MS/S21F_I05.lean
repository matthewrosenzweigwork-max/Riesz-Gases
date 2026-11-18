import HRS.MS.S21F_I02
import HRS.MC.E213O1

/-!
# S21F, packet R26-T3.I05: push the static `C_b^5` test class through a bounded synthesis

`Φ ∈ C_b^5(B)`, `S : ℓ² →L B`: `Φ ∘ S` has `‖D^j(Φ∘S)‖ ≤ ‖S‖^j ‖D^jΦ‖` (`compContinuousLinearMap` norm bound), so `A⁻¹ (Φ∘S)` lies in the
unit ball for `A = 1 + ‖S‖^5`; the third derivative of `Φ ∘ S` is `D³Φ(S ·) ∘ (S,S,S)`, i.e. the generic tensor push-forward identity.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem r26t3_push_static {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (S : SeqL2 →L[ℝ] B) (G : Measure SeqL2) (K : projTensor SeqL2 3)
    (Φ : B → ℝ) (hΦ : Φ ∈ CbUnitBall B 5) :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 + ‖S‖ ^ 5 + ‖S‖ ^ 3 ∧
      (fun z => A⁻¹ * Φ (S z)) ∈ CbUnitBall SeqL2 5 ∧
      ∀ z, (HRS.MC.E213O.tensorPow' 3 S (K : TensorDual SeqL2 3))
        (iteratedFDeriv ℝ 3 Φ (S z)) = (K : TensorDual SeqL2 3)
          (iteratedFDeriv ℝ 3 (fun y => Φ (S y)) z) := by
  have _ := G
  obtain ⟨hC, hbdd, hcb⟩ := hΦ
  set A : ℝ := 1 + ‖S‖ ^ 5 with hA
  have hS0 : 0 ≤ ‖S‖ := norm_nonneg _
  have hApos : 0 < A := by positivity
  have hjA : ∀ j : ℕ, j ≤ 5 → ‖S‖ ^ j ≤ A := fun j hj => by
    rcases le_total ‖S‖ 1 with h | h
    · have := pow_le_one₀ hS0 h (n := j); rw [hA]; have : 0 ≤ ‖S‖ ^ 5 := by positivity
      linarith
    · have := pow_le_pow_right₀ h hj; rw [hA]; linarith
  have hm : ∀ j : ℕ, j ≤ 5 → 0 ≤ ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ := fun j _ =>
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hm1 : ∀ j : ℕ, j ≤ 5 → ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ ≤ 1 := fun j hj => by
    have hle : ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ ≤
        ∑ i ∈ Finset.range 6, ⨆ z : B, ‖iteratedFDeriv ℝ i Φ z‖ :=
      Finset.single_le_sum (f := fun i => ⨆ z : B, ‖iteratedFDeriv ℝ i Φ z‖)
        (fun i hi => hm i (by have := Finset.mem_range.1 hi; omega)) (Finset.mem_range.2 (by omega))
    exact hle.trans hcb
  have hle_sup : ∀ j : ℕ, j ≤ 5 → ∀ w : B, ‖iteratedFDeriv ℝ j Φ w‖ ≤ ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ :=
    fun j hj w => le_ciSup (hbdd j hj) w
  have hcomp : ∀ j : ℕ, j ≤ 5 → ∀ z : SeqL2,
      iteratedFDeriv ℝ j (fun y => Φ (S y)) z = (iteratedFDeriv ℝ j Φ (S z)).compContinuousLinearMap fun _ => S :=
    fun j hj z => S.iteratedFDeriv_comp_right (hC.of_le (by exact_mod_cast le_refl _)) z (by exact_mod_cast hj)
  have hnorm : ∀ j : ℕ, j ≤ 5 → ∀ z : SeqL2,
      ‖iteratedFDeriv ℝ j (fun y => Φ (S y)) z‖ ≤ ‖iteratedFDeriv ℝ j Φ (S z)‖ * ‖S‖ ^ j := fun j hj z => by
    rw [hcomp j hj z]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const]
  have hcd : ContDiff ℝ 5 (fun y => Φ (S y)) := hC.comp S.contDiff
  have hgd : ∀ j : ℕ, j ≤ 5 → ∀ z : SeqL2, iteratedFDeriv ℝ j (fun y => A⁻¹ * Φ (S y)) z =
      A⁻¹ • iteratedFDeriv ℝ j (fun y => Φ (S y)) z := fun j hj z => by
    have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := A⁻¹) (f := fun y => Φ (S y)) (i := j) (x := z)
      (hcd.contDiffAt.of_le (by exact_mod_cast hj))
    simpa [smul_eq_mul] using this
  have hgb : ∀ j : ℕ, j ≤ 5 → ∀ z : SeqL2,
      ‖iteratedFDeriv ℝ j (fun y => A⁻¹ * Φ (S y)) z‖ ≤
        A⁻¹ * (‖S‖ ^ j * ⨆ w : B, ‖iteratedFDeriv ℝ j Φ w‖) := fun j hj z => by
    rw [hgd j hj z, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hApos.le)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hApos.le)
    calc ‖iteratedFDeriv ℝ j (fun y => Φ (S y)) z‖ ≤ ‖iteratedFDeriv ℝ j Φ (S z)‖ * ‖S‖ ^ j := hnorm j hj z
      _ ≤ (⨆ w : B, ‖iteratedFDeriv ℝ j Φ w‖) * ‖S‖ ^ j :=
          mul_le_mul_of_nonneg_right (hle_sup j hj _) (by positivity)
      _ = _ := mul_comm _ _
  refine ⟨A, hApos, by have : 0 ≤ ‖S‖ ^ 3 := by positivity
                       rw [hA]; linarith, ⟨contDiff_const.mul hcd, fun j hj => ?_, ?_⟩, fun z => ?_⟩
  · refine ⟨A⁻¹ * (‖S‖ ^ j * ⨆ w : B, ‖iteratedFDeriv ℝ j Φ w‖), ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hgb j hj z
  · unfold cbNorm
    calc ∑ j ∈ Finset.range (5 + 1), ⨆ z : SeqL2, ‖iteratedFDeriv ℝ j (fun y => A⁻¹ * Φ (S y)) z‖
        ≤ ∑ j ∈ Finset.range (5 + 1), ⨆ w : B, ‖iteratedFDeriv ℝ j Φ w‖ := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj5 : j ≤ 5 := by have := Finset.mem_range.1 hj; omega
          refine ciSup_le fun z => (hgb j hj5 z).trans ?_
          have hmj := hm j hj5
          have h1 : A⁻¹ * ‖S‖ ^ j ≤ 1 := by
            rw [inv_mul_le_iff₀ hApos]; simpa using hjA j hj5
          calc A⁻¹ * (‖S‖ ^ j * ⨆ w : B, ‖iteratedFDeriv ℝ j Φ w‖)
              = (A⁻¹ * ‖S‖ ^ j) * ⨆ w : B, ‖iteratedFDeriv ℝ j Φ w‖ := by ring
            _ ≤ 1 * ⨆ w : B, ‖iteratedFDeriv ℝ j Φ w‖ := mul_le_mul_of_nonneg_right h1 hmj
            _ = _ := one_mul _
      _ ≤ 1 := hcb
  · rw [HRS.MC.E213O.tensorPow'_apply, hcomp 3 (by norm_num) z]

end HRS.MS.R26T3
