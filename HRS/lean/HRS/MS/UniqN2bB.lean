import HRS.MS.UniqN2bA
import HRS.MS.UniqE1b

/-!
# N2b of `UniqPlan.md`, part (b): the coefficient `a = ∂_jρ'` and local mass facts

* `n2b_rho_coeff`: for `ρ` with `CoeffHypRd` and `r ∈ [0,T]`, `a_j = ∂_jρ^r` is Lipschitz (constant `c1A d m Λ`) and
  satisfies `⟨y⟩^{d+3}|a_j(y)| ≤ c1A d m Λ`, together with the decay bounds of `ρ^r` and `∇ρ^r`.
* `n2b_ball_eLpNorm`: `LocMass A f` bounds `‖1_{B(c,r)} f‖₂ ≤ √N |A|`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN2b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs

variable {d : ℕ}

/-- A `C²` function with bounded Hessian has Lipschitz partial derivatives. -/
theorem n2b_lip_D1 {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) {B : ℝ}
    (hB : ∀ y, ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ B) (j : Fin d) :
    HRS.PDE.ToolboxRd.IsLipschitz B (D1 j u) := by
  intro x y
  have hB0 : 0 ≤ B := le_trans (ContinuousLinearMap.opNorm_nonneg _) (hB 0)
  have hd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdiff : ∀ z, DifferentiableAt ℝ (D1 j u) z := fun z => by
    unfold D1; exact (hd z).clm_apply (differentiableAt_const _)
  have hder : ∀ z, ‖fderiv ℝ (D1 j u) z‖ ≤ B := by
    intro z
    have h1 : fderiv ℝ (D1 j u) z =
        (fderiv ℝ (fderiv ℝ u) z).flip (EuclideanSpace.single j 1) := by
      unfold D1
      rw [fderiv_clm_apply (hd z) (differentiableAt_const _)]
      simp
    rw [h1]
    refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun w => ?_
    rw [ContinuousLinearMap.flip_apply]
    calc ‖fderiv ℝ (fderiv ℝ u) z w (EuclideanSpace.single j 1)‖
        ≤ ‖fderiv ℝ (fderiv ℝ u) z w‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ u) z‖ * ‖w‖) * 1 := by
          simp only [EuclideanSpace.norm_single, norm_one]
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * ‖w‖ := by
          rw [mul_one]; gcongr; exact hB z
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
    (fun z _ => hder z) (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

theorem n2b_jbracket_le (y : Euc d) : jbracket y ≤ 1 + ‖y‖ := by
  unfold jbracket
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg y]

open HRS.MP.RdGen in
/-- Second derivative decay of `ρ^r`. -/
theorem n2b_rho_decay2 (hd : 1 ≤ d) {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hcoef : CoeffHypRd s m Λ T ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (y : Euc d) :
    ‖fderiv ℝ (fderiv ℝ (ρ r)) y‖ ≤ HRS.MS.UniqC1.c1A d m Λ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := by
  have hcb := hcoef.regular.1 r hr
  have hcb0 : 0 ≤ HRS.cbNorm (m + 3) (ρ r) :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hΛ : (weightedSupE (m + 3) ((d : ℝ) + 3) (ρ r)).toReal ≤ max Λ 0 :=
    (by linarith [hcb.2.2, hcb0] : (weightedSupE (m + 3) ((d : ℝ) + 3) (ρ r)).toReal ≤ Λ).trans
      (le_max_left _ _)
  have key := HRS.MS.UniqE1.e1_rho_decay hd hcb.2.1 hΛ 2 (by omega) y
  have h1 : ‖fderiv ℝ (fderiv ℝ (ρ r)) y‖ = ‖iteratedFDeriv ℝ 2 (ρ r) y‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  rw [h1]
  exact key

theorem n2b_rho_coeff (hd : 1 ≤ d) {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hcoef : CoeffHypRd s m Λ T ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ContDiff ℝ 1 (ρ r) ∧ ContDiff ℝ 2 (ρ r) ∧
    (∀ y, |ρ r y| ≤ HRS.MS.UniqC1.c1A d m Λ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) ∧
    (∀ y, ‖fderiv ℝ (ρ r) y‖ ≤ HRS.MS.UniqC1.c1A d m Λ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) ∧
    (∀ j, HRS.PDE.ToolboxRd.IsLipschitz (HRS.MS.UniqC1.c1A d m Λ) (D1 j (ρ r))) ∧
    (∀ j y, jbracket y ^ ((d : ℝ) + 3) * |D1 j (ρ r) y| ≤ HRS.MS.UniqC1.c1A d m Λ) := by
  have hc2 : ContDiff ℝ 2 (ρ r) :=
    (hcoef.regular.1 r hr).1.1.of_le (by exact_mod_cast (by omega : 2 ≤ m + 3))
  obtain ⟨h0, h1⟩ := HRS.MS.UniqE1.e1_rho_decay01 hd hcoef hr
  set A : ℝ := HRS.MS.UniqC1.c1A d m Λ with hA
  have hA0 : 0 ≤ A := HRS.MS.UniqE1.e1_A_nonneg m Λ
  refine ⟨HRS.MS.UniqE1.e1_rho_smooth hcoef hr, hc2, h0, h1, ?_, ?_⟩
  · refine fun j => n2b_lip_D1 hc2 (B := A) (fun y => ?_) j
    refine (n2b_rho_decay2 hd hcoef hr y).trans ?_
    have : (1 + ‖y‖) ^ (-((d : ℝ) + 3)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)
    calc A * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) ≤ A * 1 := by gcongr
      _ = A := mul_one _
  · intro j y
    have hjb : 0 < jbracket y := by unfold jbracket; positivity
    have hpos : 0 < 1 + ‖y‖ := by positivity
    have e1 : jbracket y ^ ((d : ℝ) + 3) ≤ (1 + ‖y‖) ^ ((d : ℝ) + 3) :=
      Real.rpow_le_rpow hjb.le (n2b_jbracket_le y) (by positivity)
    have e2 : |D1 j (ρ r) y| ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := (n2b_D1_le j _ y).trans (h1 y)
    calc jbracket y ^ ((d : ℝ) + 3) * |D1 j (ρ r) y|
        ≤ (1 + ‖y‖) ^ ((d : ℝ) + 3) * (A * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) :=
          mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      _ = A := by
          rw [mul_left_comm, ← Real.rpow_add hpos]; simp

/-- Mass of `f` on a ball of radius `r`: `‖1_{B(c,r)} f‖₂ ≤ √N |A|`. -/
theorem n2b_ball_eLpNorm (d : ℕ) (r : ℝ) :
    ∃ N : ℕ, ∀ (A : ℝ) (f : Euc d → ℝ), LocMass A f → ∀ c : Euc d,
      eLpNorm ((ball c r).indicator f) 2 volume ≤ ENNReal.ofReal (Real.sqrt N * |A|) := by
  obtain ⟨N, hN⟩ := exists_ball_sq_bound d r
  refine ⟨N, fun A f hf c => ?_⟩
  have hind : AEStronglyMeasurable ((ball c r).indicator f) volume :=
    hf.1.indicator measurableSet_ball
  have hsq : eLpNorm ((ball c r).indicator f) 2 volume ^ 2 ≤
      ENNReal.ofReal (Real.sqrt N * |A|) ^ 2 := by
    rw [sq_eLpNorm_two hind]
    have hl : ∫⁻ y, ‖(ball c r).indicator f y‖ₑ ^ 2 = ∫⁻ y in ball c r, ‖f y‖ₑ ^ 2 := by
      rw [← lintegral_indicator measurableSet_ball]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ ball c r <;> simp [hy]
    rw [hl, ← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), sq_abs,
      ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
    exact hN A f hf c
  by_contra hlt
  exact absurd hsq (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hlt)))

end HRS.MS.UniqN2b
