import HRS.Prob.Metrics

/-!
# EQ-INTERP packet, part 5: elementary facts on the `C_b²` unit ball and the composition estimate

* `cb_abs_le_one`, `cb_lipschitz`: `|Φ| ≤ 1` and `|Φ x - Φ y| ≤ ‖x - y‖` for `Φ` in the unit ball;
* `cb_comp`: if `‖A‖ ≤ Λ`, `Λ ≥ 1`, then `y ↦ Λ^{-2} Φ(A y)` is in the `C_b²` unit ball (TeX L4152-4154: composition with `P_R`
  maps the unit ball into a ball of radius `C R^{2(M-m)}`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInterp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem cb_norm_le_one {Φ : F → ℝ} (hΦ : Φ ∈ CbUnitBall F 2) {j : ℕ} (hj : j ≤ 2) (z : F) :
    ‖iteratedFDeriv ℝ j Φ z‖ ≤ 1 := by
  obtain ⟨-, hb, hc⟩ := hΦ
  have h1 : ‖iteratedFDeriv ℝ j Φ z‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ :=
    le_ciSup (hb j hj) z
  have h2 : (⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) ≤ cbNorm 2 Φ := by
    unfold cbNorm
    refine Finset.single_le_sum (f := fun j => ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖)
      (fun i _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))
  linarith

theorem cb_abs_le_one {Φ : F → ℝ} (hΦ : Φ ∈ CbUnitBall F 2) (z : F) : |Φ z| ≤ 1 := by
  have := cb_norm_le_one hΦ (j := 0) (by norm_num) z
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

theorem cb_lipschitz {Φ : F → ℝ} (hΦ : Φ ∈ CbUnitBall F 2) (x y : F) : |Φ x - Φ y| ≤ ‖x - y‖ := by
  have hd : ContDiff ℝ 2 Φ := hΦ.1
  have hdiff : ∀ z, DifferentiableAt ℝ Φ z := fun z =>
    (hd.differentiable (by norm_num)) z
  have := (convex_univ (𝕜 := ℝ) (E := F)).norm_image_sub_le_of_norm_fderiv_le (f := Φ) (C := 1)
    (fun z _ => hdiff z) (fun z _ => by
      have := cb_norm_le_one hΦ (j := 1) (by norm_num) z
      rwa [norm_iteratedFDeriv_one] at this) (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

theorem cb_comp (A : E →L[ℝ] F) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hA : ‖A‖ ≤ Λ) {Φ : F → ℝ}
    (hΦ : Φ ∈ CbUnitBall F 2) : (fun y : E => (Λ ^ 2)⁻¹ * Φ (A y)) ∈ CbUnitBall E 2 := by
  have hΛ0 : 0 < Λ := by linarith
  set c : ℝ := (Λ ^ 2)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hcΛ : c * Λ ^ 2 = 1 := by rw [hc]; field_simp
  have hΦ' := hΦ
  obtain ⟨hΦd, hΦb, hΦn⟩ := hΦ
  have hg : ContDiff ℝ 2 (Φ ∘ A) := hΦd.comp A.contDiff
  have hΨ : (fun y : E => c * Φ (A y)) = fun y => c • (Φ ∘ A) y := by
    funext y; simp [smul_eq_mul]
  set s : ℕ → ℝ := fun j => ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ with hs
  have hs0 : ∀ j, 0 ≤ s j := fun j => Real.iSup_nonneg fun z => norm_nonneg _
  have hΛj : ∀ j ≤ 2, Λ ^ j ≤ Λ ^ 2 := fun j hj => pow_le_pow_right₀ hΛ hj
  -- pointwise derivative bound
  have hder : ∀ j ≤ 2, ∀ y : E,
      ‖iteratedFDeriv ℝ j (fun y : E => c * Φ (A y)) y‖ ≤ c * (s j * Λ ^ j) := by
    intro j hj y
    rw [hΨ, iteratedFDeriv_const_smul_apply' ((hg.of_le (by exact_mod_cast hj)).contDiffAt),
      norm_smul, Real.norm_of_nonneg hc0.le]
    have h1 : iteratedFDeriv ℝ j (Φ ∘ A) y =
        (iteratedFDeriv ℝ j Φ (A y)).compContinuousLinearMap fun _ => A :=
      A.iteratedFDeriv_comp_right hΦd y (by exact_mod_cast hj)
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ hc0.le
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h2 : ‖iteratedFDeriv ℝ j Φ (A y)‖ ≤ s j := le_ciSup (hΦb j hj) (A y)
    have h3 : ‖A‖ ^ j ≤ Λ ^ j := pow_le_pow_left₀ (norm_nonneg A) hA j
    exact mul_le_mul h2 h3 (by positivity) (hs0 j)
  have hbd : ∀ j ≤ 2, BddAbove (Set.range fun y : E => ‖iteratedFDeriv ℝ j (fun y : E => c * Φ (A y)) y‖) :=
    fun j hj => ⟨c * (s j * Λ ^ j), by rintro _ ⟨y, rfl⟩; exact hder j hj y⟩
  have hsup : ∀ j ≤ 2, (⨆ y : E, ‖iteratedFDeriv ℝ j (fun y : E => c * Φ (A y)) y‖) ≤ s j := by
    intro j hj
    refine ciSup_le fun y => (hder j hj y).trans ?_
    calc c * (s j * Λ ^ j) ≤ c * (s j * Λ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hΛj j hj) (hs0 j)) hc0.le
      _ = s j := by rw [mul_left_comm, hcΛ, mul_one]
  refine ⟨(hΨ ▸ (hg.const_smul c)), hbd, ?_⟩
  unfold cbNorm
  calc ∑ j ∈ Finset.range 3, ⨆ y : E, ‖iteratedFDeriv ℝ j (fun y : E => c * Φ (A y)) y‖
      ≤ ∑ j ∈ Finset.range 3, s j :=
        Finset.sum_le_sum fun j hj => hsup j (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj)
    _ ≤ 1 := hΦn

end HRS.MD.EQInterp
