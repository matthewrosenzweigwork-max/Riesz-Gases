import HRS.MS.S104eC0

/-!
# S104E route C, packet C1 (part C): raising the differentiability order through directional derivatives

`s104c1_dstep`: if every directional derivative `∂_v u` is `C^{j+1}` with `D^{j+1}` bounded by `K₁‖v‖` and
Lipschitz at scale `r` with constant `K₂‖v‖`, then `u` is `C^{j+2}` with `D^{j+2}u` bounded by `K₁` and Lipschitz at scale `r`
with constant `K₂`.
-/

noncomputable section
open MeasureTheory Filter Topology Set Fin
open scoped ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole
variable {d : ℕ}

theorem s104c1_diter {u : Euc d → ℝ} {j : ℕ} (hC : ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) u)
    (x : Euc d) (m : Fin (j + 2) → Euc d) :
    iteratedFDeriv ℝ (j + 2) u x m =
      iteratedFDeriv ℝ (j + 1) (fun y => fderiv ℝ u y (m (Fin.last (j + 1)))) x (Fin.init m) := by
  rw [iteratedFDeriv_succ_apply_right]
  have hd : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ u y) :=
    hC.fderiv_right (by push_cast; norm_cast)
  have := ContinuousLinearMap.iteratedFDeriv_comp_left
    (ContinuousLinearMap.apply ℝ ℝ (m (Fin.last (j + 1)))) (f := fun y => fderiv ℝ u y) (x := x)
    hd.contDiffAt (i := j + 1) le_rfl
  have e : (fun y => fderiv ℝ u y (m (Fin.last (j + 1)))) =
      (ContinuousLinearMap.apply ℝ ℝ (m (Fin.last (j + 1)))) ∘ (fun y => fderiv ℝ u y) := rfl
  rw [e, this]
  rfl

theorem s104c1_dstep {u : Euc d → ℝ} {j : ℕ} {K1 K2 r : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hu : Differentiable ℝ u)
    (hv : ∀ v : Euc d, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ u y v))
    (h1 : ∀ v x : Euc d, ‖iteratedFDeriv ℝ (j + 1) (fun y => fderiv ℝ u y v) x‖ ≤ K1 * ‖v‖)
    (h2 : ∀ v x x' : Euc d, ‖x' - x‖ ≤ r →
      ‖iteratedFDeriv ℝ (j + 1) (fun y => fderiv ℝ u y v) x' -
        iteratedFDeriv ℝ (j + 1) (fun y => fderiv ℝ u y v) x‖ ≤ K2 * ‖x' - x‖ * ‖v‖) :
    ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) u ∧ (∀ x, ‖iteratedFDeriv ℝ (j + 2) u x‖ ≤ K1) ∧
    ∀ x x' : Euc d, ‖x' - x‖ ≤ r →
      ‖iteratedFDeriv ℝ (j + 2) u x' - iteratedFDeriv ℝ (j + 2) u x‖ ≤ K2 * ‖x' - x‖ := by
  have hC : ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) u := by
    have := (contDiff_succ_iff_fderiv_apply (𝕜 := ℝ) (D := Euc d) (E := ℝ)
      (n := ((j + 1 : ℕ) : WithTop ℕ∞)) (f := u)).2
      ⟨hu, fun h => by simp at h, hv⟩
    exact_mod_cast this
  have hp : ∀ m : Fin (j + 2) → Euc d, ∏ i : Fin (j + 2), ‖m i‖ =
      (∏ i : Fin (j + 1), ‖Fin.init m i‖) * ‖m (Fin.last (j + 1))‖ := fun m => by
    rw [Fin.prod_univ_castSucc]; rfl
  refine ⟨hC, fun x => ?_, fun x x' hx => ?_⟩
  · refine ContinuousMultilinearMap.opNorm_le_bound hK1 fun m => ?_
    rw [s104c1_diter hC x m, hp m]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have := h1 (m (Fin.last (j + 1))) x
    calc _ ≤ (K1 * ‖m (Fin.last (j + 1))‖) * ∏ i : Fin (j + 1), ‖Fin.init m i‖ :=
          mul_le_mul_of_nonneg_right this (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = _ := by ring
  · refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
    rw [ContinuousMultilinearMap.sub_apply, s104c1_diter hC x m, s104c1_diter hC x' m,
      ← ContinuousMultilinearMap.sub_apply, hp m]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have := h2 (m (Fin.last (j + 1))) x x' hx
    calc _ ≤ (K2 * ‖x' - x‖ * ‖m (Fin.last (j + 1))‖) * ∏ i : Fin (j + 1), ‖Fin.init m i‖ :=
          mul_le_mul_of_nonneg_right this (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = _ := by ring

end HRS.MS.S104e.C
