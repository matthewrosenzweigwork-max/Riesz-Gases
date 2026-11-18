import HRS.MS.SA16Y10Fd1

/-!
# S.A.16 (SA16Y10) Fd2: the drift difference of two densities (same `M`, `V`, `s`), linear in the weighted size `δ` of
`ρ₁ - ρ₂` (stability G3(c))

`sa16y10_drift_diff`: each coordinate of `meanFieldDriftW D₁ ρ₁ - meanFieldDriftW D₂ ρ₂` is `C^{m+1}` with all derivatives
(orders `0 ≤ j ≤ m+1`; needs the weighted jets of `ρ₁ - ρ₂` up to order `m+2`) bounded by `K δ`, `K = d² MB · d · C₀`.
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter MeasureTheory

namespace HRS.Whole.AppendixA.Phase2SA16P
open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 6400000 in
theorem sa16y10_drift_diff (hd : 1 ≤ d) {s MB Λ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    {D₁ D₂ : WholeDyn d} (hD₁s : D₁.s = s) (hD₂s : D₂.s = s) (hM : ∀ i j, |D₁.M i j| ≤ MB)
    (hMeq : D₁.M = D₂.M) {ρ₁ ρ₂ : 𝔼 → ℝ} (hρ₁ : IsRegularDensityW (m + 3) Λ ρ₁)
    (hρ₂ : IsRegularDensityW (m + 3) Λ ρ₂) {δ : ℝ} (hVeq : D₁.V = D₂.V)
    (hdec : ∀ j ≤ m + 2, ∀ y, ‖iteratedFDeriv ℝ j (fun y => ρ₁ y - ρ₂ y) y‖ ≤ δ * sa16p_w d y) (i : Fin d) :
    ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => meanFieldDriftW D₁ ρ₁ x i - meanFieldDriftW D₂ ρ₂ x i) ∧
      ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j (fun x => meanFieldDriftW D₁ ρ₁ x i - meanFieldDriftW D₂ ρ₂ x i) x‖ ≤
        ((d : ℝ) * d * MB) * ((d : ℝ) * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s * δ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMB0 : 0 ≤ MB := (abs_nonneg _).trans (hM ⟨0, by omega⟩ ⟨0, by omega⟩)
  set A : ℝ := (d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2) with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hb : ∀ (ρ : 𝔼 → ℝ), IsRegularDensityW (m + 3) Λ ρ → ∀ j ≤ m + 3, ∀ y, ‖iteratedFDeriv ℝ j ρ y‖ ≤ A * sa16p_w d y := by
    intro ρ hρ j hj y
    refine (sa16p_regular_bounds hρ j hj y).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sa16p_w_pos y).le
    have : (d : ℝ) ^ j ≤ (d : ℝ) ^ (m + 3) := pow_le_pow_right₀ hd1 hj
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (le_max_right _ _)) (by positivity)
  have hc1 : ∀ ρ : 𝔼 → ℝ, IsRegularDensityW (m + 3) Λ ρ → ContDiff ℝ 1 ρ := fun ρ hρ =>
    hρ.1.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
  have hg : ∀ ρ : 𝔼 → ℝ, IsRegularDensityW (m + 3) Λ ρ → ∀ y, ‖fderiv ℝ ρ y‖ ≤ A := fun ρ hρ y => by
    rw [sa16p_norm_fderiv_eq]
    exact (hb ρ hρ 1 (by omega) y).trans (mul_le_of_le_one_right hAnn (sa16p_w_le_one y))
  have hw0 : ∀ ρ : 𝔼 → ℝ, IsRegularDensityW (m + 3) Λ ρ → ∀ y, ‖ρ y‖ ≤ A * sa16p_w d y := fun ρ hρ y => by
    simpa using hb ρ hρ 0 (by omega) y
  have hsub := sa16y10_force_sub hd hs0 hsd (hc1 ρ₁ hρ₁) (hc1 ρ₂ hρ₂) (hw0 ρ₁ hρ₁) (hw0 ρ₂ hρ₂) (hg ρ₁ hρ₁) (hg ρ₂ hρ₂)
  have hρd : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (fun y => ρ₁ y - ρ₂ y) :=
    (hρ₁.1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3))).sub (hρ₂.1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3)))
  obtain ⟨hfc, hfb⟩ := sa16p_force_contDiff hd hs0 hsd (m + 1) (ρ := fun y => ρ₁ y - ρ₂ y) (A := δ) hρd hdec
  let Lm : 𝔼 →L[ℝ] 𝔼 := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) D₁.M
  have hLm : ∀ v, Torus.matVec D₁.M v = Lm v := fun v =>
    (LinearMap.congr_fun (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin D₁.M) v).symm
  have hLn : ‖Lm‖ ≤ (d : ℝ) * d * MB := ContinuousLinearMap.opNorm_le_bound _
    (by positivity)
    (fun v => by rw [← hLm]; exact sa16p_matVec_norm_le hd D₁.M hM v)
  let P : 𝔼 →L[ℝ] ℝ := (EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).comp Lm
  have hPn : ‖P‖ ≤ (d : ℝ) * d * MB := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hp : ‖(EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
      simpa using PiLp.norm_apply_le v i
    calc ‖(EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ)‖ * ‖Lm‖ ≤ 1 * ((d : ℝ) * d * MB) :=
          mul_le_mul hp hLn (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  set F' := convGradConvW (rieszKernelGrad d s) (fun y => ρ₁ y - ρ₂ y) with hF'
  have hfun : (fun x => meanFieldDriftW D₁ ρ₁ x i - meanFieldDriftW D₂ ρ₂ x i) = fun x => P (F' x) := by
    funext x
    simp only [meanFieldDriftW, hD₁s, hD₂s, ← hMeq, ← hVeq, hLm]
    rw [hsub]
    simp [P, map_sub]
  rw [hfun]
  refine ⟨P.contDiff.comp hfc, fun j hj x => ?_⟩
  have hj' : (j : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
  have h1 := P.norm_iteratedFDeriv_comp_left (f := F') (x := x) ((hfc.of_le hj').contDiffAt) le_rfl
  refine h1.trans (mul_le_mul hPn (hfb j hj x) (norm_nonneg _) (by positivity))

end HRS.Whole.AppendixA.Phase2SA16P

end
