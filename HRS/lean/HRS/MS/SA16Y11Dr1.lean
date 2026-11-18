import HRS.MS.SA16Y11Dr1a

/-!
# S.A.16 (SA16Y11) Dr1: the mean-field drift difference is bounded by the density difference (sharp, linear in `δ`)

`sa16y11_drift_diff`: for `D1, D2` with the same `s, M, V` and densities `ρ1, ρ2` (`C^{m+2}`, weights through order `1`, bounded by
any `W`), if `ρ1 - ρ2` has weights `δ` through order `m+2` then `‖D^j (b1 - b2) x‖ ≤ C δ` for `j ≤ m+1` (`b_a = meanFieldDriftW D_a ρ_a`),
`C = d²MB · d C₀`, independent of `W`, `δ`, `D_a`, `ρ_a`.  Only `m+2` derivatives of the difference are used (`sa16p_force_contDiff` at
`k = m+1`), matching `coeffNormE` at level `m+2`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16P
open HRS HRS.Whole HRS.Whole.AppendixA

section Dr1
variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 3200000 in
theorem sa16y11_drift_diff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) {MB : ℝ}
    (D1 D2 : WholeDyn d) (ρ1 ρ2 : 𝔼 → ℝ) (W δ : ℝ) (hs1 : D1.s = s) (hs2 : D2.s = s)
    (hM : D1.M = D2.M) (hV : D1.V = D2.V) (hMB : ∀ i j, |D1.M i j| ≤ MB)
    (hρ1 : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) ρ1) (hρ2 : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) ρ2)
    (hb1 : ∀ j ≤ 1, ∀ y, ‖iteratedFDeriv ℝ j ρ1 y‖ ≤ W * sa16p_w d y)
    (hb2 : ∀ j ≤ 1, ∀ y, ‖iteratedFDeriv ℝ j ρ2 y‖ ≤ W * sa16p_w d y)
    (hbd : ∀ j ≤ m + 2, ∀ y, ‖iteratedFDeriv ℝ j (fun y => ρ1 y - ρ2 y) y‖ ≤ δ * sa16p_w d y) :
    ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j (fun x => meanFieldDriftW D1 ρ1 x - meanFieldDriftW D2 ρ2 x) x‖ ≤
      ((d : ℝ) * d * MB) * ((d : ℝ) * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s * δ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMB0 : 0 ≤ MB := (abs_nonneg _).trans (hMB ⟨0, by omega⟩ ⟨0, by omega⟩)
  have hw0 : 0 < sa16p_w d (0 : 𝔼) := Real.rpow_pos_of_pos (by positivity) _
  have hW0 : 0 ≤ W := by
    have := hb1 0 (by norm_num) 0
    rw [norm_iteratedFDeriv_zero] at this
    nlinarith [norm_nonneg (ρ1 0)]
  have hρd1 : Differentiable ℝ ρ1 := hρ1.differentiable (by simp)
  have hρd2 : Differentiable ℝ ρ2 := hρ2.differentiable (by simp)
  have hw1 : ∀ y, ‖ρ1 y‖ ≤ W * sa16p_w d y := fun y => by simpa using hb1 0 (by norm_num) y
  have hw2 : ∀ y, ‖ρ2 y‖ ≤ W * sa16p_w d y := fun y => by simpa using hb2 0 (by norm_num) y
  have hf1 : ∀ y, ‖fderiv ℝ ρ1 y‖ ≤ W := fun y => by
    have := hb1 1 le_rfl y
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (mul_le_of_le_one_right hW0 (sa16p_w_le_one y))
  have hf2 : ∀ y, ‖fderiv ℝ ρ2 y‖ ≤ W := fun y => by
    have := hb2 1 le_rfl y
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (mul_le_of_le_one_right hW0 (sa16p_w_le_one y))
  have hconv := fun x => sa16y11_conv_sub hd hs0 hsd hρd1 hρd2 hw1 hw2 hf1 hf2 x
  have hρ : ContDiff ℝ ((m + 1 + 1 : ℕ) : WithTop ℕ∞) (fun y => ρ1 y - ρ2 y) := hρ1.sub hρ2
  obtain ⟨hfc, hfb⟩ := sa16p_force_contDiff hd hs0 hsd (m + 1) (ρ := fun y => ρ1 y - ρ2 y) (A := δ) hρ
    (fun j hj y => hbd j (by omega) y)
  let Lm : 𝔼 →L[ℝ] 𝔼 := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) D1.M
  have hLm : ∀ v, Torus.matVec D1.M v = Lm v := fun v =>
    (LinearMap.congr_fun (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin D1.M) v).symm
  have hLn : ‖Lm‖ ≤ (d : ℝ) * d * MB := ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (fun v => by rw [← hLm]; exact sa16p_matVec_norm_le hd D1.M hMB v)
  have hfun : (fun x => meanFieldDriftW D1 ρ1 x - meanFieldDriftW D2 ρ2 x) =
      fun x => Lm (convGradConvW (rieszKernelGrad d s) (fun y => ρ1 y - ρ2 y) x) := by
    funext x
    rw [hconv x]
    simp only [meanFieldDriftW, hs1, hs2, ← hM, ← hV, hLm, map_sub]
    abel
  intro j hj x
  rw [hfun]
  have hj2' : (j : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
  have h1 := Lm.norm_iteratedFDeriv_comp_left
    (f := convGradConvW (rieszKernelGrad d s) (fun y => ρ1 y - ρ2 y)) (x := x)
    ((hfc.of_le hj2').contDiffAt) le_rfl
  exact h1.trans (mul_le_mul hLn (hfb j hj x) (norm_nonneg _) (by positivity))

end Dr1

end HRS.Whole.AppendixA.Phase2SA16P

end
