import HRS.MS.R26T8AP15k

/-!
# S8.2 T8A P15l: the local part `F + (L_x + L_y) R` of the defect
`r26t8a_Tloc nu alpha R F` is `(F + 2 nu ZZ R) + (nu/2) PP R + Σ_i ½(α_i(x)+α_i(y)) ∂_{X_i}R + Σ_i (α_i(x)-α_i(y)) ∂_{z_i}R`.
* `r26t8a_Tloc_conormal`: if `F + 2 nu ZZ R` vanishes on `0 < |x-y| < 1` (principal cancellation, P14b), `Tloc` is `Conormal k 1 (M+1) (σ-2)`;
* `r26t8a_Tloc_eq`: `F + (Lop R(.,y) + Lop R(x,.)) = Tloc` for `x ≠ y` when `R` is `C²` there and the drift has coordinates `α_i`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

def r26t8a_Tloc (ν : ℝ) (α : Fin d → Euc d → ℝ) (R F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  (F x y + 2 * ν * r26t8a_ZZ R x y) + ν / 2 * r26t8a_PP R x y +
    ∑ i : Fin d, (1 / 2 : ℝ) * ((α i x + α i y) * r26t8a_pdir (r26t8a_e d i, 0) R x y) +
    ∑ i : Fin d, (α i x - α i y) * r26t8a_pdir (0, r26t8a_e d i) R x y

theorem r26t8a_Tloc_eq (C : WholeCoeff d) (α : Fin d → Euc d → ℝ) (hb : ∀ i x, C.drift 0 x i = α i x)
    (R F : Euc d → Euc d → ℝ) (x y : Euc d)
    (hR : ContDiffAt ℝ 2 (fun q : Euc d × Euc d => R q.1 q.2) (x, y)) :
    F x y + (r26t8a_Lop C (fun w => R w y) x + r26t8a_Lop C (R x) y) = r26t8a_Tloc C.ν α R F x y := by
  have hlap := r26t8a_p15_lap_pdir hR
  have hdr := r26t8a_p15_drift_pdir (hR.differentiableAt (by norm_num)) (C.drift 0 x) (C.drift 0 y)
  unfold r26t8a_Lop r26t8a_Tloc
  have e1 : C.ν * Laplacian.laplacian (fun w => R w y) x + C.ν * Laplacian.laplacian (fun w => R x w) y =
      C.ν * (1 / 2 * r26t8a_PP R x y + 2 * r26t8a_ZZ R x y) := by rw [← hlap]; ring
  simp only [hb] at hdr
  have e2 : ∑ i : Fin d, (1 / 2 : ℝ) * (α i x + α i y) * r26t8a_pdir (r26t8a_e d i, 0) R x y =
      ∑ i : Fin d, (1 / 2 : ℝ) * ((α i x + α i y) * r26t8a_pdir (r26t8a_e d i, 0) R x y) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e2] at hdr
  linarith

theorem r26t8a_Tloc_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k : ℕ) (M σ ν B : ℝ) (hB : 0 ≤ B)
    (α : Fin d → Euc d → ℝ) (hα : ∀ i, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (α i))
    (hαb : ∀ i, ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (R F : Euc d → Euc d → ℝ) (AR AF : ℝ), 0 ≤ AR → 0 ≤ AF →
      Conormal (k + 2) 1 M (σ - 2) AR R → Conormal k 0 M σ AF F →
      (∀ x y : Euc d, x ≠ y → ‖x - y‖ < 1 → F x y + 2 * ν * r26t8a_ZZ R x y = 0) →
      Conormal k 1 (M + 1) (σ - 2) (c * (AR + AF)) (r26t8a_Tloc ν α R F) := by
  obtain ⟨c1, hc1, h1⟩ := r26t8a_ZZ_conormal hchi k 1 M (σ - 2) (2 * ν)
  obtain ⟨c2, hc2, h2⟩ := r26t8a_PP_conormal hchi k 1 M (σ - 2) (ν / 2)
  obtain ⟨c3, hc3, h3⟩ := r26t8a_Sdrift_conormal hchi k 1 M (σ - 2) B hB α hα hαb
  obtain ⟨c4, hc4, h4⟩ := r26t8a_Ddrift_conormal hchi k 1 M (σ - 2) B hB α hα hαb
  refine ⟨1 + c1 + c2 + c3 + c4, by positivity, fun R F AR AF hAR hAF hR hF hcan => ?_⟩
  have hZ := h1 R AR hAR hR
  have hP := h2 R AR hAR hR
  have hR1 : Conormal (k + 1) 1 M (σ - 2) AR R := r26t8a_conormal_mono (Nat.le_succ (k + 1)) hR
  have hS := h3 R AR hAR hR1
  have hD := h4 R AR hAR hR1
  have hF1 : Conormal k 1 M σ AF F := r26t8a_conormal_mono_b hAF (Nat.zero_le 1) hF
  have hZ' : Conormal k 1 M σ (c1 * AR) (fun x y => 2 * ν * r26t8a_ZZ R x y) :=
    r26t8a_conormal_mono_sA (by positivity) le_rfl (le_of_eq (by ring)) hZ
  have hE0 := r26t8a_conormal_add hchi hF1 hZ'
  have hE : Conormal k 1 M (σ - 2) (AF + c1 * AR) (fun x y => F x y + 2 * ν * r26t8a_ZZ R x y) :=
    r26t8a_conormal_far (by positivity) hE0 hcan
  have hE' := r26t8a_conormal_mono_M (by positivity) (by linarith : M ≤ M + 1) hE
  have hP' := r26t8a_conormal_mono_M (by positivity) (by linarith : M ≤ M + 1) hP
  have hsum := r26t8a_conormal_add hchi (r26t8a_conormal_add hchi (r26t8a_conormal_add hchi hE' hP') hS) hD
  refine r26t8a_conormal_mono_sA (by positivity) ?_ le_rfl hsum
  nlinarith [mul_nonneg hc1 hAR, mul_nonneg hc2 hAR, mul_nonneg hc3 hAR, mul_nonneg hc4 hAR]

end HRS.MS.R26T8A
