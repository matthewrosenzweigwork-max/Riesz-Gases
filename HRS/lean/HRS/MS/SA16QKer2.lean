import HRS.MS.SA16QKer1

/-!
# S.A.16 (SA16Q), E6 part 2: the smoothed Riesz kernels and their derivatives

`γ_s = s` (`s > 0`), `1` (`s = 0`).  `Φ_s(t) = t^{-s/2}` (`s ≠ 0`), `-(log t)/2` (`s = 0`), so that
`rieszKernel d s y = Φ_s (‖y‖²)` and `Φ_s'(t) = -(γ_s/2) t^{-(s/2)-1}`.  For `ε ≥ 0`:

* `sa16q_gE s ε y = Φ_s (‖y‖² + ε²)`,
* `sa16q_K1E s ε i y = -γ_s y_i (‖y‖²+ε²)^{-(s/2)-1}`  (`= ∂_i gE`),
* `sa16q_K2E s ε i j y = -γ_s δ_{ij} (‖y‖²+ε²)^{-(s/2)-1} + γ_s (s+2) y_i y_j (‖y‖²+ε²)^{-(s/2)-2}`
  (`= ∂_j K1E_i`).

`ε = 0` gives the kernels `g`, `∂_i g`, `∂_i ∂_j g` away from the origin.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

section Kern
variable {d : ℕ}

def sa16q_gam (s : ℝ) : ℝ := if s = 0 then 1 else s

lemma sa16q_gam_pos {s : ℝ} (hs : 0 ≤ s) : 0 < sa16q_gam s := by
  unfold sa16q_gam
  split_ifs with h
  · exact one_pos
  · exact lt_of_le_of_ne hs (Ne.symm h)

def sa16q_Phi (s t : ℝ) : ℝ := if s = 0 then -(Real.log t) / 2 else t ^ (-s / 2)

lemma sa16q_rk_eq (d : ℕ) (s : ℝ) (y : Euc d) : rieszKernel d s y = sa16q_Phi s (‖y‖ ^ 2) := by
  unfold rieszKernel sa16q_Phi
  split_ifs with h
  · rw [Real.log_pow]; push_cast; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
    congr 1; push_cast; ring

lemma sa16q_Phi_deriv {s t : ℝ} (ht : 0 < t) :
    HasDerivAt (sa16q_Phi s) (-(sa16q_gam s / 2) * t ^ (-(s / 2) - 1)) t := by
  by_cases hs : s = 0
  · have h1 : sa16q_Phi s = fun t => -(Real.log t) / 2 := by
      funext t; simp [sa16q_Phi, hs]
    rw [h1]
    have h2 := ((Real.hasDerivAt_log ht.ne').neg).div_const 2
    convert h2 using 1
    simp [sa16q_gam, hs, Real.rpow_neg_one] <;> ring
  · have h1 : sa16q_Phi s = fun t => t ^ (-s / 2) := by
      funext t; simp [sa16q_Phi, hs]
    rw [h1]
    have h2 := Real.hasDerivAt_rpow_const (x := t) (p := -s / 2) (Or.inl ht.ne')
    convert h2 using 1
    rw [show sa16q_gam s = s from by simp [sa16q_gam, hs]]
    have e : -(s / 2) - 1 = -s / 2 - 1 := by ring
    rw [e]; ring

lemma sa16q_Phi_cont {s t : ℝ} (ht : 0 < t) : ContinuousAt (sa16q_Phi s) t :=
  (sa16q_Phi_deriv (s := s) ht).continuousAt

def sa16q_gE (s ε : ℝ) (y : Euc d) : ℝ := sa16q_Phi s (‖y‖ ^ 2 + ε ^ 2)

def sa16q_K1E (s ε : ℝ) (i : Fin d) (y : Euc d) : ℝ :=
  -(sa16q_gam s) * y i * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1)

def sa16q_K2E (s ε : ℝ) (i j : Fin d) (y : Euc d) : ℝ :=
  -(sa16q_gam s) * (if i = j then 1 else 0) * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1) +
    sa16q_gam s * (s + 2) * y i * y j * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 2)

lemma sa16q_gE_zero (s : ℝ) (y : Euc d) : sa16q_gE s 0 y = rieszKernel d s y := by
  simp [sa16q_gE, sa16q_rk_eq]

/-- derivative of the squared norm along a coordinate direction -/
lemma sa16q_hasFDerivAt_sq (y : Euc d) :
    HasFDerivAt (fun z : Euc d => ‖z‖ ^ 2) ((2 : ℝ) • (innerSL ℝ y)) y := by
  refine (hasStrictFDerivAt_norm_sq y).hasFDerivAt.congr_fderiv ?_
  ext v
  simp

lemma sa16q_inner_single (y : Euc d) (j : Fin d) :
    (innerSL ℝ y) (EuclideanSpace.single j (1 : ℝ)) = y j := by
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]

lemma sa16q_proj_single (i j : Fin d) :
    (EuclideanSpace.single j (1 : ℝ) : Euc d) i = if i = j then 1 else 0 := by
  simp [EuclideanSpace.single_apply]

/-- `gE` is differentiable with derivative `K1E` -/
lemma sa16q_gE_hasFDerivAt (s : ℝ) {ε : ℝ} (hε : 0 < ε) (y : Euc d) :
    HasFDerivAt (sa16q_gE s ε)
      ((-(sa16q_gam s) * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1)) • innerSL ℝ y) y := by
  have ht : 0 < ‖y‖ ^ 2 + ε ^ 2 := by positivity
  have h1 := (sa16q_hasFDerivAt_sq y).add_const (ε ^ 2)
  have h2 := (sa16q_Phi_deriv (s := s) ht).comp_hasFDerivAt y h1
  have hfun : sa16q_gE (d := d) s ε = (sa16q_Phi s) ∘ (fun z : Euc d => ‖z‖ ^ 2 + ε ^ 2) := rfl
  rw [hfun]
  refine h2.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma sa16q_gE_fderiv (s : ℝ) {ε : ℝ} (hε : 0 < ε) (y : Euc d) (j : Fin d) :
    fderiv ℝ (sa16q_gE s ε) y (EuclideanSpace.single j (1 : ℝ)) = sa16q_K1E s ε j y := by
  rw [(sa16q_gE_hasFDerivAt s hε y).fderiv]
  simp only [ContinuousLinearMap.smul_apply, sa16q_inner_single, smul_eq_mul, sa16q_K1E]
  ring

lemma sa16q_gE_diff (s : ℝ) {ε : ℝ} (hε : 0 < ε) (y : Euc d) : DifferentiableAt ℝ (sa16q_gE s ε) y :=
  (sa16q_gE_hasFDerivAt s hε y).differentiableAt

/-- `K1E` is differentiable with directional derivative `K2E` -/
lemma sa16q_K1E_hasFDerivAt (s : ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin d) (y : Euc d) :
    HasFDerivAt (sa16q_K1E s ε i)
      ((-(sa16q_gam s) * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1)) • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) +
        (-(sa16q_gam s) * y i * ((-(s / 2) - 1) * (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1 - 1) * 2)) •
          innerSL ℝ y) y := by
  have ht : 0 < ‖y‖ ^ 2 + ε ^ 2 := by positivity
  have h1 := (sa16q_hasFDerivAt_sq y).add_const (ε ^ 2)
  have h2 := ((Real.hasDerivAt_rpow_const (x := ‖y‖ ^ 2 + ε ^ 2) (p := -(s / 2) - 1)
    (Or.inl ht.ne'))).comp_hasFDerivAt y h1
  have h3 : HasFDerivAt (fun z : Euc d => z i) (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt
  have h4 := (h3.const_mul (-(sa16q_gam s))).mul h2
  refine h4.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    PiLp.proj_apply, Function.comp_apply]
  ring

lemma sa16q_K1E_fderiv (s : ℝ) {ε : ℝ} (hε : 0 < ε) (i j : Fin d) (y : Euc d) :
    fderiv ℝ (sa16q_K1E s ε i) y (EuclideanSpace.single j (1 : ℝ)) = sa16q_K2E s ε i j y := by
  rw [(sa16q_K1E_hasFDerivAt s hε i y).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    sa16q_inner_single, PiLp.proj_apply, sa16q_proj_single, sa16q_K2E]
  have ht : 0 < ‖y‖ ^ 2 + ε ^ 2 := by positivity
  have : (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 1 - 1) = (‖y‖ ^ 2 + ε ^ 2) ^ (-(s / 2) - 2) := by
    congr 1; ring
  rw [this]
  ring

lemma sa16q_K1E_diff (s : ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin d) (y : Euc d) :
    DifferentiableAt ℝ (sa16q_K1E s ε i) y := (sa16q_K1E_hasFDerivAt s hε i y).differentiableAt

end Kern

end HRS.Whole.AppendixA.Phase2SA16Q
