import HRS.MS.R26T8AA02e

/-!
# S8.2 T8A A02 (part f): the bound for `repeatedB`
`|repeatedB rho Q x y| ≤ (2 s + 4 BF) A pairWeight M' x y pole(x,y)^2`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a02_sing {s ℓ : ℝ} (hs : 1 ≤ s) (hℓ : 0 < ℓ) :
    ℓ ^ (-s - 1) * (1 + min 1 ℓ ^ (1 - s)) ≤ 2 * (1 + min 1 ℓ ^ (-s)) ^ 2 := by
  by_cases h1 : 1 ≤ ℓ
  · rw [min_eq_left h1, Real.one_rpow, Real.one_rpow]
    have : ℓ ^ (-s - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    nlinarith
  · push Not at h1
    rw [min_eq_right h1.le]
    have e1 : ℓ ^ (-s - 1) * ℓ ^ (1 - s) = ℓ ^ (-s) * ℓ ^ (-s) := by
      rw [← Real.rpow_add hℓ, ← Real.rpow_add hℓ]; congr 1; ring
    have e2 : ℓ ^ (-s - 1) ≤ ℓ ^ (-s) * ℓ ^ (-s) := by
      rw [← Real.rpow_add hℓ]
      exact Real.rpow_le_rpow_of_exponent_ge hℓ h1.le (by linarith)
    have ht : 0 ≤ ℓ ^ (-s) := Real.rpow_nonneg hℓ.le _
    nlinarith [mul_self_nonneg (ℓ ^ (-s))]

set_option maxHeartbeats 3200000 in
theorem r26t8a_a02_repeatedB_bound (d : ℕ) (hd : 2 ≤ d) {a beta M M' A : ℝ} (hMM : M ≤ M') (hA : 0 ≤ A)
    {rho : Euc d → ℝ} {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q)
    {BF : ℝ} (hBF0 : 0 ≤ BF) (hBF : ∀ u, ‖forceMean rho u‖ ≤ BF) {x y : Euc d} (hxy : x ≠ y) :
    |repeatedB rho Q x y| ≤
      (2 * criticalS d + 4 * BF) * A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y ^ 2 := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hs1 : (1 : ℝ) ≤ criticalS d := by unfold criticalS; linarith
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hpw : HRS.MS.Phase2S82.pairWeight M x y ≤ HRS.MS.Phase2S82.pairWeight M' x y := by
    unfold HRS.MS.Phase2S82.pairWeight
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le (s83_one_le_jb x) hMM)
      (Real.rpow_le_rpow_of_exponent_le (s83_one_le_jb y) hMM) (Real.rpow_nonneg (s83_jb_pos y).le _)
      (Real.rpow_nonneg (s83_jb_pos x).le _)
  have hpw0 : 0 ≤ HRS.MS.Phase2S82.pairWeight M x y :=
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le _) (Real.rpow_nonneg (s83_jb_pos y).le _)
  set fld : ℝ := A * HRS.MS.Phase2S82.pairWeight M x y * (1 + smallRadius x y ^ (1 - criticalS d)) with hfld
  have hg := hQ.gradient x y hxy
  have hXY : ‖pairGradX Q x y - pairGradY Q x y‖ ≤ fld := (norm_sub_le _ _).trans hg
  have hX : ‖pairGradX Q x y‖ ≤ fld := (le_add_of_nonneg_right (norm_nonneg _)).trans hg
  have hY : ‖pairGradY Q x y‖ ≤ fld := (le_add_of_nonneg_left (norm_nonneg _)).trans hg
  have hpole1 := r26t8a_a01_pole_ge_one x y
  have hgp := r26t8a_a01_grad_pole hxy hs1
  have hfld0 : 0 ≤ fld := by
    rw [hfld]
    have : 0 ≤ smallRadius x y ^ (1 - criticalS d) := Real.rpow_nonneg (le_min zero_le_one hn.le) _
    positivity
  have hfldp : fld ≤ A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y := by
    calc fld ≤ A * HRS.MS.Phase2S82.pairWeight M x y * pole x y :=
          mul_le_mul_of_nonneg_left hgp (mul_nonneg hA hpw0)
      _ ≤ A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpw hA) (by linarith)
  have hgn : ‖rieszKernelGrad d (criticalS d) (x - y)‖ = criticalS d * ‖x - y‖ ^ (-criticalS d - 1) :=
    r26t8a_norm_rieszGrad hs0 (sub_ne_zero.2 hxy)
  have hsing := r26t8a_a02_sing hs1 hn
  have hpoleeq : pole x y = 1 + min 1 ‖x - y‖ ^ (-criticalS d) := rfl
  have hfldeq : fld = A * HRS.MS.Phase2S82.pairWeight M x y * (1 + min 1 ‖x - y‖ ^ (1 - criticalS d)) := rfl
  -- first term
  have t1 : |inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (pairGradX Q x y - pairGradY Q x y)| ≤
      2 * criticalS d * (A * HRS.MS.Phase2S82.pairWeight M x y) * pole x y ^ 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hgn]
    calc criticalS d * ‖x - y‖ ^ (-criticalS d - 1) * ‖pairGradX Q x y - pairGradY Q x y‖
        ≤ criticalS d * ‖x - y‖ ^ (-criticalS d - 1) * fld :=
          mul_le_mul_of_nonneg_left hXY (by positivity)
      _ = criticalS d * (A * HRS.MS.Phase2S82.pairWeight M x y) *
            (‖x - y‖ ^ (-criticalS d - 1) * (1 + min 1 ‖x - y‖ ^ (1 - criticalS d))) := by rw [hfldeq]; ring
      _ ≤ criticalS d * (A * HRS.MS.Phase2S82.pairWeight M x y) * (2 * (1 + min 1 ‖x - y‖ ^ (-criticalS d)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsing (by positivity)
      _ = _ := by rw [hpoleeq]; ring
  have t2 : |inner ℝ (forceMean rho x) (pairGradX Q x y)| ≤ BF * fld := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hBF x) hX (norm_nonneg _) hBF0
  have t3 : |inner ℝ (forceMean rho y) (pairGradY Q x y)| ≤ BF * fld := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hBF y) hY (norm_nonneg _) hBF0
  have hpw1 : 0 ≤ A * HRS.MS.Phase2S82.pairWeight M x y := mul_nonneg hA hpw0
  have hp2 : pole x y ≤ pole x y ^ 2 := by nlinarith
  have hfl2 : fld ≤ A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y ^ 2 := by
    refine hfldp.trans ?_
    have h0 : 0 ≤ A * HRS.MS.Phase2S82.pairWeight M' x y :=
      mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le _) (Real.rpow_nonneg (s83_jb_pos y).le _))
    exact mul_le_mul_of_nonneg_left hp2 h0
  have hpw'1 : A * HRS.MS.Phase2S82.pairWeight M x y ≤ A * HRS.MS.Phase2S82.pairWeight M' x y :=
    mul_le_mul_of_nonneg_left hpw hA
  have hP2 : 0 ≤ pole x y ^ 2 := by positivity
  have hrep : repeatedB rho Q x y =
      inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (pairGradX Q x y - pairGradY Q x y) -
      2 * (inner ℝ (forceMean rho x) (pairGradX Q x y) + inner ℝ (forceMean rho y) (pairGradY Q x y)) := rfl
  rw [hrep]
  have hT1 : 2 * criticalS d * (A * HRS.MS.Phase2S82.pairWeight M x y) * pole x y ^ 2 ≤
      2 * criticalS d * (A * HRS.MS.Phase2S82.pairWeight M' x y) * pole x y ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpw'1 (by positivity)) hP2
  have hT2 : BF * fld ≤ BF * (A * HRS.MS.Phase2S82.pairWeight M' x y * pole x y ^ 2) :=
    mul_le_mul_of_nonneg_left hfl2 hBF0
  have a1 := abs_le.1 t1
  have a2 := abs_le.1 t2
  have a3 := abs_le.1 t3
  rw [abs_le]
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

end HRS.MS.R26T8A
