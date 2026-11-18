import HRS.MS.S82TForce
import HRS.MS.S82P2Grad3

/-!
# S8.2 (S82T): a measurable symmetric model of `repeatedB`
`repeatedB rho Q x y` uses `gradient` (junk on the diagonal).  Off the diagonal it equals
`s82t_B0 (forceMean rho) (s82p2_gt Q) x y`, which is jointly measurable, symmetric, and bounded by
`C A <x>^M <y>^M pole^2` when `forceMean rho` is bounded.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82T
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

def s82t_B0 {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) (x y : Euc d) : ℝ :=
  inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (gt x y - gt y x) -
    2 * (inner ℝ (Fm x) (gt x y) + inner ℝ (Fm y) (gt y x))

lemma s82t_pairGradY_eq {d : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x y : Euc d) (hxy : x ≠ y) :
    Phase2S82.pairGradY Q x y = s82p2_gt Q y x := by
  have hQx : Q x = fun w => Q w x := funext fun w => hQ.symmetric x w
  rw [s82p2_gt_eq hQ y x hxy.symm]
  unfold Phase2S82.pairGradY Phase2S82.pairGradX
  rw [hQx]

lemma s82t_repeatedB_eq {d : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x y : Euc d) (hxy : x ≠ y) :
    repeatedB rho Q x y = s82t_B0 (forceMean rho) (s82p2_gt Q) x y := by
  unfold repeatedB s82t_B0
  rw [s82p2_gt_eq hQ x y hxy, s82t_pairGradY_eq hQ x y hxy, ← s82p2_gt_eq hQ x y hxy]

lemma s82t_B0_measurable {d : ℕ} {Fm : Euc d → Euc d} (hFm : Measurable Fm)
    {gt : Euc d → Euc d → Euc d} (hg : Measurable (Function.uncurry gt)) :
    Measurable (Function.uncurry (s82t_B0 Fm gt)) := by
  have hG := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have h1 : Measurable (fun p : Euc d × Euc d => gt p.1 p.2) := hg
  have h2 : Measurable (fun p : Euc d × Euc d => gt p.2 p.1) := hg.comp (measurable_snd.prodMk measurable_fst)
  unfold s82t_B0 Function.uncurry
  refine Measurable.sub (Measurable.inner (hG.comp (measurable_fst.sub measurable_snd)) (h1.sub h2)) ?_
  exact measurable_const.mul (Measurable.add (Measurable.inner (hFm.comp measurable_fst) h1)
    (Measurable.inner (hFm.comp measurable_snd) h2))

lemma s82t_B0_symm {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) (x y : Euc d) :
    s82t_B0 Fm gt x y = s82t_B0 Fm gt y x := by
  by_cases hxy : x = y
  · rw [hxy]
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hodd : rieszKernelGrad d (criticalS d) (y - x) = -rieszKernelGrad d (criticalS d) (x - y) := by
    have hz' : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
    rw [HRS.Whole.movtr_rieszKernelGrad_eq _ hz', HRS.Whole.movtr_rieszKernelGrad_eq _ hz,
      show y - x = -(x - y) by abel, norm_neg, smul_neg, neg_smul]
  unfold s82t_B0
  rw [hodd, show gt y x - gt x y = -(gt x y - gt y x) by abel, inner_neg_neg]
  ring

lemma s82t_pole_ge_one {d : ℕ} (x z : Euc d) : 1 ≤ pole x z := by
  unfold pole smallRadius
  have : 0 ≤ (min 1 ‖x - z‖) ^ (-criticalS d) :=
    Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
  linarith

lemma s82t_sigma_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ HRS.Whole.movtr_sigma s := by
  unfold HRS.Whole.movtr_sigma
  split_ifs <;> linarith

/-- Radial inequalities for `0 < r ≤ 1`, `1 ≤ s`. -/
lemma s82t_radial (s r : ℝ) (hs : 1 ≤ s) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    r ^ (-s - 1) * (1 + r ^ (1 - s)) ≤ 2 * (1 + r ^ (-s)) ^ 2 ∧
      1 + r ^ (1 - s) ≤ 1 + r ^ (-s) := by
  have e1 : r ^ (-s - 1) ≤ r ^ (-(2 * s)) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  have e2 : r ^ (-s - 1) * r ^ (1 - s) = r ^ (-(2 * s)) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  have h1 : r ^ (-(2 * s)) = (r ^ (-s)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]; congr 1; push_cast; ring
  have h0 : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr0.le _
  refine ⟨?_, ?_⟩
  · calc r ^ (-s - 1) * (1 + r ^ (1 - s)) = r ^ (-s - 1) + r ^ (-s - 1) * r ^ (1 - s) := by ring
      _ = r ^ (-s - 1) + r ^ (-(2 * s)) := by rw [e2]
      _ ≤ 2 * r ^ (-(2 * s)) := by linarith
      _ = 2 * (r ^ (-s)) ^ 2 := by rw [h1]
      _ ≤ 2 * (1 + r ^ (-s)) ^ 2 := by nlinarith
  · have h2 : r ^ (1 - s) = r * r ^ (-s) := by
      rw [show 1 - s = 1 + -s by ring, Real.rpow_add hr0, Real.rpow_one]
    rw [h2]
    nlinarith

/-- Pointwise bound of the model. -/
lemma s82t_B0_bound {d : ℕ} (hd : 2 ≤ d) {a beta M A K : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (hA : 0 ≤ A) (hK0 : 0 ≤ K)
    {Fm : Euc d → Euc d} (hFm : ∀ x, ‖Fm x‖ ≤ K) (x y : Euc d) (hxy : x ≠ y) :
    |s82t_B0 Fm (s82p2_gt Q) x y| ≤
      (2 * HRS.Whole.movtr_sigma (criticalS d) + 2 * K) * (A * Phase2S82.pairWeight M x y * pole x y ^ 2) := by
  have hs1 : 1 ≤ criticalS d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    unfold criticalS; linarith
  have hs0 : 0 ≤ criticalS d := by linarith
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hzpos : 0 < ‖x - y‖ := norm_pos_iff.2 hz
  have hr0 : 0 < smallRadius x y := lt_min one_pos hzpos
  have hr1 : smallRadius x y ≤ 1 := min_le_left _ _
  have hrn : smallRadius x y ≤ ‖x - y‖ := min_le_right _ _
  have hσ0 : 0 ≤ HRS.Whole.movtr_sigma (criticalS d) := s82t_sigma_nonneg _ hs0
  have hpw : 0 ≤ Phase2S82.pairWeight M x y := by
    unfold Phase2S82.pairWeight
    exact mul_nonneg (Real.rpow_nonneg (HRS.MS.S82N.s82n_jb_pos x).le _)
      (Real.rpow_nonneg (HRS.MS.S82N.s82n_jb_pos y).le _)
  have hpole : pole x y = 1 + smallRadius x y ^ (-criticalS d) := rfl
  obtain ⟨hrad1, hrad2⟩ := s82t_radial (criticalS d) (smallRadius x y) hs1 hr0 hr1
  rw [← hpole] at hrad1 hrad2
  have e5 : 1 ≤ pole x y := s82t_pole_ge_one x y
  have e6 : pole x y ≤ pole x y ^ 2 := by nlinarith
  have hgn : ‖s82p2_gt Q x y‖ + ‖s82p2_gt Q y x‖ ≤
      A * Phase2S82.pairWeight M x y * (1 + smallRadius x y ^ (1 - criticalS d)) := by
    have := hQ.gradient x y hxy
    rwa [← s82p2_gt_eq hQ x y hxy, s82t_pairGradY_eq hQ x y hxy] at this
  have hGn : ‖rieszKernelGrad d (criticalS d) (x - y)‖ ≤
      HRS.Whole.movtr_sigma (criticalS d) * smallRadius x y ^ (-criticalS d - 1) := by
    rw [HRS.Whole.movtr_rieszKernelGrad_norm (criticalS d) hs0 hz]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hr0 hrn (by linarith)) hσ0
  have hAp : 0 ≤ A * Phase2S82.pairWeight M x y := mul_nonneg hA hpw
  have hrp : 0 ≤ smallRadius x y ^ (1 - criticalS d) := Real.rpow_nonneg hr0.le _
  have hrm : 0 ≤ smallRadius x y ^ (-criticalS d - 1) := Real.rpow_nonneg hr0.le _
  have hdiff : ‖s82p2_gt Q x y - s82p2_gt Q y x‖ ≤ ‖s82p2_gt Q x y‖ + ‖s82p2_gt Q y x‖ :=
    norm_sub_le _ _
  -- term 1
  have t1 : |inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (s82p2_gt Q x y - s82p2_gt Q y x)| ≤
      HRS.Whole.movtr_sigma (criticalS d) * (A * Phase2S82.pairWeight M x y) * (2 * pole x y ^ 2) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖rieszKernelGrad d (criticalS d) (x - y)‖ * ‖s82p2_gt Q x y - s82p2_gt Q y x‖
        ≤ (HRS.Whole.movtr_sigma (criticalS d) * smallRadius x y ^ (-criticalS d - 1)) *
            (A * Phase2S82.pairWeight M x y * (1 + smallRadius x y ^ (1 - criticalS d))) :=
          mul_le_mul hGn (hdiff.trans hgn) (norm_nonneg _) (by positivity)
      _ = HRS.Whole.movtr_sigma (criticalS d) * (A * Phase2S82.pairWeight M x y) *
            (smallRadius x y ^ (-criticalS d - 1) * (1 + smallRadius x y ^ (1 - criticalS d))) := by
          ring
      _ ≤ HRS.Whole.movtr_sigma (criticalS d) * (A * Phase2S82.pairWeight M x y) * (2 * pole x y ^ 2) :=
          mul_le_mul_of_nonneg_left hrad1 (mul_nonneg hσ0 hAp)
  -- term 2
  have t2 : |2 * (inner ℝ (Fm x) (s82p2_gt Q x y) + inner ℝ (Fm y) (s82p2_gt Q y x))| ≤
      2 * K * (A * Phase2S82.pairWeight M x y * pole x y ^ 2) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h1 : |inner ℝ (Fm x) (s82p2_gt Q x y)| ≤ K * ‖s82p2_gt Q x y‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hFm x) (norm_nonneg _))
    have h2 : |inner ℝ (Fm y) (s82p2_gt Q y x)| ≤ K * ‖s82p2_gt Q y x‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hFm y) (norm_nonneg _))
    have h3 : |inner ℝ (Fm x) (s82p2_gt Q x y) + inner ℝ (Fm y) (s82p2_gt Q y x)| ≤
        K * (A * Phase2S82.pairWeight M x y * (1 + smallRadius x y ^ (1 - criticalS d))) :=
      (abs_add_le _ _).trans (by nlinarith [norm_nonneg (s82p2_gt Q x y), norm_nonneg (s82p2_gt Q y x)])
    calc 2 * |inner ℝ (Fm x) (s82p2_gt Q x y) + inner ℝ (Fm y) (s82p2_gt Q y x)|
        ≤ 2 * (K * (A * Phase2S82.pairWeight M x y * (1 + smallRadius x y ^ (1 - criticalS d)))) := by linarith
      _ ≤ 2 * (K * (A * Phase2S82.pairWeight M x y * pole x y ^ 2)) := by
          gcongr
          linarith
      _ = _ := by ring
  unfold s82t_B0
  refine (abs_sub _ _).trans ?_
  nlinarith [t1, t2]

end HRS.MS.S82T
