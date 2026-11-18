import HRS.MS.SA12X2S
import HRS.MS.SA12Z3NearOddGrad

/-!
# S.A.12 N8 (SA12X2), part T: the `β = 1` terms `∫ ω² ∂_l Z T_i(c ∂_j Z)` via N4

With a localization `η` (`η = 1` where `ω ≠ 0` or `c ≠ 0`, hence `∂η = 0` there since `η ≤ 1`), `Z̃ = ηZ ∈ C²_c`;
`T_i(c v) = c T_i v - [c, T_i] v` (`sa12x2_commT_real`, Lipschitz `c`), and `N4` (`odd_gradient_finite`) with the
coefficient `ω² c`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- At a maximum point of `η` its derivative vanishes, so the localization does not change derivatives. -/
theorem sa12x2_eta_D1 {η Z : Euc d → ℝ} (hη : ContDiff ℝ 1 η) (hle : ∀ x, η x ≤ 1)
    (hZ : ContDiff ℝ 1 Z) (y : Euc d) (hy : η y = 1) (j : Fin d) :
    D1 j (fun x => η x * Z x) y = D1 j Z y := by
  have hmax : IsLocalMax η y := Filter.Eventually.of_forall fun x => by rw [hy]; exact hle x
  have h0 : fderiv ℝ η y = 0 := hmax.fderiv_eq_zero
  have h1 : HasFDerivAt (fun x => η x * Z x) (η y • fderiv ℝ Z y + Z y • fderiv ℝ η y) y :=
    ((hη.differentiable one_ne_zero) y).hasFDerivAt.mul ((hZ.differentiable one_ne_zero) y).hasFDerivAt
  unfold D1
  rw [h1.fderiv, h0, hy]
  simp

theorem sa12x2_N4term (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    (R Ka Ka' : ℝ) (hR : 1 ≤ R) (hKa : 0 ≤ Ka) (hKa' : 0 ≤ Ka') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c0 : Euc d) (om η c a' Z : Euc d → ℝ) (i l j : Fin d) (Ez : ℝ),
      ContDiff ℝ 2 om → HasCompactSupport om → (∀ x, |om x| ≤ 1) → Function.support om ⊆ closedBall c0 R →
      ContDiff ℝ 2 η → HasCompactSupport η → Function.support η ⊆ closedBall c0 R → (∀ x, η x ≤ 1) →
      (∀ x, om x ≠ 0 → η x = 1) → (∀ x, c x ≠ 0 → η x = 1) →
      ContDiff ℝ 1 c → (∀ x y, |c x - c y| ≤ Ka * ‖x - y‖) →
      MemCb 2 a' → cbNorm 2 a' ≤ Ka' → (∀ x, om x ^ 2 * c x = a' x) → ContDiff ℝ 2 Z → 0 ≤ Ez →
      ∫ x, (η x * Z x) ^ 2 ≤ Ez → ∫ x, ‖fderiv ℝ (fun y => η y * Z y) x‖ ^ 2 ≤ Ez →
      |∫ x, om x ^ 2 * D1 l Z x * firstRiesz d s i (fun y => c y * D1 j Z y) x| ≤ K * Ez := by
  obtain ⟨C4, hC40, hC4⟩ := odd_gradient_finite d hd s hs0 hs1 hsd
  obtain ⟨Cc, hCc0, hCc⟩ := sa12x2_commT_real hd hs0 hsd
  have hR0 : 0 < R := by linarith
  have hRd : 0 ≤ R ^ (d : ℝ) := Real.rpow_nonneg hR0.le _
  refine ⟨2 * C4 * Ka' + Cc * Ka * R ^ (d : ℝ), by positivity, ?_⟩
  intro c0 om η c a' Z i l j Ez hom homc hom1 homs hη hηc hηs hηle hηom hηc' hc hcL ha' hcb hid hZ hEz
    hE1 hE2
  set Zt : Euc d → ℝ := fun x => η x * Z x with hZt
  have hZt2 : ContDiff ℝ 2 Zt := hη.mul hZ
  have hZtc : HasCompactSupport Zt := hηc.mul_right
  have hZts : Function.support Zt ⊆ closedBall c0 R := fun y hy =>
    hηs (Function.mem_support.2 (left_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hZ1 : ContDiff ℝ 1 Z := hZ.of_le (by norm_num)
  have hDl : ∀ x, om x ≠ 0 → D1 l Zt x = D1 l Z x := fun x hx => sa12x2_eta_D1 hη1 hηle hZ1 x (hηom x hx) l
  have hDj : ∀ x, c x ≠ 0 → D1 j Zt x = D1 j Z x := fun x hx => sa12x2_eta_D1 hη1 hηle hZ1 x (hηc' x hx) j
  set v : Euc d → ℝ := D1 j Zt with hv
  have hv1 : ContDiff ℝ 1 v := D1_contDiff hZt2 j
  have hvc : HasCompactSupport v := D1_supp hZtc j
  have hvs : Function.support v ⊆ closedBall c0 R := fun y hy => by
    have : fderiv ℝ Zt y ≠ 0 := fun h0 => hy (by simp [hv, D1, h0])
    exact (closure_minimal hZts isClosed_closedBall) (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 this))
  have hfun : (fun y => c y * D1 j Z y) = fun y => c y * v y := by
    funext y
    by_cases hy : c y = 0
    · simp [hy]
    · show c y * D1 j Z y = c y * D1 j Zt y
      exact congrArg (fun z => c y * z) (hDj y hy).symm
  rw [hfun]
  set Cm : Euc d → ℝ := fun x => c x * firstRiesz d s i v x - firstRiesz d s i (fun y => c y * v y) x with hCm
  have hCmc : Continuous Cm :=
    (hc.continuous.mul (sa12z3_firstRiesz_cont hs0 hsd i hv1 hvc)).sub
      (sa12z3_firstRiesz_cont hs0 hsd i (hc.mul hv1) hvc.mul_left)
  set Dl : Euc d → ℝ := D1 l Zt with hDldef
  have hDlc : Continuous Dl := (D1_contDiff hZt2 l).continuous
  have hDls : HasCompactSupport Dl := D1_supp hZtc l
  have hpt : ∀ x, om x ^ 2 * D1 l Z x * firstRiesz d s i (fun y => c y * v y) x =
      Dl x * a' x * firstRiesz d s i v x - om x ^ 2 * Dl x * Cm x := by
    intro x
    by_cases hx : om x = 0
    · simp [hx, ← hid x]
    · rw [← hDl x hx, ← hid x]; simp only [hCm, hDldef]; ring
  -- N4
  have hZtm : MemCb 2 Zt := sa12z3_memCb_of_cc hZt2 hZtc
  obtain ⟨hI4, hb4⟩ := hC4 i j l a' ha' Zt hZtm hZtc
  have hpd1 : partialDeriv (fun _ : Fin 1 => l) Zt = Dl := sa12z3_pd_one (hZt2.of_le (by norm_num)) l
  have hpd2 : partialDeriv (fun _ : Fin 1 => j) Zt = v := sa12z3_pd_one (hZt2.of_le (by norm_num)) j
  rw [hpd1, hpd2] at hI4 hb4
  have hIc : Integrable (fun x => om x ^ 2 * Dl x * Cm x) volume :=
    (((hom.pow 2).continuous.mul hDlc).mul hCmc).integrable_of_hasCompactSupport
      (((homc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right).mul_right)
  simp_rw [hpt]
  rw [integral_sub hI4 hIc]
  -- bounds
  have hZ2int : ∀ p : Fin d, ∫ x, D1 p Zt x ^ 2 ≤ Ez := fun p => by
    refine le_trans (integral_mono ?_ ?_ fun x => ?_) hE2
    · exact Continuous.integrable_of_hasCompactSupport (f := fun x => D1 p Zt x ^ 2)
        ((D1_contDiff hZt2 p).continuous.pow 2)
        ((D1_supp hZtc p).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
    · exact Continuous.integrable_of_hasCompactSupport (f := fun x => ‖fderiv ℝ Zt x‖ ^ 2)
        ((hZt2.continuous_fderiv (by norm_num)).norm.pow 2)
        ((hZtc.fderiv (𝕜 := ℝ)).norm.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
    · exact pow_le_pow_left₀ (abs_nonneg _) (sa12z3_D1_le p Zt x) 2 |>.trans' (by rw [sq_abs])
  have hcomm : |∫ x, om x ^ 2 * Dl x * Cm x| ≤ Cc * Ka * R ^ (d : ℝ) * Ez := by
    have hU : Continuous (fun x => om x ^ 2 * Dl x) := (hom.pow 2).continuous.mul hDlc
    have hUc : HasCompactSupport (fun x => om x ^ 2 * Dl x) :=
      (homc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right
    have hUs : Function.support (fun x => om x ^ 2 * Dl x) ⊆ closedBall c0 R := fun y hy =>
      homs (Function.mem_support.2 (fun h0 => (Function.mem_support.1 hy) (by simp [h0])))
    refine (sa12x2_pairU hU hUc hUs hCmc).trans ?_
    have hb := hCc i R hR c0 c v Ka hKa hc hcL hv1 hvc hvs
    have hU2 : ∫ x, (om x ^ 2 * Dl x) ^ 2 ≤ Ez := by
      refine le_trans (integral_mono ?_ ?_ fun x => ?_) (hZ2int l)
      · exact Continuous.integrable_of_hasCompactSupport (f := fun x => (om x ^ 2 * Dl x) ^ 2)
          (hU.pow 2) (hUc.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
      · exact Continuous.integrable_of_hasCompactSupport (f := fun x => D1 l Zt x ^ 2)
          (hDlc.pow 2) (hDls.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
      · have h1 : (om x ^ 2) ^ 2 ≤ 1 := by
          have := hom1 x
          have h2 : om x ^ 2 ≤ 1 := by nlinarith [abs_nonneg (om x), sq_abs (om x)]
          nlinarith [sq_nonneg (om x)]
        calc (om x ^ 2 * Dl x) ^ 2 = (om x ^ 2) ^ 2 * Dl x ^ 2 := by ring
          _ ≤ 1 * Dl x ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
          _ = D1 l Zt x ^ 2 := by simp [hDldef]
    have h3 : Real.sqrt (∫ x, (om x ^ 2 * Dl x) ^ 2) ≤ Real.sqrt Ez := Real.sqrt_le_sqrt hU2
    have h4 : Real.sqrt (∫ x, v x ^ 2) ≤ Real.sqrt Ez := Real.sqrt_le_sqrt (hZ2int j)
    have h5 : Real.sqrt (∫ x, ((closedBall c0 R).indicator Cm x) ^ 2) ≤
        Cc * Ka * R ^ (d : ℝ) * Real.sqrt Ez :=
      hb.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
    calc Real.sqrt (∫ x, (om x ^ 2 * Dl x) ^ 2) *
          Real.sqrt (∫ x, ((closedBall c0 R).indicator Cm x) ^ 2)
        ≤ Real.sqrt Ez * (Cc * Ka * R ^ (d : ℝ) * Real.sqrt Ez) :=
          mul_le_mul h3 h5 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Cc * Ka * R ^ (d : ℝ) * (Real.sqrt Ez * Real.sqrt Ez) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hEz]
  have hb4' : |∫ x, Dl x * a' x * firstRiesz d s i v x| ≤ 2 * C4 * Ka' * Ez := by
    refine hb4.trans ?_
    have hcb0 := sa12z3_cb_nonneg ha'
    calc C4 * cbNorm 2 a' * ((∫ x, Zt x ^ 2) + ∫ x, ‖fderiv ℝ Zt x‖ ^ 2)
        ≤ C4 * Ka' * (Ez + Ez) := by gcongr
      _ = _ := by ring
  calc |(∫ x, Dl x * a' x * firstRiesz d s i v x) - ∫ x, om x ^ 2 * Dl x * Cm x|
      ≤ |∫ x, Dl x * a' x * firstRiesz d s i v x| + |∫ x, om x ^ 2 * Dl x * Cm x| := abs_sub _ _
    _ ≤ 2 * C4 * Ka' * Ez + Cc * Ka * R ^ (d : ℝ) * Ez := add_le_add hb4' hcomm
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12Near
