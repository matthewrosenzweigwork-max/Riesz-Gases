import HRS.MS.SA12X2M
import HRS.MS.SA12Z3NearN4E
import HRS.MS.SA12Z3NearN4

/-!
# S.A.12 N8 (SA12X2), part N: the `H¹`-pairing estimate for `T_i`

For `d - 1 < s < d`, `w ∈ C²`, `h ∈ C¹_c`, `ω ∈ C²_c`:
`∫ ω² ∂_l w T_i h = ∫ (∂_l h) T_i(ω² w) + ∫ h T_i(w ∂_l ω²)`
(skew-adjointness of `T_i`, `T_i ∂_l = ∂_l T_i`, one integration by parts), hence by `sa12z3_T_pair`
a bound by `‖∂_l h‖ (‖ω²w‖ + ‖∇(ω²w)‖) + ‖h‖ (‖w ∂_lω²‖ + ‖∇(w ∂_l ω²)‖)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- `T_i ∂_l = ∂_l T_i` on `C²_c`. -/
theorem sa12x2_T_comm {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i l : Fin d) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    firstRiesz d s i (D1 l f) = D1 l (firstRiesz d s i f) ∧ ContDiff ℝ 1 (firstRiesz d s i f) := by
  have hc := sa12n_conv_contDiff hs0 hsd hf hfc
  have hTi : firstRiesz d s i f = D1 i (HRS.Whole.convFun (rieszKernel d s) f) := rfl
  have hD1f : ContDiff ℝ 1 (D1 l f) := D1_contDiff hf l
  have hTl : firstRiesz d s i (D1 l f) =
      D1 i (HRS.Whole.convFun (rieszKernel d s) (D1 l f)) := rfl
  refine ⟨?_, ?_⟩
  · have e1 : HRS.Whole.convFun (rieszKernel d s) (D1 l f) =
        D1 l (HRS.Whole.convFun (rieszKernel d s) f) := by
      funext x
      have := sa12z3_pd_conv hs0 hsd 1 f (hf.of_le (by norm_num)) hfc (fun _ => l) x
      rw [sa12z3_pd_one (hc.of_le (by norm_num)) l, sa12z3_pd_one (hf.of_le (by norm_num)) l] at this
      exact this.symm
    rw [hTl, hTi, e1]
    funext x
    exact (HRS.MS.UniqN3c.n3c_hess_symm hc i l x).symm
  · rw [hTi]
    exact D1_contDiff hc i


/-- The pairing identity. -/
theorem sa12x2_B2_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i l : Fin d)
    {om w h : Euc d → ℝ} (hom : ContDiff ℝ 2 om) (homc : HasCompactSupport om)
    (hw : ContDiff ℝ 2 w) (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h) :
    ∫ x, om x ^ 2 * D1 l w x * firstRiesz d s i h x =
      (∫ x, D1 l h x * firstRiesz d s i (fun y => om y ^ 2 * w y) x) +
        ∫ x, h x * firstRiesz d s i (fun y => w y * D1 l (fun z => om z ^ 2) y) x := by
  have ho2 : ContDiff ℝ 2 (fun y => om y ^ 2) := hom.pow 2
  have ho2c : HasCompactSupport (fun y => om y ^ 2) := homc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  set f1 : Euc d → ℝ := fun y => om y ^ 2 * w y with hf1
  set f2 : Euc d → ℝ := fun y => w y * D1 l (fun z => om z ^ 2) y with hf2
  set f0 : Euc d → ℝ := fun y => om y ^ 2 * D1 l w y with hf0
  have hf1d : ContDiff ℝ 2 f1 := ho2.mul hw
  have hf1c : HasCompactSupport f1 := ho2c.mul_right
  have hf2d : ContDiff ℝ 1 f2 := (hw.of_le (by norm_num)).mul (D1_contDiff ho2 l)
  have hf2c : HasCompactSupport f2 := (D1_supp ho2c l).mul_left
  have hDw : ContDiff ℝ 1 (D1 l w) := D1_contDiff hw l
  have hf0d : ContDiff ℝ 1 f0 := (ho2.of_le (by norm_num)).mul hDw
  have hf0c : HasCompactSupport f0 := ho2c.mul_right
  have hDf1 : ContDiff ℝ 1 (D1 l f1) := D1_contDiff hf1d l
  have hDf1c : HasCompactSupport (D1 l f1) := D1_supp hf1c l
  -- `f0 = ∂_l f1 - f2`
  have hdec : f0 = fun y => 1 * D1 l f1 y - f2 y := by
    funext y
    have h1 : HasFDerivAt (fun z => om z ^ 2) (fderiv ℝ (fun z => om z ^ 2) y) y :=
      ((ho2.differentiable (by norm_num)) y).hasFDerivAt
    have h2 : HasFDerivAt w (fderiv ℝ w y) y := ((hw.differentiable (by norm_num)) y).hasFDerivAt
    have h3 : HasFDerivAt (fun z => om z ^ 2 * w z) (om y ^ 2 • fderiv ℝ w y +
        w y • fderiv ℝ (fun z => om z ^ 2) y) y := h1.mul h2
    have : D1 l f1 y = om y ^ 2 * D1 l w y + w y * D1 l (fun z => om z ^ 2) y := by
      unfold D1
      rw [show f1 = fun y => om y ^ 2 * w y from rfl, h3.fderiv]
      simp
    rw [this]; simp only [hf0, hf2]; ring
  obtain ⟨hTc, hTd⟩ := sa12x2_T_comm hs0 hsd i l hf1d hf1c
  have hskew := sa12z3_T_skew hd hs0 hsd i hf0d hf0c hh hhc
  have hlin := sa12x2_first_lin hs0 hsd i hDf1 hDf1c hf2d hf2c 1
  have hT0 : ∀ x, firstRiesz d s i f0 x = D1 l (firstRiesz d s i f1) x - firstRiesz d s i f2 x := by
    intro x
    rw [hdec, hlin, one_mul, hTc]
  have e1 : ∫ x, om x ^ 2 * D1 l w x * firstRiesz d s i h x = ∫ x, f0 x * firstRiesz d s i h x := rfl
  rw [e1, hskew]
  simp_rw [hT0]
  have hΦ := hTd
  have hI1 : Integrable (fun x => h x * D1 l (firstRiesz d s i f1) x) volume := by
    refine (hh.continuous.mul ((hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport hhc.mul_right
  have hI2 : Integrable (fun x => h x * firstRiesz d s i f2 x) volume :=
    (hh.continuous.mul (sa12z3_firstRiesz_cont hs0 hsd i hf2d hf2c)).integrable_of_hasCompactSupport
      hhc.mul_right
  have hibp := HRS.MS.UniqN0.n0_ibp (F := h) (k := firstRiesz d s i f1) hh hhc
    (fun t _ => hΦ.contDiffAt) (EuclideanSpace.single l 1)
  have hsplit : ∫ x, h x * (D1 l (firstRiesz d s i f1) x - firstRiesz d s i f2 x) =
      (∫ x, h x * D1 l (firstRiesz d s i f1) x) - ∫ x, h x * firstRiesz d s i f2 x := by
    rw [← integral_sub hI1 hI2]; congr 1; funext x; ring
  have e2 : ∫ x, firstRiesz d s i f1 x * D1 l h x = -∫ x, D1 l (firstRiesz d s i f1) x * h x := hibp
  have e3 : ∫ x, h x * D1 l (firstRiesz d s i f1) x = ∫ x, D1 l (firstRiesz d s i f1) x * h x :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have e4 : ∫ x, D1 l h x * firstRiesz d s i f1 x = ∫ x, firstRiesz d s i f1 x * D1 l h x :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hsplit, e3, e4, e2]
  ring


theorem sa12x2_B2_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i l : Fin d) (om w h : Euc d → ℝ), ContDiff ℝ 2 om → HasCompactSupport om →
      ContDiff ℝ 2 w → ContDiff ℝ 1 h → HasCompactSupport h →
      |∫ x, om x ^ 2 * D1 l w x * firstRiesz d s i h x| ≤
        C * (Real.sqrt (∫ x, D1 l h x ^ 2) *
            (Real.sqrt (∫ x, (om x ^ 2 * w x) ^ 2) +
              Real.sqrt (∫ x, ‖fderiv ℝ (fun y => om y ^ 2 * w y) x‖ ^ 2)) +
          Real.sqrt (∫ x, h x ^ 2) *
            (Real.sqrt (∫ x, (w x * D1 l (fun z => om z ^ 2) x) ^ 2) +
              Real.sqrt (∫ x, ‖fderiv ℝ (fun y => w y * D1 l (fun z => om z ^ 2) y) x‖ ^ 2))) := by
  obtain ⟨C, hC0, hC⟩ := sa12z3_T_pair hd hs0 hsd hs1
  refine ⟨C, hC0, fun i l om w h hom homc hw hh hhc => ?_⟩
  have ho2 : ContDiff ℝ 2 (fun y => om y ^ 2) := hom.pow 2
  have ho2c : HasCompactSupport (fun y => om y ^ 2) := homc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hf1d : ContDiff ℝ 2 (fun y => om y ^ 2 * w y) := ho2.mul hw
  have hf1c : HasCompactSupport (fun y => om y ^ 2 * w y) := ho2c.mul_right
  have hf2d : ContDiff ℝ 1 (fun y => w y * D1 l (fun z => om z ^ 2) y) :=
    (hw.of_le (by norm_num)).mul (D1_contDiff ho2 l)
  have hf2c : HasCompactSupport (fun y => w y * D1 l (fun z => om z ^ 2) y) := (D1_supp ho2c l).mul_left
  have hDh : Continuous (D1 l h) := (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [sa12x2_B2_eq hd hs0 hsd i l hom homc hw hh hhc]
  have b1 := hC i (fun y => om y ^ 2 * w y) (D1 l h) (hf1d.of_le (by norm_num)) hf1c hDh (D1_supp hhc l)
  have b2 := hC i (fun y => w y * D1 l (fun z => om z ^ 2) y) h hf2d hf2c hh.continuous hhc
  refine (abs_add_le _ _).trans ?_
  have e1 : |∫ x, D1 l h x * firstRiesz d s i (fun y => om y ^ 2 * w y) x| ≤ _ := b1
  have e2 : |∫ x, h x * firstRiesz d s i (fun y => w y * D1 l (fun z => om z ^ 2) y) x| ≤ _ := b2
  calc _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12Near
