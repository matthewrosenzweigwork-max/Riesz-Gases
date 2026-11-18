import HRS.MS.UniqN0b
import HRS.MS.UniqN0c
import HRS.MS.Sf8

/-!
# N2a of `UniqPlan.md`, part (a): the kernel `κ = ∂_i g`, the regularised kernel `G_δ`, integration by parts

For `0 < s < d` and `i : Fin d` put `kap d s i z := rieszKernelGrad d s z i` (the force `∂_i g`).
This file proves the properties of `kap` needed for `S.B.8` (odd, smooth off `0`, measurable,
`|κ z| ≤ max 1 s ‖z‖^{-s-1}`), introduces the smooth regularisation `G_δ(z) = (‖z‖²+δ²)^{-s/2}` with
`∂_i G_δ = -s z_i (‖z‖²+δ²)^{-s/2-1}`, and proves the integration by parts
`∫ ∂_iG_δ(z) ψ(y-z) dz = ∫ G_δ(z) ∂_iψ(y-z) dz` for `ψ ∈ C¹_c`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN2a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqN0 HRS.MS.UniqM1

variable {d : ℕ}

/-- The force component `∂_i g`. -/
abbrev kap (d : ℕ) (s : ℝ) (i : Fin d) : Euc d → ℝ := fun z => rieszKernelGrad d s z i

theorem kap_neg (s : ℝ) (i : Fin d) (z : Euc d) : kap d s i (-z) = - kap d s i z := by
  simp [kap, HRS.Whole.Q09B.q09b_rkg_neg]

theorem kap_bound {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    |kap d s i z| ≤ max 1 s * ‖z‖ ^ (-s - 1) := by
  simp only [kap]; rw [n0_gradRK s i hz]; exact n0_qH_bound hs0 i hz

theorem kap_contDiffOn (s : ℝ) (i : Fin d) : ContDiffOn ℝ ∞ (kap d s i) {z | z ≠ 0} := by
  intro z hz
  exact (n0_qH_contDiffAt s i hz).contDiffWithinAt.congr (fun w hw => n0_gradRK s i hw)
    (n0_gradRK s i hz)

theorem kap_measurable (s : ℝ) (i : Fin d) : Measurable (kap d s i) := by
  have h1 : Measurable (fun z : Euc d => rieszKernelGrad d s z) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (rieszKernel d s))
  exact (EuclideanSpace.proj i).continuous.measurable.comp h1

theorem rieszKernel_of_ne {s : ℝ} (hs : s ≠ 0) (z : Euc d) : rieszKernel d s z = ‖z‖ ^ (-s) := by
  simp [rieszKernel, hs]

/-! ### The regularised kernel -/

/-- `G_δ(z) = (‖z‖²+δ²)^{-s/2}`. -/
def G (s δ : ℝ) (z : Euc d) : ℝ := (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2)

/-- `∂_i G_δ(z) = -s z_i (‖z‖²+δ²)^{-s/2-1}`. -/
def DG (s δ : ℝ) (i : Fin d) (z : Euc d) : ℝ := -s * z i * (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1)

theorem G_hasFDerivAt (s : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (z : Euc d) :
    HasFDerivAt (G s δ) ((-s / 2 * (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1)) • (2 • innerSL ℝ z)) z := by
  have hpos : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  have h1 : HasFDerivAt (fun z : Euc d => ‖z‖ ^ 2 + δ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const _
  have h2 : HasDerivAt (fun t : ℝ => t ^ (-s / 2)) ((-s / 2) * (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1))
      (‖z‖ ^ 2 + δ ^ 2) := Real.hasDerivAt_rpow_const (Or.inl hpos.ne')
  exact h2.comp_hasFDerivAt z h1

theorem G_fderiv_apply (s : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (i : Fin d) (z : Euc d) :
    fderiv ℝ (G s δ) z (EuclideanSpace.single i (1 : ℝ)) = DG s δ i z := by
  rw [(G_hasFDerivAt s hδ z).fderiv]
  simp [DG, innerSL_apply_apply, EuclideanSpace.inner_single_right]
  ring

theorem G_contDiff (s : ℝ) {δ : ℝ} (hδ : δ ≠ 0) : ContDiff ℝ 1 (G (d := d) s δ) := by
  unfold G
  exact ((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne (fun x => by positivity)

theorem G_continuous (s : ℝ) {δ : ℝ} (hδ : δ ≠ 0) : Continuous (G (d := d) s δ) :=
  (G_contDiff s hδ).continuous

theorem DG_continuous (s : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (i : Fin d) : Continuous (DG s δ i) := by
  have h : Continuous (fun z : Euc d => fderiv ℝ (G s δ) z (EuclideanSpace.single i (1 : ℝ))) :=
    ((G_contDiff s hδ).continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact h.congr (fun z => G_fderiv_apply s hδ i z)

theorem DG_neg (s δ : ℝ) (i : Fin d) (z : Euc d) : DG s δ i (-z) = - DG s δ i z := by
  simp [DG]

/-- Integration by parts for `G_δ` against `z ↦ ψ(y-z)`, `ψ ∈ C¹_c`. -/
theorem ibp_G (s : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (i : Fin d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (y : Euc d) :
    ∫ z, DG s δ i z * ψ (y - z) =
      ∫ z, G s δ z * fderiv ℝ ψ (y - z) (EuclideanSpace.single i (1 : ℝ)) := by
  set F : Euc d → ℝ := fun z => ψ (y - z) with hFdef
  have hF : ContDiff ℝ 1 F := hψ.comp (contDiff_const.sub contDiff_id)
  have hFc : HasCompactSupport F := hψc.comp_homeomorph (Homeomorph.subLeft y)
  have h := n0_ibp hF hFc (k := G s δ) (fun t _ => (G_contDiff s hδ).contDiffAt)
    (EuclideanSpace.single i (1 : ℝ))
  have hFd : ∀ t, fderiv ℝ F t (EuclideanSpace.single i (1 : ℝ)) =
      - fderiv ℝ ψ (y - t) (EuclideanSpace.single i (1 : ℝ)) := by
    intro t
    have hd : HasFDerivAt F ((fderiv ℝ ψ (y - t)).comp (0 - ContinuousLinearMap.id ℝ (Euc d))) t :=
      ((hψ.differentiable one_ne_zero) (y - t)).hasFDerivAt.comp t
        ((hasFDerivAt_const y t).sub (hasFDerivAt_id t))
    rw [hd.fderiv]
    simp
  simp only [hFd, G_fderiv_apply s hδ] at h
  simp only [mul_neg, integral_neg, neg_inj] at h
  exact h.symm

/-! ### Integrable majorants -/

/-- `‖z‖^{-(s+1)}` outside the unit ball. -/
def tailF (s : ℝ) (z : Euc d) : ℝ := if 1 ≤ ‖z‖ then ‖z‖ ^ (-(s + 1)) else 0

theorem tailF_nonneg (s : ℝ) (z : Euc d) : 0 ≤ tailF s z := by
  unfold tailF; split_ifs <;> positivity

theorem tailF_measurable (s : ℝ) : Measurable (tailF (d := d) s) := by
  unfold tailF
  exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
    (measurable_norm.pow_const _) measurable_const

theorem tailF_integrable {s : ℝ} (hs : (d : ℝ) < s + 1) : Integrable (tailF (d := d) s) := by
  have hκ0 : 0 ≤ s + 1 := le_trans (Nat.cast_nonneg d) hs.le
  have hi := (n0_decay_integrable (d := d) hs 0).const_mul (2 ^ (s + 1))
  refine hi.mono' (tailF_measurable s).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailF_nonneg s z)]
  unfold tailF
  split_ifs with h
  · have hz : 0 < ‖z‖ := by linarith
    have h1 : (2 * ‖z‖) ^ (-(s + 1)) ≤ (1 + ‖z - 0‖) ^ (-(s + 1)) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) (by simp; linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hz.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at h1
    have h3 : (0 : ℝ) < 2 ^ (s + 1) := by positivity
    calc ‖z‖ ^ (-(s + 1)) = 2 ^ (s + 1) * ((2 ^ (s + 1))⁻¹ * ‖z‖ ^ (-(s + 1))) := by
          field_simp
      _ ≤ _ := by gcongr
  · positivity

/-- The ball part `1_{B(0,1)} ‖z‖^{-s}`. -/
def ballF (s : ℝ) (z : Euc d) : ℝ := if ‖z‖ < 1 then ‖z‖ ^ (-s) else 0

theorem ballF_nonneg (s : ℝ) (z : Euc d) : 0 ≤ ballF s z := by
  unfold ballF; split_ifs <;> positivity

theorem ballF_integrable {s : ℝ} (hs0 : 0 < s) (hsd : s < d) : Integrable (ballF (d := d) s) := by
  have hloc := rieszKernel_locallyIntegrable (d := d) hs0.le hsd
  have h1 : IntegrableOn (rieszKernel d s) (ball (0 : Euc d) 1) :=
    (hloc.integrableOn_isCompact (isCompact_closedBall (0 : Euc d) 1)).mono_set ball_subset_closedBall
  have h2 := (integrable_indicator_iff (measurableSet_ball (x := (0 : Euc d)) (ε := 1))).2 h1
  refine h2.congr (Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ < 1
  · have : z ∈ ball (0 : Euc d) 1 := by simpa using hz
    simp [Set.indicator_of_mem this, ballF, hz, rieszKernel_of_ne hs0.ne']
  · have : z ∉ ball (0 : Euc d) 1 := by simpa using hz
    simp [Set.indicator_of_notMem this, ballF, hz]

/-- The majorant `‖z‖^{-s}` inside the unit ball, `‖z‖^{-s-1}` outside. -/
def Wf (s : ℝ) (z : Euc d) : ℝ := ballF s z + tailF s z

theorem Wf_nonneg (s : ℝ) (z : Euc d) : 0 ≤ Wf s z := add_nonneg (ballF_nonneg s z) (tailF_nonneg s z)

theorem Wf_integrable {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hs1 : (d : ℝ) < s + 1) :
    Integrable (Wf (d := d) s) := (ballF_integrable hs0 hsd).add (tailF_integrable hs1)

/-- Indicator of the unit ball is integrable. -/
theorem ind_ball_integrable : Integrable ((ball (0 : Euc d) 1).indicator (fun _ => (1 : ℝ))) := 
  (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)

/-- `DG` is integrable (for fixed `δ ≠ 0`). -/
theorem DG_integrable {s : ℝ} (hs0 : 0 < s) (hs1 : (d : ℝ) < s + 1) {δ : ℝ} (hδ : δ ≠ 0)
    (i : Fin d) : Integrable (DG s δ i) := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  set M : ℝ := s * (δ ^ 2) ^ (-s / 2 - 1) + s with hM
  have hM0 : 0 ≤ M := by positivity
  have hi := ((ind_ball_integrable (d := d)).const_mul M).add ((tailF_integrable hs1).const_mul M)
  refine hi.mono' (DG_continuous s hδ i).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  have hq : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  have hzi : |z i| ≤ ‖z‖ := n0_coord_le z i
  have hexp : 0 ≤ s / 2 + 1 := by positivity
  have habs : |DG s δ i z| = s * |z i| * (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1) := by
    unfold DG
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hs0, abs_of_pos (Real.rpow_pos_of_pos hq _)]
  rw [habs]
  by_cases h1 : ‖z‖ < 1
  · have hz : z ∈ ball (0 : Euc d) 1 := by simpa using h1
    rw [Set.indicator_of_mem hz]
    have : tailF s z = 0 := by unfold tailF; simp [not_le.2 h1]
    rw [this, mul_zero, add_zero, mul_one]
    have h2 : (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1) ≤ (δ ^ 2) ^ (-s / 2 - 1) :=
      Real.rpow_le_rpow_of_nonpos hδ2 (by nlinarith [sq_nonneg ‖z‖]) (by linarith)
    have h3 : |z i| ≤ 1 := hzi.trans h1.le
    have h4 : 0 ≤ (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1) := by positivity
    calc s * |z i| * (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1)
        ≤ s * 1 * (δ ^ 2) ^ (-s / 2 - 1) := by
          gcongr
      _ ≤ M := by rw [hM]; linarith
  · have hz : z ∉ ball (0 : Euc d) 1 := by simpa using h1
    rw [Set.indicator_of_notMem hz, mul_zero, zero_add]
    have h1' : 1 ≤ ‖z‖ := not_lt.1 h1
    have hzp : 0 < ‖z‖ := by linarith
    have h2 : (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1) ≤ (‖z‖ ^ 2) ^ (-s / 2 - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h5 : (‖z‖ ^ 2) ^ (-s / 2 - 1) = ‖z‖ ^ (-s - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hzp.le]; congr 1; push_cast; ring
    have h6 : ‖z‖ * ‖z‖ ^ (-s - 2) = ‖z‖ ^ (-(s + 1)) := by
      rw [← Real.rpow_one_add' hzp.le (by linarith)]; congr 1; ring
    have h4 : 0 ≤ (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1) := by positivity
    have h7 : tailF s z = ‖z‖ ^ (-(s + 1)) := by unfold tailF; simp [h1']
    rw [h7]
    calc s * |z i| * (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1)
        ≤ s * ‖z‖ * ‖z‖ ^ (-s - 2) := by
          rw [← h5] at *
          gcongr
      _ = s * ‖z‖ ^ (-(s + 1)) := by rw [mul_assoc, h6]
      _ ≤ M * ‖z‖ ^ (-(s + 1)) := by
          have : 0 ≤ ‖z‖ ^ (-(s + 1)) := by positivity
          have : 0 ≤ s * (δ ^ 2) ^ (-s / 2 - 1) := by positivity
          nlinarith

/-- `∫ DG = 0` by oddness. -/
theorem DG_integral_zero (s δ : ℝ) (i : Fin d) : ∫ z, DG s δ i z = 0 := by
  have h : ∫ z, DG s δ i (-z) = ∫ z, DG s δ i z := integral_neg_eq_self (fun z => DG s δ i z) volume
  simp only [DG_neg, integral_neg] at h
  linarith

end HRS.MS.UniqN2a
