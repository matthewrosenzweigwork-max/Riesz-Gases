import HRS.MS.FcauAux1
import HRS.MS.UniqN1aC
import HRS.MS.UniqN1cA
import HRS.MS.UniqC2c
import HRS.MH.DualityRdC1a
import HRS.MH.DualityRdB2Aux
import HRS.MS.UniqN2bA
import HRS.MS.UniqE1
import HRS.MS.UniqNDefs

/-!
# F-CAU, part 2: duality of the nonlocal term of the generator

`fcau_nonlocal_duality`: for `u ∈ C_b²`, `ψ ∈ C_c^∞` and a regular density `ρ'`,
`∫ ψ · (nonlocal term of generatorW along u) = nMain D ρ' u ψ`
(the nonlocal term of `forwardPairing`, with `kernelConvDeriv`).  The proof is the
cancellation-convention Fubini bridge: the kernel is truncated by an even smooth cutoff
`Φ_ε` (vanishing on `|z| ≤ ε`), Fubini is applied at fixed `ε`, and `∂_j g` is moved onto
`ψ` by integration by parts; the boundary layer `∫ ψ g ∂_jΦ_ε` vanishes as `ε → 0` by
oddness of `∂_jΦ_ε`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.Fcau

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqN1a HRS.MS.UniqT3
  HRS.MS.UniqN0

variable {d : ℕ}

/-! ### An even smooth cutoff -/

theorem fcau_fderiv_comp_neg {f : Euc d → ℝ} {z : Euc d} (hf : DifferentiableAt ℝ f (-z)) :
    fderiv ℝ (fun x => f (-x)) z = -fderiv ℝ f (-z) := by
  have h1 : HasFDerivAt (fun x : Euc d => -x) (-ContinuousLinearMap.id ℝ (Euc d)) z :=
    (hasFDerivAt_id z).neg
  have h2 := hf.hasFDerivAt.comp z h1
  have : (fderiv ℝ f (-z)).comp (-ContinuousLinearMap.id ℝ (Euc d)) = -fderiv ℝ f (-z) := by
    ext v; simp
  rw [this] at h2
  exact h2.fderiv

/-- The even cutoff `Φ_ε(z) = (n1aΦ ε z + n1aΦ ε (-z))/2`. -/
def fcauΦ (ε : ℝ) (z : Euc d) : ℝ := (n1aΦ ε z + n1aΦ ε (-z)) / 2

theorem fcauΦ_contDiff (ε : ℝ) : ContDiff ℝ ∞ (fcauΦ (d := d) ε) := by
  unfold fcauΦ
  exact ((n1aΦ_contDiff (d := d) ε).add ((n1aΦ_contDiff (d := d) ε).comp contDiff_neg)).div_const 2

theorem fcauΦ_even (ε : ℝ) (z : Euc d) : fcauΦ ε (-z) = fcauΦ ε z := by
  unfold fcauΦ; rw [neg_neg]; ring

theorem fcauΦ_zero {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : ‖z‖ ≤ ε) : fcauΦ ε z = 0 := by
  unfold fcauΦ
  rw [n1aΦ_zero hε hz, n1aΦ_zero hε (by simpa using hz)]; ring

theorem fcauΦ_one {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : 2 * ε ≤ ‖z‖) : fcauΦ ε z = 1 := by
  unfold fcauΦ
  rw [n1aΦ_one hε hz, n1aΦ_one hε (by simpa using hz)]; ring

theorem fcauΦ_nonneg (ε : ℝ) (z : Euc d) : 0 ≤ fcauΦ ε z := by
  unfold fcauΦ
  have := n1aΦ_nonneg (d := d) ε z
  have := n1aΦ_nonneg (d := d) ε (-z)
  linarith

theorem fcauΦ_le_one (ε : ℝ) (z : Euc d) : fcauΦ ε z ≤ 1 := by
  unfold fcauΦ
  have := n1aΦ_le_one (d := d) ε z
  have := n1aΦ_le_one (d := d) ε (-z)
  linarith

theorem fcauΦ_fderiv_bound {L : ℝ} (hL : ∀ w : Euc d, ‖fderiv ℝ (n1aBump d) w‖ ≤ L) {ε : ℝ}
    (hε : 0 < ε) (z : Euc d) : ‖fderiv ℝ (fcauΦ (d := d) ε) z‖ ≤ L * ε⁻¹ := by
  have h1 := n1aΦ_fderiv_bound hL hε z
  have h2 := n1aΦ_fderiv_bound hL hε (-z)
  have hd1 : DifferentiableAt ℝ (n1aΦ (d := d) ε) z :=
    ((n1aΦ_contDiff (d := d) ε).differentiable (by simp)) z
  have hd2 : DifferentiableAt ℝ (fun x : Euc d => n1aΦ (d := d) ε (-x)) z :=
    (((n1aΦ_contDiff (d := d) ε).differentiable (by simp)) (-z)).comp z differentiableAt_id.neg
  have hB : HasFDerivAt (fun x : Euc d => n1aΦ (d := d) ε (-x))
      (-fderiv ℝ (n1aΦ (d := d) ε) (-z)) z := by
    have := hd2.hasFDerivAt
    rwa [fcau_fderiv_comp_neg (((n1aΦ_contDiff (d := d) ε).differentiable (by simp)) (-z))] at this
  have hC := (hd1.hasFDerivAt.add hB).const_smul (2 : ℝ)⁻¹
  have hfun : fcauΦ (d := d) ε =
      fun x => (2 : ℝ)⁻¹ • (n1aΦ (d := d) ε x + n1aΦ (d := d) ε (-x)) := by
    funext x; simp only [fcauΦ, smul_eq_mul]; ring
  have e : fderiv ℝ (fcauΦ (d := d) ε) z =
      (2 : ℝ)⁻¹ • (fderiv ℝ (n1aΦ (d := d) ε) z + -fderiv ℝ (n1aΦ (d := d) ε) (-z)) := by
    rw [hfun]; exact hC.fderiv
  rw [e, norm_smul]
  have : ‖fderiv ℝ (n1aΦ (d := d) ε) z + -fderiv ℝ (n1aΦ (d := d) ε) (-z)‖ ≤ 2 * (L * ε⁻¹) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]; linarith
  have h0 : 0 ≤ L * ε⁻¹ := (norm_nonneg _).trans h1
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
  linarith

/-- The derivative of the even cutoff is odd. -/
theorem fcauΦ_fderiv_odd (ε : ℝ) (z : Euc d) :
    fderiv ℝ (fcauΦ (d := d) ε) (-z) = -fderiv ℝ (fcauΦ (d := d) ε) z := by
  have h : (fun x : Euc d => fcauΦ ε (-x)) = fcauΦ ε := funext (fcauΦ_even ε)
  have h1 := fcau_fderiv_comp_neg (f := fcauΦ (d := d) ε) (z := z)
    (((fcauΦ_contDiff (d := d) ε).differentiable (by simp)) (-z))
  rw [h] at h1
  rw [h1, neg_neg]

/-! ### The truncated kernel -/

section Core

open HRS.MP.RdGen HRS.MH.DualityRd

theorem fcau_G_neg (s : ℝ) (j : Fin d) {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s (-z) j = -rieszKernelGrad d s z j := by
  have hz' : -z ≠ 0 := neg_ne_zero.2 hz
  rw [movtr_rieszKernelGrad_eq s hz', movtr_rieszKernelGrad_eq s hz]
  simp [norm_neg]

/-- `|Φ_ε G_j| ≤ σ ε^{-s-1}`. -/
theorem fcau_PhiG_bound {s : ℝ} (hs0 : 0 ≤ s) (j : Fin d) {ε : ℝ} (hε : 0 < ε) (z : Euc d) :
    |fcauΦ ε z * rieszKernelGrad d s z j| ≤ movtr_sigma s * ε ^ (-s - 1) := by
  have hσ := rg_sigma_nonneg hs0
  by_cases hz : ‖z‖ ≤ ε
  · rw [fcauΦ_zero hε hz]; simp only [zero_mul, abs_zero]
    exact mul_nonneg hσ (Real.rpow_nonneg hε.le _)
  · push Not at hz
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz; linarith
    have h1 := (rgKerComp_ok (d := d) hs0 j).bound z hz0
    have h2 : ‖z‖ ^ (-s - 1) ≤ ε ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos hε hz.le (by linarith)
    rw [abs_mul, abs_of_nonneg (fcauΦ_nonneg ε z)]
    calc fcauΦ ε z * |rieszKernelGrad d s z j| ≤ 1 * (movtr_sigma s * ‖z‖ ^ (-s - 1)) :=
          mul_le_mul (fcauΦ_le_one ε z) h1 (abs_nonneg _) zero_le_one
      _ ≤ movtr_sigma s * ε ^ (-s - 1) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left h2 hσ

theorem fcau_G_meas (s : ℝ) (j : Fin d) : Measurable (fun z : Euc d => rieszKernelGrad d s z j) :=
  ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.measurable).comp
    (movtr_rieszKernelGrad_measurable (d := d) s)

theorem fcau_PhiG_meas (s : ℝ) (j : Fin d) (ε : ℝ) :
    Measurable (fun z : Euc d => fcauΦ ε z * rieszKernelGrad d s z j) :=
  ((fcauΦ_contDiff (d := d) ε).continuous.measurable).mul (fcau_G_meas s j)

/-- The odd function `1_{|z| ≤ 1/4} Φ_ε G_j` has integral zero. -/
theorem fcau_odd_integral (s : ℝ) (j : Fin d) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, (closedBall (0 : Euc d) (1 / 4)).indicator
      (fun z => fcauΦ ε z * rieszKernelGrad d s z j) z = 0 := by
  set om : Euc d → ℝ := fun z => (closedBall (0 : Euc d) (1 / 4)).indicator
      (fun z => fcauΦ ε z * rieszKernelGrad d s z j) z with hom
  have hodd : ∀ z, om (-z) = -om z := by
    intro z
    by_cases h1 : ‖z‖ ≤ 1 / 4
    · have m1 : z ∈ closedBall (0 : Euc d) (1 / 4) := by simpa using h1
      have m2 : -z ∈ closedBall (0 : Euc d) (1 / 4) := by simpa using h1
      simp only [hom, Set.indicator_of_mem m1, Set.indicator_of_mem m2]
      by_cases hz : z = 0
      · subst hz
        simp [fcauΦ_zero hε (show ‖(0 : Euc d)‖ ≤ ε by simpa using hε.le)]
      · rw [fcauΦ_even, fcau_G_neg s j hz]; ring
    · have m1 : z ∉ closedBall (0 : Euc d) (1 / 4) := by simpa using h1
      have m2 : -z ∉ closedBall (0 : Euc d) (1 / 4) := by simpa using h1
      simp only [hom, Set.indicator_of_notMem m1, Set.indicator_of_notMem m2, neg_zero]
  have h := integral_neg_eq_self om (volume : Measure (Euc d))
  have h2 : ∫ z, om (-z) = -∫ z, om z := by
    simp_rw [hodd]; rw [integral_neg]
  linarith

/-- Insertion of the cancellation subtraction: for the even truncation the subtraction integrates to `0`. -/
theorem fcau_trunc_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (j : Fin d) {h : Euc d → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hh : RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c h) {ε : ℝ}
    (hε : 0 < ε) (x : Euc d) :
    ∫ z, fcauΦ ε z * (rieszKernelGrad d s z j * movtr_R h x z) =
      ∫ z, fcauΦ ε z * rieszKernelGrad d s z j * h (x - z) := by
  obtain ⟨hdiff, hcont, h0, h1, hb⟩ := dc1a_rgW_facts hc hh
  have hw : Integrable (fun z : Euc d => (1 + ‖x - z‖) ^ (-((d : ℝ) + 1))) :=
    (rg_W_integrable hd).comp_sub_left x
  set σε : ℝ := movtr_sigma s * ε ^ (-s - 1) with hσε
  have hI1 : Integrable (fun z => fcauΦ ε z * rieszKernelGrad d s z j * h (x - z)) := by
    refine Integrable.mono' (hw.const_mul (σε * c)) ?_ (Eventually.of_forall fun z => ?_)
    · exact ((fcau_PhiG_meas s j ε).mul
        (hcont.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      calc |fcauΦ ε z * rieszKernelGrad d s z j| * ‖h (x - z)‖
          ≤ σε * (c * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1))) :=
            mul_le_mul (fcau_PhiG_bound hs0 j hε z) (h0 _) (norm_nonneg _)
              (mul_nonneg (rg_sigma_nonneg hs0) (Real.rpow_nonneg hε.le _))
        _ = σε * c * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1)) := by ring
  have hI2 : Integrable (fun z => (closedBall (0 : Euc d) (1 / 4)).indicator
      (fun z => fcauΦ ε z * rieszKernelGrad d s z j) z * h x) := by
    refine Integrable.mul_const ?_ _
    rw [integrable_indicator_iff measurableSet_closedBall]
    refine Measure.integrableOn_of_bounded (M := σε) measure_closedBall_lt_top.ne
      (fcau_PhiG_meas s j ε).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    exact fcau_PhiG_bound hs0 j hε z
  have hsplit : ∀ z : Euc d, fcauΦ ε z * (rieszKernelGrad d s z j * movtr_R h x z) =
      fcauΦ ε z * rieszKernelGrad d s z j * h (x - z) -
        (closedBall (0 : Euc d) (1 / 4)).indicator
          (fun z => fcauΦ ε z * rieszKernelGrad d s z j) z * h x := by
    intro z
    unfold movtr_R
    by_cases hz : ‖z‖ ≤ 1 / 4
    · have : z ∈ closedBall (0 : Euc d) (1 / 4) := by simpa using hz
      simp only [hz, ite_true, Set.indicator_of_mem this]; ring
    · have : z ∉ closedBall (0 : Euc d) (1 / 4) := by simpa using hz
      simp only [hz, ite_false, Set.indicator_of_notMem this]; ring
  simp_rw [hsplit]
  rw [integral_sub hI1 hI2, integral_mul_const, fcau_odd_integral s j hε]
  simp

/-- The pointwise majorant of the cancellation-convention integrand. -/
theorem fcau_dom (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (j : Fin d) {h : Euc d → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hh : RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c h) (ε : ℝ)
    (x z : Euc d) (hz : z ≠ 0) :
    ‖fcauΦ ε z * (rieszKernelGrad d s z j * movtr_R h x z)‖ ≤ rgMaj d s (movtr_sigma s) c c x z := by
  obtain ⟨hdiff, hcont, h0, h1, hb⟩ := dc1a_rgW_facts hc hh
  have := rg_norm_le hs0 (rgKerComp_ok (d := d) hs0 j) hdiff hc hc h0 h1 x z hz
  rw [norm_mul]
  calc ‖fcauΦ ε z‖ * ‖rieszKernelGrad d s z j * movtr_R h x z‖
      ≤ 1 * ‖rieszKernelGrad d s z j * movtr_R h x z‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg (fcauΦ_nonneg ε z)]; exact fcauΦ_le_one ε z
    _ ≤ _ := by
        rw [one_mul]
        simpa [smul_eq_mul, rg_movtr_R_eq] using this

theorem fcau_trunc_meas (s : ℝ) (j : Fin d) {h : Euc d → ℝ} (hcont : Continuous h) (ε : ℝ)
    (x : Euc d) :
    Measurable (fun z => fcauΦ ε z * (rieszKernelGrad d s z j * movtr_R h x z)) := by
  have hR : Measurable (fun z : Euc d => movtr_R h x z) := by
    unfold movtr_R
    exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
      ((hcont.measurable.comp (measurable_const.sub measurable_id)).sub measurable_const)
      (hcont.measurable.comp (measurable_const.sub measurable_id))
  exact ((fcauΦ_contDiff (d := d) ε).continuous.measurable).mul ((fcau_G_meas s j).mul hR)

/-- Uniform bound of the truncated integrals. -/
theorem fcau_trunc_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d)
    {h : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hh : RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c h) (ε : ℝ) (x : Euc d) :
    |∫ z, fcauΦ ε z * (rieszKernelGrad d s z j * movtr_R h x z)| ≤
      movtr_sigma s * (c * rgNear d s + 4 ^ (s + 1) * c * rgW d) := by
  obtain ⟨hdiff, hcont, h0, h1, hb⟩ := dc1a_rgW_facts hc hh
  rw [← rg_integral_maj hd hsd (movtr_sigma s) c c x, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (rg_maj_integrable hd hsd (movtr_sigma s) c c x) ?_
  filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
  exact fcau_dom hd hs0 j hc hh ε x z hz

/-- Pointwise convergence of the truncated integrals to the cancellation-convention integral. -/
theorem fcau_trunc_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d)
    {h : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hh : RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c h) (x : Euc d) :
    Tendsto (fun ε : ℝ => ∫ z, fcauΦ ε z * (rieszKernelGrad d s z j * movtr_R h x z))
      (𝓝[>] 0) (𝓝 (∫ z, rieszKernelGrad d s z j * movtr_R h x z)) := by
  obtain ⟨hdiff, hcont, h0, h1, hb⟩ := dc1a_rgW_facts hc hh
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => rgMaj d s (movtr_sigma s) c c x z) ?_ ?_
    (rg_maj_integrable hd hsd (movtr_sigma s) c c x) ?_
  · exact Eventually.of_forall fun ε => (fcau_trunc_meas s j hcont ε x).aestronglyMeasurable
  · refine Eventually.of_forall fun ε => ?_
    filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
    exact fcau_dom hd hs0 j hc hh ε x z hz
  · filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖z‖ / 2 by positivity)] with ε hε
    rw [fcauΦ_one hε.1 (by linarith [hε.2]), one_mul]

/-- Fubini at fixed `ε`: the truncated convolution against `ψ` moves onto `ψ`. -/
theorem fcau_swap (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (j : Fin d) {h : Euc d → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hh : RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c h) {ψ : Euc d → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, ψ x * (∫ z, fcauΦ ε z * rieszKernelGrad d s z j * h (x - z)) =
      ∫ y, h y * ∫ x, ψ x * (fcauΦ ε (x - y) * rieszKernelGrad d s (x - y) j) := by
  obtain ⟨hdiff, hcont, h0, h1, hb⟩ := dc1a_rgW_facts hc hh
  set PG : Euc d → ℝ := fun w => fcauΦ ε w * rieszKernelGrad d s w j with hPG
  have hh1 : Integrable h volume := by
    refine Integrable.mono' ((rg_W_integrable hd).const_mul c) hcont.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simpa [mul_comm] using h0 y
  have hψ1 : Integrable ψ volume := hψ.integrable_of_hasCompactSupport hψc
  have e1 : ∀ x : Euc d, ∫ z, fcauΦ ε z * rieszKernelGrad d s z j * h (x - z) =
      ∫ y, PG (x - y) * h y := by
    intro x
    have := integral_sub_left_eq_self (fun z : Euc d => PG z * h (x - z)) (volume : Measure (Euc d)) x
    simp only [sub_sub_cancel] at this
    rw [this]
  simp_rw [e1]
  have hFi : Integrable (fun p : Euc d × Euc d => ψ p.1 * (PG (p.1 - p.2) * h p.2))
      (volume.prod volume) := by
    have hprod := (hψ1.norm.const_mul (movtr_sigma s * ε ^ (-s - 1))).mul_prod hh1.norm
    refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (hψ.measurable.comp measurable_fst).mul
        (((fcau_PhiG_meas s j ε).comp (measurable_fst.sub measurable_snd)).mul
          (hcont.measurable.comp measurable_snd)) |>.aestronglyMeasurable
    · rw [norm_mul, norm_mul]
      show ‖ψ p.1‖ * (‖PG (p.1 - p.2)‖ * ‖h p.2‖) ≤ (movtr_sigma s * ε ^ (-s - 1) * ‖ψ p.1‖) * ‖h p.2‖
      have hb := fcau_PhiG_bound hs0 j hε (p.1 - p.2)
      rw [Real.norm_eq_abs (PG (p.1 - p.2))]
      calc ‖ψ p.1‖ * (|PG (p.1 - p.2)| * ‖h p.2‖)
          ≤ ‖ψ p.1‖ * ((movtr_sigma s * ε ^ (-s - 1)) * ‖h p.2‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
  have hswap := integral_integral_swap (μ := volume) (ν := volume)
    (f := fun x y => ψ x * (PG (x - y) * h y)) hFi
  calc ∫ x, ψ x * ∫ y, PG (x - y) * h y
      = ∫ x, ∫ y, ψ x * (PG (x - y) * h y) := by
        congr 1; funext x; rw [integral_const_mul]
    _ = ∫ y, ∫ x, ψ x * (PG (x - y) * h y) := hswap
    _ = ∫ y, h y * ∫ x, ψ x * PG (x - y) := by
        congr 1; funext y
        rw [← integral_const_mul]
        congr 1; funext x; ring

/-- The product `Φ_ε(· - y) g(· - y)` is `C¹` (it vanishes near `y`). -/
theorem fcau_k_contDiffAt (s : ℝ) {ε : ℝ} (hε : 0 < ε) (y t : Euc d) :
    ContDiffAt ℝ 1 (fun x => fcauΦ ε (x - y) * rieszKernel d s (x - y)) t := by
  by_cases ht : t = y
  · subst ht
    have : (fun x : Euc d => fcauΦ ε (x - t) * rieszKernel d s (x - t)) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds t hε] with x hx
      rw [fcauΦ_zero hε (by rw [mem_ball_iff_norm] at hx; exact hx.le), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have h1 : ContDiffAt ℝ 1 (fun x : Euc d => fcauΦ ε (x - y)) t :=
      (((fcauΦ_contDiff (d := d) ε).of_le (by exact_mod_cast le_top)).contDiffAt).comp t
        (contDiffAt_id.sub contDiffAt_const)
    have hne : t - y ≠ 0 := sub_ne_zero.2 ht
    have h2 : ContDiffAt ℝ 1 (fun x : Euc d => rieszKernel d s (x - y)) t :=
      (n0_g_contDiffAt s hne).comp t (contDiffAt_id.sub contDiffAt_const)
    exact h1.mul h2

/-- The derivative of `k = Φ_ε(· - y) g(· - y)` in direction `e_j`. -/
theorem fcau_k_fderiv (s : ℝ) (j : Fin d) {ε : ℝ} (hε : 0 < ε) (y t : Euc d) :
    fderiv ℝ (fun x => fcauΦ ε (x - y) * rieszKernel d s (x - y)) t (EuclideanSpace.single j 1) =
      fderiv ℝ (fcauΦ ε) (t - y) (EuclideanSpace.single j 1) * rieszKernel d s (t - y) +
        fcauΦ ε (t - y) * rieszKernelGrad d s (t - y) j := by
  by_cases ht : t = y
  · subst ht
    have h0 : (fun x : Euc d => fcauΦ ε (x - t) * rieszKernel d s (x - t)) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds t hε] with x hx
      rw [fcauΦ_zero hε (by rw [mem_ball_iff_norm] at hx; exact hx.le), zero_mul]
    have h1 : fderiv ℝ (fun x : Euc d => fcauΦ ε (x - t) * rieszKernel d s (x - t)) t = 0 := by
      rw [h0.fderiv_eq]; simp
    have h2 : fderiv ℝ (fcauΦ (d := d) ε) 0 = 0 := by
      have : (fcauΦ (d := d) ε) =ᶠ[𝓝 0] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : Euc d) hε] with x hx
        exact fcauΦ_zero hε (by rw [mem_ball_zero_iff] at hx; exact hx.le)
      rw [this.fderiv_eq]; simp
    rw [h1, sub_self, h2, fcauΦ_zero hε (by simpa using hε.le)]
    simp
  · have hne : t - y ≠ 0 := sub_ne_zero.2 ht
    have hΦ : HasFDerivAt (fun x : Euc d => fcauΦ ε (x - y)) (fderiv ℝ (fcauΦ (d := d) ε) (t - y)) t := by
      have := (((fcauΦ_contDiff (d := d) ε).differentiable (by simp)) (t - y)).hasFDerivAt.comp t
        ((hasFDerivAt_id t).sub_const y)
      simpa [Function.comp_def] using this
    have hg : HasFDerivAt (fun x : Euc d => rieszKernel d s (x - y))
        (fderiv ℝ (rieszKernel d s) (t - y)) t := by
      have := (((n0_g_contDiffAt s hne).differentiableAt one_ne_zero)).hasFDerivAt.comp t
        ((hasFDerivAt_id t).sub_const y)
      simpa [Function.comp_def] using this
    have hm : HasFDerivAt (fun x : Euc d => fcauΦ ε (x - y) * rieszKernel d s (x - y)) _ t := hΦ.mul hg
    rw [hm.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    unfold rieszKernelGrad
    rw [q09_gradient_apply]
    ring

/-- Integration by parts at fixed `ε` and `y`. -/
theorem fcau_ibp_eps {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) (y : Euc d) :
    ∫ x, ψ x * (fcauΦ ε (x - y) * rieszKernelGrad d s (x - y) j) =
      -(∫ x, D1 j ψ x * (fcauΦ ε (x - y) * rieszKernel d s (x - y))) -
        ∫ x, ψ x * (rieszKernel d s (x - y) *
          fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j 1)) := by
  have key := n0_ibp hψ hψc (k := fun x => fcauΦ ε (x - y) * rieszKernel d s (x - y))
    (fun t _ => fcau_k_contDiffAt s hε y t) (EuclideanSpace.single j (1 : ℝ))
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hDΦc : Continuous (fun x : Euc d =>
      fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j (1 : ℝ))) :=
    (((fcauΦ_contDiff (d := d) ε).continuous_fderiv (by simp)).comp
      (continuous_id.sub continuous_const)).clm_apply continuous_const
  have hIa : Integrable (fun x : Euc d => ψ x * (rieszKernel d s (x - y) *
      fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j (1 : ℝ)))) volume := by
    have := n1a_conv_integrable (d := d) hl
      (h := fun x : Euc d => ψ x * fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j (1 : ℝ)))
      (hψ.continuous.mul hDΦc) (hψc.mul_right) y
    refine this.congr (Eventually.of_forall fun x => ?_)
    have e : rieszKernel d s (y - x) = rieszKernel d s (x - y) := by
      rw [← neg_sub, rieszKernel_neg]
    simp only [e]; ring
  have hIb : Integrable (fun x : Euc d => ψ x * (fcauΦ ε (x - y) * rieszKernelGrad d s (x - y) j))
      volume := by
    have hψ1 : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
    refine Integrable.mono' (hψ1.norm.const_mul (movtr_sigma s * ε ^ (-s - 1))) ?_
      (Eventually.of_forall fun x => ?_)
    · exact (hψ.continuous.measurable.mul
        ((fcau_PhiG_meas s j ε).comp (measurable_id.sub measurable_const))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs (fcauΦ ε (x - y) * rieszKernelGrad d s (x - y) j)]
      have := fcau_PhiG_bound hs0 j hε (x - y)
      calc ‖ψ x‖ * |fcauΦ ε (x - y) * rieszKernelGrad d s (x - y) j|
          ≤ ‖ψ x‖ * (movtr_sigma s * ε ^ (-s - 1)) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = _ := by ring
  have hfd : ∀ t : Euc d, fderiv ℝ (fun x => fcauΦ ε (x - y) * rieszKernel d s (x - y)) t
        (EuclideanSpace.single j (1 : ℝ)) * ψ t =
      ψ t * (rieszKernel d s (t - y) *
          fderiv ℝ (fcauΦ (d := d) ε) (t - y) (EuclideanSpace.single j (1 : ℝ))) +
        ψ t * (fcauΦ ε (t - y) * rieszKernelGrad d s (t - y) j) := by
    intro t
    rw [fcau_k_fderiv s j hε y t]; ring
  have h2 : ∫ t, fderiv ℝ (fun x => fcauΦ ε (x - y) * rieszKernel d s (x - y)) t
        (EuclideanSpace.single j (1 : ℝ)) * ψ t =
      (∫ x, ψ x * (rieszKernel d s (x - y) *
          fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j (1 : ℝ)))) +
        ∫ x, ψ x * (fcauΦ ε (x - y) * rieszKernelGrad d s (x - y) j) := by
    simp_rw [hfd]
    exact integral_add hIa hIb
  rw [h2] at key
  have h3 : ∫ t, (fcauΦ ε (t - y) * rieszKernel d s (t - y)) *
      fderiv ℝ ψ t (EuclideanSpace.single j (1 : ℝ)) =
      ∫ x, D1 j ψ x * (fcauΦ ε (x - y) * rieszKernel d s (x - y)) := by
    congr 1; funext x; simp only [D1]; ring
  simp only at key
  rw [h3] at key
  linarith

/-! ### The limit `ε → 0` -/

/-- `K_ε → K = kernelConvDeriv` pointwise. -/
theorem fcau_K_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (y : Euc d) :
    Tendsto (fun ε : ℝ => ∫ x, D1 j ψ x * (fcauΦ ε (x - y) * rieszKernel d s (x - y)))
      (𝓝[>] 0) (𝓝 (kernelConvDeriv d s j ψ y)) := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hDc : Continuous (D1 j ψ) := (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDcs : HasCompactSupport (D1 j ψ) := D1_supp hψc j
  have hI := n1a_conv_integrable hl hDc hDcs y
  have e : ∀ x : Euc d, rieszKernel d s (y - x) = rieszKernel d s (x - y) := fun x => by
    rw [← neg_sub, rieszKernel_neg]
  have hK : kernelConvDeriv d s j ψ y = ∫ x, D1 j ψ x * rieszKernel d s (x - y) := by
    unfold kernelConvDeriv
    congr 1; funext x; simp only [e, D1]; ring
  rw [hK]
  have hI' : Integrable (fun x => D1 j ψ x * rieszKernel d s (x - y)) volume :=
    hI.congr (Eventually.of_forall fun x => by simp only [e]; ring)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖D1 j ψ x * rieszKernel d s (x - y)‖) ?_ ?_ hI'.norm ?_
  · refine Eventually.of_forall fun ε => ?_
    exact (hDc.measurable.mul (((fcauΦ_contDiff (d := d) ε).continuous.measurable.comp
      (measurable_id.sub measurable_const)).mul
      ((g_meas (d := d) s).comp (measurable_id.sub measurable_const))))
      |>.aestronglyMeasurable
  · refine Eventually.of_forall fun ε => Eventually.of_forall fun x => ?_
    have : D1 j ψ x * (fcauΦ ε (x - y) * rieszKernel d s (x - y)) =
        fcauΦ ε (x - y) * (D1 j ψ x * rieszKernel d s (x - y)) := by ring
    rw [this, norm_mul, Real.norm_eq_abs, abs_of_nonneg (fcauΦ_nonneg ε _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (fcauΦ_le_one ε _)
  · filter_upwards [HRS.MH.Screened.k3_ae_ne hd y] with x hx
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖x - y‖ / 2 by positivity)] with ε hε
    rw [fcauΦ_one hε.1 (by linarith [hε.2]), one_mul]

/-- Support, size and oddness of the directional derivative of `Φ_ε`. -/
theorem fcau_Dj_facts (j : Fin d) {L : ℝ} (hL : ∀ w : Euc d, ‖fderiv ℝ (n1aBump d) w‖ ≤ L) {ε : ℝ}
    (hε : 0 < ε) :
    (∀ w : Euc d, 2 * ε < ‖w‖ → fderiv ℝ (fcauΦ (d := d) ε) w (EuclideanSpace.single j 1) = 0) ∧
    (∀ w : Euc d, |fderiv ℝ (fcauΦ (d := d) ε) w (EuclideanSpace.single j 1)| ≤ L * ε⁻¹) ∧
    (∀ w : Euc d, fderiv ℝ (fcauΦ (d := d) ε) (-w) (EuclideanSpace.single j 1) =
      -fderiv ℝ (fcauΦ (d := d) ε) w (EuclideanSpace.single j 1)) := by
  refine ⟨fun w hw => ?_, fun w => ?_, fun w => ?_⟩
  · have : (fcauΦ (d := d) ε) =ᶠ[𝓝 w] fun _ => 1 := by
      have hopen : IsOpen {v : Euc d | 2 * ε < ‖v‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact fcauΦ_one hε hv.le
    rw [this.fderiv_eq]; simp
  · have h1 := fcauΦ_fderiv_bound hL hε w
    calc |fderiv ℝ (fcauΦ (d := d) ε) w (EuclideanSpace.single j 1)|
        = ‖fderiv ℝ (fcauΦ (d := d) ε) w (EuclideanSpace.single j 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fcauΦ (d := d) ε) w‖ * ‖(EuclideanSpace.single j 1 : Euc d)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ε⁻¹ := by
          rw [EuclideanSpace.norm_single]; simpa using h1
  · rw [fcauΦ_fderiv_odd]; simp

/-- The boundary layer is small, uniformly in `y`. -/
theorem fcau_R_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) {ψ : Euc d → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {L Lψ : ℝ}
    (hL : ∀ w : Euc d, ‖fderiv ℝ (n1aBump d) w‖ ≤ L) (hLψ0 : 0 ≤ Lψ)
    (hLψ : ∀ x y, |ψ x - ψ y| ≤ Lψ * ‖x - y‖)
    {ε : ℝ} (hε : 0 < ε) (y : Euc d) :
    |∫ x, ψ x * (rieszKernel d s (x - y) *
        fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j 1))| ≤
      2 * L * Lψ * ∫ w, (closedBall (0 : Euc d) (2 * ε)).indicator
        (fun w => |rieszKernel d s w|) w := by
  obtain ⟨hsupp, hbd, hodd⟩ := fcau_Dj_facts j hL hε
  set Dj : Euc d → ℝ := fun w => fderiv ℝ (fcauΦ (d := d) ε) w (EuclideanSpace.single j 1) with hDj
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hDc : Continuous Dj :=
    ((fcauΦ_contDiff (d := d) ε).continuous_fderiv (by simp)).clm_apply continuous_const
  have hDcs : HasCompactSupport Dj := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) (2 * ε)) ?_
    intro w hw
    rw [mem_closedBall_zero_iff]
    by_contra hcon
    exact hw (hsupp w (not_le.1 hcon))
  -- substitution `x = w + y`
  have hsub : ∫ x, ψ x * (rieszKernel d s (x - y) * Dj (x - y)) =
      ∫ w, ψ (w + y) * (rieszKernel d s w * Dj w) := by
    have := integral_sub_right_eq_self (μ := (volume : Measure (Euc d)))
      (fun w : Euc d => ψ (w + y) * (rieszKernel d s w * Dj w)) y
    simp only [sub_add_cancel] at this
    exact this
  have hgD : Integrable (fun w => rieszKernel d s w * Dj w) volume := by
    have := hl.integrable_smul_right_of_hasCompactSupport hDc hDcs
    simpa [smul_eq_mul] using this
  have hgψD : Integrable (fun w => ψ (w + y) * (rieszKernel d s w * Dj w)) volume := by
    have := hl.integrable_smul_right_of_hasCompactSupport (g := fun w => ψ (w + y) * Dj w)
      ((hψ.comp (continuous_id.add continuous_const)).mul hDc) (hDcs.mul_left)
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp only [smul_eq_mul]; ring
  have hzero : ∫ w, rieszKernel d s w * Dj w = 0 := by
    have h1 := integral_neg_eq_self (fun w : Euc d => rieszKernel d s w * Dj w) (volume : Measure (Euc d))
    have h2 : ∫ w, rieszKernel d s (-w) * Dj (-w) = -∫ w, rieszKernel d s w * Dj w := by
      simp_rw [rieszKernel_neg, hDj, hodd]
      simp only [mul_neg]
      rw [integral_neg]
    linarith
  have hcenter : ∫ w, ψ (w + y) * (rieszKernel d s w * Dj w) =
      ∫ w, (ψ (w + y) - ψ y) * (rieszKernel d s w * Dj w) := by
    simp_rw [sub_mul]
    rw [integral_sub hgψD (hgD.const_mul (ψ y)), integral_const_mul, hzero]
    simp
  rw [hsub, hcenter]
  have hind : Integrable ((closedBall (0 : Euc d) (2 * ε)).indicator (fun w => |rieszKernel d s w|))
      volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (hl.integrableOn_isCompact (isCompact_closedBall (0 : Euc d) (2 * ε))).abs
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hind.const_mul _) (Eventually.of_forall fun w => ?_)
  by_cases hw : ‖w‖ ≤ 2 * ε
  · have hm : w ∈ closedBall (0 : Euc d) (2 * ε) := by simpa using hw
    rw [Set.indicator_of_mem hm, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have h1 : |ψ (w + y) - ψ y| ≤ Lψ * (2 * ε) := by
      have := hLψ (w + y) y
      simp only [add_sub_cancel_right] at this
      exact this.trans (mul_le_mul_of_nonneg_left hw hLψ0)
    have h2 := hbd w
    calc |ψ (w + y) - ψ y| * (|rieszKernel d s w| * |Dj w|)
        ≤ (Lψ * (2 * ε)) * (|rieszKernel d s w| * (L * ε⁻¹)) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) (by positivity)
            (by positivity)
      _ = 2 * L * Lψ * |rieszKernel d s w| := by field_simp
  · push Not at hw
    have hm : w ∉ closedBall (0 : Euc d) (2 * ε) := by simpa using hw
    have hD0 : Dj w = 0 := hsupp w hw
    rw [Set.indicator_of_notMem hm, hD0]
    simp

/-- `∫_{B(0,2ε)} |g| → 0`, and it is bounded by `∫_{B(0,1)} |g|` for `ε ≤ 1/2`. -/
theorem fcau_g_small (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Tendsto (fun ε : ℝ => ∫ w, (closedBall (0 : Euc d) (2 * ε)).indicator
      (fun w => |rieszKernel d s w|) w) (𝓝[>] 0) (𝓝 0) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∫ w, (closedBall (0 : Euc d) (2 * ε)).indicator
      (fun w => |rieszKernel d s w|) w ≤ ∫ w, (closedBall (0 : Euc d) 1).indicator
      (fun w => |rieszKernel d s w|) w := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hint : ∀ r : ℝ, Integrable ((closedBall (0 : Euc d) r).indicator
      (fun w => |rieszKernel d s w|)) volume := fun r => by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (hl.integrableOn_isCompact (isCompact_closedBall (0 : Euc d) r)).abs
  have hnn : ∀ (r : ℝ) (w : Euc d), 0 ≤ (closedBall (0 : Euc d) r).indicator
      (fun w => |rieszKernel d s w|) w := fun r w =>
    Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
  have hmono : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ w : Euc d,
      (closedBall (0 : Euc d) (2 * ε)).indicator (fun w => |rieszKernel d s w|) w ≤
        (closedBall (0 : Euc d) 1).indicator (fun w => |rieszKernel d s w|) w := by
    intro ε hε hε2 w
    by_cases hw : w ∈ closedBall (0 : Euc d) (2 * ε)
    · have hw' : w ∈ closedBall (0 : Euc d) 1 :=
        closedBall_subset_closedBall (by linarith) hw
      rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw']
    · rw [Set.indicator_of_notMem hw]; exact hnn _ _
  refine ⟨?_, fun ε hε hε2 => ?_⟩
  · have := tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (Euc d))) (l := 𝓝[>] (0 : ℝ))
      (F := fun (ε : ℝ) (w : Euc d) => (closedBall (0 : Euc d) (2 * ε)).indicator
        (fun w => |rieszKernel d s w|) w)
      (f := fun _ => 0)
      (fun w => (closedBall (0 : Euc d) 1).indicator (fun w => |rieszKernel d s w|) w)
      ?_ ?_ (hint 1) ?_
    · simpa using this
    · refine Eventually.of_forall fun ε => ?_
      exact (hint (2 * ε)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      refine Eventually.of_forall fun w => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn _ _)]
      exact hmono ε hε.1 hε.2.le w
    · filter_upwards [HRS.MH.Screened.k3_ae_ne hd (0 : Euc d)] with w hw
      have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖w‖ / 2 by positivity)] with ε hε
      have : w ∉ closedBall (0 : Euc d) (2 * ε) := by
        rw [mem_closedBall_zero_iff]; push Not; linarith [hε.2]
      rw [Set.indicator_of_notMem this]
  · exact integral_mono (hint _) (hint _) (hmono ε hε hε2)

/-- Joint measurability of the cancellation difference. -/
theorem fcau_movtrR_meas {h : Euc d → ℝ} (hcont : Continuous h) :
    Measurable (fun p : Euc d × Euc d => movtr_R h p.1 p.2) := by
  unfold movtr_R
  exact Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_const)
    ((hcont.measurable.comp (measurable_fst.sub measurable_snd)).sub
      (hcont.measurable.comp measurable_fst))
    (hcont.measurable.comp (measurable_fst.sub measurable_snd))

/-- **The cancellation-convention Fubini bridge.**  For `h` in the weighted `C¹` class with
`‖y‖ h(y)` integrable and `ψ ∈ C_c¹`:
`∫ ψ · (∇g ⋆ h)_j = - ∫ h · kernelConvDeriv_j ψ`. -/
theorem fcau_core (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) {h : Euc d → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (hh : RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c h)
    (hh2 : Integrable (fun y : Euc d => ‖y‖ * h y) volume) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, ψ x * (convGradConvW (rieszKernelGrad d s) h x) j =
      -∫ y, h y * kernelConvDeriv d s j ψ y := by
  obtain ⟨hdiff, hcont, h0, h1, hb⟩ := dc1a_rgW_facts hc hh
  have hψcont : Continuous ψ := hψ.continuous
  have hψ1 : Integrable ψ volume := hψcont.integrable_of_hasCompactSupport hψc
  have hh1 : Integrable h volume := by
    refine Integrable.mono' ((rg_W_integrable hd).const_mul c) hcont.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simpa [mul_comm] using h0 y
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hDc : Continuous (D1 j ψ) := (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDcs : HasCompactSupport (D1 j ψ) := D1_supp hψc j
  obtain ⟨L, hL0, hL⟩ := n1a_bump_fderiv_bound (d := d)
  obtain ⟨Lψ', hLψ'⟩ := hψ.lipschitzWith_of_hasCompactSupport hψc one_ne_zero
  set Lψ : ℝ := (Lψ' : ℝ) with hLψdef
  have hLψ0 : 0 ≤ Lψ := Lψ'.2
  have hLψ : ∀ x y, |ψ x - ψ y| ≤ Lψ * ‖x - y‖ := fun x y => by
    have := hLψ'.dist_le_mul x y
    simpa [Real.dist_eq, dist_eq_norm] using this
  obtain ⟨hsmall, hsmall2⟩ := fcau_g_small hd hs0 hsd (d := d)
  set Cg : ℝ := ∫ w, (closedBall (0 : Euc d) 1).indicator (fun w => |rieszKernel d s w|) w with hCg
  -- the pair integrability
  have hpair := n0_pair_integrable (d := d) hs0 hsd hDc hDcs hcont hh1 hh2
  have hKbar : Integrable (fun y : Euc d => ‖h y‖ * ∫ x, ‖D1 j ψ x * rieszKernel d s (x - y)‖) volume := by
    have := hpair.integral_norm_prod_right
    refine this.congr (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [mul_comm, ← integral_mul_const]
    congr 1; funext x
    simp only [norm_mul]
    ring
  have hconv : ∀ y : Euc d, Integrable (fun x => D1 j ψ x * rieszKernel d s (x - y)) volume := by
    intro y
    have e : ∀ x : Euc d, rieszKernel d s (y - x) = rieszKernel d s (x - y) := fun x => by
      rw [← neg_sub, rieszKernel_neg]
    exact (n1a_conv_integrable hl hDc hDcs y).congr
      (Eventually.of_forall fun x => by simp only [e]; ring)
  set G : Euc d → ℝ := fun z => rieszKernelGrad d s z j with hG
  -- the truncated integrals
  set T : ℝ → ℝ := fun ε => ∫ x, ψ x * ∫ z, fcauΦ ε z * (G z * movtr_R h x z) with hT
  set Bd : ℝ := movtr_sigma s * (c * rgNear d s + 4 ^ (s + 1) * c * rgW d) with hBd
  have hT1 : Tendsto T (𝓝[>] 0) (𝓝 (∫ x, ψ x * (convGradConvW (rieszKernelGrad d s) h x) j)) := by
    have e : ∀ x : Euc d, (convGradConvW (rieszKernelGrad d s) h x) j =
        ∫ z, G z * movtr_R h x z := fun x => dc1a_force_eq hd hs0 hsd hc hh x j
    simp_rw [e]
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖ψ x‖ * Bd) ?_ ?_
      (hψ1.norm.mul_const Bd) ?_
    · refine Eventually.of_forall fun ε => ?_
      have hm : Measurable (fun p : Euc d × Euc d =>
          fcauΦ ε p.2 * (G p.2 * movtr_R h p.1 p.2)) :=
        ((fcauΦ_contDiff (d := d) ε).continuous.measurable.comp measurable_snd).mul
          ((fcau_G_meas s j).comp measurable_snd |>.mul (fcau_movtrR_meas hcont))
      exact (hψcont.measurable.mul hm.stronglyMeasurable.integral_prod_right.measurable)
        |>.aestronglyMeasurable
    · refine Eventually.of_forall fun ε => Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs (∫ z, _)]
      exact mul_le_mul_of_nonneg_left (fcau_trunc_bound hd hs0 hsd j hc hh ε x) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (fcau_trunc_tendsto hd hs0 hsd j hc hh x).const_mul (ψ x)
  have hT2 : ∀ ε : ℝ, 0 < ε → T ε =
      ∫ y, h y * ∫ x, ψ x * (fcauΦ ε (x - y) * rieszKernelGrad d s (x - y) j) := by
    intro ε hε
    have : T ε = ∫ x, ψ x * ∫ z, fcauΦ ε z * rieszKernelGrad d s z j * h (x - z) := by
      simp only [hT]
      congr 1; funext x
      rw [fcau_trunc_eq hd hs0 j hc hh hε x]
    rw [this]
    exact fcau_swap hd hs0 j hc hh hψcont hψc hε
  set I : ℝ → Euc d → ℝ := fun ε y =>
    ∫ x, ψ x * (fcauΦ ε (x - y) * rieszKernelGrad d s (x - y) j) with hI
  have hT3 : Tendsto (fun ε : ℝ => ∫ y, h y * I ε y) (𝓝[>] 0)
      (𝓝 (∫ y, h y * (-kernelConvDeriv d s j ψ y))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => ‖h y‖ * (∫ x, ‖D1 j ψ x * rieszKernel d s (x - y)‖) +
        ‖h y‖ * (2 * L * Lψ * Cg)) ?_ ?_ (hKbar.add (hh1.norm.mul_const _)) ?_
    · refine Eventually.of_forall fun ε => ?_
      have hm : Measurable (fun p : Euc d × Euc d =>
          ψ p.2 * (fcauΦ ε (p.2 - p.1) * rieszKernelGrad d s (p.2 - p.1) j)) :=
        (hψcont.measurable.comp measurable_snd).mul
          ((fcau_PhiG_meas s j ε).comp (measurable_snd.sub measurable_fst))
      exact (hcont.measurable.mul hm.stronglyMeasurable.integral_prod_right.measurable)
        |>.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      refine Eventually.of_forall fun y => ?_
      have hid := fcau_ibp_eps hs0 hsd j hψ hψc hε.1 y
      have hKb : ‖∫ x, D1 j ψ x * (fcauΦ ε (x - y) * rieszKernel d s (x - y))‖ ≤
          ∫ x, ‖D1 j ψ x * rieszKernel d s (x - y)‖ := by
        refine norm_integral_le_of_norm_le (hconv y).norm (Eventually.of_forall fun x => ?_)
        have : D1 j ψ x * (fcauΦ ε (x - y) * rieszKernel d s (x - y)) =
            fcauΦ ε (x - y) * (D1 j ψ x * rieszKernel d s (x - y)) := by ring
        rw [this, norm_mul, Real.norm_eq_abs, abs_of_nonneg (fcauΦ_nonneg ε _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (fcauΦ_le_one ε _)
      have hRb := fcau_R_bound hs0 hsd j hψcont hψc hL hLψ0 hLψ hε.1 y
      have hCg2 := hsmall2 ε hε.1 hε.2.le
      have hRb2 : |∫ x, ψ x * (rieszKernel d s (x - y) *
          fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j 1))| ≤ 2 * L * Lψ * Cg :=
        hRb.trans (mul_le_mul_of_nonneg_left hCg2 (by positivity))
      have hIb : |I ε y| ≤ (∫ x, ‖D1 j ψ x * rieszKernel d s (x - y)‖) + 2 * L * Lψ * Cg := by
        simp only [hI]
        rw [hid]
        rw [Real.norm_eq_abs] at hKb
        calc |-(∫ x, D1 j ψ x * (fcauΦ ε (x - y) * rieszKernel d s (x - y))) -
              ∫ x, ψ x * (rieszKernel d s (x - y) *
                fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j 1))|
            ≤ |-(∫ x, D1 j ψ x * (fcauΦ ε (x - y) * rieszKernel d s (x - y)))| +
              |∫ x, ψ x * (rieszKernel d s (x - y) *
                fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j 1))| :=
              abs_sub _ _
          _ ≤ _ := by rw [abs_neg]; linarith
      rw [norm_mul, Real.norm_eq_abs (I ε y)]
      calc ‖h y‖ * |I ε y| ≤ ‖h y‖ * ((∫ x, ‖D1 j ψ x * rieszKernel d s (x - y)‖) +
            2 * L * Lψ * Cg) := mul_le_mul_of_nonneg_left hIb (norm_nonneg _)
        _ = _ := by ring
    · refine Eventually.of_forall fun y => ?_
      have hK := fcau_K_tendsto hd hs0 hsd j hψ hψc y
      have hR : Tendsto (fun ε : ℝ => ∫ x, ψ x * (rieszKernel d s (x - y) *
          fderiv ℝ (fcauΦ (d := d) ε) (x - y) (EuclideanSpace.single j 1))) (𝓝[>] 0) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ (by simpa using hsmall.const_mul (2 * L * Lψ))
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [Real.norm_eq_abs]
        exact fcau_R_bound hs0 hsd j hψcont hψc hL hLψ0 hLψ hε y
      have hI0 : Tendsto (fun ε : ℝ => I ε y) (𝓝[>] 0) (𝓝 (-kernelConvDeriv d s j ψ y)) := by
        have := hK.neg.sub hR
        simp only [sub_zero] at this
        refine this.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [hI]
        rw [fcau_ibp_eps hs0 hsd j hψ hψc hε y]
      exact hI0.const_mul (h y)
  have hT4 : Tendsto T (𝓝[>] 0) (𝓝 (∫ y, h y * (-kernelConvDeriv d s j ψ y))) := by
    refine hT3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hT2 ε hε]
  have := tendsto_nhds_unique hT1 hT4
  rw [this]
  simp_rw [mul_neg]
  rw [integral_neg]

/-! ### Assembly: the nonlocal term of `generatorW` against a test function -/

section Assembly

open HRS.MS.UniqN2b HRS.MS.UniqN1c HRS.MS.UniqE1 HRS.MS.UniqNDefs

/-- **Duality of the nonlocal term.**  For `u ∈ C_b²`, a regular density `ρ'` and `ψ ∈ C_c²`,
`∫ ψ · (nonlocal term of generatorW along u) = nMain D ρ' u ψ`, the nonlocal term of
`forwardPairing`. -/
theorem fcau_nonlocal_duality (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    {ρ' : Euc d → ℝ} (hρ' : RegSliceRd ρ') {u : Euc d → ℝ} (hu : MemCb 2 u) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => ψ x * nlTermRd D ρ' u x) volume ∧
      ∫ x, ψ x * nlTermRd D ρ' u x = nMain D ρ' u ψ := by
  have hρ'' := hρ'
  obtain ⟨hprob, hmem3, hfin⟩ := hρ'
  have hψcont : Continuous ψ := hψ.continuous
  have hψ1 : Integrable ψ volume := hψcont.integrable_of_hasCompactSupport hψc
  have hψ1' : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  -- decay of the density
  set Λ : ℝ := (weightedSupE 3 ((d : ℝ) + 3) ρ').toReal with hΛ
  have key := e1_rho_decay hd hfin (le_refl Λ)
  set Cρ : ℝ := (d : ℝ) ^ 3 * Λ * 2 ^ ((d : ℝ) + 3) with hCρ
  have hρ0 : ∀ y, |ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := fun y => by
    have := key 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hρ1 : ∀ y, ‖fderiv ℝ ρ' y‖ ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := fun y => by
    have := key 1 (by norm_num) y
    rwa [norm_iteratedFDeriv_one] at this
  have hρC1 : ContDiff ℝ 1 ρ' := hmem3.1.of_le (by norm_num)
  have hρc : Continuous ρ' := hρC1.continuous
  -- bounds on `u`
  obtain ⟨Bu, hBu0, hBu⟩ := db1_iteratedFDeriv_bdd hu (j := 0) (by norm_num)
  obtain ⟨B1, hB10, hB1⟩ := db1_iteratedFDeriv_bdd hu (j := 1) (by norm_num)
  have hub : ∀ x, |u x| ≤ Bu := fun x => by
    have := hBu x; rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hD1u : ∀ i x, |D1 i u x| ≤ B1 := fun i x =>
    (n2b_D1_le i u x).trans (by have := hB1 x; rwa [norm_iteratedFDeriv_one] at this)
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by norm_num)
  have hucont : Continuous u := hu1.continuous
  have hD1ucont : ∀ i, Continuous (D1 i u) := fun i =>
    (hu1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- the kernels `K_i`
  have hKc : ∀ i, Continuous (kernelConvDeriv d D.s i ψ) := fun i =>
    K_cont hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
  have hKb : ∀ i, ∃ C1, ∀ y, |kernelConvDeriv d D.s i ψ y| ≤ C1 * (1 + ‖y‖) := fun i => by
    obtain ⟨C1, hC1⟩ := conv_bound hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
    exact ⟨C1, hC1⟩
  have hKdb : ∀ i j, ∃ C1, ∀ y, |D1 j (kernelConvDeriv d D.s i ψ) y| ≤ C1 * (1 + ‖y‖) := fun i j => by
    obtain ⟨C1, hC1⟩ := conv_bound hs0 hsd (n2b_D1D1_cont hψ i j)
      (D1_supp (D1_supp hψc i) j)
    refine ⟨C1, fun y => ?_⟩
    rw [n1c_D1_kcd hs0 hsd hψ hψc i j]
    exact hC1 y
  have hKdc : ∀ i j, Continuous (D1 j (kernelConvDeriv d D.s i ψ)) :=
    fun i j => n1c_D1_kcd_cont hs0 hsd hψ hψc i j
  have hKdiff : ∀ i, Differentiable ℝ (kernelConvDeriv d D.s i ψ) := fun i =>
    convFun_diff hl (D1_contDiff hψ i) (D1_supp hψc i)
  -- integrability of products with a bounded function
  have hbdd_int : ∀ {a h : Euc d → ℝ} {Ca C : ℝ}, (∀ y, |a y| ≤ Ca * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) →
      (∀ y, |h y| ≤ C * (1 + ‖y‖)) → AEStronglyMeasurable a volume → AEStronglyMeasurable h volume →
      ∀ {b : Euc d → ℝ} {Bb : ℝ}, AEStronglyMeasurable b volume → (∀ y, |b y| ≤ Bb) →
        Integrable (fun y => b y * (a y * h y)) volume := by
    intro a h Ca C ha hh ham hhm b Bb hbm hbb
    refine Integrable.mono' ((wt_integrable (d := d)).const_mul (Bb * (Ca * C))) (hbm.mul (ham.mul hhm))
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |b y| * |a y * h y| ≤ Bb * ((Ca * C) * wt d y) :=
          mul_le_mul (hbb y) (n2b_wt_dom ha hh y) (abs_nonneg _) ((abs_nonneg _).trans (hbb y))
      _ = Bb * (Ca * C) * wt d y := by ring
  -- the product rule for `ρ' K_i`
  have hgfd : ∀ i j x, fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ y) x
      (EuclideanSpace.single j (1 : ℝ)) =
        D1 j ρ' x * kernelConvDeriv d D.s i ψ x + ρ' x * D1 j (kernelConvDeriv d D.s i ψ) x := by
    intro i j x
    rw [n2b_fderiv_prod hs0 hsd hρC1 hψ hψc i j x, ← n1c_D1_kcd hs0 hsd hψ hψc i j x]
  have hρd1 : ∀ j y, |D1 j ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := fun j y =>
    (n2b_D1_le j ρ' y).trans (hρ1 y)
  have hρdc : ∀ j, Continuous (D1 j ρ') := fun j =>
    (hρC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- integrations by parts
  have hIBP : ∀ i j, ∫ x, u x * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ y) x
      (EuclideanSpace.single j (1 : ℝ)) =
        -∫ x, D1 j u x * (ρ' x * kernelConvDeriv d D.s i ψ x) := by
    intro i j
    obtain ⟨C1, hC1⟩ := hKb i
    obtain ⟨C2, hC2⟩ := hKdb i j
    have hfg : Integrable (fun x => u x * (ρ' x * kernelConvDeriv d D.s i ψ x)) volume :=
      hbdd_int hρ0 hC1 hρc.aestronglyMeasurable (hKc i).aestronglyMeasurable
        hucont.aestronglyMeasurable hub
    have hf'g : Integrable (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ)) *
        (ρ' x * kernelConvDeriv d D.s i ψ x)) volume :=
      hbdd_int hρ0 hC1 hρc.aestronglyMeasurable (hKc i).aestronglyMeasurable
        (hD1ucont j).aestronglyMeasurable (hD1u j)
    have hfg' : Integrable (fun x => u x * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ y) x
        (EuclideanSpace.single j (1 : ℝ))) volume := by
      have h1 := hbdd_int (hρd1 j) hC1 (hρdc j).aestronglyMeasurable (hKc i).aestronglyMeasurable
        hucont.aestronglyMeasurable hub
      have h2 := hbdd_int hρ0 hC2 hρc.aestronglyMeasurable (hKdc i j).aestronglyMeasurable
        hucont.aestronglyMeasurable hub
      refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
      simp only [hgfd, Pi.add_apply]; ring
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := u)
      (g := fun y => ρ' y * kernelConvDeriv d D.s i ψ y) (v := EuclideanSpace.single j (1 : ℝ))
      hf'g hfg' hfg (fun x _ => (hu1.differentiable one_ne_zero) x)
      (fun x _ => (hρC1.differentiable one_ne_zero x).mul (hKdiff i x))
    exact this
  -- the weighted class of `h_j = ρ' · (Mᵀ∇u)_j`
  obtain ⟨C, hC0, hρW⟩ := dc1a_rho_rgW hd hρ''
  choose cv hcv0 hvW using fun j : Fin d => dc1a_v_rgW hu D.M j
  have hhW : ∀ j : Fin d, RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1
      (2 ^ 1 * C * cv j) (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j) :=
    fun j => dc1a_mul_rgW hC0 (hcv0 j) hρW (hvW j)
  have hc2 : ∀ j : Fin d, 0 ≤ 2 ^ 1 * C * cv j := fun j =>
    mul_nonneg (mul_nonneg (by norm_num) hC0) (hcv0 j)
  have hvb : ∀ j y, |(Torus.matVec D.M.transpose (gradient u y)) j| ≤ cv j := fun j y => by
    have := (hvW j).2 0 (by norm_num) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    simpa using this
  have hh2 : ∀ j : Fin d, Integrable (fun y : Euc d => ‖y‖ *
      (ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j)) volume := by
    intro j
    have hvc : Continuous fun y => (Torus.matVec D.M.transpose (gradient u y)) j := (hvW j).1.continuous
    refine Integrable.mono' ((wt_integrable (d := d)).const_mul (Cρ * cv j))
      ((continuous_norm.mul (hρc.mul hvc)).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg y)]
    have h1 := hρ0 y
    have h2 := hvb j y
    have hw := n2b_wt_mul (d := d) y
    have hpos : 0 ≤ (1 + ‖y‖) := by positivity
    calc ‖y‖ * (|ρ' y| * |(Torus.matVec D.M.transpose (gradient u y)) j|)
        ≤ (1 + ‖y‖) * ((Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * cv j) :=
          mul_le_mul (by linarith [norm_nonneg y]) (mul_le_mul h1 h2 (abs_nonneg _)
            ((abs_nonneg _).trans h1)) (by positivity) hpos
      _ = Cρ * cv j * ((1 + ‖y‖) ^ (-((d : ℝ) + 3)) * (1 + ‖y‖)) := by ring
      _ = Cρ * cv j * wt d y := by rw [hw]
  -- the pieces of the left side
  have hcoef : ∀ j : Fin d, ∀ x, (convGradConvW (rieszKernelGrad d D.s)
      (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j) x) j =
        ∫ z, rieszKernelGrad d D.s z j * movtr_R
          (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j) x z :=
    fun j x => dc1a_force_eq hd hs0 hsd (hc2 j) (hhW j) x j
  have hconvInt : ∀ j : Fin d, Integrable (fun x => ψ x * (convGradConvW (rieszKernelGrad d D.s)
      (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j) x) j) volume := by
    intro j
    obtain ⟨B, hB0, hB⟩ := dc1a_force_bound' hd hs0 hsd (hc2 j) (hhW j) j
    have hvc : Continuous fun y => (Torus.matVec D.M.transpose (gradient u y)) j := (hvW j).1.continuous
    have hm : AEStronglyMeasurable (fun x => (convGradConvW (rieszKernelGrad d D.s)
        (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j) x) j) volume := by
      have e : (fun x => (convGradConvW (rieszKernelGrad d D.s)
          (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j) x) j) =
          fun x => ∫ z, rieszKernelGrad d D.s z j * movtr_R
            (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j) x z := funext (hcoef j)
      rw [e]
      exact (dc1a_meas_int (fcau_G_meas D.s j) (hρc.mul hvc)).aestronglyMeasurable
    refine Integrable.mono' (hψ1.norm.mul_const B) (hψcont.aestronglyMeasurable.mul hm)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
  have hA : ∫ x, ψ x * nlTermRd D ρ' u x =
      ∑ j : Fin d, -∫ y, ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j *
        kernelConvDeriv d D.s j ψ y := by
    unfold nlTermRd
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun j _ => hconvInt j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact fcau_core hd hs0 hsd j (hc2 j) (hhW j) (hh2 j) hψ1' hψc
  -- the pieces of the right side
  have hB : nMain D ρ' u ψ = ∑ i : Fin d, ∑ j : Fin d,
      D.M j i * -∫ x, D1 j u x * (ρ' x * kernelConvDeriv d D.s i ψ x) := by
    unfold nMain
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hIBP i j]
  have hC : ∀ j : Fin d, ∫ y, ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j *
      kernelConvDeriv d D.s j ψ y = ∑ i : Fin d, D.M i j *
        ∫ x, D1 i u x * (ρ' x * kernelConvDeriv d D.s j ψ x) := by
    intro j
    obtain ⟨C1, hC1⟩ := hKb j
    have e : ∀ y, ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j *
        kernelConvDeriv d D.s j ψ y = ∑ i : Fin d, D.M i j *
          (D1 i u y * (ρ' y * kernelConvDeriv d D.s j ψ y)) := by
      intro y
      rw [HRS.Whole.Q09B.q09b_matVec_apply]
      simp only [Matrix.transpose_apply]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [D1, q09_gradient_apply]
      ring
    simp_rw [e]
    rw [integral_finsetSum _ (fun i _ => ((hbdd_int hρ0 hC1 hρc.aestronglyMeasurable
      (hKc j).aestronglyMeasurable (hD1ucont i).aestronglyMeasurable (hD1u i)).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  refine ⟨?_, ?_⟩
  · unfold nlTermRd
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun j _ => hconvInt j)
  rw [hA, hB]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hC j, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Assembly

/-! ### The local terms and the slice identity -/

section Slice

open HRS.MS.UniqNDefs

theorem fcau_dvv {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (v x : Euc d) :
    iteratedFDeriv ℝ 2 f x ![v, v] = fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hd1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [iteratedFDeriv_two_apply]
  have := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ f) (u := fun _ : Euc d => v) (x := x)
    (hd1 x) (differentiableAt_const v)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [this]
  simp

/-- Green's identity `∫ ψ Δu = ∫ u Δψ` for `u ∈ C²`, `ψ ∈ C²_c`. -/
theorem fcau_green {u ψ : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, ψ x * Laplacian.laplacian u x = ∫ x, u x * Laplacian.laplacian ψ x := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hLu : ∀ x, Laplacian.laplacian u x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ u y ((stdOrthonormalBasis ℝ (Euc d)) i)) x
        ((stdOrthonormalBasis ℝ (Euc d)) i) := fun x => by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    exact Finset.sum_congr rfl fun i _ => fcau_dvv hu _ x
  have hLψ : ∀ x, Laplacian.laplacian ψ x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ ψ y ((stdOrthonormalBasis ℝ (Euc d)) i)) x
        ((stdOrthonormalBasis ℝ (Euc d)) i) := fun x => by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    exact Finset.sum_congr rfl fun i _ => fcau_dvv hψ _ x
  have hcd : ∀ (f : Euc d → ℝ), ContDiff ℝ 2 f → ∀ v : Euc d,
      ContDiff ℝ 1 (fun y => fderiv ℝ f y v) := fun f hf v =>
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hcont : ∀ (f : Euc d → ℝ), ContDiff ℝ 2 f → ∀ v : Euc d,
      Continuous (fun y => fderiv ℝ (fun y => fderiv ℝ f y v) y v) := fun f hf v =>
    ((hcd f hf v).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDψc : ∀ v : Euc d, HasCompactSupport (fun y => fderiv ℝ ψ y v) := fun v =>
    (hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
  have hDDc : ∀ v : Euc d, HasCompactSupport (fun y => fderiv ℝ (fun y => fderiv ℝ ψ y v) y v) :=
    fun v => ((hDψc v).fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
  simp_rw [hLu, hLψ, Finset.mul_sum]
  rw [integral_finsetSum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    set v := (stdOrthonormalBasis ℝ (Euc d)) i
    have h1 := n0_ibp (F := ψ) hψ1 hψc (k := fun y => fderiv ℝ u y v)
      (fun t _ => (hcd u hu v).contDiffAt) v
    have h2 := n0_ibp (F := fun y => fderiv ℝ ψ y v) (hcd ψ hψ v) (hDψc v) (k := u)
      (fun t _ => hu1.contDiffAt) v
    have e1 : ∫ x, ψ x * fderiv ℝ (fun y => fderiv ℝ u y v) x v =
        -∫ t, fderiv ℝ u t v * fderiv ℝ ψ t v := by
      rw [h1, neg_neg]; congr 1; funext t; ring
    have e2 : ∫ x, u x * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v =
        -∫ t, fderiv ℝ u t v * fderiv ℝ ψ t v := by
      rw [h2]
    rw [e1, e2]
  · exact fun i _ => (hu1.continuous.mul (hcont ψ hψ _)).integrable_of_hasCompactSupport
      (hDDc _).mul_left
  · exact fun i _ => (hψ1.continuous.mul (hcont u hu _)).integrable_of_hasCompactSupport
      hψc.mul_right

/-- **Slice identity.**  Testing `generatorW` along `u ∈ C_b²` against `ψ ∈ C_c^∞` gives the
pairing `forwardPairing` of S.A.33 (time `r = t - σ`). -/
theorem fcau_slice (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (ρ : ℝ → Euc d → ℝ) (t σ : ℝ) (hρ : RegSliceRd (ρ (t - σ)))
    (hb : ∀ i : Fin d, ContDiff ℝ 1 (fun y => meanFieldDriftW D (ρ (t - σ)) y i))
    {u : Euc d → ℝ} (hu : MemCb 2 u) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, ψ x * generatorW (D.coeff ρ) (t - σ) u x = forwardPairing D ρ t σ u ψ := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hu2 : ContDiff ℝ 2 u := hu.1
  have hu1 : ContDiff ℝ 1 u := hu2.of_le (by norm_num)
  have hgen : ∀ x, generatorW (D.coeff ρ) (t - σ) u x = D.invβ * Laplacian.laplacian u x +
      ∑ i : Fin d, meanFieldDriftW D (ρ (t - σ)) x i * D1 i u x -
        nlTermRd D (ρ (t - σ)) u x := by
    intro x
    unfold generatorW
    show D.invβ * Laplacian.laplacian u x + inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient u x) -
      nlTermRd D (ρ (t - σ)) u x = _
    congr 2
    simp only [PiLp.inner_apply, D1, ← q09_gradient_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨hNLi, hNL⟩ := fcau_nonlocal_duality hd D hs0 hsd hρ hu hψ2 hψc
  have hψint : Continuous ψ := hψ.continuous
  have hI1 : Integrable (fun x => ψ x * Laplacian.laplacian u x) volume :=
    (hψint.mul (db1_laplacian_continuous hu2)).integrable_of_hasCompactSupport hψc.mul_right
  have hI2 : ∀ i : Fin d, Integrable (fun x => ψ x * (meanFieldDriftW D (ρ (t - σ)) x i *
      D1 i u x)) volume := fun i => by
    have hbc : Continuous fun x => meanFieldDriftW D (ρ (t - σ)) x i := (hb i).continuous
    have hDc : Continuous (D1 i u) := (hu1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hψint.mul (hbc.mul hDc)).integrable_of_hasCompactSupport hψc.mul_right
  have hsum : ∫ x, ψ x * generatorW (D.coeff ρ) (t - σ) u x =
      D.invβ * (∫ x, ψ x * Laplacian.laplacian u x) +
        (∑ i : Fin d, ∫ x, ψ x * (meanFieldDriftW D (ρ (t - σ)) x i * D1 i u x)) -
          ∫ x, ψ x * nlTermRd D (ρ (t - σ)) u x := by
    simp_rw [hgen]
    have e : ∀ x, ψ x * (D.invβ * Laplacian.laplacian u x +
        ∑ i : Fin d, meanFieldDriftW D (ρ (t - σ)) x i * D1 i u x - nlTermRd D (ρ (t - σ)) u x) =
        D.invβ * (ψ x * Laplacian.laplacian u x) +
          (∑ i : Fin d, ψ x * (meanFieldDriftW D (ρ (t - σ)) x i * D1 i u x)) -
            ψ x * nlTermRd D (ρ (t - σ)) u x := fun x => by
      rw [← Finset.mul_sum]; ring
    simp_rw [e]
    have hA : Integrable (fun x => ∑ i : Fin d, ψ x * (meanFieldDriftW D (ρ (t - σ)) x i *
        D1 i u x)) volume := integrable_finsetSum _ fun i _ => hI2 i
    have hB : Integrable (fun x => D.invβ * (ψ x * Laplacian.laplacian u x)) volume :=
      hI1.const_mul _
    have hAB : Integrable (fun x => D.invβ * (ψ x * Laplacian.laplacian u x) +
        ∑ i : Fin d, ψ x * (meanFieldDriftW D (ρ (t - σ)) x i * D1 i u x)) volume := hB.add hA
    rw [integral_sub hAB hNLi, integral_add hB hA, integral_const_mul,
      integral_finsetSum _ fun i _ => hI2 i]
  have hT : ∀ i : Fin d, ∫ x, ψ x * (meanFieldDriftW D (ρ (t - σ)) x i * D1 i u x) =
      -∫ x, u x * fderiv ℝ (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) x
        (EuclideanSpace.single i (1 : ℝ)) := fun i => by
    have := n0_ibp (F := fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) ((hb i).mul hψ1)
      hψc.mul_left (k := u) (fun t _ => hu1.contDiffAt) (EuclideanSpace.single i (1 : ℝ))
    rw [this, neg_neg]
    congr 1; funext x; simp only [D1]; ring
  have hTint : ∀ i : Fin d, Integrable (fun x => u x * fderiv ℝ
      (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) x (EuclideanSpace.single i (1 : ℝ))) volume :=
    fun i => by
      have hc : ContDiff ℝ 1 (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) := (hb i).mul hψ1
      have hcs : HasCompactSupport (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) := hψc.mul_left
      have hDcs : HasCompactSupport (fun x => fderiv ℝ
          (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) x (EuclideanSpace.single i (1 : ℝ))) :=
        (hcs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
          (by simp)
      exact (hu1.continuous.mul ((hc.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
        hDcs.mul_left
  rw [hsum, hNL, UniqNDefs.forwardPairing_eq]
  have hG := fcau_green hu2 hψ2 hψc
  rw [hG]
  simp_rw [hT]
  rw [Finset.sum_neg_distrib]
  have this : ∫ x, u x * ∑ i : Fin d, fderiv ℝ (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) x
      (EuclideanSpace.single i (1 : ℝ)) =
      ∑ i : Fin d, ∫ x, u x * fderiv ℝ (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) x
        (EuclideanSpace.single i (1 : ℝ)) := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ fun i _ => hTint i
  rw [this]
  ring

end Slice

end Core

end HRS.MS.Fcau
