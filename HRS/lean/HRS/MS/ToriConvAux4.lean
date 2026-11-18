import HRS.MS.ToriConvAux3

/-!
# MS-TORI-DRIFTCONV, helper file 4: the concrete kernels, whole-space coordinates, vector bounds

* `tcv_kerns_coord`: the package `tcv_Kerns` for the coordinates of `∇γ_L` and of `∇g_E`
  (bounds of `ToriCoefBAux3`, `ker1_E_bound` with `n = 1`, convergence of `expanding_tori_kernel_proof` (c)).
* `tcv_convW_coord`: the coordinates of `convGradConvW` are the scalar operators `tcv_TE`.
* `tcv_vec_pt`: pointwise bound of the `n`-th derivative of a vector `∑_i U_i e_i`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriConv

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA HRS.MS.ToriCoefB
  HRS.MS.Ker1

variable {d : ℕ}

theorem tcv_coord_le (v : Euc d) (i : Fin d) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  rwa [Real.norm_eq_abs] at this

theorem tcv_grad_sub_norm (f g : Euc d → ℝ) (z : Euc d) :
    ‖gradient f z - gradient g z‖ = ‖iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 g z‖ := by
  have h1 := tcv_iter_fderiv_sub_norm f g 0 z
  rw [tcv_iter_zero_sub_norm] at h1
  unfold gradient
  rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
  simpa using h1

theorem tcv_meas_gradient (f : Euc d → ℝ) : Measurable (gradient f) := by
  have : gradient f = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ f := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem tcv_meas_coord (f : Euc d → ℝ) (i : Fin d) : Measurable fun z => gradient f z i :=
  (by fun_prop : Continuous fun v : Euc d => v i).measurable.comp (tcv_meas_gradient f)

theorem tcv_kerns_coord (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ Kf Cn : ℝ, ∀ (γ : ℝ → Euc d → ℝ), (∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L)) →
      ∀ i : Fin d, tcv_Kerns d s (fun L z => gradient (γ L) z i)
        (fun z => gradient (rieszKernel d s) z i) Kf Cn := by
  obtain ⟨C₁, A₀, hC₁, hA₀, hkern⟩ := tcb_kern_coord hd hs0 hsd
  obtain ⟨C₂, hC₂, hbd⟩ := tcb_grad_bounds hd hs0 hsd
  obtain ⟨CE, hCE0, hCE⟩ := ker1_E_bound (d := d) hs0 1 (by norm_num; linarith)
  have e1 : -s - ((1 : ℕ) : ℝ) = -(s + 1) := by push_cast; ring
  have hCE' : ∀ ξ : Euc d, ξ ≠ 0 → ‖gradient (rieszKernel d s) ξ‖ ≤ CE * ‖ξ‖ ^ (-(s + 1)) := by
    intro ξ hξ
    have := hCE ξ hξ
    rw [e1] at this
    rwa [tcb_norm_gradient]
  have hq : 0 ≤ CE * (1 / 4 : ℝ) ^ (-(s + 1)) := mul_nonneg hCE0 (Real.rpow_nonneg (by norm_num) _)
  refine ⟨max C₁ (CE * (1 / 4 : ℝ) ^ (-(s + 1))), max C₂ CE, fun γ hγ i => ?_⟩
  have hKf0 : 0 ≤ max C₁ (CE * (1 / 4 : ℝ) ^ (-(s + 1))) := (le_max_left _ _).trans' hC₁
  refine ⟨hKf0, (le_max_left _ _).trans' hC₂, fun L hL => ?_, fun L hL z hz => ?_,
    tcv_meas_coord _ i, fun z hz => ?_, fun z hz => ?_, fun δ hδ => ?_, fun δ R η hδ hη => ?_⟩
  · obtain ⟨hk1, -⟩ := hkern L hL (γ L) (hγ L hL) i
    exact ⟨hL, hKf0, hk1.meas, hk1.intN, fun z hzQ hz4 => (hk1.far z hzQ hz4).trans (le_max_left _ _)⟩
  · by_cases hz0 : z = 0
    · subst hz0
      simp only [norm_zero, mul_zero]
      exact mul_nonneg ((le_max_left _ _).trans' hC₂) (Real.rpow_nonneg le_rfl _)
    · have h1 := (tcv_coord_le (gradient (γ L) z) i).trans ((hbd L hL (γ L) (hγ L hL)).1 z hz0 hz)
      have h2 : ‖z‖ ^ (-s) = ‖z‖ ^ (-(s + 1)) * ‖z‖ := by
        rw [← Real.rpow_add_one (norm_ne_zero_iff.2 hz0)]
        congr 1; ring
      rw [h2]
      have := mul_le_mul_of_nonneg_right h1 (norm_nonneg z)
      have h3 : C₂ * ‖z‖ ^ (-(s + 1)) ≤ max C₂ CE * ‖z‖ ^ (-(s + 1)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
      have h4 : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
  · by_cases hz0 : z = 0
    · subst hz0
      simp only [norm_zero, mul_zero]
      exact mul_nonneg ((le_max_right _ _).trans' hCE0) (Real.rpow_nonneg le_rfl _)
    · have h1 := (tcv_coord_le (gradient (rieszKernel d s) z) i).trans (hCE' z hz0)
      have h2 : ‖z‖ ^ (-s) = ‖z‖ ^ (-(s + 1)) * ‖z‖ := by
        rw [← Real.rpow_add_one (norm_ne_zero_iff.2 hz0)]
        congr 1; ring
      rw [h2]
      have := mul_le_mul_of_nonneg_right h1 (norm_nonneg z)
      have h3 : CE * ‖z‖ ^ (-(s + 1)) ≤ max C₂ CE * ‖z‖ ^ (-(s + 1)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)
      have h4 : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
  · have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; linarith
    have h1 := (tcv_coord_le (gradient (rieszKernel d s) z) i).trans (hCE' z hz0)
    refine h1.trans ((le_max_right _ _).trans' ?_)
    have h2 : ‖z‖ ^ (-(s + 1)) ≤ (1 / 4 : ℝ) ^ (-(s + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hz.le (by linarith)
    exact mul_le_mul_of_nonneg_left h2 hCE0
  · refine ⟨CE * δ ^ (-(s + 1)), fun z hz => ?_⟩
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; linarith
    have h1 := (tcv_coord_le (gradient (rieszKernel d s) z) i).trans (hCE' z hz0)
    refine h1.trans ?_
    have h2 : ‖z‖ ^ (-(s + 1)) ≤ δ ^ (-(s + 1)) :=
      Real.rpow_le_rpow_of_nonpos hδ hz (by linarith)
    exact mul_le_mul_of_nonneg_left h2 hCE0
  · have hKc : IsCompact {w : Euc d | δ ≤ ‖w‖ ∧ ‖w‖ ≤ R} := ker1_isCompact_annulus
    have hne : ∀ w ∈ {w : Euc d | δ ≤ ‖w‖ ∧ ‖w‖ ≤ R}, w ≠ 0 := by
      intro w hw h
      have := hw.1
      rw [h, norm_zero] at this
      linarith
    obtain ⟨L₀, hL₀⟩ := (expanding_tori_kernel_proof hd s hs0 hsd 0).2.2 _ hKc hne 1 (by omega) η hη
    refine ⟨max L₀ 1, fun L hL z hzδ hzR => ?_⟩
    have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
    have h1 := ((hL₀ L ((le_max_left _ _).trans hL) (γ L) (hγ L hL1)).1
      (by norm_num; linarith) z ⟨hzδ, hzR⟩)
    have h2 := tcv_coord_le (gradient (γ L) z - gradient (rieszKernel d s) z) i
    rw [tcv_grad_sub_norm] at h2
    simpa using h2.trans h1

/-- The coordinates of `convGradConvW` are the scalar operators `tcv_TE`. -/
theorem tcv_convW_coord (G : Euc d → Euc d) (ρ : Euc d → ℝ) (x : Euc d)
    (hint : ∀ j : Fin d, Integrable (tcb_F (fun z => G z j) ρ x)) (i : Fin d) :
    convGradConvW G ρ x i = tcv_TE (fun z => G z i) ρ x := by
  set Φ : Euc d → Euc d := fun z =>
    if ‖z‖ ≤ 1 / 4 then (ρ (x - z) - ρ x) • G z else ρ (x - z) • G z with hΦ
  have e : convGradConvW G ρ x = ∫ z, Φ z := by
    have := integral_sub_left_eq_self Φ volume x
    simp only [hΦ, sub_sub_cancel] at this
    unfold convGradConvW
    exact this
  have hΦint : Integrable Φ := by
    have e2 : Φ = fun z => ∑ j : Fin d, (tcb_F (fun z => G z j) ρ x z) •
        (EuclideanSpace.single j (1 : ℝ) : Euc d) := by
      funext z
      ext b
      rw [hΦ]
      simp only []
      rw [tcb_integrand_coord G ρ x z b]
      simp [Pi.single_apply]
    rw [e2]
    exact integrable_finsetSum _ fun j _ => (hint j).smul_const _
  rw [e]
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hΦint
  have e3 : (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) (∫ z, Φ z) = (∫ z, Φ z) i := rfl
  rw [← e3, ← this]
  unfold tcv_TE
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact tcb_integrand_coord G ρ x z i

/-- Pointwise bound of the `n`-th derivative of `∑_i U_i • e_i`. -/
theorem tcv_vec_pt (n : ℕ) (U : Fin d → Euc d → ℝ) (hU : ∀ i, ContDiff ℝ (n : WithTop ℕ∞) (U i))
    (x : Euc d) :
    ‖iteratedFDeriv ℝ n (fun x => ∑ i, U i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) x‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ n (U i) x‖ := by
  have hcd : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      ContDiffAt ℝ (n : WithTop ℕ∞)
        (fun x => U i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) x :=
    fun i _ => ((hU i).smul contDiff_const).contDiffAt
  rw [iteratedFDeriv_fun_sum_apply hcd]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  set c : ℝ →L[ℝ] Euc d := ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)
  have hc : ‖c‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => ?_
    simp [c, norm_smul]
  have e : (fun x => U i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) = c ∘ U i := by
    funext x; simp [c]
  rw [e]
  have h1 := c.norm_iteratedFDeriv_comp_left ((hU i).contDiffAt (x := x)) (le_refl (n : WithTop ℕ∞))
  have h3 : 0 ≤ ‖iteratedFDeriv ℝ n (U i) x‖ := norm_nonneg _
  calc _ ≤ ‖c‖ * ‖iteratedFDeriv ℝ n (U i) x‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (U i) x‖ := mul_le_mul_of_nonneg_right hc h3
    _ = _ := one_mul _

end HRS.MS.ToriConv
