import HRS.MS.MfeConfAux127

/-!
# S.B.1 (SB5), R1 (part 5): the estimate E2 (Lipschitz bound of the force defect)

`e_j = a_j - F_j` is differentiable with `∂_i e_j = rgT (∂_jk) (∂_iρ) - rgT (∂_jg) (∂_iρ)` (integration by parts for the first
term, `D F_j = rgT ∂_jg (Dρ)` for the second), hence `‖e(x) - e(y)‖ ≤ d² K₁ η_M ‖x-y‖` (`sb1_E2`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.RdGen HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_clm_norm_le (L : Euc d →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |L (sb1e i)| ≤ c) : ‖L‖ ≤ d * c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [sb1_clm_expand L w, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |w i * L (sb1e i)| ≤ ∑ _i : Fin d, c * ‖w‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        have h1 : |w i| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w i
        calc |w i| * |L (sb1e i)| ≤ ‖w‖ * c := mul_le_mul h1 (h i) (abs_nonneg _) (norm_nonneg _)
          _ = c * ‖w‖ := mul_comm _ _
    _ = d * c * ‖w‖ := by simp; ring

theorem sb1eta_nonneg (s r : ℝ) : 0 ≤ sb1eta d s r :=
  setIntegral_nonneg Metric.isClosed_closedBall.measurableSet fun z _ => Real.rpow_nonneg (norm_nonneg z) _

section Lip

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_e_comp (hk4 : IsP4Kernel d D.s r₀ k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) (j : Fin d) :
    sb1_lv_e D k hT ρ r x j = sb1_lv_a k (ρ r) j x - sb1F d D.s (ρ r) j x := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  have hrb : sb1_lv_rb hT ρ r = ρ r := sb1_lv_rb_mem hT ρ hr
  have := sb1_lv_u_sub_v hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg H.tr.V (sb1_lv_rb_rho H hT r)
    (sb1_lv_rb_slice H hT r) (sb1_lv_rb_pos H hT r) x j
  unfold sb1_lv_e sb1_lv_U
  rw [hrb] at this ⊢
  simpa using this

theorem sb1_e_deriv (hk4 : IsP4Kernel d D.s r₀ k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) (j : Fin d) :
    ∃ L : Euc d →L[ℝ] ℝ, HasFDerivAt (fun x => sb1_lv_e D k hT ρ r x j) L x ∧ ∀ i : Fin d,
      L (sb1e i) = rgT (sb1_lv_dk k j) (fun y => fderiv ℝ (ρ r) y (sb1e i)) x -
        rgT (fun z => (rieszKernelGrad d D.s z) j) (fun y => fderiv ℝ (ρ r) y (sb1e i)) x := by
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 hs0
  obtain ⟨L2, -, hL2⟩ := sb1_lv_hess_bound hk4
  have hρd : Differentiable ℝ (ρ r) := (H.tr.slice r hr).decay.1.differentiable (by norm_num)
  have hρ' : Continuous (fderiv ℝ (ρ r)) := (H.tr.slice r hr).decay.1.continuous_fderiv (by norm_num)
  have hR := H.rho hd hr
  have h1 := sb1_lv_dG_hasFDerivAt hk4 hd hs0 hsd hRg hRg.gbd hL2 hR j x
  have h2 := sb1F_fderiv hd hs0 hsd (H.tr.slice r hr) j x
  have hfun : (fun x => sb1_lv_e D k hT ρ r x j) = fun x => fderiv ℝ (sb1G k (ρ r)) x (sb1e j) - sb1F d D.s (ρ r) j x :=
    funext fun x => sb1_e_comp H hT hk4 hr x j
  rw [hfun]
  refine ⟨_, h1.sub h2, fun i => ?_⟩
  have hint : Integrable (fun y => ρ r y • fderiv ℝ (sb1_lv_dk k j) (x - y)) := by
    refine (hR.integrable.norm.mul_const L2).mono' (hR.meas'.smul
      ((sb1_lv_dk_fderiv_cont hk4.smooth j).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (sb1_lv_dk_fderiv_bound hk4.smooth hL2 j _) (norm_nonneg _)
  have hrbi : Integrable (fun y => fderiv ℝ (ρ r) y (sb1e i)) := by
    have := (sb1_lv_dh_facts H hT r i).1
    rwa [sb1_lv_rb_mem hT ρ hr] at this
  have e1 : (∫ y, ρ r y • fderiv ℝ (sb1_lv_dk k j) (x - y)) (sb1e i) =
      rgT (sb1_lv_dk k j) (fun y => fderiv ℝ (ρ r) y (sb1e i)) x := by
    rw [ContinuousLinearMap.integral_apply hint]
    have : ∀ y, (ρ r y • fderiv ℝ (sb1_lv_dk k j) (x - y)) (sb1e i) =
        ρ r y * fderiv ℝ (sb1_lv_dk k j) (x - y) (sb1e i) := fun y => by simp
    simp only [this]
    rw [sb1_lv_ibp_cv (sb1_lv_dk_diff hk4.smooth j) (sb1_lv_dk_fderiv_cont hk4.smooth j)
      (sb1_lv_dk_fderiv_bound hk4.smooth hL2 j) (sb1_lv_dk_bound hRg.gbd j) hρd hρd.continuous hρ' hR.integrable
      (sb1e i) hrbi x]
    have := sb1_cv_eq_rgT (sb1_lv_dk_cont hk4.smooth j).measurable (sb1_lv_dk_bound hRg.gbd j)
      (fun z => sb1_fderiv_odd (hk4.smooth.differentiable (by norm_num)) hk4.even z (sb1e j)) hrbi x
    rw [← this]
    unfold sb1_lv_cv
    rfl
  have e2 : (rgT (fun z => (rieszKernelGrad d D.s z) j) (fderiv ℝ (ρ r)) x) (sb1e i) =
      rgT (fun z => (rieszKernelGrad d D.s z) j) (fun y => fderiv ℝ (ρ r) y (sb1e i)) x := by
    obtain ⟨hc, -, h1', -, h2', -⟩ := sb1_slice_facts (H.tr.slice r hr)
    exact sb1_lv_rgT_apply hd hs0 hsd (rgKerComp_ok hs0 j)
      ((hc.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num))
      (H.tr.slice r hr).C_nonneg (H.tr.slice r hr).C_nonneg h1' h2' x (sb1e i)
  simp only [ContinuousLinearMap.sub_apply]
  rw [e1, e2]

/-- **E2**: Lipschitz bound of the force defect -/
theorem sb1_E2 (M : ℕ) {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ j : Fin d, RgKer d D.s A (sb1_lv_dk (sb1kM d D.s M) j))
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x y : Euc d) :
    ‖sb1_lv_e D (sb1kM d D.s M) hT ρ r x - sb1_lv_e D (sb1kM d D.s M) hT ρ r y‖ ≤
      d * (d * ((A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3) *
        sb1eta d D.s (1 / ((M : ℝ) + 1)))) * ‖x - y‖ := by
  have hs0 := H.tr.hs0
  have hk4 := sb1kM_isKernel (d := d) D.s hs0 M
  set K : ℝ := (A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3) * sb1eta d D.s (1 / ((M : ℝ) + 1)) with hK
  have hσ : 0 ≤ Whole.movtr_sigma D.s := by
    unfold Whole.movtr_sigma; split_ifs <;> linarith
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg (add_nonneg hA0 hσ) (mul_nonneg (by positivity) H.C3nn)) (sb1eta_nonneg _ _)
  have hcoef : 0 ≤ (A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3) :=
    mul_nonneg (add_nonneg hA0 hσ) (mul_nonneg (by positivity) H.C3nn)
  have hdK : ∀ z (i j : Fin d), |rgT (sb1_lv_dk (sb1kM d D.s M) j) (fun y => fderiv ℝ (ρ r) y (sb1e i)) z -
      rgT (fun w => (rieszKernelGrad d D.s w) j) (fun y => fderiv ℝ (ρ r) y (sb1e i)) z| ≤ K := by
    intro z i j
    refine (sb1_dEM_bound H hs0 M hA hr z i j).trans ?_
    rw [hK]
    refine mul_le_mul_of_nonneg_right ?_ (sb1eta_nonneg _ _)
    have hw := sb1w_le_one (d := d) (p := (d : ℝ) + 3) (by positivity) z
    calc (A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3 * sb1w ((d : ℝ) + 3) z)
        = (A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3) * sb1w ((d : ℝ) + 3) z := by ring
      _ ≤ (A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3) := mul_le_of_le_one_right hcoef hw
  have hcomp : ∀ j : Fin d, |sb1_lv_e D (sb1kM d D.s M) hT ρ r x j - sb1_lv_e D (sb1kM d D.s M) hT ρ r y j| ≤
      d * K * ‖x - y‖ := by
    intro j
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun x => sb1_lv_e D (sb1kM d D.s M) hT ρ r x j)
      (C := d * K) (s := Set.univ) (x := y) (y := x)
      (fun z _ => (sb1_e_deriv H hT hk4 hr z j).elim fun L hL => hL.1.differentiableAt)
      (fun z _ => by
        obtain ⟨L, hL, hLi⟩ := sb1_e_deriv H hT hk4 hr z j
        rw [hL.fderiv]
        exact sb1_clm_norm_le L hK0 fun i => by rw [hLi i]; exact hdK z i j)
      convex_univ (Set.mem_univ _) (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact this
  refine (sb1_lv_norm_le_sum _).trans ?_
  calc ∑ j, |(sb1_lv_e D (sb1kM d D.s M) hT ρ r x - sb1_lv_e D (sb1kM d D.s M) hT ρ r y) j|
      ≤ ∑ _j : Fin d, d * K * ‖x - y‖ := Finset.sum_le_sum fun j _ => by
        simp only [PiLp.sub_apply]; exact hcomp j
    _ = _ := by simp; ring

end Lip

end HRS.MS.MfeConf
