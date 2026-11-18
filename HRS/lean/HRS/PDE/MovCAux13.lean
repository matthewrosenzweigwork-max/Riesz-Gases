import HRS.PDE.MovCAux12
import HRS.PDE.MovAFinal

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_commKernel_measurable {G v : Torus d → Euc d} (hG : Measurable G) (hv : Measurable v) :
    Measurable (Function.uncurry (commKernel G v)) := by
  unfold commKernel
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  exact ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).inner
    (hG.comp (measurable_fst.sub measurable_snd))

theorem movc_continuous_mfeTransport (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (hV : Torus.IsCk 2 D.V) : Continuous (mfeTransport D ρ) := by
  have hρ1 := mova_isCk_one_of_two hρ
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  refine mova_continuous_of_components fun j => ?_
  have e : (fun x => (mfeTransport D ρ x).ofLp j) = fun x => D.invβ * (Torus.partialDeriv j ρ x / ρ x) +
      convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) x + Torus.partialDeriv j D.V x :=
    funext fun x => mova_mfeTransport_apply D hρ hpos j x
  rw [e]
  exact ((continuous_const.mul ((mova_continuous_partialDeriv hρ1 j).div
    (mova_continuous_of_isCk hρ) (fun x => (hpos x).ne'))).add
    (PDE.MFAux.continuous_convFun hgi (mova_continuous_partialDeriv hρ1 j))).add
    (mova_continuous_partialDeriv (mova_isCk_one_of_two hV) j)

theorem movc_uReg_tendsto (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) {Λ : ℝ}
    (hΛ : Torus.cbNorm 2 ρ ≤ Λ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    (z : Torus d) :
    Tendsto (fun n => movT_uReg D (M n) ρ z) atTop (𝓝 (mfeTransport D ρ z)) := by
  have hρ1 := mova_isCk_one_of_two hρ
  have hδ : Tendsto (fun n => mova_L1 (mova_kM D (M n))) atTop (𝓝 0) := by
    have := movc_gReg_L1_tendsto (b15_one_le_d D) D.hs0 D.hsd hM hM0
    simpa [mova_L1_kM_eq] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖movT_uReg D (M n) ρ z - mfeTransport D ρ z‖ ≤
      d * (mova_L1 (mova_kM D (M n)) * Λ) := by
    intro n
    refine (mova_norm_le_sum _).trans ?_
    have hj : ∀ j : Fin d, |(movT_uReg D (M n) ρ z - mfeTransport D ρ z).ofLp j| ≤
        mova_L1 (mova_kM D (M n)) * Λ := by
      intro j
      rw [mova_uReg_sub_apply D (M n) hρ1 j z]
      exact mova_abs_convFun_le (mova_integrable_kM D (M n)) (mova_continuous_partialDeriv hρ1 j)
        (fun y => (mova_abs_partialDeriv_le hρ j y).trans hΛ) z
    refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine squeeze_zero (fun n => norm_nonneg _) hb ?_
  simpa using (hδ.mul_const Λ).const_mul (d : ℝ)

theorem movc_kernel_dom {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {r : ℝ}
    (h : MovTraj D T ρ) (hr : r ∈ Set.Icc 0 T) :
    ∃ W : Torus d → ℝ, Integrable W ∧ Measurable W ∧ (∀ z, 0 ≤ W z) ∧
      (∀ M : ℝ, 0 ≤ M → ∀ x y, |commKernel (Torus.grad (b15c_gReg d D.s M)) (movT_uReg D M (ρ r)) x y|
          ≤ W (x - y)) ∧
      (∀ x y, |commKernel (periodicRieszGrad d D.s) (mfeTransport D (ρ r)) x y| ≤ W (x - y)) := by
  have hd : 1 ≤ d := b15_one_le_d D
  obtain ⟨cstar, A, hA, hc1, hc0, hdom⟩ := movsx_hdom (d := d) (s := D.s) hd D.hs0 D.hsd
  obtain ⟨c₀, Lu, hc₀, hLu, -, hL⟩ := mova_traj_bounds h
  obtain ⟨Λ₂, hΛ₂⟩ := h.bounds
  have hΛ : Torus.cbNorm 2 (ρ r) ≤ max Λ₂ 0 := (hΛ₂ r hr).trans (le_max_left _ _)
  have hΛ0 : 0 ≤ max Λ₂ 0 := le_max_right _ _
  set Λ := max Λ₂ 0 with hΛdef
  have hL10 := mova_L1_nonneg (mova_kM D 0)
  set L' := Lu + d * (Λ * mova_L1 (mova_kM D 0)) with hL'
  have hL'0 : 0 ≤ L' := by rw [hL']; positivity
  have hLuL' : Lu ≤ L' := by rw [hL']; have : 0 ≤ (d : ℝ) * (Λ * mova_L1 (mova_kM D 0)) := by positivity
                             linarith
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hgm := CoercAux.measurable_periodicRiesz_one hd D.hs0 D.hsd
  have hg0 : ∀ z : Torus d, 0 ≤ periodicRiesz d D.s z + cstar := fun z => by
    by_cases hz : z = 0
    · subst hz; exact hc0
    · linarith [hc1 z hz]
  refine ⟨fun z => (A * L') * (periodicRiesz d D.s z + cstar),
    (hgi.add (integrable_const cstar)).const_mul _, (hgm.add_const cstar).const_mul _,
    fun z => mul_nonneg (mul_nonneg hA hL'0) (hg0 z), fun M hM x y => ?_, fun x y => ?_⟩
  · have hLM : IsLipschitzVF L' (movT_uReg D M (ρ r)) := by
      refine mova_isLipschitzVF_mono ?_ (mova_lip_uReg D M (h.ck r hr) hΛ (hL r hr))
      rw [hL']
      have := mova_L1_kM_le D hM
      have h2 : (d : ℝ) * (Λ * mova_L1 (mova_kM D M)) ≤ d * (Λ * mova_L1 (mova_kM D 0)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hΛ0) (Nat.cast_nonneg d)
      linarith
    rw [movsx_commKernel_gReg hd D.hs0 D.hsd M, abs_mul,
      abs_of_nonneg (movsx_lam_nonneg D.s M (x - y))]
    refine (mul_le_mul_of_nonneg_right (movsx_lam_le_one D.s M (x - y)) (abs_nonneg _)).trans ?_
    rw [one_mul]
    exact hdom L' _ hL'0 hLM x y
  · refine (hdom Lu _ hLu.le (hL r hr) x y).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLuL' hA) (hg0 _)

theorem movc_kernel_meas {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {r : ℝ}
    (h : MovTraj D T ρ) (hr : r ∈ Set.Icc 0 T) (M : ℝ) :
    Measurable (Function.uncurry (commKernel (Torus.grad (b15c_gReg d D.s M)) (movT_uReg D M (ρ r)))) ∧
    Measurable (Function.uncurry (commKernel (periodicRieszGrad d D.s) (mfeTransport D (ρ r)))) := by
  have hρ := h.ck r hr
  have hpos := h.pos r hr
  refine ⟨movc_commKernel_measurable (mova_continuous_gradGReg D M).measurable
    (mova_continuous_uReg D M hρ hpos h.V_reg).measurable, ?_⟩
  exact movc_commKernel_measurable (KernelGrad.measurable_periodicRieszGrad D.hsd)
    (movc_continuous_mfeTransport D hρ hpos h.V_reg).measurable

theorem movc_kernel_conv {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {r : ℝ}
    (h : MovTraj D T ρ) (hr : r ∈ Set.Icc 0 T) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop)
    (hM0 : ∀ n, 0 ≤ M n) (x y : Torus d) (hxy : x ≠ y) :
    Tendsto (fun n => commKernel (Torus.grad (b15c_gReg d D.s (M n))) (movT_uReg D (M n) (ρ r)) x y)
      atTop (𝓝 (commKernel (periodicRieszGrad d D.s) (mfeTransport D (ρ r)) x y)) := by
  have hd : 1 ≤ d := b15_one_le_d D
  obtain ⟨Λ₂, hΛ₂⟩ := h.bounds
  have hΛ : Torus.cbNorm 2 (ρ r) ≤ max Λ₂ 0 := (hΛ₂ r hr).trans (le_max_left _ _)
  have hlam : Tendsto (fun n => movsx_lam d D.s (M n) (x - y)) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hM.eventually (eventually_ge_atTop (periodicRiesz d D.s (x - y)))] with n hn
    unfold movsx_lam
    rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring
  have hc : Tendsto (fun n => commKernel (periodicRieszGrad d D.s) (movT_uReg D (M n) (ρ r)) x y)
      atTop (𝓝 (commKernel (periodicRieszGrad d D.s) (mfeTransport D (ρ r)) x y)) := by
    unfold commKernel
    simp only [hxy, if_false]
    exact ((movc_uReg_tendsto D (h.ck r hr) hΛ hM hM0 x).sub
      (movc_uReg_tendsto D (h.ck r hr) hΛ hM hM0 y)).inner tendsto_const_nhds
  have e : ∀ n, commKernel (Torus.grad (b15c_gReg d D.s (M n))) (movT_uReg D (M n) (ρ r)) x y =
      movsx_lam d D.s (M n) (x - y) *
        commKernel (periodicRieszGrad d D.s) (movT_uReg D (M n) (ρ r)) x y := fun n =>
    movsx_commKernel_gReg hd D.hs0 D.hsd (M n) _ x y
  simp_rw [e]
  simpa using hlam.mul hc

end HRS
