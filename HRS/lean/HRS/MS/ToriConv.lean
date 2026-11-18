import HRS.MS.ToriConvAux7

/-!
# MS-TORI-DRIFTCONV: convergence of the drifts (`expanding_tori_drift_convergence`, S.A.34)

`expanding_tori_drift_convergence_proof` restates `HRS.Whole.AppendixALemmas.expanding_tori_drift_convergence`
(frozen in `HRS/Whole/AppendixALemmas.lean`, statement copied verbatim).

Route (see `ToriConvPlan.md`): `b_L = M F_L - ∇V_L`, `b = M F_E - ∇V`, with `F_L`, `F_E` the vectors of the scalar
operators `T^{Q_L}_{k_{L,i}} μ_L` and `T^E_{k_{E,i}} ρ` (`ToriCoefBAux5`, `ToriConvAux4`); `D^j T^{Q_L} μ_L → D^j T^E ρ`
locally uniformly (`tcv_main`, by induction on `j`, with the differentiability of `T^E ρ` obtained from the locally
uniform limit), and `V_L = V` on `|y| < L/4`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriConv

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

/-- `V_L = V` on `|y| < L/4`. -/
theorem tcv_VL_eq {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) {L : ℝ} (hL : 0 < L)
    (V : Euc d → ℝ) (y : Euc d) (hy : ‖y‖ < L / 4) :
    perL L (fun x => ζ (L⁻¹ • x) * V x) y = V y := by
  have hvan : ∀ y : Euc d, L / 3 ≤ ‖y‖ → ζ (L⁻¹ • y) * V y = 0 := fun y hy => by
    rw [tca_zeta_far_val hζ L hL y hy, zero_mul]
  have h0 := tca_perL_central L hL (fun x => ζ (L⁻¹ • x) * V x) hvan y (by linarith) 0
  rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp] at h0
  simp only [Function.comp_apply] at h0
  have h1 := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.injective h0
  rw [h1]
  have hz1 : ζ (L⁻¹ • y) = 1 := by
    apply hζ.2.2.2.2
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hL), inv_mul_eq_div, div_le_iff₀ hL]
    linarith
  rw [hz1, one_mul]

theorem tcv_VL_eventuallyEq {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) {L : ℝ} (hL : 0 < L)
    (V : Euc d → ℝ) (x : Euc d) (hx : ‖x‖ < L / 4) :
    gradient (perL L (fun x => ζ (L⁻¹ • x) * V x)) =ᶠ[𝓝 x] gradient V := by
  have hmem : Metric.ball (0 : Euc d) (L / 4) ∈ 𝓝 x :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hx)
  have heq : perL L (fun x => ζ (L⁻¹ • x) * V x) =ᶠ[𝓝 x] V := by
    filter_upwards [hmem] with y hy
    exact tcv_VL_eq hζ hL V y (by rwa [Metric.mem_ball, dist_zero_right] at hy)
  filter_upwards [Filter.EventuallyEq.fderiv (𝕜 := ℝ) heq] with y hy
  unfold gradient
  rw [hy]

theorem expanding_tori_drift_convergence_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (T Λ ΛV MB G₀ : ℝ) (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ)
    (M : Matrix (Fin d) (Fin d) ℝ) (V : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hM : PDE.MatBound MB M) (hV : VHypRd (m + 3) ΛV G₀ V)
    (hρ : CoeffHypRd s m Λ T ρ)
    (γ : ℝ → Euc d → ℝ) (hγ : ∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L))
    (invβ : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (K : Set (Euc d)) (hK : IsCompact K)
    (j : ℕ) (hj : j ≤ m + 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, max 1 L₀ ≤ L → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (torusDriftL M L (γ L)
          (perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x))
          (perL L fun x => ζ (L⁻¹ • x) * V x)) x -
        iteratedFDeriv ℝ j (meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ t)) x‖ ≤ ε := by
  classical
  obtain ⟨Kf, Cn, hKern⟩ := tcv_kerns_coord hd hs0 hsd
  have hk := fun i => hKern γ hγ i
  set μ : ℝ → Euc d → ℝ := fun L => perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ *
    (ζ (L⁻¹ • x) * ρ t x) with hμ
  set VL : ℝ → Euc d → ℝ := fun L => perL L fun x => ζ (L⁻¹ • x) * V x with hVL
  have hlvl : tcv_Lvl d j μ (ρ t) := tcv_lvl_mu m T Λ s ζ hζ ρ hρ t ht j hj
  have main := fun i => tcv_main hd hsd (hk i) j ℝ μ (ρ t) hlvl
  obtain ⟨L₁, Bd, hL₁, hcd, hcdg, hb, hbg, hint, hloc, htail⟩ := hlvl
  obtain ⟨Tm, hTm, hTmn⟩ := tcb_matVec_clm hd M MB hM
  obtain ⟨RK, hRK⟩ := hK.isBounded.exists_norm_le
  have hTm0 : 0 ≤ ‖Tm‖ := norm_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hε'0 : 0 < ε / ((‖Tm‖ + 1) * ((d : ℝ) + 1)) := by positivity
  choose L₀i hL₀i using fun i : Fin d => (main i).2 K hK _ hε'0
  refine ⟨∑ i, |L₀i i| + |L₁| + 4 * |RK| + 1, fun L hL x hx => ?_⟩
  have hL' : ∑ i, |L₀i i| + |L₁| + 4 * |RK| + 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hS0 : 0 ≤ ∑ i, |L₀i i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hLi : ∀ i : Fin d, L₀i i ≤ L := fun i => by
    have h1 : |L₀i i| ≤ ∑ i, |L₀i i| :=
      Finset.single_le_sum (f := fun i => |L₀i i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := le_abs_self (L₀i i)
    have := abs_nonneg L₁
    have := abs_nonneg RK
    linarith
  have hLL₁ : L₁ ≤ L := by
    have := le_abs_self L₁
    have := abs_nonneg RK
    linarith
  have hxL : ‖x‖ < L / 4 := by
    have h1 := hRK x hx
    have := le_abs_self RK
    have := abs_nonneg L₁
    linarith
  -- bounds on `μ L`
  have hμcd : ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) (μ L) := hcd L hLL₁
  have hμ1 : ContDiff ℝ 1 (μ L) := by
    refine hμcd.of_le ?_
    exact_mod_cast (by omega : 1 ≤ j + 2)
  have hμ0 : ∀ y, ‖μ L y‖ ≤ Bd := fun y => by
    have := hb L hLL₁ 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hμ1b : ∀ y, ‖fderiv ℝ (μ L) y‖ ≤ Bd := fun y => by
    have := hb L hLL₁ 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have hρd : Differentiable ℝ (ρ t) := tcv_cd_diff hcdg
  have hρ1 : ∀ y, ‖fderiv ℝ (ρ t) y‖ ≤ Bd := fun y => by
    have := hbg 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have hρint : Integrable (ρ t) := by
    have h0 := hint 0 (by omega)
    simp only [norm_iteratedFDeriv_zero] at h0
    exact (integrable_norm_iff hρd.continuous.aestronglyMeasurable).1 h0
  -- the coordinates of `F_L` and `F_E`
  have hFLc : ∀ x' c, convGradConvL L (gradient (γ L)) (μ L) x' c =
      tcb_T L (fun z => gradient (γ L) z c) (μ L) x' := fun x' c =>
    tcb_conv_coord (gradient (γ L)) (fun i => (hk i).kern L hL1) (μ L) hμ1 Bd Bd hμ0 hμ1b x' c
  have hFEc : ∀ x' c, convGradConvW (rieszKernelGrad d s) (ρ t) x' c =
      tcv_TE (fun z => gradient (rieszKernel d s) z c) (ρ t) x' := fun x' c =>
    tcv_convW_coord (rieszKernelGrad d s) (ρ t) x'
      (fun i => tcv_F_integrable_E hd hsd (hk i) (ρ t) hρd Bd hρ1 hρint x') c
  have hFLvec : convGradConvL L (gradient (γ L)) (μ L) = fun x' =>
      ∑ i : Fin d, tcb_T L (fun z => gradient (γ L) z i) (μ L) x' •
        (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    funext x'
    ext c
    rw [hFLc x' c]
    simp [Pi.single_apply]
  have hFEvec : convGradConvW (rieszKernelGrad d s) (ρ t) = fun x' =>
      ∑ i : Fin d, tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ t) x' •
        (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    funext x'
    ext c
    rw [hFEc x' c]
    simp [Pi.single_apply]
  -- regularity of the scalar operators
  have hTLcd : ∀ i : Fin d, ContDiff ℝ (j : WithTop ℕ∞)
      (tcb_T L (fun z => gradient (γ L) z i) (μ L)) := fun i =>
    tcv_T_contDiff ((hk i).kern L hL1) Bd j ℝ (μ L) hμcd (hb L hLL₁)
  have hTEcd : ∀ i : Fin d, ContDiff ℝ (j : WithTop ℕ∞)
      (tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ t)) := fun i => (main i).1
  have hFLcd : ContDiff ℝ (j : WithTop ℕ∞) (convGradConvL L (gradient (γ L)) (μ L)) := by
    rw [hFLvec]
    exact ContDiff.sum fun i _ => (hTLcd i).smul contDiff_const
  have hFEcd : ContDiff ℝ (j : WithTop ℕ∞) (convGradConvW (rieszKernelGrad d s) (ρ t)) := by
    rw [hFEvec]
    exact ContDiff.sum fun i _ => (hTEcd i).smul contDiff_const
  have hPLcd : ContDiff ℝ (j : WithTop ℕ∞) (fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y)) :=
    Tm.contDiff.comp hFLcd
  have hPEcd : ContDiff ℝ (j : WithTop ℕ∞)
      (fun y => Tm (convGradConvW (rieszKernelGrad d s) (ρ t) y)) := Tm.contDiff.comp hFEcd
  have hgV : ContDiff ℝ (j : WithTop ℕ∞) (gradient V) :=
    (tcb_grad_contDiff V m hV.1).of_le (by exact_mod_cast hj)
  -- the drifts
  have hdriftL : torusDriftL M L (γ L) (μ L) (VL L) =
      fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y) - gradient (VL L) y := by
    funext y
    show Torus.matVec M (convGradConvL L (gradient (γ L)) (μ L) y) - gradient (VL L) y = _
    rw [hTm]
  have hdriftE : meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ t) =
      fun y => Tm (convGradConvW (rieszKernelGrad d s) (ρ t) y) - gradient V y := by
    funext y
    show Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ t) y) - gradient V y = _
    rw [hTm]
  have hVeq := tcv_VL_eventuallyEq hζ hL0 V x hxL
  have hbeq : torusDriftL M L (γ L) (μ L) (VL L) =ᶠ[𝓝 x]
      fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y) - gradient V y := by
    filter_upwards [hVeq] with y hy
    rw [hdriftL]
    show Tm (convGradConvL L (gradient (γ L)) (μ L) y) - gradient (VL L) y = _
    rw [show gradient (VL L) y = gradient V y from hy]
  have e1 : iteratedFDeriv ℝ j (torusDriftL M L (γ L) (μ L) (VL L)) x =
      iteratedFDeriv ℝ j (fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y)) x -
        iteratedFDeriv ℝ j (gradient V) x := by
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hbeq j).eq_of_nhds]
    exact iteratedFDeriv_sub_apply hPLcd.contDiffAt hgV.contDiffAt
  have e2 : iteratedFDeriv ℝ j (meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ t)) x =
      iteratedFDeriv ℝ j (fun y => Tm (convGradConvW (rieszKernelGrad d s) (ρ t) y)) x -
        iteratedFDeriv ℝ j (gradient V) x := by
    rw [hdriftE]
    exact iteratedFDeriv_sub_apply hPEcd.contDiffAt hgV.contDiffAt
  have e3 : iteratedFDeriv ℝ j (fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y)) x -
      iteratedFDeriv ℝ j (fun y => Tm (convGradConvW (rieszKernelGrad d s) (ρ t) y)) x =
      iteratedFDeriv ℝ j (fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y -
        convGradConvW (rieszKernelGrad d s) (ρ t) y)) x := by
    rw [← iteratedFDeriv_sub_apply hPLcd.contDiffAt hPEcd.contDiffAt]
    congr 1
    funext y
    simp [map_sub]
  -- the difference vector
  have hDvec : (fun y => convGradConvL L (gradient (γ L)) (μ L) y -
      convGradConvW (rieszKernelGrad d s) (ρ t) y) = fun y => ∑ i : Fin d,
        (tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
          tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ t) y) •
          (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    funext y
    rw [hFLvec, hFEvec]
    simp only [sub_smul, Finset.sum_sub_distrib]
  have hUcd : ∀ i : Fin d, ContDiff ℝ (j : WithTop ℕ∞) (fun y =>
      tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
        tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ t) y) := fun i =>
    (hTLcd i).sub (hTEcd i)
  have hDcd : ContDiff ℝ (j : WithTop ℕ∞) (fun y => convGradConvL L (gradient (γ L)) (μ L) y -
      convGradConvW (rieszKernelGrad d s) (ρ t) y) := hFLcd.sub hFEcd
  have h4 := Tm.norm_iteratedFDeriv_comp_left (hDcd.contDiffAt (x := x)) (le_refl (j : WithTop ℕ∞))
  have h5 : ‖iteratedFDeriv ℝ j (fun y => convGradConvL L (gradient (γ L)) (μ L) y -
      convGradConvW (rieszKernelGrad d s) (ρ t) y) x‖ ≤
      ∑ i : Fin d, ‖iteratedFDeriv ℝ j (fun y =>
        tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
          tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ t) y) x‖ := by
    rw [hDvec]
    exact tcv_vec_pt j _ hUcd x
  have h6 : ∀ i : Fin d, ‖iteratedFDeriv ℝ j (fun y =>
      tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
        tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ t) y) x‖ ≤
      ε / ((‖Tm‖ + 1) * ((d : ℝ) + 1)) := fun i => by
    show ‖iteratedFDeriv ℝ j ((tcb_T L (fun z => gradient (γ L) z i) (μ L)) -
      (tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ t))) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (hTLcd i).contDiffAt (hTEcd i).contDiffAt]
    exact hL₀i i L (hLi i) x hx
  have h7 : ∑ i : Fin d, ‖iteratedFDeriv ℝ j (fun y =>
      tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
        tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ t) y) x‖ ≤
      d * (ε / ((‖Tm‖ + 1) * ((d : ℝ) + 1))) := by
    calc _ ≤ ∑ i : Fin d, ε / ((‖Tm‖ + 1) * ((d : ℝ) + 1)) := Finset.sum_le_sum fun i _ => h6 i
      _ = _ := by simp
  have hfin : ‖Tm‖ * (d * (ε / ((‖Tm‖ + 1) * ((d : ℝ) + 1)))) ≤ ε := by
    have hden : 0 < (‖Tm‖ + 1) * ((d : ℝ) + 1) := by positivity
    have e : ‖Tm‖ * (d * (ε / ((‖Tm‖ + 1) * ((d : ℝ) + 1)))) =
        ε * ((‖Tm‖ / (‖Tm‖ + 1)) * (d / (d + 1))) := by
      field_simp
    have hq1 : ‖Tm‖ / (‖Tm‖ + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hq2 : (d : ℝ) / (d + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hq : (‖Tm‖ / (‖Tm‖ + 1)) * (d / (d + 1)) ≤ 1 :=
      mul_le_one₀ hq1 (by positivity) hq2
    rw [e]
    calc ε * ((‖Tm‖ / (‖Tm‖ + 1)) * (d / (d + 1))) ≤ ε * 1 :=
          mul_le_mul_of_nonneg_left hq hε.le
      _ = ε := mul_one ε
  have hgoal : ‖iteratedFDeriv ℝ j (torusDriftL M L (γ L) (μ L) (VL L)) x -
      iteratedFDeriv ℝ j (meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ t)) x‖ ≤ ε := by
    rw [e1, e2, sub_sub_sub_cancel_right, e3]
    calc _ ≤ ‖Tm‖ * ‖iteratedFDeriv ℝ j (fun y => convGradConvL L (gradient (γ L)) (μ L) y -
          convGradConvW (rieszKernelGrad d s) (ρ t) y) x‖ := h4
      _ ≤ ‖Tm‖ * (d * (ε / ((‖Tm‖ + 1) * ((d : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left (h5.trans h7) hTm0
      _ ≤ ε := hfin
  exact hgoal

example := (@expanding_tori_drift_convergence_proof :
  type_of% @HRS.Whole.AppendixALemmas.expanding_tori_drift_convergence)

end HRS.MS.ToriConv
