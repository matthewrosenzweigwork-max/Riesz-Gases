import HRS.MS.SA12K10

/-!
# S.A.12 C1, convergence of the mollified periodic drifts along a diagonal

The assembly of `expanding_tori_drift_convergence_proof` (`ToriConv`) with the level hypothesis supplied by
`sa12k_lvl_diag`: for `τh(L) → τs`, `D^j b̃_L[τh L] → D^j b[τs]` locally uniformly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv

variable {d : ℕ}

theorem sa12k_drift_conv_diag (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (T Λ : ℝ)
    (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ)
    (hM : PDE.MatBound MB M) (V : Euc d → ℝ) (hV : ContDiff ℝ ∞ V) {ρ : ℝ → Euc d → ℝ}
    (hρ : CoeffHypRd s m Λ T ρ) (γ : ℝ → Euc d → ℝ)
    (hγ : ∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L)) (invβ : ℝ)
    {τh : ℝ → ℝ} (hτh : ∀ L, τh L ∈ Icc (0 : ℝ) T) {τs : ℝ} (hτs : τs ∈ Icc (0 : ℝ) T)
    (htend : Tendsto τh atTop (𝓝 τs)) {j : ℕ} (hj : j ≤ m + 1) (K : Set (Euc d)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, max 1 L₀ ≤ L → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (torusDriftL M L (γ L)
          (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ (τh L)) L))
          (perL L fun x => ζ (L⁻¹ • x) * V x)) x -
        iteratedFDeriv ℝ j (meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ τs)) x‖ ≤ ε := by
  classical
  obtain ⟨Kf, Cn, hKern⟩ := tcv_kerns_coord hd hs0 hsd
  have hk := fun i => hKern γ hγ i
  set μ : ℝ → Euc d → ℝ := fun L =>
    sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ (τh L)) L) with hμ
  set VL : ℝ → Euc d → ℝ := fun L => perL L fun x => ζ (L⁻¹ • x) * V x with hVL
  have hlvl : tcv_Lvl d j μ (ρ τs) := sa12k_lvl_diag s m T Λ ζ hζ hρ hτh hτs htend hj
  have main := fun i => tcv_main hd hsd (hk i) j ℝ μ (ρ τs) hlvl
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
  have hρd : Differentiable ℝ (ρ τs) := tcv_cd_diff hcdg
  have hρ1 : ∀ y, ‖fderiv ℝ (ρ τs) y‖ ≤ Bd := fun y => by
    have := hbg 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have hρint : Integrable (ρ τs) := by
    have h0 := hint 0 (by omega)
    simp only [norm_iteratedFDeriv_zero] at h0
    exact (integrable_norm_iff hρd.continuous.aestronglyMeasurable).1 h0
  -- the coordinates of `F_L` and `F_E`
  have hFLc : ∀ x' c, convGradConvL L (gradient (γ L)) (μ L) x' c =
      tcb_T L (fun z => gradient (γ L) z c) (μ L) x' := fun x' c =>
    tcb_conv_coord (gradient (γ L)) (fun i => (hk i).kern L hL1) (μ L) hμ1 Bd Bd hμ0 hμ1b x' c
  have hFEc : ∀ x' c, convGradConvW (rieszKernelGrad d s) (ρ τs) x' c =
      tcv_TE (fun z => gradient (rieszKernel d s) z c) (ρ τs) x' := fun x' c =>
    tcv_convW_coord (rieszKernelGrad d s) (ρ τs) x'
      (fun i => tcv_F_integrable_E hd hsd (hk i) (ρ τs) hρd Bd hρ1 hρint x') c
  have hFLvec : convGradConvL L (gradient (γ L)) (μ L) = fun x' =>
      ∑ i : Fin d, tcb_T L (fun z => gradient (γ L) z i) (μ L) x' •
        (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    funext x'
    ext c
    rw [hFLc x' c]
    simp [Pi.single_apply]
  have hFEvec : convGradConvW (rieszKernelGrad d s) (ρ τs) = fun x' =>
      ∑ i : Fin d, tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ τs) x' •
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
      (tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ τs)) := fun i => (main i).1
  have hFLcd : ContDiff ℝ (j : WithTop ℕ∞) (convGradConvL L (gradient (γ L)) (μ L)) := by
    rw [hFLvec]
    exact ContDiff.sum fun i _ => (hTLcd i).smul contDiff_const
  have hFEcd : ContDiff ℝ (j : WithTop ℕ∞) (convGradConvW (rieszKernelGrad d s) (ρ τs)) := by
    rw [hFEvec]
    exact ContDiff.sum fun i _ => (hTEcd i).smul contDiff_const
  have hPLcd : ContDiff ℝ (j : WithTop ℕ∞) (fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y)) :=
    Tm.contDiff.comp hFLcd
  have hPEcd : ContDiff ℝ (j : WithTop ℕ∞)
      (fun y => Tm (convGradConvW (rieszKernelGrad d s) (ρ τs) y)) := Tm.contDiff.comp hFEcd
  have hgV : ContDiff ℝ (j : WithTop ℕ∞) (gradient V) :=
    (tcb_grad_contDiff V m hV).of_le (by exact_mod_cast hj)
  -- the drifts
  have hdriftL : torusDriftL M L (γ L) (μ L) (VL L) =
      fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y) - gradient (VL L) y := by
    funext y
    show Torus.matVec M (convGradConvL L (gradient (γ L)) (μ L) y) - gradient (VL L) y = _
    rw [hTm]
  have hdriftE : meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ τs) =
      fun y => Tm (convGradConvW (rieszKernelGrad d s) (ρ τs) y) - gradient V y := by
    funext y
    show Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ τs) y) - gradient V y = _
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
  have e2 : iteratedFDeriv ℝ j (meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ τs)) x =
      iteratedFDeriv ℝ j (fun y => Tm (convGradConvW (rieszKernelGrad d s) (ρ τs) y)) x -
        iteratedFDeriv ℝ j (gradient V) x := by
    rw [hdriftE]
    exact iteratedFDeriv_sub_apply hPEcd.contDiffAt hgV.contDiffAt
  have e3 : iteratedFDeriv ℝ j (fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y)) x -
      iteratedFDeriv ℝ j (fun y => Tm (convGradConvW (rieszKernelGrad d s) (ρ τs) y)) x =
      iteratedFDeriv ℝ j (fun y => Tm (convGradConvL L (gradient (γ L)) (μ L) y -
        convGradConvW (rieszKernelGrad d s) (ρ τs) y)) x := by
    rw [← iteratedFDeriv_sub_apply hPLcd.contDiffAt hPEcd.contDiffAt]
    congr 1
    funext y
    simp [map_sub]
  -- the difference vector
  have hDvec : (fun y => convGradConvL L (gradient (γ L)) (μ L) y -
      convGradConvW (rieszKernelGrad d s) (ρ τs) y) = fun y => ∑ i : Fin d,
        (tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
          tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ τs) y) •
          (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    funext y
    rw [hFLvec, hFEvec]
    simp only [sub_smul, Finset.sum_sub_distrib]
  have hUcd : ∀ i : Fin d, ContDiff ℝ (j : WithTop ℕ∞) (fun y =>
      tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
        tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ τs) y) := fun i =>
    (hTLcd i).sub (hTEcd i)
  have hDcd : ContDiff ℝ (j : WithTop ℕ∞) (fun y => convGradConvL L (gradient (γ L)) (μ L) y -
      convGradConvW (rieszKernelGrad d s) (ρ τs) y) := hFLcd.sub hFEcd
  have h4 := Tm.norm_iteratedFDeriv_comp_left (hDcd.contDiffAt (x := x)) (le_refl (j : WithTop ℕ∞))
  have h5 : ‖iteratedFDeriv ℝ j (fun y => convGradConvL L (gradient (γ L)) (μ L) y -
      convGradConvW (rieszKernelGrad d s) (ρ τs) y) x‖ ≤
      ∑ i : Fin d, ‖iteratedFDeriv ℝ j (fun y =>
        tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
          tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ τs) y) x‖ := by
    rw [hDvec]
    exact tcv_vec_pt j _ hUcd x
  have h6 : ∀ i : Fin d, ‖iteratedFDeriv ℝ j (fun y =>
      tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
        tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ τs) y) x‖ ≤
      ε / ((‖Tm‖ + 1) * ((d : ℝ) + 1)) := fun i => by
    show ‖iteratedFDeriv ℝ j ((tcb_T L (fun z => gradient (γ L) z i) (μ L)) -
      (tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ τs))) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (hTLcd i).contDiffAt (hTEcd i).contDiffAt]
    exact hL₀i i L (hLi i) x hx
  have h7 : ∑ i : Fin d, ‖iteratedFDeriv ℝ j (fun y =>
      tcb_T L (fun z => gradient (γ L) z i) (μ L) y -
        tcv_TE (fun z => gradient (rieszKernel d s) z i) (ρ τs) y) x‖ ≤
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
      iteratedFDeriv ℝ j (meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ τs)) x‖ ≤ ε := by
    rw [e1, e2, sub_sub_sub_cancel_right, e3]
    calc _ ≤ ‖Tm‖ * ‖iteratedFDeriv ℝ j (fun y => convGradConvL L (gradient (γ L)) (μ L) y -
          convGradConvW (rieszKernelGrad d s) (ρ τs) y) x‖ := h4
      _ ≤ ‖Tm‖ * (d * (ε / ((‖Tm‖ + 1) * ((d : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left (h5.trans h7) hTm0
      _ ≤ ε := hfin
  exact hgoal


end HRS.MH.AdjointRd.Phase2SA12Construction
