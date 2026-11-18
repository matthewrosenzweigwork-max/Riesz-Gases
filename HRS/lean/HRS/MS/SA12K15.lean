import HRS.MS.SA12K14

/-!
# S.A.12 C1: `periodic_coefficients_time`

The contract `periodic_coefficients_time` of `skeleton/cores/SA12-CONSTRUCTION.lean`: the regularised periodic
coefficients `μ_{L,ε}(τ) = η_{1/L} * perL_L(Z⁻¹ ζ_L μ(max (t-τ) 0))` (independent of `ε`) and
`V_L = perL_L(ζ_L (V - V 0))`, with `PerApprox` (uniform `PerData` bounds and uniform-in-time convergence of the
drifts and densities) and `PeriodicTimeSmooth`.
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

theorem sa12k_mfd_eq (D : WholeDyn d) {s : ℝ} (hs : D.s = s) (ρ : Euc d → ℝ) :
    meanFieldDriftW (⟨s, D.M, fun x => D.V x - D.V 0, D.invβ⟩ : WholeDyn d) ρ =
      meanFieldDriftW D ρ := by
  funext x
  unfold meanFieldDriftW
  show Torus.matVec D.M (convGradConvW (rieszKernelGrad d s) ρ x) -
    gradient (fun x => D.V x - D.V 0) x = Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x) -
    gradient D.V x
  rw [hs, sa12k_grad_shift]

set_option maxHeartbeats 4000000 in
theorem sa12k_periodic_coefficients_time (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ) (ζ : Euc d → ℝ)
    (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ Λ' ΛV' Cb L₀ : ℝ, ∀ (D : WholeDyn d) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ →
      ∀ γ : ℝ → Euc d → ℝ,
      (∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L)) →
      ∀ t ∈ Ioc (0 : ℝ) T,
      ∃ (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ),
        PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL ∧
        ∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε ∈ Ioc (0 : ℝ) 1,
          PeriodicTimeSmooth T (μL L ε) := by
  classical
  obtain ⟨Bd, Bc, L₁, hBd0, hBc0, hL₁, hbase⟩ := sa12k_base s m T Λ ζ hζ
  obtain ⟨ΛA, LA, hA⟩ :=
    HRS.MS.ToriCoefA.expanding_tori_coefficients_A_proof hd s hs0 hsd m T Λ ΛV MB G₀ 0 ζ hζ
  obtain ⟨P, hP0, hPF⟩ := sa12k_drift_F hd hs0 hsd m MB
  choose Kz hKz0 hKz using fun i : ℕ => tca_bdd_iter ζ hζ i
  set MV : ℝ := |G₀| + |ΛV| with hMV
  set CV : ℝ := (Kz 0 + Kz 1) * MV with hCV
  have hCV0 : 0 ≤ CV := mul_nonneg (add_nonneg (hKz0 0) (hKz0 1)) (by positivity)
  set Q : ℝ := P * (Bd + Bc) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨(2 : ℝ) ^ ((d : ℝ) + 3) * Bd, ΛA, Q + |ΛA| + CV, max L₁ LA, ?_⟩
  intro D μ hD γ hγ t ht
  -- the reversed path and the shifted potential
  set ρ : ℝ → Euc d → ℝ := fun τ => μ (max (t - τ) 0) with hρdef
  have hρ : CoeffHypRd s m Λ T ρ := sa12k_rev_hyp hD.hμ ht
  set V' : Euc d → ℝ := fun x => D.V x - D.V 0 with hV'def
  have hV' : VHypRd (m + 3) ΛV G₀ V' := sa12k_shift_hyp hD.hV
  have hV'0 : V' 0 = 0 := by simp [hV'def]
  have hT0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, ht.1.le.trans ht.2⟩
  have hΛ0 : 0 ≤ ΛV := (norm_nonneg _).trans (hV'.2.1 2 le_rfl (by omega) 0)
  have hG0 : 0 ≤ G₀ := (norm_nonneg _).trans hV'.2.2
  have hV'cd : ContDiff ℝ ∞ V' := hV'.1
  set μL : ℝ → ℝ → ℝ → Euc d → ℝ :=
    fun L ε τ => sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L) with hμL
  set VL : ℝ → ℝ → Euc d → ℝ := fun L ε => perL L (fun x => ζ (L⁻¹ • x) * V' x) with hVL
  have hbaseL := fun (L : ℝ) (hL : max L₁ LA ≤ L) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) =>
    hbase ρ hρ L ((le_max_left _ _).trans hL) τ hτ
  have H1 : ∀ L : ℝ, max L₁ LA ≤ L →
      PeriodicTimeSmooth T (fun τ => sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) := by
    intro L hL
    have hL7 : 7 ≤ L := hL₁.trans ((le_max_left _ _).trans hL)
    have hL0 : 0 < L := by linarith
    exact sa12k_timeSmooth hρ hζ hL0 (fun τ hτ => (hbaseL L hL τ hτ).1)
      (fun τ hτ => (hbaseL L hL τ hτ).2.1)
      (fun τ hτ => (hbaseL L hL τ hτ).2.2.2.1.continuous) (B := Bd)
      (fun τ hτ y => by
        have := (hbaseL L hL τ hτ).2.2.2.2.1 0 (by omega) y
        rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
      (sa12k_etaL_moll L)
  have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) + 3) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have H2 : ∀ L : ℝ, max L₁ LA ≤ L → ∀ ε : ℝ,
      PerData s m MB ((2 : ℝ) ^ ((d : ℝ) + 3) * Bd) ΛA νbar (Q + |ΛA| + CV) T L (γ L) D.M D.invβ
        (μL L ε) (VL L ε)
        (fun τ => torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) := by
    intro L hL ε
    have hLL1 : L₁ ≤ L := (le_max_left _ _).trans hL
    have hLLA : LA ≤ L := (le_max_right _ _).trans hL
    have hL7 : 7 ≤ L := hL₁.trans hLL1
    have hL1 : 1 ≤ L := by linarith
    have hfacts : ∀ τ ∈ Icc (0 : ℝ) T,
        (∀ (x : Euc d) (k : Fin d → ℤ),
          sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L) (x + L • latticePt k) =
            sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L) x) ∧
        ContDiff ℝ ∞ (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) ∧
        (∀ x, 0 ≤ sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L) x) ∧
        ∫ x in periodBox d L, sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L) x = 1 ∧
        (∀ j ≤ m + 3, ∀ y : Euc d,
          ‖iteratedFDeriv ℝ j (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) y‖ ≤ Bd) ∧
        (∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
          jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
            ‖iteratedFDeriv ℝ j (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) x‖ ≤
              (2 : ℝ) ^ ((d : ℝ) + 3) * Bd) ∧
        (∀ j ≤ m + 3, ∀ x : Euc d,
          ∫ z in tcb_Q d L,
            ‖iteratedFDeriv ℝ j (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) (x - z)‖ ≤ Bc) := by
      intro τ hτ
      obtain ⟨hZ, hvan, hf0cd, hμcd, hμbd, hfw, hcube, hnn, hint⟩ := hbaseL L hL τ hτ
      exact sa12k_moll_facts L hL7 (sa12k_etaL_moll L) (sa12k_rad_le_one L) hvan hnn hint hμcd hμbd
        hfw hcube
    obtain ⟨-, -, hVsm, hVbd⟩ := hA D.M V' ρ hD.hM hV' (by rw [hV'0]; simp) hρ γ hγ L
      (max_le hL1 hLLA) 0 hT0
    have hPS : PerSmooth s T L (γ L) D.M D.invβ (μL L ε) (VL L ε)
        (fun τ => torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) :=
      { hL := hL1
        hγ := hγ L hL1
        hν := hD.hν.1
        μ_periodic := fun τ hτ => (hfacts τ hτ).1
        μ_smooth := fun τ hτ => (hfacts τ hτ).2.1
        μ_prob := fun τ hτ => ⟨(hfacts τ hτ).2.2.1, (hfacts τ hτ).2.2.2.1⟩
        V_periodic := sa12k_perL_periodic L _
        V_smooth := hVsm
        b_eq := fun τ hτ => rfl }
    have hdr := sa12v_drift hd hs0 hsd hPS (H1 L hL)
    have hdata : ∀ τ ∈ Icc (0 : ℝ) T,
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j
          (torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) x‖ ≤ Q + |ΛA|) ∧
        (∀ x, ‖torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε) x‖ ≤ (Q + CV) * (1 + ‖x‖)) := by
      intro τ hτ
      obtain ⟨hper, hsm, hnn, hmass, hjet, hdec, hcub⟩ := hfacts τ hτ
      obtain ⟨hFcd, hFb⟩ := hPF L hL1 (γ L) (hγ L hL1) D.M hD.hM (μL L ε τ) Bd Bc hBd0 hBc0
        (hsm.of_le (sa12k_le_infty (m + 3))) hjet (fun i hi x => hcub i (by omega) x)
      refine sa12k_drift_data (CV := CV) hCV0 hFcd hFb hVsm hVbd (fun x => ?_)
      exact sa12k_gradVL_growth hζ L hL1 V' hV'cd ΛV G₀ hΛ0 hG0
        (fun x => hV'.2.1 2 le_rfl (by omega) x) hV'.2.2 hV'0 Kz hKz hKz0 MV
        (by rw [hMV]; linarith [le_abs_self G₀, le_abs_self ΛV]) x
    refine ⟨hPS, hD.hM, hD.hν.2, fun τ hτ j hj x => ?_, fun τ hτ j hj x => ?_, hVbd, ?_⟩
    · have := (hfacts τ hτ).2.2.2.2.1 j hj x
      exact this.trans (le_mul_of_one_le_left hBd0 hp1)
    · exact (hfacts τ hτ).2.2.2.2.2.1 j hj x
    · refine ⟨hdr.2, fun τ hτ => ?_, fun τ hτ j h1 h2 x => ?_, fun τ hτ x => ?_⟩
      · exact_mod_cast (hdata τ hτ).1
      · exact ((hdata τ hτ).2.1 j h1 h2 x).trans (by linarith)
      · exact ((hdata τ hτ).2.2 x).trans (mul_le_mul_of_nonneg_right
          (by linarith [abs_nonneg ΛA]) (by positivity))
  refine ⟨μL, VL, ?_, fun L hL ε hε => H1 L ((le_max_right 1 _).trans hL)⟩
  unfold PerApprox
  refine ⟨fun L hL ε hε => H2 L ((le_max_right 1 _).trans hL) ε, ?_⟩
  intro K hK j hj δ hδ
  -- the drift
  have hH : ∀ τs ∈ Icc (0 : ℝ) T, ∀ τh : ℝ → ℝ, (∀ L, τh L ∈ Icc (0 : ℝ) T) →
      Tendsto τh atTop (𝓝 τs) → ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (torusDriftL D.M L (γ L)
            (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ (τh L)) L))
            (perL L fun x => ζ (L⁻¹ • x) * V' x)) x -
          iteratedFDeriv ℝ j (meanFieldDriftW (⟨s, D.M, V', D.invβ⟩ : WholeDyn d) (ρ τs)) x‖ ≤ ε := by
    intro τs hτs τh hτh htend ε hε
    obtain ⟨L₀, h⟩ := sa12k_drift_conv_diag hd s hs0 hsd m T Λ ζ hζ D.M MB hD.hM V' hV'cd hρ γ hγ
      D.invβ hτh hτs htend (by omega) K hK ε hε
    exact ⟨max 1 L₀, fun L hL x hx => h L hL x hx⟩
  obtain ⟨L₁d, h1⟩ := sa12k_uniformize
    (fun (L τ : ℝ) (x : Euc d) => iteratedFDeriv ℝ j (torusDriftL D.M L (γ L)
      (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) (perL L fun x => ζ (L⁻¹ • x) * V' x)) x)
    (fun (τ : ℝ) (x : Euc d) =>
      iteratedFDeriv ℝ j (meanFieldDriftW (⟨s, D.M, V', D.invβ⟩ : WholeDyn d) (ρ τ)) x) T K hH δ hδ
  -- the density
  have hHμ : ∀ τs ∈ Icc (0 : ℝ) T, ∀ τh : ℝ → ℝ, (∀ L, τh L ∈ Icc (0 : ℝ) T) →
      Tendsto τh atTop (𝓝 τs) → ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ (τh L)) L)) x -
          iteratedFDeriv ℝ j (ρ τs) x‖ ≤ ε := by
    intro τs hτs τh hτh htend ε hε
    obtain ⟨-, -, -, -, -, -, -, -, hloc, -⟩ := sa12k_lvl_diag s m T Λ ζ hζ hρ hτh hτs htend hj
    exact hloc j le_rfl K hK ε hε
  obtain ⟨L₁m, h2⟩ := sa12k_uniformize
    (fun (L τ : ℝ) (x : Euc d) =>
      iteratedFDeriv ℝ j (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) x)
    (fun (τ : ℝ) (x : Euc d) => iteratedFDeriv ℝ j (ρ τ) x) T K hHμ δ hδ
  refine ⟨max L₁d L₁m, 1, one_pos, fun L hL ε hε hε1 τ hτ x hx => ⟨?_, ?_⟩⟩
  · have e : (D.coeff μ).drift (max (t - τ) 0) =
        meanFieldDriftW (⟨s, D.M, V', D.invβ⟩ : WholeDyn d) (ρ τ) :=
      (sa12k_mfd_eq D hD.hs.1 (ρ τ)).symm
    rw [e]
    exact h1 L ((le_max_left _ _).trans hL) τ hτ x hx
  · exact h2 L ((le_max_right _ _).trans hL) τ hτ x hx

end HRS.MH.AdjointRd.Phase2SA12Construction
