import HRS.MS.ToriCoefBAux6

/-!
# MS-TORI-COEFB: part B of `expanding_tori_coefficients` (S.A.34, coefficient part, conjuncts 4-6)

`expanding_tori_coefficients_B_proof` proves the drift conjuncts (regularity, `C^j` bounds `1 ≤ j ≤ m+1`, linear
growth on the central cube) with the existential `Λ' C L₀` replaced by `C L₀`; `expanding_tori_coefficients_proof`
assembles the frozen statement `HRS.Whole.AppendixALemmas.expanding_tori_coefficients` from part A
(`HRS.MS.ToriCoefA.expanding_tori_coefficients_A_proof`) and part B.

Route: `b_L = M F - ∇V_L` with `F = convGradConvL L ∇γ_L μ_L`; the coordinates of `F` are the operators `T_{k_i}`
of `ToriCoefBAux1`-`ToriCoefBAux2` (differentiation under the integral sign, the derivative falling on `μ_L`),
whose kernel hypotheses are `ToriCoefBAux3` (`∇γ_L = O(|z|^{-s-1})`, `ker1_eq_gam` and scaling), whose cube
`L¹` hypothesis on `D^j μ_L` is `ToriCoefBAux4`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefB

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA

variable {d : ℕ}

theorem expanding_tori_coefficients_B_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (T Λ ΛV MB G₀ V₀ : ℝ) (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ C L₀ : ℝ, ∀ (M : Matrix (Fin d) (Fin d) ℝ) (V : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      PDE.MatBound MB M → VHypRd (m + 3) ΛV G₀ V → |V 0| ≤ V₀ → CoeffHypRd s m Λ T ρ →
      ∀ γ : ℝ → Euc d → ℝ, (∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L)) →
      let μL : ℝ → ℝ → Euc d → ℝ := fun L t =>
        perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)
      let VL : ℝ → Euc d → ℝ := fun L => perL L fun x => ζ (L⁻¹ • x) * V x
      ∀ L : ℝ, max 1 L₀ ≤ L → ∀ t ∈ Set.Icc (0 : ℝ) T,
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (torusDriftL M L (γ L) (μL L t) (VL L)) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (torusDriftL M L (γ L) (μL L t) (VL L)) x‖ ≤ C) ∧
        (∀ x : Euc d, ‖x‖ ≤ L / 2 →
          ‖torusDriftL M L (γ L) (μL L t) (VL L) x‖ ≤ C * (1 + ‖x‖)) := by
  obtain ⟨Λ', L₁, hA⟩ :=
    HRS.MS.ToriCoefA.expanding_tori_coefficients_A_proof hd s hs0 hsd m T Λ ΛV MB G₀ V₀ ζ hζ
  choose K hK0 hK using fun i : ℕ => tca_bdd_iter ζ hζ i
  obtain ⟨N, hN⟩ := tca_tail (d := d) (1 / (2 * (|Λ| + 1))) (by positivity)
  have hBε : |Λ| * (1 / (2 * (|Λ| + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg Λ]
  obtain ⟨C₀, A₀, hC₀, hA₀, hkern⟩ := tcb_kern_coord hd hs0 hsd
  set I₀ : ℝ := ∫ w : Euc d, tca_g w with hI₀
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun w => (tcb_g_pos w).le
  set Bd : ℝ := ∑ j ∈ Finset.range (m + 4), 2 * tca_S d K |Λ| j with hBd
  have hS0 : ∀ j : ℕ, 0 ≤ tca_S d K |Λ| j := fun j => tca_S_nonneg d K hK0 |Λ| (abs_nonneg _) j
  have hBd0 : 0 ≤ Bd := Finset.sum_nonneg fun j _ => by linarith [hS0 j]
  have hBdle : ∀ j : ℕ, j ≤ m + 3 → 2 * tca_S d K |Λ| j ≤ Bd := fun j hj =>
    Finset.single_le_sum (f := fun j => 2 * tca_S d K |Λ| j) (fun i _ => by linarith [hS0 i])
      (Finset.mem_range.2 (by omega))
  set Bc : ℝ := 2 ^ d * Bd * I₀ with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  set b : ℝ := A₀ * Bd + C₀ * Bc with hb
  have hb0 : 0 ≤ b := by positivity
  set MV : ℝ := |V₀| + |G₀| + |ΛV| with hMV
  set CV : ℝ := (K 0 + K 1) * MV with hCV
  have hCV0 : 0 ≤ CV := mul_nonneg (add_nonneg (hK0 0) (hK0 1)) (by positivity)
  set P : ℝ := (d : ℝ) ^ 2 * |MB| * (d * b) with hP
  have hP0 : 0 ≤ P := by positivity
  refine ⟨P + |Λ'| + CV, max L₁ (4 * (N : ℝ)), ?_⟩
  intro M V ρ hM hV hV0 hρ γ hγ μL VL L hL t ht
  have hL1 : 1 ≤ L := le_trans (le_max_left 1 _) hL
  have hL4 : (N : ℝ) ≤ L / 4 := by
    have := le_trans (le_max_right L₁ (4 * (N : ℝ))) (le_trans (le_max_right 1 _) hL)
    linarith
  have hL0 : 0 < L := by linarith
  have hLA : max 1 L₁ ≤ L :=
    max_le hL1 (le_trans (le_max_left L₁ (4 * (N : ℝ))) (le_trans (le_max_right 1 _) hL))
  obtain ⟨-, -, hVsm, hVbd⟩ := hA M V ρ hM hV hV0 hρ γ hγ L hLA t ht
  -- the density `ρ t`
  have hprob : HRS.Whole.IsProbDensity (ρ t) := hρ.prob t ht
  obtain ⟨hMC, hWfin, hWle⟩ := hρ.regular.1 t ht
  have hWle' : (weightedSupE (m + 3) ((d : ℝ) + 3) (ρ t)).toReal ≤ |Λ| := by
    have hcb0 : 0 ≤ cbNorm (m + 3) (ρ t) :=
      Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _
    have := le_abs_self Λ
    linarith
  have hWk : ∀ k : ℕ, k ≤ m + 3 → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k (ρ t) w‖ ≤ (d : ℝ) ^ k * |Λ| := fun k hk w =>
    (tca_weight_le (m + 3) ((d : ℝ) + 3) (ρ t) hWfin.ne k hk w).trans
      (mul_le_mul_of_nonneg_left hWle' (pow_nonneg (Nat.cast_nonneg d) _))
  have hρB : ∀ y : Euc d, |ρ t y| ≤ |Λ| * tca_g y := by
    intro y
    exact tca_abs_le_weight (ρ t) |Λ| (fun y' => by
      have := hWk 0 (Nat.zero_le _) y'
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, one_mul] at this
      exact this) y
  have hZ : 1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * ρ t y :=
    tca_Z_ge hζ (ρ t) hprob |Λ| (abs_nonneg _) hρB L hL0 N hL4 _ hN hBε
  have hc0 : 0 < (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ := inv_pos.2 (by linarith)
  have hc2 : (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  have hμdef : μL L t = perL L (fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)) := rfl
  have hVdef : VL L = perL L (fun x => ζ (L⁻¹ • x) * V x) := rfl
  have hvan : ∀ y : Euc d, L / 3 ≤ ‖y‖ →
      (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • y) * ρ t y) = 0 := by
    intro y hy
    rw [tca_zeta_far_val hζ L hL0 y hy, zero_mul, mul_zero]
  obtain ⟨hcd, hglob, -⟩ := tca_mu_package hζ L hL1 (m + 3) (ρ t) hMC.1 K hK hK0 |Λ|
    (abs_nonneg _) hWk _ hc0 hc2
  have hfw := fun j hj w => tcb_f_weighted hζ L hL1 (m + 3) (ρ t) hMC.1 K hK hK0 |Λ|
    (abs_nonneg _) hWk _ hc0 hc2 j hj w
  -- the coefficient `μ = μL L t`
  set μ : Euc d → ℝ := μL L t with hμ
  have hD : ∀ i ≤ m + 1 + 2, ∀ y, ‖iteratedFDeriv ℝ i μ y‖ ≤ Bd := fun i hi y =>
    (hglob i (by omega) y).trans (hBdle i (by omega))
  have hcube : ∀ i ≤ m + 1, ∀ x, ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ i μ (x - z)‖ ≤ Bc := by
    intro i hi x
    refine (tcb_cube_l1 hL0 _ hvan i (2 * tca_S d K |Λ| i) (hfw i (by omega)) x).trans ?_
    rw [hBc]
    have := hBdle i (by omega)
    have h2 : (0 : ℝ) ≤ 2 ^ d := by positivity
    calc 2 ^ d * (2 * tca_S d K |Λ| i) * ∫ w : Euc d, tca_g w
        ≤ 2 ^ d * Bd * ∫ w : Euc d, tca_g w :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h2) hI₀0
      _ = _ := rfl
  have hμ3 : ContDiff ℝ ((m + 1 + 2 : ℕ) : WithTop ℕ∞) μ := hcd
  have hμ1 : ContDiff ℝ 1 μ := hcd.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
  have hμ0 : ∀ y, ‖μ y‖ ≤ Bd := fun y => by
    have := hD 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hμ1b : ∀ y, ‖fderiv ℝ μ y‖ ≤ Bd := fun y => by
    have := hD 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  -- the kernel
  have hkc : ∀ i : Fin d, tcb_Kern L (fun z => gradient (γ L) z i) C₀ ∧
      tcb_a (fun z => gradient (γ L) z i) ≤ A₀ := hkern L hL1 (γ L) (hγ L hL1)
  -- the scalar operators
  have hTi : ∀ i : Fin d,
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (tcb_T L (fun z => gradient (γ L) z i) μ) ∧
      ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j (tcb_T L (fun z => gradient (γ L) z i) μ) x‖ ≤ b := by
    intro i
    obtain ⟨h1, h2⟩ := tcb_main (hkc i).1 Bd Bc (m + 1) ℝ μ hμ3 hD hcube
    refine ⟨h1, fun j hj x => (h2 j hj x).trans ?_⟩
    rw [hb]
    have := mul_le_mul_of_nonneg_right (hkc i).2 hBd0
    linarith
  -- the vector `F`
  set F : Euc d → Euc d := convGradConvL L (gradient (γ L)) μ with hF
  have hFc : ∀ x c, F x c = tcb_T L (fun z => gradient (γ L) z c) μ x := fun x c =>
    tcb_conv_coord (gradient (γ L)) (fun i => (hkc i).1) μ hμ1 Bd Bd hμ0 hμ1b x c
  have hFvec : F = fun x => ∑ i, tcb_T L (fun z => gradient (γ L) z i) μ x •
      (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    funext x
    ext c
    rw [hFc x c]
    simp [Pi.single_apply]
  obtain ⟨hFcd, hFb⟩ := tcb_vec_bound (m + 1) (fun i => tcb_T L (fun z => gradient (γ L) z i) μ) b
    (fun i => (hTi i).1) (fun i => (hTi i).2)
  rw [← hFvec] at hFcd hFb
  -- the matrix
  obtain ⟨Tm, hTm, hTmn⟩ := tcb_matVec_clm hd M MB hM
  have hTmn' : ‖Tm‖ ≤ (d : ℝ) ^ 2 * |MB| :=
    hTmn.trans (mul_le_mul_of_nonneg_left (le_abs_self MB) (by positivity))
  have hdrift : torusDriftL M L (γ L) μ (VL L) = fun x => Tm (F x) - gradient (VL L) x := by
    funext x
    show Torus.matVec M (F x) - gradient (VL L) x = Tm (F x) - gradient (VL L) x
    rw [hTm]
  have hgrad_cd : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (gradient (VL L)) :=
    tcb_grad_contDiff (VL L) m hVsm
  have hTF : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => Tm (F x)) :=
    Tm.contDiff.comp hFcd
  have hTFb : ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j (fun x => Tm (F x)) x‖ ≤ P := by
    intro j hj x
    have h1 := Tm.norm_iteratedFDeriv_comp_left (hFcd.of_le (by exact_mod_cast hj)).contDiffAt
      (x := x) (le_refl (j : WithTop ℕ∞))
    have h2 := hFb j hj x
    calc _ ≤ ‖Tm‖ * ‖iteratedFDeriv ℝ j F x‖ := h1
      _ ≤ ((d : ℝ) ^ 2 * |MB|) * (d * b) :=
          mul_le_mul hTmn' h2 (norm_nonneg _) (by positivity)
      _ = P := by rw [hP]
  rw [hdrift]
  refine ⟨hTF.sub hgrad_cd, fun j hj1 hjm x => ?_, fun x hx => ?_⟩
  · have e : iteratedFDeriv ℝ j (fun x => Tm (F x) - gradient (VL L) x) x =
        iteratedFDeriv ℝ j (fun x => Tm (F x)) x - iteratedFDeriv ℝ j (gradient (VL L)) x :=
      iteratedFDeriv_sub_apply ((hTF.of_le (by exact_mod_cast hjm)).contDiffAt)
        ((hgrad_cd.of_le (by exact_mod_cast hjm)).contDiffAt)
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hTFb j hjm x
    have h2 : ‖iteratedFDeriv ℝ j (gradient (VL L)) x‖ ≤ Λ' := by
      rw [tcb_grad_iter_norm]
      exact hVbd (j + 1) (by omega) (by omega) x
    have h3 : Λ' ≤ |Λ'| := le_abs_self _
    linarith
  · refine (norm_sub_le _ _).trans ?_
    have h1 : ‖Tm (F x)‖ ≤ P := by
      have := hTFb 0 (by omega) x
      rwa [norm_iteratedFDeriv_zero] at this
    have hx1 : 0 ≤ ‖x‖ := norm_nonneg x
    -- the gradient of `V_L` on the central cube
    have hV2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 V x‖ ≤ ΛV := fun x => hV.2.1 2 le_rfl (by omega) x
    have hV3 : ‖gradient V 0‖ ≤ G₀ := hV.2.2
    have hΛ0 : 0 ≤ ΛV := (norm_nonneg _).trans (hV2 0)
    have hG0 : 0 ≤ G₀ := (norm_nonneg _).trans hV3
    have hV0₀ : 0 ≤ V₀ := (abs_nonneg _).trans hV0
    have hMabs : V₀ + G₀ + ΛV ≤ MV := by
      rw [hMV]; linarith [le_abs_self V₀, le_abs_self G₀, le_abs_self ΛV]
    have hvanV : ∀ y : Euc d, L / 3 ≤ ‖y‖ → ζ (L⁻¹ • y) * V y = 0 := fun y hy => by
      rw [tca_zeta_far_val hζ L hL0 y hy, zero_mul]
    have h2 : ‖gradient (VL L) x‖ ≤ CV * (1 + ‖x‖) := by
      have e1 : ‖gradient (VL L) x‖ = ‖iteratedFDeriv ℝ 1 (VL L) x‖ := tcb_norm_gradient _ _
      have e2 : iteratedFDeriv ℝ 1 (VL L) x =
          iteratedFDeriv ℝ 1 (fun x => ζ (L⁻¹ • x) * V x) x := by
        rw [hVdef]
        exact tca_perL_central L hL0 (fun x => ζ (L⁻¹ • x) * V x) hvanV x hx 1
      have e3 := tcb_VL_grad_central hζ L hL1 V hV.1 ΛV G₀ V₀ hΛ0 hG0 hV0₀ hV2 hV3 hV0 K hK hK0 MV
        hMabs x
      rw [e1, e2]
      exact e3
    have h3 : |Λ'| ≥ 0 := abs_nonneg _
    have h4 : P ≤ P * (1 + ‖x‖) := le_mul_of_one_le_right hP0 (by linarith)
    have h5 : 0 ≤ |Λ'| * (1 + ‖x‖) := mul_nonneg h3 (by linarith)
    have h6 : (P + |Λ'| + CV) * (1 + ‖x‖) =
        P * (1 + ‖x‖) + |Λ'| * (1 + ‖x‖) + CV * (1 + ‖x‖) := by ring
    rw [h6]
    linarith [h1, h2, h4, h5]

/-- The frozen statement `HRS.Whole.AppendixALemmas.expanding_tori_coefficients`, assembled from part A
(conjuncts 1-3) and part B (conjuncts 4-6). -/
theorem expanding_tori_coefficients_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (T Λ ΛV MB G₀ V₀ : ℝ) (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ Λ' C L₀ : ℝ, ∀ (M : Matrix (Fin d) (Fin d) ℝ) (V : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      PDE.MatBound MB M → VHypRd (m + 3) ΛV G₀ V → |V 0| ≤ V₀ → CoeffHypRd s m Λ T ρ →
      ∀ γ : ℝ → Euc d → ℝ, (∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L)) →
      let μL : ℝ → ℝ → Euc d → ℝ := fun L t =>
        perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)
      let VL : ℝ → Euc d → ℝ := fun L => perL L fun x => ζ (L⁻¹ • x) * V x
      ∀ L : ℝ, max 1 L₀ ≤ L → ∀ t ∈ Set.Icc (0 : ℝ) T,
        (0 < ∫ y, ζ (L⁻¹ • y) * ρ t y) ∧
        (ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (μL L t) ∧ MemCb (m + 3) (μL L t) ∧
          cbNorm (m + 3) (μL L t) ≤ Λ' ∧
          ∀ j ≤ m + 3, ∀ x : Euc d, ‖x‖ ≤ L / 2 →
            jbracket x ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (μL L t) x‖ ≤ Λ') ∧
        (ContDiff ℝ ∞ (VL L) ∧
          ∀ j : ℕ, 2 ≤ j → j ≤ m + 3 → ∀ x : Euc d, ‖iteratedFDeriv ℝ j (VL L) x‖ ≤ Λ') ∧
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (torusDriftL M L (γ L) (μL L t) (VL L)) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (torusDriftL M L (γ L) (μL L t) (VL L)) x‖ ≤ C) ∧
        (∀ x : Euc d, ‖x‖ ≤ L / 2 →
          ‖torusDriftL M L (γ L) (μL L t) (VL L) x‖ ≤ C * (1 + ‖x‖)) := by
  obtain ⟨Λ', L₁, hA⟩ :=
    HRS.MS.ToriCoefA.expanding_tori_coefficients_A_proof hd s hs0 hsd m T Λ ΛV MB G₀ V₀ ζ hζ
  obtain ⟨C, L₂, hB⟩ := expanding_tori_coefficients_B_proof hd s hs0 hsd m T Λ ΛV MB G₀ V₀ ζ hζ
  refine ⟨Λ', C, max L₁ L₂, ?_⟩
  intro M V ρ hM hV hV0 hρ γ hγ μL VL L hL t ht
  have hLA : max 1 L₁ ≤ L :=
    max_le (le_trans (le_max_left _ _) hL)
      (le_trans (le_max_left L₁ L₂) (le_trans (le_max_right _ _) hL))
  have hLB : max 1 L₂ ≤ L :=
    max_le (le_trans (le_max_left _ _) hL)
      (le_trans (le_max_right L₁ L₂) (le_trans (le_max_right _ _) hL))
  obtain ⟨h1, h2, h3⟩ := hA M V ρ hM hV hV0 hρ γ hγ L hLA t ht
  obtain ⟨h4, h5, h6⟩ := hB M V ρ hM hV hV0 hρ γ hγ L hLB t ht
  exact ⟨h1, h2, h3, h4, h5, h6⟩

example := (@expanding_tori_coefficients_proof :
  type_of% @HRS.Whole.AppendixALemmas.expanding_tori_coefficients)

end HRS.MS.ToriCoefB
