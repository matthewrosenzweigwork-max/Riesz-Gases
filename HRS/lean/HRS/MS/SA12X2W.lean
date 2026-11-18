import HRS.MS.SA12X2V

/-!
# S.A.12 N8 (SA12X2), part W: one term `∫ ω² ∂_l Z T_i(∂^σ[(∂_l a) ∂_j ∂^t F])` of the telescoped remainder

`∂^σ[c K] = c ∂_j Z + L` with `Z = ∂^σ ∂^t F`; the first part is `sa12x2_N4term`, the second `sa12x2_Lterm`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_term (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    (m : ℕ) (Ka Kw Ke Kp R : ℝ) (hKa : 0 ≤ Ka) (hKw : 0 ≤ Kw) (hKe : 0 ≤ Ke) (hKp : 0 ≤ Kp)
    (hR : 1 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c0 : Euc d) (om η a μ W F : Euc d → ℝ) (i l j : Fin d) (r s' : ℕ)
      (σ : Fin r → Fin d) (t : Fin s' → Fin d),
      r + s' + 1 ≤ m →
      ContDiff ℝ 2 om → HasCompactSupport om → (∀ x, |om x| ≤ 1) →
      (∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k om x‖ ≤ Kw) → Function.support om ⊆ closedBall c0 R →
      ContDiff ℝ 2 η → HasCompactSupport η → Function.support η ⊆ closedBall c0 R → (∀ x, η x ≤ 1) →
      (∀ k ≤ 1, ∀ x, ‖iteratedFDeriv ℝ k η x‖ ≤ Ke) →
      (∀ x, om x ≠ 0 → η x = 1) → (∀ x ∈ tsupport a, η x = 1) →
      Continuous W → HasCompactSupport W → (∀ y, 0 ≤ W y) → (∀ y ∈ tsupport om, 1 ≤ W y) →
      (∀ y ∈ tsupport η, 1 ≤ W y) →
      ContDiff ℝ (m + 1) a → Function.support a ⊆ closedBall c0 R →
      (∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka) →
      ContDiff ℝ 3 μ → (∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k μ x‖ ≤ Kp) →
      (∀ x, om x ^ 2 * D1 l a x = om x ^ 2 * D1 l μ x) → ContDiff ℝ ∞ F →
      |∫ x, om x ^ 2 * D1 l (partialDeriv σ (partialDeriv t F)) x *
          firstRiesz d s i (sa12x2_tv a F j ⟨r, s', σ, t, l⟩) x| ≤
        K * ∫ x, W x * sa12z3_Y m F x := by
  obtain ⟨K4, hK40, hK4⟩ := sa12x2_N4term hd hs0 hsd hs1 R Ka (48 * Kw ^ 2 * Kp) hR hKa
    (by positivity)
  obtain ⟨KL, hKL0, hKL⟩ := sa12x2_Lterm hd hs0 hsd hs1 m Ka Kw hKa hKw
  set cT := sa12z3_cT d m with hcT
  have hcT0 : 0 ≤ cT := sa12z3_cT_nonneg d m
  refine ⟨K4 * ((2 * Ke) ^ 2 * cT) + KL, by positivity, ?_⟩
  intro c0 om η a μ W F i l j r s' σ t hrs hom homc hom1 hKwb homs hη hηc hηs hηle hηb hηom hηa
    hW hWcs hW0 hWo hWη ha hasup hKab hμ hμb hamu hF
  have hm1 : 1 ≤ m := by omega
  have hG : ContDiff ℝ ∞ (partialDeriv t F) := sa12z3_pd_contDiff_inf hF t
  have hZinf : ContDiff ℝ ∞ (partialDeriv σ (partialDeriv t F)) := sa12z3_pd_contDiff_inf hG σ
  set Z : Euc d → ℝ := partialDeriv σ (partialDeriv t F) with hZdef
  have hZ2 : ContDiff ℝ 2 Z := sa12z3_cd_of_inf hZinf 2
  have ha2 : ContDiff ℝ 2 a := ha.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hμ2 : ContDiff ℝ 2 μ := hμ.of_le (by norm_num)
  have hasupc : HasCompactSupport a :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hasup
  -- `c = ∂_l a`
  set c : Euc d → ℝ := D1 l a with hc
  have hc1 : ContDiff ℝ 1 c := D1_contDiff ha2 l
  have hcsupp : HasCompactSupport c := D1_supp hasupc l
  have hcts : ∀ x, c x ≠ 0 → x ∈ tsupport a := fun x hx => by
    have : fderiv ℝ a x ≠ 0 := fun h0 => hx (by simp [hc, D1, h0])
    exact support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 this)
  have hcL : ∀ x y, |c x - c y| ≤ Ka * ‖x - y‖ := by
    refine sa12x2_lip_D1 ha2 hKa (fun x => ?_) l
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ a), norm_iteratedFDeriv_fderiv]
    exact hKab 2 (by omega) x
  -- the decomposition
  have hcomm : ∀ y, partialDeriv σ (D1 j (partialDeriv t F)) y =
      D1 j (partialDeriv σ (partialDeriv t F)) y := fun y =>
    sa12z3_pd_D1_comm j r (partialDeriv t F) (sa12z3_cd_of_inf hG _) σ y
  obtain ⟨hL1, hLc, hLs⟩ := sa12x2_L_reg ha hF hasup l j (by omega) σ t
  set L : Euc d → ℝ := sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ with hL
  have hdec : ∀ y, sa12x2_tv a F j ⟨r, s', σ, t, l⟩ y = c y * D1 j Z y + L y := by
    intro y
    simp only [sa12x2_tv, hL, sa12x2_L, hc, hZdef, hcomm y]
    ring
  have hZ1 : ContDiff ℝ 1 Z := hZ2.of_le (by norm_num)
  have hDjZ : ContDiff ℝ 1 (D1 j Z) := D1_contDiff hZ2 j
  have hf1 : ContDiff ℝ 1 (fun y => c y * D1 j Z y) := hc1.mul hDjZ
  have hf1c : HasCompactSupport (fun y => c y * D1 j Z y) := hcsupp.mul_right
  have hfun : sa12x2_tv a F j ⟨r, s', σ, t, l⟩ = fun y => c y * D1 j Z y + L y := funext hdec
  rw [hfun]
  have hTadd := fun x => sa12x2_first_add hs0 hsd i hf1 hf1c hL1 hLc x
  simp_rw [hTadd]
  -- integrability
  have hom2c : HasCompactSupport (fun x => om x ^ 2) :=
    homc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hU : Continuous (fun x => om x ^ 2 * D1 l Z x) :=
    (hom.continuous.pow 2).mul (D1_contDiff hZ2 l).continuous
  have hUc : HasCompactSupport (fun x => om x ^ 2 * D1 l Z x) := hom2c.mul_right
  have hT1 : Continuous (firstRiesz d s i (fun y => c y * D1 j Z y)) :=
    sa12z3_firstRiesz_cont hs0 hsd i hf1 hf1c
  have hT2 : Continuous (firstRiesz d s i L) := sa12z3_firstRiesz_cont hs0 hsd i hL1 hLc
  have hI1 : Integrable (fun x => om x ^ 2 * D1 l Z x * firstRiesz d s i (fun y => c y * D1 j Z y) x)
      volume := (hU.mul hT1).integrable_of_hasCompactSupport hUc.mul_right
  have hI2 : Integrable (fun x => om x ^ 2 * D1 l Z x * firstRiesz d s i L x) volume :=
    (hU.mul hT2).integrable_of_hasCompactSupport hUc.mul_right
  simp_rw [mul_add]
  rw [integral_add hI1 hI2]
  have he0 : 0 ≤ ∫ x, W x * sa12z3_Y m F x :=
    integral_nonneg fun x => mul_nonneg (hW0 x) (sa12z3_Y_nonneg _ _ _)
  set e : ℝ := ∫ x, W x * sa12z3_Y m F x with he
  -- second part
  have hb2 := hKL c0 R om a W F i l j r s' σ t hrs hom homc hom1 hKwb hW hWcs hW0 hWo
    (fun y hy => hWη y (by
      have := hηa y hy
      exact subset_tsupport η (fun h0 => by rw [h0] at this; exact zero_ne_one this)))
    ha hasup hKab hF
  -- first part
  have hKz : ∀ y, |Z y| ≤ sa12z3_T m F y := fun y =>
    ((sa12z3_pd_le_norm _ y σ).trans ((sa12x2_jet hF s' r t y).trans
      (sa12x2_iter_le_T _ (by omega) y)))
  have hKz1 : ∀ y, ‖fderiv ℝ Z y‖ ≤ sa12z3_T m F y := fun y => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact (sa12x2_jet hG r 1 σ y).trans ((sa12x2_jet hF s' (1 + r) t y).trans
      (sa12x2_iter_le_T _ (by omega) y))
  have hKt : ∀ y, 0 ≤ sa12z3_T m F y := fun y => sa12z3_T_nonneg m F y
  have hηe0 : ∀ y, |η y| ≤ Ke := fun y => by
    have := hηb 0 (by norm_num) y
    simpa [norm_iteratedFDeriv_zero] using this
  have hηe1 : ∀ y, ‖fderiv ℝ η y‖ ≤ Ke := fun y => by
    have := hηb 1 le_rfl y
    rwa [norm_iteratedFDeriv_one (𝕜 := ℝ)] at this
  have hηd : ∀ y, DifferentiableAt ℝ η y := fun y => (hη.differentiable (by norm_num)) y
  have hZd : ∀ y, DifferentiableAt ℝ Z y := fun y => (hZ2.differentiable (by norm_num)) y
  have hηZ : ContDiff ℝ 2 (fun x => η x * Z x) := hη.mul hZ2
  have hηZc : HasCompactSupport (fun x => η x * Z x) := hηc.mul_right
  have hsupp1 : ∀ y, η y * Z y ≠ 0 → 1 ≤ W y := fun y hy =>
    hWη y (subset_tsupport η (left_ne_zero_of_mul hy))
  have b1 := sa12x2_wl2 (m := m) (K := 2 * Ke) hW hWcs hF hηZ.continuous hηZc hsupp1
    (fun y => by
      rw [abs_mul]
      have := mul_le_mul (hηe0 y) (hKz y) (abs_nonneg _) hKe
      have h3 : Ke * sa12z3_T m F y ≤ 2 * Ke * sa12z3_T m F y := by nlinarith [hKt y]
      linarith) hW0
  have b2 := sa12x2_wl2 (m := m) (K := 2 * Ke) hW hWcs hF
    ((hηZ.continuous_fderiv (by norm_num)).norm) (hηZc.fderiv (𝕜 := ℝ)).norm
    (fun y hy => hWη y (tsupport_mul_subset_left (f := η) (g := Z)
      (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2
        (fun h0 => hy (by simp [h0]))))))
    (fun y => by
      rw [abs_of_nonneg (norm_nonneg _)]
      refine (sa12x2_fderiv_mul_norm y (hηd y) (hZd y)).trans ?_
      have h1 := mul_le_mul (hηe0 y) (hKz1 y) (norm_nonneg _) hKe
      have h2 := mul_le_mul (hKz y) (hηe1 y) (norm_nonneg _) (hKt y)
      nlinarith [h1, h2, hKt y]) hW0
  -- the coefficient `a' = ω² ∂_l μ`
  set a' : Euc d → ℝ := fun x => om x ^ 2 * D1 l μ x with ha'
  have hDlμ : ContDiff ℝ 2 (D1 l μ) :=
    (hμ.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have ha'2 : ContDiff ℝ 2 a' := (hom.pow 2).mul hDlμ
  have ha'c : HasCompactSupport a' := hom2c.mul_right
  have hQj := sa12x2_sq_jets hom hKwb
  have ha'jet : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k a' x‖ ≤ 16 * Kw ^ 2 * Kp := by
    intro k hk x
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (2 : WithTop ℕ∞)) (f := fun y => om y ^ 2)
      (g := D1 l μ) (hf := hom.pow 2) (hg := hDlμ) x (n := k) (by exact_mod_cast hk)
    refine h1.trans ?_
    have h2 : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => om y ^ 2) x‖ *
        ‖iteratedFDeriv ℝ (k - i) (D1 l μ) x‖ ≤ (k.choose i : ℝ) * (4 * Kw ^ 2 * Kp) := by
      intro i hi
      have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have b1 := hQj i (by omega) x
      have b2 : ‖iteratedFDeriv ℝ (k - i) (D1 l μ) x‖ ≤ Kp :=
        (sa12x2_norm_D1' (k := k - i) (hμ.of_le (by
          exact_mod_cast (by omega : k - i + 1 ≤ 3))) l x).trans (hμb _ (by omega) x)
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => om y ^ 2) x‖ *
            ‖iteratedFDeriv ℝ (k - i) (D1 l μ) x‖ ≤ (k.choose i : ℝ) * (4 * Kw ^ 2) * Kp := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum h2).trans ?_
    rw [← Finset.sum_mul]
    have : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by exact_mod_cast Nat.sum_range_choose k
    rw [this]
    have h3 : (2 : ℝ) ^ k ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hk
    have h4 : 0 ≤ 4 * Kw ^ 2 * Kp := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  have ha'cb : MemCb 2 a' := sa12z3_memCb_of_cc ha'2 ha'c
  have ha'cbn : cbNorm 2 a' ≤ 48 * Kw ^ 2 * Kp := by
    refine (sa12x2_cb_le ha'jet).trans (le_of_eq ?_)
    push_cast; ring
  have hb1 := hK4 c0 om η c a' Z i l j ((2 * Ke) ^ 2 * cT * e) hom homc hom1 homs hη hηc hηs hηle
    hηom (fun x hx => hηa x (hcts x hx)) hc1 hcL ha'cb ha'cbn hamu hZ2 (by positivity) b1 b2
  have hb1' : |∫ x, om x ^ 2 * D1 l Z x * firstRiesz d s i (fun y => c y * D1 j Z y) x| ≤
      K4 * ((2 * Ke) ^ 2 * cT * e) := by
    exact hb1
  have hb2' : |∫ x, om x ^ 2 * D1 l Z x * firstRiesz d s i L x| ≤ KL * e := hb2
  refine (abs_add_le _ _).trans ?_
  nlinarith [hb1', hb2']

end HRS.MH.AdjointRd.Phase2SA12Near
