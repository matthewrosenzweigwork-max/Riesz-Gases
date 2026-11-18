import HRS.MS.SA12X2R

/-!
# S.A.12 N8 (SA12X2), part S: the second-order Leibniz terms `∫ ω² ∂_l Z T_i(L)`

By `sa12x2_B2_bound` (skew-adjointness and one integration by parts) and the pointwise bounds of
`L`, `∂_p L`, `Z`, `∂Z` by the jet sum `T_m F`, together with `sa12x2_wl2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_sqrt_bd {g : Euc d → ℝ} {K cT e : ℝ} (hK : 0 ≤ K) (hcT : 0 ≤ cT)
    (h : ∫ x, g x ^ 2 ≤ K ^ 2 * cT * e) :
    Real.sqrt (∫ x, g x ^ 2) ≤ K * Real.sqrt cT * Real.sqrt e := by
  refine (Real.sqrt_le_sqrt h).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]

theorem sa12x2_fderiv_mul_norm {f g : Euc d → ℝ} (y : Euc d) (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) :
    ‖fderiv ℝ (fun z => f z * g z) y‖ ≤ |f y| * ‖fderiv ℝ g y‖ + |g y| * ‖fderiv ℝ f y‖ := by
  have h : HasFDerivAt (fun z => f z * g z) (f y • fderiv ℝ g y + g y • fderiv ℝ f y) y :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [h.fderiv]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs]
  exact le_rfl

theorem sa12x2_Lterm (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    (m : ℕ) (Ka Kw : ℝ) (hKa : 0 ≤ Ka) (hKw : 0 ≤ Kw) :
    ∃ KL : ℝ, 0 ≤ KL ∧ ∀ (c0 : Euc d) (R : ℝ) (om a W F : Euc d → ℝ) (i l j : Fin d) (r s' : ℕ)
      (σ : Fin r → Fin d) (t : Fin s' → Fin d),
      r + s' + 1 ≤ m → ContDiff ℝ 2 om → HasCompactSupport om → (∀ x, |om x| ≤ 1) →
      (∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k om x‖ ≤ Kw) →
      Continuous W → HasCompactSupport W → (∀ y, 0 ≤ W y) → (∀ y ∈ tsupport om, 1 ≤ W y) →
      (∀ y ∈ tsupport a, 1 ≤ W y) → ContDiff ℝ (m + 1) a → Function.support a ⊆ closedBall c0 R →
      (∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka) → ContDiff ℝ ∞ F →
      |∫ x, om x ^ 2 * D1 l (partialDeriv σ (partialDeriv t F)) x *
          firstRiesz d s i (sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ) x| ≤
        KL * ∫ x, W x * sa12z3_Y m F x := by
  obtain ⟨CB, hCB0, hCB⟩ := sa12x2_B2_bound hd hs0 hsd hs1
  set cT := sa12z3_cT d m with hcT
  have hcT0 : 0 ≤ cT := sa12z3_cT_nonneg d m
  set KLg : ℝ := Ka * (2 ^ m + 1) with hKLg
  set KLh : ℝ := Ka * 2 ^ m with hKLh
  have hKLg0 : 0 ≤ KLg := by positivity
  have hKLh0 : 0 ≤ KLh := by positivity
  set Kq : ℝ := 4 * Kw ^ 2 with hKq
  have hKq0 : 0 ≤ Kq := by positivity
  -- constants of the six `L²` norms
  set K3 : ℝ := 1 with hK3
  set K4 : ℝ := 1 + Kq with hK4
  set K5 : ℝ := Kq with hK5
  set K6 : ℝ := 2 * Kq with hK6
  refine ⟨CB * cT * (KLg * (K3 + K4) + KLh * (K5 + K6)), by positivity, ?_⟩
  intro c0 R om a W F i l j r s' σ t hrs hom hoc hom1 hKwb hW hWcs hW0 hWo hWa ha hasup hKa' hF
  set h : Euc d → ℝ := sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ with hhdef
  set Z : Euc d → ℝ := partialDeriv σ (partialDeriv t F) with hZdef
  set Q : Euc d → ℝ := fun y => om y ^ 2 with hQdef
  obtain ⟨hh1, hhc, hhs⟩ := sa12x2_L_reg ha hF hasup l j (by omega) σ t
  have hG : ContDiff ℝ ∞ (partialDeriv t F) := sa12z3_pd_contDiff_inf hF t
  have hZinf : ContDiff ℝ ∞ Z := sa12z3_pd_contDiff_inf hG σ
  have hZ2 : ContDiff ℝ 2 Z := sa12z3_cd_of_inf hZinf 2
  have hQ2 : ContDiff ℝ 2 Q := hom.pow 2
  have hQc : HasCompactSupport Q := hoc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hKws : ∀ y, 0 ≤ sa12z3_T m F y := fun y => sa12z3_T_nonneg m F y
  -- bounds on `Z`
  have hZ0 : ∀ y, |Z y| ≤ sa12z3_T m F y := fun y =>
    ((sa12z3_pd_le_norm _ y σ).trans ((sa12x2_jet hF s' r t y).trans
      (sa12x2_iter_le_T _ (by omega) y)))
  have hZ1 : ∀ y, ‖fderiv ℝ Z y‖ ≤ sa12z3_T m F y := fun y => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact (sa12x2_jet hG r 1 σ y).trans ((sa12x2_jet hF s' (1 + r) t y).trans
      (sa12x2_iter_le_T _ (by omega) y))
  -- bounds on `Q`
  have hQj := sa12x2_sq_jets hom hKwb
  have hQ1 : ∀ y, ‖fderiv ℝ Q y‖ ≤ Kq := fun y => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]; exact hQj 1 (by norm_num) y
  have hQ2' : ∀ y, ‖fderiv ℝ (fderiv ℝ Q) y‖ ≤ Kq := fun y => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ Q), norm_iteratedFDeriv_fderiv]
    exact hQj 2 le_rfl y
  have hDQ0 : ∀ y, |D1 l Q y| ≤ Kq := fun y => (sa12z3_D1_le l Q y).trans (hQ1 y)
  have hDQ1 : ∀ y, ‖fderiv ℝ (D1 l Q) y‖ ≤ Kq := fun y =>
    (sa12z3_fderiv_D1_le hQ2 l y).trans (hQ2' y)
  have hQ0 : ∀ y, |Q y| ≤ 1 := fun y => by
    show |om y ^ 2| ≤ 1
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hom1 y)
  have hQts : tsupport Q ⊆ tsupport om :=
    closure_minimal (fun z hz => subset_tsupport om (fun h0 => hz (by simp [hQdef, h0])))
      (isClosed_tsupport _)
  have hDQne : ∀ y, D1 l Q y ≠ 0 → y ∈ tsupport Q := by
    intro y hy
    have : fderiv ℝ Q y ≠ 0 := fun h0 => hy (by simp [D1, h0])
    exact support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 this)
  have hDQts : tsupport (D1 l Q) ⊆ tsupport Q :=
    closure_minimal (fun z hz => hDQne z hz) (isClosed_tsupport _)
  have hhts : tsupport h ⊆ tsupport a := closure_minimal hhs (isClosed_tsupport a)
  have hDh : Continuous (D1 l h) := (hh1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hf1d : ContDiff ℝ 2 (fun y => Q y * Z y) := hQ2.mul hZ2
  have hf1c : HasCompactSupport (fun y => Q y * Z y) := hQc.mul_right
  have hf2d : ContDiff ℝ 1 (fun y => Z y * D1 l Q y) :=
    (hZ2.of_le (by norm_num)).mul (D1_contDiff hQ2 l)
  have hf2c : HasCompactSupport (fun y => Z y * D1 l Q y) := (D1_supp hQc l).mul_left
  have hQd : ∀ y, DifferentiableAt ℝ Q y := fun y => (hQ2.differentiable (by norm_num)) y
  have hZd : ∀ y, DifferentiableAt ℝ Z y := fun y => (hZ2.differentiable (by norm_num)) y
  have hDQd : ∀ y, DifferentiableAt ℝ (D1 l Q) y := fun y =>
    ((D1_contDiff hQ2 l).differentiable one_ne_zero) y
  -- the six `L²` bounds
  have b1 := sa12x2_wl2 (m := m) (K := KLg) hW hWcs hF hDh (D1_supp hhc l)
    (fun y hy => hWa y (hhts (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2
      (fun h0 => hy (by simp [D1, h0]))))))
    (fun y => sa12x2_L_grad ha hF hKa' l j (by omega) σ t l y) hW0
  have b2 := sa12x2_wl2 (m := m) (K := KLh) hW hWcs hF hh1.continuous hhc
    (fun y hy => hWa y (hhs (Function.mem_support.2 hy)))
    (fun y => sa12x2_L_pt ha hF hKa' l j (by omega) σ t y) hW0
  have b3 := sa12x2_wl2 (m := m) (K := K3) hW hWcs hF (hf1d.continuous) hf1c
    (fun y hy => hWo y (hQts (subset_tsupport _ (fun h0 => hy (by simp [h0])))))
    (fun y => by
      show |Q y * Z y| ≤ 1 * sa12z3_T m F y
      rw [abs_mul]
      exact mul_le_mul (hQ0 y) (hZ0 y) (abs_nonneg _) zero_le_one) hW0
  have b4 := sa12x2_wl2 (m := m) (K := K4) hW hWcs hF
    ((hf1d.continuous_fderiv (by norm_num)).norm) (hf1c.fderiv (𝕜 := ℝ)).norm
    (fun y hy => hWo y (hQts ((tsupport_mul_subset_left (f := Q) (g := Z))
      (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2
        (fun h0 => hy (by simp [h0])))))))
    (fun y => by
      rw [abs_of_nonneg (norm_nonneg _)]
      refine (sa12x2_fderiv_mul_norm y (hQd y) (hZd y)).trans ?_
      have h1 := mul_le_mul (hQ0 y) (hZ1 y) (norm_nonneg _) zero_le_one
      have h2 := mul_le_mul (hZ0 y) (hQ1 y) (norm_nonneg _) (hKws y)
      show _ ≤ (1 + Kq) * _
      nlinarith [h1, h2, hKws y]) hW0
  have b5 := sa12x2_wl2 (m := m) (K := K5) hW hWcs hF hf2d.continuous hf2c
    (fun y hy => hWo y (hQts (hDQts (subset_tsupport _ (fun h0 => hy (by simp [h0]))))))
    (fun y => by
      show |Z y * D1 l Q y| ≤ Kq * sa12z3_T m F y
      rw [abs_mul]
      have := mul_le_mul (hZ0 y) (hDQ0 y) (abs_nonneg _) (hKws y)
      linarith) hW0
  have b6 := sa12x2_wl2 (m := m) (K := K6) hW hWcs hF
    ((hf2d.continuous_fderiv one_ne_zero).norm) (hf2c.fderiv (𝕜 := ℝ)).norm
    (fun y hy => hWo y (hQts (hDQts ((tsupport_mul_subset_right (f := Z) (g := D1 l Q))
      (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2
        (fun h0 => hy (by simp [h0])))))))) 
    (fun y => by
      rw [abs_of_nonneg (norm_nonneg _)]
      refine (sa12x2_fderiv_mul_norm y (hZd y) (hDQd y)).trans ?_
      have h1 := mul_le_mul (hZ0 y) (hDQ1 y) (norm_nonneg _) (hKws y)
      have h2 := mul_le_mul (hDQ0 y) (hZ1 y) (norm_nonneg _) hKq0
      show _ ≤ (2 * Kq) * _
      nlinarith [h1, h2, hKws y]) hW0
  have he0 : 0 ≤ ∫ x, W x * sa12z3_Y m F x :=
    integral_nonneg fun x => mul_nonneg (hW0 x) (sa12z3_Y_nonneg _ _ _)
  set e : ℝ := ∫ x, W x * sa12z3_Y m F x with he
  have hB := hCB i l om Z h hom hoc hZ2 hh1 hhc
  have s1 := sa12x2_sqrt_bd (g := D1 l h) hKLg0 hcT0 b1
  have s2 := sa12x2_sqrt_bd (g := h) hKLh0 hcT0 b2
  have s3 := sa12x2_sqrt_bd (g := fun x => om x ^ 2 * Z x) (by norm_num : (0 : ℝ) ≤ K3) hcT0 b3
  have s4 := sa12x2_sqrt_bd (g := fun x => ‖fderiv ℝ (fun y => om y ^ 2 * Z y) x‖)
    (by positivity : (0 : ℝ) ≤ K4) hcT0 b4
  have s5 := sa12x2_sqrt_bd (g := fun x => Z x * D1 l (fun z => om z ^ 2) x) hKq0 hcT0 b5
  have s6 := sa12x2_sqrt_bd (g := fun x => ‖fderiv ℝ (fun y => Z y * D1 l (fun z => om z ^ 2) y) x‖)
    (by positivity : (0 : ℝ) ≤ K6) hcT0 b6
  have hsc := Real.mul_self_sqrt hcT0
  have hse := Real.mul_self_sqrt he0
  have hsq0 := Real.sqrt_nonneg cT
  have hse0 := Real.sqrt_nonneg e
  refine hB.trans ?_
  have hA : Real.sqrt (∫ x, D1 l h x ^ 2) * (Real.sqrt (∫ x, (om x ^ 2 * Z x) ^ 2) +
      Real.sqrt (∫ x, ‖fderiv ℝ (fun y => om y ^ 2 * Z y) x‖ ^ 2)) ≤
      (KLg * Real.sqrt cT * Real.sqrt e) * ((K3 * Real.sqrt cT * Real.sqrt e) +
        (K4 * Real.sqrt cT * Real.sqrt e)) :=
    mul_le_mul s1 (add_le_add s3 s4) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by positivity)
  have hC : Real.sqrt (∫ x, h x ^ 2) * (Real.sqrt (∫ x, (Z x * D1 l (fun z => om z ^ 2) x) ^ 2) +
      Real.sqrt (∫ x, ‖fderiv ℝ (fun y => Z y * D1 l (fun z => om z ^ 2) y) x‖ ^ 2)) ≤
      (KLh * Real.sqrt cT * Real.sqrt e) * ((K5 * Real.sqrt cT * Real.sqrt e) +
        (K6 * Real.sqrt cT * Real.sqrt e)) :=
    mul_le_mul s2 (add_le_add s5 s6) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by positivity)
  have hfin : CB * (Real.sqrt (∫ x, D1 l h x ^ 2) * (Real.sqrt (∫ x, (om x ^ 2 * Z x) ^ 2) +
      Real.sqrt (∫ x, ‖fderiv ℝ (fun y => om y ^ 2 * Z y) x‖ ^ 2)) +
      Real.sqrt (∫ x, h x ^ 2) * (Real.sqrt (∫ x, (Z x * D1 l (fun z => om z ^ 2) x) ^ 2) +
      Real.sqrt (∫ x, ‖fderiv ℝ (fun y => Z y * D1 l (fun z => om z ^ 2) y) x‖ ^ 2))) ≤
      CB * ((KLg * Real.sqrt cT * Real.sqrt e) * ((K3 * Real.sqrt cT * Real.sqrt e) +
        (K4 * Real.sqrt cT * Real.sqrt e)) + (KLh * Real.sqrt cT * Real.sqrt e) *
        ((K5 * Real.sqrt cT * Real.sqrt e) + (K6 * Real.sqrt cT * Real.sqrt e))) :=
    mul_le_mul_of_nonneg_left (add_le_add hA hC) hCB0
  refine hfin.trans (le_of_eq ?_)
  have : (Real.sqrt cT * Real.sqrt e) * (Real.sqrt cT * Real.sqrt e) = cT * e := by
    calc _ = (Real.sqrt cT * Real.sqrt cT) * (Real.sqrt e * Real.sqrt e) := by ring
      _ = _ := by rw [hsc, hse]
  calc _ = CB * (KLg * (K3 + K4) * ((Real.sqrt cT * Real.sqrt e) * (Real.sqrt cT * Real.sqrt e)) +
        KLh * (K5 + K6) * ((Real.sqrt cT * Real.sqrt e) * (Real.sqrt cT * Real.sqrt e))) := by ring
    _ = _ := by rw [this]; ring

end HRS.MH.AdjointRd.Phase2SA12Near
