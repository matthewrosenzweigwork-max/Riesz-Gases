import HRS.MS.SA12V3H

/-!
# S.A.12 N2 (SA12V3 worker): locally uniform convergence of the boxed periodic nonlocal test term

`sa12v3_N2`: exactly the hypothesis `N2` of `sa12k_L8_of_nonlocal`.  Route: expand both test terms
(`sa12v3_NT_expand`), `∂μ_L → ∂μ`, `μ_L → μ` locally uniformly (`PerApprox`), and `γ_L * ∂^αψ → g * ∂^αψ` locally
uniformly (`sa12v3_loc_conv`, the constant `c_L` cancels because `∫ ∂^α ψ = 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_NT_diff {γ₁ γ₂ : Euc d → ℝ} (h₁ : LocallyIntegrable γ₁ volume) (h₂ : LocallyIntegrable γ₂ volume)
    (M : Matrix (Fin d) (Fin d) ℝ) {μ₁ μ₂ ψ : Euc d → ℝ} (hμ₁ : Differentiable ℝ μ₁) (hμ₂ : Differentiable ℝ μ₂)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (x : Euc d) {P Q a N : ℝ}
    (hP : ∀ i, |sa12vH γ₁ (sa12v3_D1 ψ i) x| ≤ P)
    (hP2 : ∀ i j, |sa12vH γ₁ (sa12v3_D1 (sa12v3_D1 ψ i) j) x| ≤ P)
    (hQ : ∀ i, |sa12vH γ₁ (sa12v3_D1 ψ i) x - sa12vH γ₂ (sa12v3_D1 ψ i) x| ≤ Q)
    (hQ2 : ∀ i j, |sa12vH γ₁ (sa12v3_D1 (sa12v3_D1 ψ i) j) x - sa12vH γ₂ (sa12v3_D1 (sa12v3_D1 ψ i) j) x| ≤ Q)
    (ha1 : ∀ j, |fderiv ℝ μ₁ x (EuclideanSpace.single j (1 : ℝ)) - fderiv ℝ μ₂ x (EuclideanSpace.single j (1 : ℝ))| ≤ a)
    (ha0 : |μ₁ x - μ₂ x| ≤ a)
    (hN1 : ∀ j, |fderiv ℝ μ₂ x (EuclideanSpace.single j (1 : ℝ))| ≤ N) (hN0 : |μ₂ x| ≤ N) :
    |sa12v3_NT γ₁ M μ₁ ψ x - sa12v3_NT γ₂ M μ₂ ψ x| ≤
      (∑ i : Fin d, ∑ j : Fin d, |M j i|) * (2 * a * P + 2 * N * Q) := by
  rw [sa12v3_NT_expand h₁ M hμ₁ hψ hψc x, sa12v3_NT_expand h₂ M hμ₂ hψ hψc x]
  simp only [← Finset.sum_sub_distrib]
  have hterm : ∀ i j : Fin d, |M j i *
      (fderiv ℝ μ₁ x (EuclideanSpace.single j (1 : ℝ)) * sa12vH γ₁ (sa12v3_D1 ψ i) x +
        μ₁ x * sa12vH γ₁ (sa12v3_D1 (sa12v3_D1 ψ i) j) x) -
      M j i * (fderiv ℝ μ₂ x (EuclideanSpace.single j (1 : ℝ)) * sa12vH γ₂ (sa12v3_D1 ψ i) x +
        μ₂ x * sa12vH γ₂ (sa12v3_D1 (sa12v3_D1 ψ i) j) x)| ≤ |M j i| * (2 * a * P + 2 * N * Q) := by
    intro i j
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    set A1 := fderiv ℝ μ₁ x (EuclideanSpace.single j (1 : ℝ))
    set A2 := fderiv ℝ μ₂ x (EuclideanSpace.single j (1 : ℝ))
    set H1 := sa12vH γ₁ (sa12v3_D1 ψ i) x
    set H1' := sa12vH γ₂ (sa12v3_D1 ψ i) x
    set G1 := sa12vH γ₁ (sa12v3_D1 (sa12v3_D1 ψ i) j) x
    set G1' := sa12vH γ₂ (sa12v3_D1 (sa12v3_D1 ψ i) j) x
    have e : A1 * H1 + μ₁ x * G1 - (A2 * H1' + μ₂ x * G1') =
        ((A1 - A2) * H1 + A2 * (H1 - H1')) + (((μ₁ x - μ₂ x) * G1) + μ₂ x * (G1 - G1')) := by ring
    rw [e]
    have b1 : |(A1 - A2) * H1| ≤ a * P := by
      rw [abs_mul]; exact mul_le_mul (ha1 j) (hP i) (abs_nonneg _) ((abs_nonneg _).trans (ha1 j))
    have b2 : |A2 * (H1 - H1')| ≤ N * Q := by
      rw [abs_mul]; exact mul_le_mul (hN1 j) (hQ i) (abs_nonneg _) ((abs_nonneg _).trans (hN1 j))
    have b3 : |(μ₁ x - μ₂ x) * G1| ≤ a * P := by
      rw [abs_mul]; exact mul_le_mul ha0 (hP2 i j) (abs_nonneg _) ((abs_nonneg _).trans ha0)
    have b4 : |μ₂ x * (G1 - G1')| ≤ N * Q := by
      rw [abs_mul]; exact mul_le_mul hN0 (hQ2 i j) (abs_nonneg _) ((abs_nonneg _).trans hN0)
    calc _ ≤ |(A1 - A2) * H1 + A2 * (H1 - H1')| + |(μ₁ x - μ₂ x) * G1 + μ₂ x * (G1 - G1')| := abs_add_le _ _
      _ ≤ (|(A1 - A2) * H1| + |A2 * (H1 - H1')|) + (|(μ₁ x - μ₂ x) * G1| + |μ₂ x * (G1 - G1')|) :=
          add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ ≤ _ := by linarith
  calc _ ≤ ∑ i : Fin d, |∑ j : Fin d, (M j i *
        (fderiv ℝ μ₁ x (EuclideanSpace.single j (1 : ℝ)) * sa12vH γ₁ (sa12v3_D1 ψ i) x +
          μ₁ x * sa12vH γ₁ (sa12v3_D1 (sa12v3_D1 ψ i) j) x) -
        M j i * (fderiv ℝ μ₂ x (EuclideanSpace.single j (1 : ℝ)) * sa12vH γ₂ (sa12v3_D1 ψ i) x +
          μ₂ x * sa12vH γ₂ (sa12v3_D1 (sa12v3_D1 ψ i) j) x))| := by
        have := Finset.abs_sum_le_sum_abs (fun i : Fin d => ∑ j : Fin d, (M j i *
        (fderiv ℝ μ₁ x (EuclideanSpace.single j (1 : ℝ)) * sa12vH γ₁ (sa12v3_D1 ψ i) x +
          μ₁ x * sa12vH γ₁ (sa12v3_D1 (sa12v3_D1 ψ i) j) x) -
        M j i * (fderiv ℝ μ₂ x (EuclideanSpace.single j (1 : ℝ)) * sa12vH γ₂ (sa12v3_D1 ψ i) x +
          μ₂ x * sa12vH γ₂ (sa12v3_D1 (sa12v3_D1 ψ i) j) x))) Finset.univ
        exact this
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |M j i| * (2 * a * P + 2 * N * Q) :=
        Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => hterm i j)
    _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

theorem sa12v3_norm_one_sub (f g : Euc d → ℝ) (x : Euc d) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 g x‖ = ‖fderiv ℝ f x - fderiv ℝ g x‖ := by
  have h1 := HRS.MS.ToriConv.tcv_iter_fderiv_sub_norm f g 0 x
  have h2 := HRS.MS.ToriConv.tcv_iter_zero_sub_norm (fderiv ℝ f) (fderiv ℝ g) x
  rw [zero_add] at h1
  rw [← h1, h2]

theorem sa12v3_dir_le (A B : Euc d →L[ℝ] ℝ) (j : Fin d) {a : ℝ} (h : ‖A - B‖ ≤ a) :
    |A (EuclideanSpace.single j (1 : ℝ)) - B (EuclideanSpace.single j (1 : ℝ))| ≤ a := by
  have := (A - B).le_opNorm (EuclideanSpace.single j (1 : ℝ))
  simp only [ContinuousLinearMap.sub_apply, Real.norm_eq_abs] at this
  simp at this
  exact this.trans h

/-- **N2** of `sa12k_L8_of_nonlocal`: locally uniform convergence of the boxed periodic nonlocal test term. -/
theorem sa12v3_N2 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (Λ' ΛV' Cb L₀ t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (γ : ℝ → Euc d → ℝ) (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ)
    (hA : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ∀ (R δ : ℝ), 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R →
        |(centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x -
          nonlocalTestRd (D.coeff μ) (t - σ) ψ x| ≤ δ := by
  intro Rb δ hδ
  set Rb' : ℝ := max Rb 0 with hRb'
  obtain ⟨Rt, B, hRt, hB, hT1, hT2⟩ := sa12v3_tests hψ
  obtain ⟨Cbx, hCbx, hbox⟩ := sa12v3_box_bound hd s hs0 hsd Rt hRt
  have hT0 : 0 ≤ T := ht.1.le.trans ht.2
  have hΛ' : 0 ≤ Λ' := by
    have := (hA.1 (max 1 L₀) le_rfl 1 ⟨one_pos, le_rfl⟩).μ_bdd 0 ⟨le_rfl, hT0⟩ 0 (by omega) 0
    exact (norm_nonneg _).trans this
  set Sm : ℝ := ∑ i : Fin d, ∑ j : Fin d, |D.M j i| with hSm
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set W : ℝ := Sm * (2 * (Cbx * B) + 2 * (Λ' + 1) * B) + 1 with hW
  have hW0 : 0 < W := by positivity
  set δ' : ℝ := min 1 (δ / W) with hδ'
  have hδ'0 : 0 < δ' := lt_min one_pos (div_pos hδ hW0)
  have hδ'1 : δ' ≤ 1 := min_le_left _ _
  have hδ'W : δ' * W ≤ δ := by
    have := min_le_right 1 (δ / W)
    calc δ' * W ≤ (δ / W) * W := mul_le_mul_of_nonneg_right this hW0.le
      _ = δ := div_mul_cancel₀ _ hW0.ne'
  obtain ⟨L₁a, ε₀a, hε₀a, ha⟩ := hA.2 (Metric.closedBall (0 : Euc d) Rb') (isCompact_closedBall _ _) 0
    (by omega) δ' hδ'0
  obtain ⟨L₁b, ε₀b, hε₀b, hb⟩ := hA.2 (Metric.closedBall (0 : Euc d) Rb') (isCompact_closedBall _ _) 1
    (by omega) δ' hδ'0
  obtain ⟨L₁c, hL₁c, hc⟩ := sa12v3_loc_conv hd s hs0 hsd Rt Rb' hRt (le_max_right _ _) δ' hδ'0
  refine ⟨max (max (max L₁a L₁b) (max L₁c (2 * Rb' + 1))) (max 1 L₀), min (min ε₀a ε₀b) 1,
    lt_min (lt_min hε₀a hε₀b) one_pos, fun L hL ε hε hεle σ hσ x hx => ?_⟩
  have hLa : L₁a ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLb : L₁b ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLc : L₁c ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hL2 : 2 * Rb' + 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hL0 : max 1 L₀ ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL0
  have hεa : ε ≤ ε₀a := hεle.trans (((min_le_left _ _).trans (min_le_left _ _)))
  have hεb : ε ≤ ε₀b := hεle.trans (((min_le_left _ _).trans (min_le_right _ _)))
  have hεI : ε ∈ Ioc (0 : ℝ) 1 := ⟨hε, hεle.trans (min_le_right _ _)⟩
  have hσT : σ ∈ Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans ht.2⟩
  have hmax : max (t - σ) 0 = t - σ := max_eq_left (by linarith [hσ.2])
  have hτT : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hxn : ‖x‖ ≤ Rb' := hx.trans (le_max_left _ _)
  have hxK : x ∈ Metric.closedBall (0 : Euc d) Rb' := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hxn
  have hxbox : x ∈ centeredBox d L := by
    intro i
    have h1 : |x i| ≤ ‖x‖ := by
      have := PiLp.norm_apply_le x i
      simpa [Real.norm_eq_abs] using this
    have h2 := abs_le.1 (h1.trans hxn)
    constructor <;> linarith [h2.1, h2.2]
  have hP := hA.1 L hL0 ε hεI
  have hγ : IsPeriodicRieszKernel d s L (γ L) := hP.hγ
  have hμ₁ : Differentiable ℝ (μL L ε σ) := (hP.μ_smooth σ hσT).differentiable (by simp)
  have hμ₂ : Differentiable ℝ (μ (t - σ)) :=
    ((hD.hμ.regular.1 (t - σ) hτT).1.1.differentiable (by simp))
  have hg := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  -- coefficient convergence
  have e0 := (ha L hLa ε hε hεa σ hσT x hxK).2
  have e1 := (hb L hLb ε hε hεb σ hσT x hxK).2
  rw [hmax, HRS.MS.ToriConv.tcv_iter_zero_sub_norm, Real.norm_eq_abs] at e0
  rw [hmax, sa12v3_norm_one_sub] at e1
  have hb0 : ‖iteratedFDeriv ℝ 0 (μL L ε σ) x‖ ≤ Λ' := hP.μ_bdd σ hσT 0 (by omega) x
  have hb1 : ‖iteratedFDeriv ℝ 1 (μL L ε σ) x‖ ≤ Λ' := hP.μ_bdd σ hσT 1 (by omega) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb0
  rw [norm_iteratedFDeriv_one] at hb1
  have hN0 : |μ (t - σ) x| ≤ Λ' + 1 := by
    have : |μ (t - σ) x| ≤ |μL L ε σ x| + |μL L ε σ x - μ (t - σ) x| := by
      calc |μ (t - σ) x| = |μL L ε σ x - (μL L ε σ x - μ (t - σ) x)| := by rw [sub_sub_cancel]
        _ ≤ _ := abs_sub _ _
    linarith
  have hN1 : ∀ j : Fin d, |fderiv ℝ (μ (t - σ)) x (EuclideanSpace.single j (1 : ℝ))| ≤ Λ' + 1 := by
    intro j
    have h2 := (fderiv ℝ (μ (t - σ)) x).le_opNorm (EuclideanSpace.single j (1 : ℝ))
    simp only [Real.norm_eq_abs, EuclideanSpace.norm_single, norm_one, mul_one] at h2
    have h3 : ‖fderiv ℝ (μ (t - σ)) x‖ ≤ ‖fderiv ℝ (μL L ε σ) x‖ +
        ‖fderiv ℝ (μL L ε σ) x - fderiv ℝ (μ (t - σ)) x‖ := by
      calc ‖fderiv ℝ (μ (t - σ)) x‖ = ‖fderiv ℝ (μL L ε σ) x - (fderiv ℝ (μL L ε σ) x - fderiv ℝ (μ (t - σ)) x)‖ := by
            rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hdiff := sa12v3_NT_diff (γ₁ := γ L) (γ₂ := rieszKernel d s) hγ.locInt hg D.M hμ₁ hμ₂ hψ.1 hψ.2 x
    (P := Cbx * B) (Q := δ' * B) (a := δ') (N := Λ' + 1)
    (fun i => hbox L hL1 (γ L) hγ B _ (hT1 i) x hxbox)
    (fun i j => hbox L hL1 (γ L) hγ B _ (hT2 i j) x hxbox)
    (fun i => hc L hLc (γ L) hγ B _ (hT1 i) x hxn)
    (fun i j => hc L hLc (γ L) hγ B _ (hT2 i j) x hxn)
    (fun j => sa12v3_dir_le _ _ j e1) e0 hN1 hN0
  rw [indicator_of_mem hxbox, sa12v3_per_eq, sa12v3_rd_eq]
  have hs : (D.coeff μ).s = s := hD.hs.1
  rw [hs]
  refine hdiff.trans ?_
  have : Sm * (2 * δ' * (Cbx * B) + 2 * (Λ' + 1) * (δ' * B)) ≤ δ' * W := by
    rw [hW]
    have : Sm * (2 * δ' * (Cbx * B) + 2 * (Λ' + 1) * (δ' * B)) =
        δ' * (Sm * (2 * (Cbx * B) + 2 * (Λ' + 1) * B)) := by ring
    rw [this]
    nlinarith [mul_nonneg hSm0 (by positivity : (0 : ℝ) ≤ 2 * (Cbx * B) + 2 * (Λ' + 1) * B)]
  exact this.trans hδ'W

end HRS.MH.AdjointRd.Phase2SA12V3
