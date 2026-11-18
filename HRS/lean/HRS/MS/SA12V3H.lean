import HRS.MS.SA12V3G

/-!
# S.A.12 N1 (SA12V3 worker): uniform decay of the boxed periodic nonlocal test term

`sa12v3_N1`: `c ⟨x⟩^{-(d+3)}` bound for `1_{centeredBox} nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ`, uniformly in
`L ≥ max 1 L₀`, `ε ∈ (0,1]`, `σ ∈ [0,t]`; exactly the hypothesis `N1` of `sa12k_L8_of_nonlocal`.
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

theorem sa12v3_jbracket_le (hd : 1 ≤ d) {L : ℝ} {x : Euc d} (hx : x ∈ centeredBox d L) (k : Fin d → ℤ) :
    jbracket x ≤ Real.sqrt d * jbracket (x - L • latticePt k) := by
  set a' : ℝ := ‖x - L • latticePt k‖ with ha'
  have hcoord : ∀ i, |x i| ≤ a' := fun i => by
    refine (sa12v3_box_coord hx k i).trans ?_
    have h1 := PiLp.norm_apply_le (x - L • latticePt k) i
    simpa [Real.norm_eq_abs] using h1
  have h1 : ‖x‖ ≤ Real.sqrt d * a' := by
    have := sa12v3_norm_le_of_coord hcoord
    rwa [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg _)] at this
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold jbracket
  rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine Real.sqrt_le_sqrt ?_
  have h2 : ‖x‖ ^ 2 ≤ d * a' ^ 2 := by
    calc ‖x‖ ^ 2 ≤ (Real.sqrt d * a') ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = d * a' ^ 2 := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  nlinarith [sq_nonneg a']

theorem sa12v3_box_decay (hd : 1 ≤ d) {L : ℝ} {x : Euc d} (hx : x ∈ centeredBox d L) (k : Fin d → ℤ)
    {Λ Y : ℝ} (hY : 0 ≤ Y) (h : jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * Y ≤ Λ) :
    Y ≤ Λ * (Real.sqrt d) ^ ((d : ℝ) + 3) * jbracket x ^ (-((d : ℝ) + 3)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by linarith)
  have ha : 0 < jbracket (x - L • latticePt k) := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)
  have hp : (0 : ℝ) ≤ (d : ℝ) + 3 := by positivity
  have hbd := sa12v3_jbracket_le hd hx k
  set a := jbracket (x - L • latticePt k)
  set b := jbracket x
  have h1 : Y ≤ Λ * a ^ (-((d : ℝ) + 3)) := by
    rw [Real.rpow_neg ha.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos ha _)]
    linarith
  have h2 : a ^ (-((d : ℝ) + 3)) ≤ (b / Real.sqrt d) ^ (-((d : ℝ) + 3)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hb hsd) ((div_le_iff₀ hsd).2 (by linarith)) (by linarith)
  have h3 : (b / Real.sqrt d) ^ (-((d : ℝ) + 3)) = (Real.sqrt d) ^ ((d : ℝ) + 3) * b ^ (-((d : ℝ) + 3)) := by
    rw [Real.div_rpow hb.le hsd.le, Real.rpow_neg hsd.le, div_inv_eq_mul, mul_comm]
  have hΛ : 0 ≤ Λ := by
    have : 0 ≤ a ^ ((d : ℝ) + 3) * Y := mul_nonneg (Real.rpow_nonneg ha.le _) hY
    linarith
  calc Y ≤ Λ * a ^ (-((d : ℝ) + 3)) := h1
    _ ≤ Λ * ((Real.sqrt d) ^ ((d : ℝ) + 3) * b ^ (-((d : ℝ) + 3))) :=
        mul_le_mul_of_nonneg_left (h2.trans h3.le) hΛ
    _ = _ := by ring

theorem sa12v3_NT_box_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsCcInfty ψ) (M : Matrix (Fin d) (Fin d) ℝ) (Λ : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ μ : Euc d → ℝ, Differentiable ℝ μ →
      (∀ x ∈ centeredBox d L, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ 0 μ x‖ ≤ Λ) →
      (∀ x ∈ centeredBox d L, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ 1 μ x‖ ≤ Λ) →
      ∀ x ∈ centeredBox d L, |sa12v3_NT γ M μ ψ x| ≤ c * jbracket x ^ (-((d : ℝ) + 3)) := by
  obtain ⟨R, B, hR, hB, hT1, hT2⟩ := sa12v3_tests hψ
  obtain ⟨C, hC, hbox⟩ := sa12v3_box_bound hd s hs0 hsd R hR
  set Sm : ℝ := ∑ i : Fin d, ∑ j : Fin d, |M j i| with hSm
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set K : ℝ := max Λ 0 * (Real.sqrt d) ^ ((d : ℝ) + 3) with hK
  have hK0 : 0 ≤ K := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  refine ⟨Sm * (2 * (C * B) * K), by positivity, ?_⟩
  intro L hL γ hγ μ hμ h0 h1 x hx
  set E : ℝ := K * jbracket x ^ (-((d : ℝ) + 3)) with hE
  have hE0 : 0 ≤ E := mul_nonneg hK0 (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hdec : ∀ (j : ℕ), (∃ k : Fin d → ℤ, jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
      ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ) → ‖iteratedFDeriv ℝ j μ x‖ ≤ E := by
    rintro j ⟨k, hk⟩
    have := sa12v3_box_decay hd hx k (norm_nonneg _) hk
    refine this.trans ?_
    rw [hE, hK]
    have h1' : Λ ≤ max Λ 0 := le_max_left _ _
    have h2' : 0 ≤ (Real.sqrt d) ^ ((d : ℝ) + 3) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have h3' : 0 ≤ jbracket x ^ (-((d : ℝ) + 3)) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    calc Λ * (Real.sqrt d) ^ ((d : ℝ) + 3) * jbracket x ^ (-((d : ℝ) + 3))
        ≤ max Λ 0 * (Real.sqrt d) ^ ((d : ℝ) + 3) * jbracket x ^ (-((d : ℝ) + 3)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1' h2') h3'
      _ = _ := by ring
  have hμ0 : |μ x| ≤ E := by
    have := hdec 0 (h0 x hx)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hμ1 : ∀ j : Fin d, |fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ))| ≤ E := by
    intro j
    have := hdec 1 (h1 x hx)
    rw [norm_iteratedFDeriv_one] at this
    have h2 := (fderiv ℝ μ x).le_opNorm (EuclideanSpace.single j (1 : ℝ))
    rw [Real.norm_eq_abs] at h2
    simp at h2
    linarith
  rw [sa12v3_NT_expand hγ.locInt M hμ hψ.1 hψ.2 x]
  have hterm : ∀ i j : Fin d, |M j i * (fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) *
        sa12vH γ (sa12v3_D1 ψ i) x + μ x * sa12vH γ (sa12v3_D1 (sa12v3_D1 ψ i) j) x)| ≤
      |M j i| * (2 * (C * B) * E) := by
    intro i j
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have e1 : |sa12vH γ (sa12v3_D1 ψ i) x| ≤ C * B := hbox L hL γ hγ B _ (hT1 i) x hx
    have e2 : |sa12vH γ (sa12v3_D1 (sa12v3_D1 ψ i) j) x| ≤ C * B := hbox L hL γ hγ B _ (hT2 i j) x hx
    have hCB : 0 ≤ C * B := mul_nonneg hC hB
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have a1 := mul_le_mul (hμ1 j) e1 (abs_nonneg _) hE0
    have a2 := mul_le_mul hμ0 e2 (abs_nonneg _) hE0
    nlinarith
  calc _ ≤ ∑ i : Fin d, |∑ j : Fin d, M j i * (fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) *
        sa12vH γ (sa12v3_D1 ψ i) x + μ x * sa12vH γ (sa12v3_D1 (sa12v3_D1 ψ i) j) x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |M j i * (fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) *
        sa12vH γ (sa12v3_D1 ψ i) x + μ x * sa12vH γ (sa12v3_D1 (sa12v3_D1 ψ i) j) x)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |M j i| * (2 * (C * B) * E) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = Sm * (2 * (C * B) * E) := by
        rw [hSm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    _ = _ := by rw [hE]; ring

/-- **N1** of `sa12k_L8_of_nonlocal`: uniform `⟨x⟩^{-(d+3)}` decay of the boxed periodic nonlocal test term. -/
theorem sa12v3_N1 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ' ΛV' νbar Cb T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ) (t L₀ : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (γ : ℝ → Euc d → ℝ) (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ)
    (hA : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 →
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d,
        |(centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x| ≤
          c * jbracket x ^ (-((d : ℝ) + 3)) := by
  obtain ⟨c, hc0, hc⟩ := sa12v3_NT_box_bound hd s hs0 hsd hψ D.M Λ'
  refine ⟨c, hc0, fun L hL ε hε σ hσ x => ?_⟩
  have hP := hA.1 L hL ε hε
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hσT : σ ∈ Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans ht.2⟩
  by_cases hx : x ∈ centeredBox d L
  · rw [indicator_of_mem hx, sa12v3_per_eq]
    exact hc L hL1 (γ L) hP.hγ (μL L ε σ) ((hP.μ_smooth σ hσT).differentiable (by simp))
      (fun y _ => hP.μ_decay σ hσT 0 (by omega) y) (fun y _ => hP.μ_decay σ hσT 1 (by omega) y) x hx
  · rw [indicator_of_notMem hx, abs_zero]
    exact mul_nonneg hc0 (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

end HRS.MH.AdjointRd.Phase2SA12V3
