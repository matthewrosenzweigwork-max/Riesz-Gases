import HRS.MS.SA12X3N1K

/-!
# S.A.12 N1 (SA12X3): uniform pointwise decay of the boxed periodic nonlocal test term
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MS.ToriConv
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3n_box_norm {L : ℝ} (hL : 0 < L) {x : Euc d} (hx : x ∈ centeredBox d L) (k : Fin d → ℤ) :
    ‖x‖ ≤ ‖x - L • latticePt k‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have e : (x - L • latticePt k) i = x i - L * k i := by simp [latticePt]
  rw [e]
  have h1 := hx i
  have hsq : |x i| ≤ |x i - L * k i| := by
    by_cases hk : k i = 0
    · simp [hk]
    · have hk1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
        have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hk
        exact_mod_cast this
      have h3 : L * |(k i : ℝ)| ≤ |x i - L * k i| + |x i| := by
        have : L * (k i : ℝ) = x i - (x i - L * k i) := by ring
        calc L * |(k i : ℝ)| = |L * (k i : ℝ)| := by rw [abs_mul, abs_of_pos hL]
          _ = |x i - (x i - L * k i)| := by rw [← this]
          _ ≤ |x i| + |x i - L * k i| := abs_sub _ _
          _ = _ := add_comm _ _
      have h4 : L ≤ L * |(k i : ℝ)| := by nlinarith
      have h5 : |x i| ≤ L / 2 := by rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
      linarith
  exact pow_le_pow_left₀ (abs_nonneg _) hsq 2

theorem sa12x3n_N1 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (Λ' ΛV' Cb L₀ : ℝ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (γ : ℝ → Euc d → ℝ) (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ)
    (hA : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ∃ Lmin c : ℝ, max 1 L₀ ≤ Lmin ∧ 0 ≤ c ∧ ∀ L : ℝ, Lmin ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 →
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d,
        |(centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x| ≤
          c * jbracket x ^ (-((d : ℝ) + 3)) := by
  obtain ⟨L₁, Kc, hL₁, hKc, hP1, -⟩ := sa12x3n_nl_bounds hd s hs0 hsd hψ.1 hψ.2 D.M
  refine ⟨max (max 1 L₀) L₁, Kc * (2 * max Λ' 0), le_max_left _ _, by positivity, ?_⟩
  intro L hL ε hε σ hσ x
  have hLa : max 1 L₀ ≤ L := (le_max_left _ _).trans hL
  have hLb : L₁ ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hLa)
  have hjp : 0 < jbracket x ^ (-((d : ℝ) + 3)) := Real.rpow_pos_of_pos (by unfold jbracket; positivity) _
  by_cases hx : x ∈ centeredBox d L
  · rw [indicator_of_mem hx]
    have hPD := hA.1 L hLa ε hε
    have hσT : σ ∈ Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans ht.2⟩
    have hμ1 : ContDiff ℝ 1 (μL L ε σ) := (hPD.μ_smooth σ hσT).of_le (by simp)
    refine (hP1 L hLb (γ L) hPD.hγ (μL L ε σ) hμ1 x).trans ?_
    have hdec : ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (μL L ε σ) x‖ ≤ max Λ' 0 * jbracket x ^ (-((d : ℝ) + 3)) := by
      intro j hj
      obtain ⟨k, hk⟩ := hPD.μ_decay σ hσT j (by omega) x
      have hJ : jbracket x ≤ jbracket (x - L • latticePt k) := by
        unfold jbracket
        exact Real.sqrt_le_sqrt (by nlinarith [sa12x3n_box_norm hL0 hx k, norm_nonneg x])
      have hx0 : 0 < jbracket x := by unfold jbracket; positivity
      have h1 : jbracket x ^ ((d : ℝ) + 3) ≤ jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) :=
        Real.rpow_le_rpow hx0.le hJ (by positivity)
      have hpos : 0 < jbracket x ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos hx0 _
      rw [Real.rpow_neg hx0.le]
      have h2 : jbracket x ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (μL L ε σ) x‖ ≤ Λ' :=
        (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans hk
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      calc ‖iteratedFDeriv ℝ j (μL L ε σ) x‖ * jbracket x ^ ((d : ℝ) + 3) ≤ Λ' := by linarith
        _ ≤ max Λ' 0 := le_max_left _ _
    have e0 := hdec 0 (by norm_num)
    have e1 := hdec 1 le_rfl
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at e0
    rw [norm_iteratedFDeriv_one] at e1
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add e1 e0) hKc]
  · rw [indicator_of_notMem hx, abs_zero]
    positivity

end HRS.MH.AdjointRd.Phase2SA12Limit
