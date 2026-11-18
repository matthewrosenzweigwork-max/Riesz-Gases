import HRS.MS.S82RN18

/-!
# S8.2 R02 (S82R), N19: `PinComparison.1` (sup norm of the reference marginal density) for a `WeakReferenceSetup`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.External

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem s82r_part1 (hd : 2 ≤ d) (a beta C0 : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ, WeakReferenceSetup d a beta rho q h C0 → ∀ N : ℕ, 2 ≤ N →
        eLpNorm (fun x => ((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
          (HRS.Whole.withDensityReal rho) x).toReal - 1) ∞ (HRS.Whole.withDensityReal rho) ≤
            ENNReal.ofReal (C * HRS.MS.Phase2S82.deltaN N) := by
  obtain ⟨Cth, cth, hG, hρ0, hρG, hMb⟩ := s82r_thermal_pack hd a beta ha hbeta
  set γ : ℝ := 1 / (1000 * beta) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hβγ : beta * γ = 1 / 1000 := by rw [hγ]; field_simp
  have hK3 : Real.exp (1 / 1000 + 1 / 4 + (1 / 4 + 1 / 1000)) ≤ 3 :=
    (Real.exp_le_exp.2 (by norm_num : (1 : ℝ) / 1000 + 1 / 4 + (1 / 4 + 1 / 1000) ≤ 1)).trans
      (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hK0 := Real.exp_pos (1 / 1000 + 1 / 4 + (1 / 4 + 1 / 1000))
  have hα : beta * γ * (Real.exp (1 / 1000 + 1 / 4 + (1 / 4 + 1 / 1000)) +
      Real.exp (1 / 1000 + 1 / 4 + (1 / 4 + 1 / 1000)) ^ 2) < 1 := by
    rw [hβγ]; nlinarith
  obtain ⟨CL, hCL0, hCL⟩ := s82r_pin_density hd hq Cth (Mψ := 1 / 1000 + 1 / 4) (M₁ := 1 / 4)
    (P := 1 / 1000) hbeta hγ0 (by rw [hβγ]) hα
  set KL : ℝ := Real.exp (1 / 1000 + 1 / 4 + 1 / 4 + beta * γ) with hKL
  have hKL1 : 1 ≤ KL := Real.one_le_exp (by rw [hβγ]; norm_num)
  have hKL3 : KL ≤ 3 := by
    rw [hKL, hβγ]
    refine le_trans (le_of_eq ?_) hK3
    congr 1; ring
  obtain ⟨CD, hCD0, hCD⟩ := s82r_cavD hd hq Cth hbeta (Cν := KL) (γ0 := γ) hKL1 hγ0
  set A : ℝ := C0 + CD + (1 + CL) / 1000 with hA
  have hAC0 : C0 ≤ A := by rw [hA]; linarith
  obtain ⟨N1, hN12, hN1⟩ := s82r_eventually_C0_delta hd (8 * A)
  set Kc : ℝ := Real.exp (1 / 1000 + C0 + C0 + beta * γ) with hKc
  have hKc0 : 0 < Kc := Real.exp_pos _
  have hN1r : (2 : ℝ) ≤ N1 := by exact_mod_cast hN12
  refine ⟨max (5 * A) ((Kc + 1) * N1) + 1, by positivity, ?_⟩
  intro rho hrho h hW N hN
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  have hρ0r : HRS.Whole.IsProbDensity rho := by rw [hrho_eq]; exact hρ0
  have hρGr : HRS.Whole.HasR2GaussianUpper (Cth + 1) cth rho := by rw [hrho_eq]; exact hρG
  have hMbr : ∀ x, rho x ≤ Cth := fun x => by rw [hrho_eq]; exact hMb x
  haveI hμ := s82r_isProb hρ0r
  have hC0 : 0 ≤ C0 := hW.positive.le
  have hsr := hW.small_row
  have hAnn : 0 ≤ A := hC0.trans hAC0
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  by_cases hbig : N1 ≤ N
  swap
  · push_neg at hbig
    have hN0 : 0 < N := by omega
    haveI : NeZero N := ⟨hN0.ne'⟩
    have hδ1 : HRS.MS.Phase2S82.deltaN N ≤ 1 := HRS.MS.S82P2.s82p2_deltaN_le_one (by omega)
    have hbound := hW.hbound N hN
    have hC0δ : C0 * HRS.MS.Phase2S82.deltaN N ≤ C0 := mul_le_of_le_one_right hC0 hδ1
    obtain ⟨V, hVM, hVM', hVγ, hVq, hψ, hVφ, hMarg⟩ := s82r_part1_ident hd hbeta hq hsr hG hρ0r hρGr
      (N := N) (t := C0) (hW.hmeas N) (fun x => (hbound x).trans hC0δ) hN0
    rw [hMarg]
    have d2 := s82r_marg_density_le V hbeta.le hN0 (fun e : Empty => e.elim) (n := N) (by simp)
      (0 : Fin N)
    have hKc' : Real.exp (V.M + V.M' + beta * V.γ) = Kc := by rw [hVM, hVM', hVγ, hKc, hγ]
    rw [hKc'] at d2
    have d2' : ∀ᵐ x ∂(HRS.Whole.withDensityReal rho),
        ((RefMarg.cavMarg V (beta / N) N).rnDeriv
          (HRS.Whole.withDensityReal rho) x).toReal ≤ Kc := d2
    have hfm : Measurable (fun x => ((RefMarg.cavMarg V (beta / N) N).rnDeriv
        (HRS.Whole.withDensityReal rho) x).toReal - 1) :=
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal).sub_const 1
    refine (s82r_top_le hfm (B := Kc + 1) ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · filter_upwards [d2'] with x hx
      have h0 := ENNReal.toReal_nonneg (a := (RefMarg.cavMarg V (beta / N) N).rnDeriv
        (HRS.Whole.withDensityReal rho) x)
      rw [abs_le]; constructor <;> linarith
    · have hNN1 : (N : ℝ) ≤ N1 := by exact_mod_cast hbig.le
      have hδN : 1 / (N1 : ℝ) ≤ HRS.MS.Phase2S82.deltaN N :=
        (one_div_le_one_div_of_le hNr hNN1).trans (s82r_delta_ge2 (by omega))
      have hδ0 : 0 ≤ HRS.MS.Phase2S82.deltaN N := s82r_deltaN_nonneg (by omega)
      have hmax : (Kc + 1) * N1 ≤ max (5 * A) ((Kc + 1) * N1) + 1 := by
        have := le_max_right (5 * A) ((Kc + 1) * N1)
        linarith
      calc Kc + 1 = ((Kc + 1) * N1) * (1 / (N1 : ℝ)) := by field_simp
        _ ≤ (max (5 * A) ((Kc + 1) * N1) + 1) * HRS.MS.Phase2S82.deltaN N :=
            mul_le_mul hmax hδN (by positivity) (by positivity)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hδ := hN1 (n + 1) hbig
  have hδ0 : 0 ≤ HRS.MS.Phase2S82.deltaN (n + 1) := s82r_deltaN_nonneg hN0
  have hδN : 1 / ((n + 1 : ℕ) : ℝ) ≤ HRS.MS.Phase2S82.deltaN (n + 1) := s82r_delta_ge2 hN0
  have hNr' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hAδ : A * HRS.MS.Phase2S82.deltaN (n + 1) ≤ 1 / 32 := by nlinarith
  have hbound := hW.hbound (n + 1) hN
  have hC0δ : C0 * HRS.MS.Phase2S82.deltaN (n + 1) ≤ 1 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hAC0 hδ0]
  obtain ⟨V, hVM, hVM', hVγ, hVq, hψ, hVφ, hMarg⟩ := s82r_part1_ident hd hbeta hq hsr hG hρ0r hρGr
    (N := n + 1) (t := 1 / 4) (hW.hmeas (n + 1)) (fun x => (hbound x).trans hC0δ) hN0
  rw [hMarg]
  set lam : ℝ := beta / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hKV : Real.exp (V.M + V.M' + beta * V.γ) = KL := by rw [hVM, hVM', hVγ]
  have hVC : Real.exp (V.M + V.M' + beta * V.γ) ≤ KL := hKV.le
  have hV3 : Real.exp (V.M + V.M' + beta * V.γ) ≤ 3 := hKV.le.trans hKL3
  have hκ : weakKappa V beta ≤ 1 / 2 := by
    unfold weakKappa
    have h1 : beta * V.γ = 1 / 1000 := by rw [hVγ]; exact hβγ
    rw [h1] at hV3 ⊢
    nlinarith [Real.exp_pos (V.M + V.M' + 1 / 1000)]
  -- the cavity equation
  obtain ⟨c, hform⟩ := s82r_cav_formula V hbeta.le (n := n) (lam := lam) hlam
  haveI := isProb_pinnedLaw V hlam0 (n + 1) (fun e : Empty => e.elim)
  haveI := isProb_pinnedLaw V hlam0 n (fun e : Empty => e.elim)
  haveI hP1 : IsProbabilityMeasure (RefMarg.cavMarg V lam (n + 1)) :=
    inferInstanceAs (IsProbabilityMeasure ((pinnedLaw V lam (n + 1) (fun e : Empty => e.elim)).map
      (fun y => y 0)))
  haveI hP0 : IsProbabilityMeasure (RefMarg.cavMarg V lam n) :=
    inferInstanceAs (IsProbabilityMeasure ((pinnedLaw V lam n (fun e : Empty => e.elim)).map
      (fun y => y 0)))
  have hm1 : RefMarg.cavMarg V lam (n + 1) ≤ ENNReal.ofReal KL • (HRS.Whole.withDensityReal rho) := by
    have := RefMarg.marginal_le_smul (B := Empty) V hbeta.le hN0 (n := n + 1) (by simp)
      (fun e : Empty => e.elim) 0
    rw [hKV] at this
    exact this
  have hm0 : RefMarg.cavMarg V lam n ≤ ENNReal.ofReal KL • (HRS.Whole.withDensityReal rho) := by
    have := RefMarg.marginal_le_smul (B := Empty) V hbeta.le hN0 (n := n) (by simp)
      (fun e : Empty => e.elim) 0
    rw [hKV] at this
    exact this
  have hac1 := Measure.absolutelyContinuous_of_le_smul hm1
  have hpm : Measurable (fun x => ((RefMarg.cavMarg V lam (n + 1)).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal) := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hp1 : ∫ x, ((RefMarg.cavMarg V lam (n + 1)).rnDeriv (HRS.Whole.withDensityReal rho) x).toReal
      ∂(HRS.Whole.withDensityReal rho) = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac1]; simp
  have hpi : Integrable (fun x => ((RefMarg.cavMarg V lam (n + 1)).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal) (HRS.Whole.withDensityReal rho) :=
    s82r_rn_integrable
  have hp3 : ∀ᵐ x ∂(HRS.Whole.withDensityReal rho), ((RefMarg.cavMarg V lam (n + 1)).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal ≤ 3 :=
    (s82r_rn_le (by linarith) hm1).mono fun x hx => hx.trans hKL3
  have hp0 : ∀ᵐ x ∂(HRS.Whole.withDensityReal rho), 0 < ((RefMarg.cavMarg V lam (n + 1)).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal := hform.mono fun x hx => hx.1
  have hstepraw := hCL rho hρ0r hMbr _ rfl V hVq hVγ hVM.le hVM'.le hψ (p := 0) (n := n) (k := 1)
    (fun i : Fin 0 => i.elim0) (Nat.zero_le 1) (by norm_num) (0 : Fin n)
  have hstep : ∀ᵐ x ∂(HRS.Whole.withDensityReal rho),
      |((RefMarg.cavMarg V lam n).rnDeriv (HRS.Whole.withDensityReal rho) x).toReal -
        ((RefMarg.cavMarg V lam (n + 1)).rnDeriv (HRS.Whole.withDensityReal rho) x).toReal| ≤
        CL / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hstepraw] with x hx
    have h1 := hx.1
    rw [s82r_cavMarg_fin0 V lam n] at h1
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one] at h1
    exact h1
  have hD : ∀ x : Euc d,
      0 ≤ Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) +
        lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n) ∧
      Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) +
        lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n) ≤ CD * HRS.MS.Phase2S82.deltaN (n + 1) :=
    fun x => hCD rho hρ0r hMbr V hVq (by rw [hVγ]) hVC hκ (n + 1) n (Nat.le_succ n) x
  have hrow : ∀ x : Euc d, ∫ y, V.q y x ∂(HRS.Whole.withDensityReal rho) ≤ γ := fun x =>
    (integral_congr_ae (Filter.Eventually.of_forall fun y => V.q_symm y x)).trans_le
      ((V.row_le x).trans hVγ.le)
  have hqnn : ∀ x y : Euc d, 0 ≤ V.q y x := fun x y => V.q_nonneg _ _
  have hcv : ∀ x : Euc d, ∫ y, V.q y x ∂(HRS.Whole.withDensityReal rho) =
      HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x := fun x => by
    unfold HRS.Whole.convMeasure
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show V.q y x = q (x - y)
    rw [hVq, ← neg_sub x y, hq.even]
  have hcv0 : ∀ x : Euc d, 0 ≤ HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x :=
    fun x => s82r_conv_nonneg hq _ x
  have hgi : ∀ x : Euc d, Integrable (fun y => V.q y x) (HRS.Whole.withDensityReal rho) := fun x =>
    (V.integrable_q x).congr (Filter.Eventually.of_forall fun y => V.q_symm x y)
  set Err : Euc d → ℝ := fun x => h (n + 1) x + beta / ((n + 1 : ℕ) : ℝ) *
      HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x -
      lam * n * (∫ y, V.q y x * (((RefMarg.cavMarg V lam n).rnDeriv (HRS.Whole.withDensityReal rho) y).toReal - 1)
        ∂(HRS.Whole.withDensityReal rho)) +
      (Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) +
        lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n)) with hErr
  have hlog : ∀ᵐ x ∂(HRS.Whole.withDensityReal rho), Real.log (((RefMarg.cavMarg V lam (n + 1)).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal) = c - 0 + Err x := by
    filter_upwards [hform] with x hx
    rw [hx.2, hVφ x, hcv x, hErr]
    simp only
    rw [hlam]
    push_cast
    field_simp
    ring
  have hE : ∀ e : ℝ, 0 ≤ e → (∀ᵐ x ∂(HRS.Whole.withDensityReal rho), |((RefMarg.cavMarg V lam (n + 1)).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal - 1| ≤ e) →
      ∀ᵐ x ∂(HRS.Whole.withDensityReal rho), |Err x| ≤ A * HRS.MS.Phase2S82.deltaN (n + 1) + e / 1000 := by
    intro e he hae
    have hνb : ∀ᵐ y ∂(HRS.Whole.withDensityReal rho),
        |((RefMarg.cavMarg V lam n).rnDeriv (HRS.Whole.withDensityReal rho) y).toReal - 1| ≤
          e + CL / ((n + 1 : ℕ) : ℝ) := by
      filter_upwards [hae, hstep] with y h1 h2
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    refine ae_of_all _ fun x => ?_
    have hs : CL / ((n + 1 : ℕ) : ℝ) ≤ CL * HRS.MS.Phase2S82.deltaN (n + 1) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hδN hCL0
    have hĔ : |∫ y, V.q y x * (((RefMarg.cavMarg V lam n).rnDeriv (HRS.Whole.withDensityReal rho) y).toReal - 1)
        ∂(HRS.Whole.withDensityReal rho)| ≤ (e + CL / ((n + 1 : ℕ) : ℝ)) * γ := by
      have hen : 0 ≤ e + CL / ((n + 1 : ℕ) : ℝ) := by positivity
      calc _ = ‖∫ y, V.q y x * (((RefMarg.cavMarg V lam n).rnDeriv (HRS.Whole.withDensityReal rho) y).toReal - 1)
              ∂(HRS.Whole.withDensityReal rho)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ y, V.q y x * (e + CL / ((n + 1 : ℕ) : ℝ)) ∂(HRS.Whole.withDensityReal rho) := by
            refine norm_integral_le_of_norm_le ((hgi x).mul_const _) ?_
            filter_upwards [hνb] with y hy
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hqnn x y), Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hy (hqnn x y)
        _ = (∫ y, V.q y x ∂(HRS.Whole.withDensityReal rho)) * (e + CL / ((n + 1 : ℕ) : ℝ)) :=
            integral_mul_const _ _
        _ ≤ γ * (e + CL / ((n + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right (hrow x) hen
        _ = _ := mul_comm _ _
    obtain ⟨hD1, hD2⟩ := hD x
    have hhx := hbound x
    have hconv1 : beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤ 1 / 1000 := hsr x
    have hconv0 := hcv0 x
    have hlamn : lam * (n : ℝ) ≤ beta := by
      rw [hlam]
      have : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      calc beta / ((n + 1 : ℕ) : ℝ) * n ≤ beta / ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = beta := by field_simp
    have hlamn0 : 0 ≤ lam * (n : ℝ) := by positivity
    have hb0 : 0 ≤ beta / ((n + 1 : ℕ) : ℝ) * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x := by
      positivity
    have hb1 : beta / ((n + 1 : ℕ) : ℝ) * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤
        HRS.MS.Phase2S82.deltaN (n + 1) / 1000 := by
      have h2 : beta / ((n + 1 : ℕ) : ℝ) * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x =
          (beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x) * (1 / ((n + 1 : ℕ) : ℝ)) := by
        field_simp
      rw [h2]
      calc _ ≤ (1 / 1000) * (1 / ((n + 1 : ℕ) : ℝ)) :=
            mul_le_mul hconv1 le_rfl (by positivity) (by norm_num)
        _ ≤ (1 / 1000) * HRS.MS.Phase2S82.deltaN (n + 1) := mul_le_mul_of_nonneg_left hδN (by norm_num)
        _ = _ := by ring
    have hc : |lam * n * (∫ y, V.q y x * (((RefMarg.cavMarg V lam n).rnDeriv (HRS.Whole.withDensityReal rho) y).toReal - 1)
        ∂(HRS.Whole.withDensityReal rho))| ≤ (e + CL * HRS.MS.Phase2S82.deltaN (n + 1)) / 1000 := by
      rw [abs_mul, abs_of_nonneg hlamn0]
      calc lam * n * _ ≤ beta * ((e + CL / ((n + 1 : ℕ) : ℝ)) * γ) :=
            mul_le_mul hlamn hĔ (abs_nonneg _) hbeta.le
        _ = (e + CL / ((n + 1 : ℕ) : ℝ)) * (beta * γ) := by ring
        _ = (e + CL / ((n + 1 : ℕ) : ℝ)) / 1000 := by rw [hβγ]; ring
        _ ≤ (e + CL * HRS.MS.Phase2S82.deltaN (n + 1)) / 1000 := by linarith
    rw [hErr]
    simp only
    rw [abs_le] at hhx hc ⊢
    have hCDδ := hD2
    have hA' : A * HRS.MS.Phase2S82.deltaN (n + 1) =
        C0 * HRS.MS.Phase2S82.deltaN (n + 1) + CD * HRS.MS.Phase2S82.deltaN (n + 1) +
          (1 + CL) * HRS.MS.Phase2S82.deltaN (n + 1) / 1000 := by rw [hA]; ring
    constructor <;> linarith [hhx.1, hhx.2, hc.1, hc.2, hD1, hD2, hb0, hb1, hA']
  have habs := s82r_absorb (μ := HRS.Whole.withDensityReal rho)
    (p := fun x => ((RefMarg.cavMarg V lam (n + 1)).rnDeriv (HRS.Whole.withDensityReal rho) x).toReal)
    (Err := Err) hpm hp0 hp1 hpi hp3 (c := c) (A := A) (δ := HRS.MS.Phase2S82.deltaN (n + 1))
    hAnn hδ0 (by linarith) hlog hE
  refine habs.trans (ENNReal.ofReal_le_ofReal ?_)
  have := le_max_left (5 * A) ((Kc + 1) * N1)
  nlinarith

end HRS.MS.S82R

end
