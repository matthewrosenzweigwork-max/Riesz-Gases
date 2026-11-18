import HRS.MS.S82RN13

/-!
# S8.2 R02 (S82R), N14: the pointwise part of `PinComparison` for a `WeakReferenceSetup`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.External

variable {d : ℕ}

/-- The weak potential of the reference field, with the identifications needed downstream. -/
lemma s82r_part2_ident (hd : 2 ≤ d) {beta : ℝ} (hbeta : 0 < beta) {q : Euc d → ℝ}
    (hq : ShortRangePole d q) {rho : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hsr : ∀ x, beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤ 1 / 1000)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} {t : ℝ}
    (hhm : Measurable (h N)) (hh : ∀ x, |h N x| ≤ t) (hN0 : 0 < N) {p n : ℕ} (pins : Fin p → Euc d) :
    ∃ V : WeakPotential (HRS.Whole.withDensityReal rho), V.M = 1 / 1000 + t ∧ V.M' = t ∧
      V.γ = 1 / (1000 * beta) ∧ (∀ x y, V.q x y = q (x - y)) ∧
      IsField (HRS.Whole.withDensityReal rho) V.φ (1 / 1000 + t) t ∧
      referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins = pinnedLaw V (beta / N) n pins ∧
      refMarginal q h (HRS.Whole.withDensityReal rho) beta N =
        (haveI : NeZero N := ⟨hN0.ne'⟩; RefMarg.cavMarg V (beta / N) N) := by
  haveI := s82r_isProb hρ
  refine ⟨s82r_potW hd hbeta hq hsr hG hρ hρG hhm hh, rfl, rfl, rfl, fun x y => rfl,
    s82r_isFieldW hd hbeta hq hsr hG hρ hρG hhm hh, ?_, ?_⟩
  · exact s82r_referenceLaw_eq_pot (s82r_potW hd hbeta hq hsr hG hρ hρG hhm hh) rfl (fun x y => rfl)
      hbeta.le pins
  · exact s82r_refMarg_eq hN0 (s82r_potW hd hbeta hq hsr hG hρ hρG hhm hh) rfl (fun x y => rfl) hbeta.le


/-- The thermal data used throughout: a probability density with Gaussian upper bound. -/
lemma s82r_thermal_pack (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ Cth cth : ℝ, 0 < Cth + 1 ∧
      HRS.Whole.IsProbDensity (HRS.Whole.thermalDensity d (criticalS d) a beta) ∧
      HRS.Whole.HasR2GaussianUpper (Cth + 1) cth (HRS.Whole.thermalDensity d (criticalS d) a beta) ∧
      ∀ x, HRS.Whole.thermalDensity d (criticalS d) a beta x ≤ Cth := by
  have hs0 := (s82r_criticalS_pos (by omega : 1 ≤ d)).le
  have hsd := s82r_criticalS_lt (by omega : 1 ≤ d)
  obtain ⟨Cth, cth, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hbeta
  have hρ0 : HRS.Whole.IsProbDensity (HRS.Whole.thermalDensity d (criticalS d) a beta) := hT.prob
  refine ⟨Cth, cth, by linarith [hT.C0], hρ0, ⟨hT.hc, fun x => ?_⟩, fun x => ?_⟩
  · have h1 := (le_abs_self _).trans (hT.h0 x)
    have h2 : 0 ≤ Real.exp (-cth * ‖x‖ ^ 2) := (Real.exp_pos _).le
    nlinarith
  · have h1 := (le_abs_self _).trans (hT.h0 x)
    have h2 : Real.exp (-cth * ‖x‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
    nlinarith [hT.C0]

lemma s82r_cap_large {f1 f2 KL CL Cf S Nn : ℝ} (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) (hNn : 0 < Nn)
    (hS : 0 ≤ S) (h1 : |f1 - f2| ≤ CL / Nn * (1 + S)) (h2 : f1 ≤ KL) (h3 : f2 ≤ KL)
    (hCf1 : KL ≤ Cf) (hCf2 : CL ≤ Cf) : |f1 - f2| ≤ Cf * min 1 ((1 + S) / Nn) := by
  have hx0 : 0 ≤ (1 + S) / Nn := by positivity
  rcases le_or_gt 1 ((1 + S) / Nn) with hx | hx
  · rw [min_eq_left hx, mul_one]
    rw [abs_le]; constructor <;> linarith
  · rw [min_eq_right hx.le]
    have hCL0 : 0 ≤ CL := by
      by_contra hneg
      push_neg at hneg
      have : CL / Nn * (1 + S) < 0 := mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hneg hNn) (by linarith)
      linarith [abs_nonneg (f1 - f2)]
    calc |f1 - f2| ≤ CL / Nn * (1 + S) := h1
      _ = CL * ((1 + S) / Nn) := by ring
      _ ≤ Cf * ((1 + S) / Nn) := mul_le_mul_of_nonneg_right hCf2 hx0

lemma s82r_cap_small {f1 f2 K Cf S Nn N1 : ℝ} (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) (h2 : f1 ≤ K) (h3 : f2 ≤ K)
    (hNn : 0 < Nn) (hS : 0 ≤ S) (hN1 : Nn ≤ N1) (hN11 : 1 ≤ N1) (hCf : K * N1 ≤ Cf) :
    |f1 - f2| ≤ Cf * min 1 ((1 + S) / Nn) := by
  have hN10 : 0 < N1 := lt_of_lt_of_le hNn hN1
  have hK0 : 0 ≤ K := hf1.trans h2
  have hmin : 1 / N1 ≤ min 1 ((1 + S) / Nn) := by
    refine le_min ?_ ?_
    · rw [div_le_one hN10]
      exact hN11
    · calc 1 / N1 ≤ 1 / Nn := one_div_le_one_div_of_le hNn hN1
        _ ≤ (1 + S) / Nn := div_le_div_of_nonneg_right (by linarith) hNn.le
  calc |f1 - f2| ≤ K := by rw [abs_le]; constructor <;> linarith
    _ = (K * N1) * (1 / N1) := by field_simp
    _ ≤ Cf * min 1 ((1 + S) / Nn) :=
        mul_le_mul hCf hmin (by positivity) ((mul_nonneg hK0 hN10.le).trans hCf)

/-- **Pointwise pin comparison, part 2** (`PinComparison.2`). -/
theorem s82r_part2 (hd : 2 ≤ d) (a beta C0 : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ, WeakReferenceSetup d a beta rho q h C0 →
      ∀ N : ℕ, 2 ≤ N → ∀ p n : ℕ, p ≤ 2 → n + p ≤ N → N - (n + p) ≤ 2 →
        ∀ pins : Fin p → Euc d, ∀ i : Fin n,
          ∀ᵐ z ∂HRS.Whole.withDensityReal rho,
            |(((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
                (fun X => X i)).rnDeriv (HRS.Whole.withDensityReal rho) z).toReal -
              ((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
                (HRS.Whole.withDensityReal rho) z).toReal| ≤
              C * min 1 ((1 + ∑ j, q (z - pins j)) / N) := by
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
  obtain ⟨N1, hN12, hN1⟩ := s82r_eventually_C0_delta hd C0
  set KL : ℝ := Real.exp (1 / 1000 + 1 / 4 + 1 / 4 + beta * γ) with hKL
  set Kc : ℝ := Real.exp (1 / 1000 + C0 + C0 + beta * γ) with hKc
  have hKL0 : 0 < KL := Real.exp_pos _
  have hKc0 : 0 < Kc := Real.exp_pos _
  have hN1r : (2 : ℝ) ≤ N1 := by exact_mod_cast hN12
  refine ⟨max (max KL CL) (Kc * N1) + 1, by positivity, ?_⟩
  intro rho hrho h hW N hN p n hp hnp hrem pins i
  haveI : NeZero n := ⟨i.pos.ne'⟩
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  subst hrho_eq
  obtain ⟨k, hk⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
  subst hk
  haveI hμ := s82r_isProb hρ0
  have hN0 : 0 < n + k := by omega
  have hNr : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by exact_mod_cast hN0
  have hpk : p ≤ k := by omega
  have hk4 : k ≤ 4 := by omega
  have hδ1 : HRS.MS.Phase2S82.deltaN (n + k) ≤ 1 := HRS.MS.S82P2.s82p2_deltaN_le_one (by omega)
  have hC0 : 0 ≤ C0 := hW.positive.le
  have hbound := hW.hbound (n + k) hN
  have hmeas := hW.hmeas (n + k)
  have hsr := hW.small_row
  set Cf : ℝ := max (max KL CL) (Kc * N1) + 1 with hCf
  have hCf1 : KL ≤ Cf := by
    have := le_max_left (max KL CL) (Kc * N1)
    have := le_max_left KL CL
    linarith
  have hCf2 : CL ≤ Cf := by
    have := le_max_left (max KL CL) (Kc * N1)
    have := le_max_right KL CL
    linarith
  have hCf3 : Kc * N1 ≤ Cf := by
    have := le_max_right (max KL CL) (Kc * N1)
    linarith
  have hCf0 : 0 < Cf := by positivity
  have hsum0 : ∀ z : Euc d, 0 ≤ ∑ j, q (z - pins j) := fun z =>
    Finset.sum_nonneg fun j _ => hq.nonneg _
  by_cases hbig : N1 ≤ n + k
  · obtain ⟨V, hVM, hVM', hVγ, hVq, hψ, hRef, hMarg⟩ := s82r_part2_ident hd hbeta hq hsr hG hρ0 hρG
      (t := 1 / 4) hmeas (fun x => (hbound x).trans (hN1 _ hbig)) hN0 pins
    rw [hRef, hMarg]
    have key := hCL _ hρ0 hMb _ rfl V hVq hVγ hVM.le hVM'.le hψ pins hpk hk4 i
    filter_upwards [key] with z hz
    obtain ⟨h1, h2, h3⟩ := hz
    have hf1 := ENNReal.toReal_nonneg (a := (((pinnedLaw V (beta / ((n + k : ℕ) : ℝ)) n pins).map
      (fun y => y i)).rnDeriv (HRS.Whole.withDensityReal (thermalDensity d (criticalS d) a beta)) z))
    have hf2 := ENNReal.toReal_nonneg (a := ((RefMarg.cavMarg V (beta / ((n + k : ℕ) : ℝ)) (n + k)).rnDeriv
      (HRS.Whole.withDensityReal (thermalDensity d (criticalS d) a beta)) z))
    exact s82r_cap_large hf1 hf2 hNr (hsum0 z) h1 h2 h3 hCf1 hCf2
  · push_neg at hbig
    have hC0δ : C0 * HRS.MS.Phase2S82.deltaN (n + k) ≤ C0 := mul_le_of_le_one_right hC0 hδ1
    obtain ⟨V, hVM, hVM', hVγ, hVq, hψ, hRef, hMarg⟩ := s82r_part2_ident hd hbeta hq hsr hG hρ0 hρG
      (t := C0) hmeas (fun x => (hbound x).trans hC0δ) hN0 pins
    rw [hRef, hMarg]
    have d1 := s82r_marg_density_le V hbeta.le hN0 pins (n := n)
      (by simp only [Fintype.card_fin]; omega) i
    have d2 := s82r_marg_density_le V hbeta.le hN0 (fun e : Empty => e.elim) (n := n + k)
      (by simp) (0 : Fin (n + k))
    have hKc' : Real.exp (V.M + V.M' + beta * V.γ) = Kc := by
      rw [hVM, hVM', hVγ, hKc, hγ]
    rw [hKc'] at d1 d2
    filter_upwards [d1, d2] with z h2 h3
    have hf1 := ENNReal.toReal_nonneg (a := (((pinnedLaw V (beta / ((n + k : ℕ) : ℝ)) n pins).map
      (fun y => y i)).rnDeriv (HRS.Whole.withDensityReal (thermalDensity d (criticalS d) a beta)) z))
    have hf2 := ENNReal.toReal_nonneg (a := ((RefMarg.cavMarg V (beta / ((n + k : ℕ) : ℝ)) (n + k)).rnDeriv
      (HRS.Whole.withDensityReal (thermalDensity d (criticalS d) a beta)) z))
    refine s82r_cap_small hf1 hf2 h2 h3 hNr (hsum0 z) ?_ (by linarith) hCf3
    have : ((n + k : ℕ) : ℝ) ≤ N1 := by exact_mod_cast hbig.le
    exact this

end HRS.MS.S82R

end
