import HRS.MS.WadAux75

/-!
# S8.3, packet S8E-1, part 5: the a priori estimate with an abstract source

`s8e_apriori_gen`: for `S8eSol q a ν t M Φ w` with `t ≤ T` whose source satisfies the weighted bound
`Wt M ((cB Θ + Ex) ρ_λ(s)) (q s)` for every admissible constant `Θ` of `w`, the solution is admissible with the
constant `K (Φ + Ex)` and `|w_r(y)| ≤ K (Φ + Ex) ⟨y⟩^M`; `λ` and `K` depend only on `d, M, a, ν, T, cB`.
(For `q = 𝓑 w`, `Ex = 0`, `cB = 2 C_B` this is `s8d_apriori_adm` and `s84_apriori`.)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_apriori_gen {a ν T M cB : ℝ} (ha : 0 < a) (hν : 0 < ν) (hT : 0 < T) (hM : 0 ≤ M)
    (hcB : 0 ≤ cB) :
    ∃ lam K : ℝ, 0 ≤ lam ∧ 0 ≤ K ∧ ∀ {t Φ Ex : ℝ} {q w : ℝ → Euc d → ℝ}, 0 < t → t ≤ T → 0 ≤ Ex →
      S8eSol q a ν t M Φ w →
      (∀ Θ : ℝ, 0 ≤ Θ → S84Adm lam t M w Θ → ∀ s ∈ Set.Ico 0 t,
        Wt M ((cB * Θ + Ex) * s84_wt lam t s) (q s)) →
      S84Adm lam t M w (K * (Φ + Ex)) ∧
        ∀ r ∈ Set.Icc 0 t, ∀ y : Euc d, |w r y| ≤ K * (Φ + Ex) * jbracket y ^ M := by
  obtain ⟨K₂, hK₂0, hK₂⟩ := s84_P_fderiv_holder (d := d) (a := a) (ν := ν) (T := T) (M := M) ha hν hM
  set K₁ : ℝ := s84_K1 d M a ν T with hK₁
  have hK₁0 : 0 ≤ K₁ := s84_K1_nonneg M ha hν
  have hT0 : 0 ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg hT.le _
  set Kst : ℝ := K₁ * T ^ (1 / 4 : ℝ) + K₂ with hKst
  have hKst0 : 0 ≤ Kst := by positivity
  set c0 : ℝ := 3 ^ M * Kst * cB with hc0
  have hc00 : 0 ≤ c0 := by positivity
  set εk : ℝ := 1 / (2 * (c0 + 1)) with hεk
  have hεk0 : 0 < εk := by positivity
  have hεk1 : εk ≤ 1 := by
    rw [hεk, div_le_one (by positivity)]; linarith
  obtain ⟨lam, hlam0, hlam⟩ := s84_kernel hT hεk0
  set KP : ℝ := 2 ^ M * mom d M (Real.sqrt (ν / a)) with hKP
  have hKP0 : 0 ≤ KP := mul_nonneg (by positivity) (s83_mom_nonneg _ _ (Real.sqrt_nonneg _))
  set E' : ℝ := 4 * Real.exp (lam * T) * T ^ (1 / 4 : ℝ) with hE'
  have hE'0 : 0 ≤ E' := by positivity
  set K : ℝ := max (max 1 (2 * (3 ^ M * Kst))) (KP * (1 + 2 * cB * (3 ^ M * Kst) * E' + E')) with hK
  have hK1 : 1 ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hK2 : 2 * (3 ^ M * Kst) ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hK3 : KP * (1 + 2 * cB * (3 ^ M * Kst) * E' + E') ≤ K := le_max_right _ _
  refine ⟨lam, K, hlam0.le, by linarith, ?_⟩
  intro t Φ Ex q w ht htT hEx sol hq
  have hΦ0 : 0 ≤ Φ := sol.term_wt.nonneg
  have hker : ∀ r' : ℝ, 0 ≤ r' → r' < t → (∫ s in r'..t, (s - r') ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) ≤
      εk * (Real.exp (lam * (t - r')) * (t - r') ^ (-(3 / 4 : ℝ))) := fun r' hr0 hr't =>
    hlam r' t hr't (by linarith)
  have hstep : ∀ Θ : ℝ, 0 ≤ Θ → S84Adm lam t M w Θ →
      S84Adm lam t M w (3 ^ M * Kst * (Φ + Ex) + Θ / 2) := by
    intro Θ hΘ hadm
    have := s8e_step ha hν hM htT hK₂0 hK₂ hcB hEx sol hΘ hlam0.le hεk0.le
      (hq Θ hΘ hadm) hker hadm
    refine this.mono ?_
    have hεc : c0 * εk ≤ 1 / 2 := by
      rw [hεk, ← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h3 : 0 ≤ 3 ^ M * Kst := by positivity
    have e : 3 ^ M * Kst * (cB * Θ * εk) = (c0 * εk) * Θ := by rw [hc0]; ring
    calc 3 ^ M * (K₁ * T ^ (1 / 4 : ℝ) + K₂) * (Φ + (cB * Θ + Ex) * εk)
        = 3 ^ M * Kst * Φ + (c0 * εk) * Θ + 3 ^ M * Kst * (Ex * εk) := by
          rw [← e, hKst]; ring
      _ ≤ 3 ^ M * Kst * (Φ + Ex) + Θ / 2 := by
          have h1 := mul_le_mul_of_nonneg_right hεc hΘ
          have h2 : Ex * εk ≤ Ex := by nlinarith
          have h4 := mul_le_mul_of_nonneg_left h2 h3
          nlinarith
  obtain ⟨Θ₀, hΘ₀, hadm₀⟩ := s8e_adm_start sol hM ht htT hlam0.le
  have hA : 0 ≤ 3 ^ M * Kst * (Φ + Ex) := by positivity
  have hfix := s84_adm_fix hA ⟨Θ₀, hΘ₀, hadm₀⟩ hstep
  have hAK : 2 * (3 ^ M * Kst * (Φ + Ex)) ≤ K * (Φ + Ex) := by
    have := mul_le_mul_of_nonneg_right hK2 (add_nonneg hΦ0 hEx)
    linarith
  refine ⟨hfix.mono hAK, fun r hr y => ?_⟩
  have hjy : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s83_one_le_jb y) hM
  have hjy0 : 0 ≤ jbracket y ^ M := le_trans zero_le_one hjy
  have hΦE : 0 ≤ Φ + Ex := add_nonneg hΦ0 hEx
  rcases hr.2.eq_or_lt with hrt | hrt
  · subst hrt
    have := sol.term_wt y
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have h1 : Φ * jbracket y ^ M ≤ K * (Φ + Ex) * jbracket y ^ M := by
      refine mul_le_mul_of_nonneg_right ?_ hjy0
      have := mul_le_mul_of_nonneg_right hK1 hΦE
      linarith
    exact h1
  · have hrI : r ∈ Set.Ico 0 t := ⟨hr.1, hrt⟩
    have hz := s8e_zero_bound ha hν hM htT hcB hEx sol (by positivity) hlam0.le (hq _ (by positivity) hfix)
      hfix hrI y
    refine hz.trans ?_
    have hb : Φ + (cB * (2 * (3 ^ M * Kst * (Φ + Ex))) + Ex) * E' ≤
        (1 + 2 * cB * (3 ^ M * Kst) * E' + E') * (Φ + Ex) := by
      have h0 : 0 ≤ 2 * cB * (3 ^ M * Kst) * E' := by positivity
      nlinarith [mul_nonneg hEx hE'0, mul_nonneg hΦ0 hE'0]
    calc KP * jbracket y ^ M * (Φ + (cB * (2 * (3 ^ M * Kst * (Φ + Ex))) + Ex) * E')
        ≤ KP * jbracket y ^ M * ((1 + 2 * cB * (3 ^ M * Kst) * E' + E') * (Φ + Ex)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (KP * (1 + 2 * cB * (3 ^ M * Kst) * E' + E')) * (Φ + Ex) * jbracket y ^ M := by ring
      _ ≤ K * (Φ + Ex) * jbracket y ^ M := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK3 hΦE) hjy0

end HRS.MS.Wad
