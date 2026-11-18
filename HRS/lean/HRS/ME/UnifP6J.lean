import HRS.ME.UnifP6I

/-!
# Uniform Proposition 4.9, part J (packet P6): `l49_time_integral`

Uniform form of `l49_time_integral` (`HRS/Equilibrium/L49Aux13.lean`): the constants
`K₁ K₂ K₃ Cc lam0` are chosen before `β ∈ [βm, βp]` and `ρ ∈ UFam d c₀ Λ`.  The structural facts
`D ≥ 0` and the integral formula for the defect are taken pointwise from `cavity_response_proof`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.L48 HRS.L49

variable {d : ℕ} {s : ℝ}

set_option maxHeartbeats 6400000 in
/-- Uniform `l49_time_integral`. -/
theorem l49_time_integral_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ) (hCR : CavRespUnif d s c βm βp c₀ Λ) :
    ∃ K₁ K₂ K₃ Cc lam0 : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ 0 ≤ K₃ ∧ 0 < lam0 ∧ lam0 ≤ 1 ∧
      (∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ x : Torus d,
        Integrable (fun y => taylorH (lam * gPlus d s c (x - y))) (withDensityReal ρ) ∧
        |∫ y, taylorH (lam * gPlus d s c (x - y)) ∂(withDensityReal ρ) -
            sphereArea d / d * ρ x * lam ^ 2 * Real.log (1 / lam)| ≤ Cc * lam ^ 2) ∧
      ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → β / N ≤ lam0 → ∀ x : Torus d,
        |insertionDefect d s c β ρ N x -
            ((N - 1 : ℕ) : ℝ) * ∫ y, taylorH ((β / N) * gPlus d s c (x - y)) ∂(withDensityReal ρ)| ≤
          ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 *
            ((K₁ + K₂ * Real.sqrt (1 + |Real.log (β / N)|) +
                K₃ * Real.sqrt (deltaN d s N) * (1 + |Real.log (β / N)|)) +
              (K₂ + K₃ * Real.sqrt (deltaN d s N))) := by
  obtain ⟨K₁, K₂, K₃, hK₁, hK₂, hK₃, hVc⟩ :=
    l49_V_close_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hc₀ hΛ hCR
  obtain ⟨Cc, lam0, hl0, hl01, hcomp⟩ := l49_compensated_unif hd hcrit c hc c₀ Λ (by linarith)
  refine ⟨K₁, K₂, K₃, Cc, lam0, hK₁, hK₂, hK₃, hl0, hl01, hcomp, ?_⟩
  intro β hβI ρ hF
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  obtain ⟨C, hcav⟩ := cavity_response_proof hd hcrit β hβ ρ hρ c hc
  intro N hN hlamle x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set lam : ℝ := β / N with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 := hlamle.trans hl01
  set n : ℝ := ((N - 1 : ℕ) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hδ0 : 0 ≤ Real.sqrt (deltaN d s N) := Real.sqrt_nonneg _
  set a : ℝ := |Real.log lam| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  set A₀ : ℝ := K₁ + K₂ * Real.sqrt (1 + a) + K₃ * Real.sqrt (deltaN d s N) * (1 + a) with hA₀
  set B₀ : ℝ := K₂ + K₃ * Real.sqrt (deltaN d s N) with hB₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hB₀0 : 0 ≤ B₀ := by positivity
  obtain ⟨-, -, hD0, hDeq, -⟩ := (hcav N hN).1 x
  have hI := (hcomp ρ hF lam hlam0 hlamle x).1
  set P : ℝ → Measure (Config d (N - 1)) := fun t => critPole d s c β ρ N x t with hP
  set I : ℝ := ∫ y, taylorH (lam * gPlus d s c (x - y)) ∂(withDensityReal ρ) with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun y => l49_H_nonneg _
  -- the error integrand
  set R : ℝ → ℝ := fun t => lam ^ 2 * n * (A₀ + B₀ * |Real.log t|) with hR
  have hRm : Measurable fun t : ℝ => ENNReal.ofReal (R t) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (measurable_const.add (measurable_const.mul (Real.measurable_log.abs))))
  have hRint : ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (R t) =
      ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀)) := by
    have e : ∀ t : ℝ, R t = (lam ^ 2 * n * A₀) + (lam ^ 2 * n * B₀) * |Real.log t| := fun t => by
      simp only [hR]; ring
    simp_rw [e]
    rw [l49_lintegral_log _ _ (by positivity) (by positivity)]
    congr 1; ring
  -- pointwise bounds
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      (ENNReal.ofReal ((1 - t) * lam ^ 2) * evariance (fun Y : Config d (N - 1) =>
        ∑ i, gPlus d s c (x - Y i)) (P t) ≤
        ENNReal.ofReal ((1 - t) * lam ^ 2 * (n * l49_J d s c ρ x (t * lam))) + ENNReal.ofReal (R t)) ∧
      ENNReal.ofReal ((1 - t) * lam ^ 2 * (n * l49_J d s c ρ x (t * lam))) ≤
        ENNReal.ofReal ((1 - t) * lam ^ 2) * evariance (fun Y : Config d (N - 1) =>
        ∑ i, gPlus d s c (x - Y i)) (P t) + ENNReal.ofReal (R t) := by
    intro t ht
    obtain ⟨hmem, hbd⟩ := hVc β hβI ρ hF N hN hlam1 x t ht
    rw [← hlam, ← hn] at hbd
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
    haveI hPprob : IsProbabilityMeasure (P t) := by
      simp only [hP]
      rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
      exact pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam0.le x t ht.1.le
    set V : ℝ := (evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) (P t)).toReal with hV
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    have hev : evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) (P t) =
        ENNReal.ofReal V := by
      rw [hV, ENNReal.ofReal_toReal]
      exact hmem.evariance_ne_top
    have hlogb : |Real.log (t * lam)| ≤ |Real.log t| + a := l49_log_mul_bound ht.1 hlam0
    have hE := l49_E_bound (K₁ := K₁) (K₂ := K₂) (K₃ := K₃) (δs := Real.sqrt (deltaN d s N))
      (a := a) (ℓ := |Real.log t|) (L := |Real.log (t * lam)|)
      hK₂ hK₃ hδ0 ha0 (abs_nonneg (Real.log t)) (abs_nonneg _) (by linarith)
    have hbd' : |V - n * l49_J d s c ρ x (t * lam)| ≤ n * (A₀ + B₀ * |Real.log t|) := by
      refine hbd.trans (mul_le_mul_of_nonneg_left ?_ hn0)
      have := hE
      simp only [hA₀, hB₀]
      linarith
    have hw0 : 0 ≤ (1 - t) * lam ^ 2 := by positivity
    have hw1 : (1 - t) * lam ^ 2 ≤ lam ^ 2 := by nlinarith [ht.1.le, sq_nonneg lam]
    have hwR : (1 - t) * lam ^ 2 * (n * (A₀ + B₀ * |Real.log t|)) ≤ R t := by
      simp only [hR]
      have : 0 ≤ n * (A₀ + B₀ * |Real.log t|) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hw1 this]
    rw [hev, ← ENNReal.ofReal_mul hw0]
    have hup : (1 - t) * lam ^ 2 * V ≤ (1 - t) * lam ^ 2 * (n * l49_J d s c ρ x (t * lam)) + R t := by
      have := (abs_le.1 hbd').2
      nlinarith [mul_le_mul_of_nonneg_left (show V ≤ n * l49_J d s c ρ x (t * lam) + n * (A₀ + B₀ * |Real.log t|) by linarith) hw0]
    have hlo : (1 - t) * lam ^ 2 * (n * l49_J d s c ρ x (t * lam)) ≤ (1 - t) * lam ^ 2 * V + R t := by
      have := (abs_le.1 hbd').1
      nlinarith [mul_le_mul_of_nonneg_left (show n * l49_J d s c ρ x (t * lam) ≤ V + n * (A₀ + B₀ * |Real.log t|) by linarith) hw0]
    have hRn : 0 ≤ R t := by simp only [hR]; positivity
    constructor
    · refine (ENNReal.ofReal_le_ofReal hup).trans ?_
      exact ENNReal.ofReal_add_le
    · refine (ENNReal.ofReal_le_ofReal hlo).trans ?_
      exact ENNReal.ofReal_add_le
  have hT := l49_tonelli hd hcrit hβ hρ hc hlam0 hlam1 hn0 x hI
  have hDe : ENNReal.ofReal (insertionDefect d s c β ρ N x) =
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * lam ^ 2) *
        evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) (P t) := by
    rw [hDeq]
  -- upper bound
  have hup : ENNReal.ofReal (insertionDefect d s c β ρ N x) ≤
      ENNReal.ofReal (n * I) + ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀)) := by
    rw [hDe, ← hT, ← hRint, ← lintegral_add_right _ hRm]
    exact setLIntegral_mono' measurableSet_Ioc fun t ht => (hpt t ht).1
  have hlo : ENNReal.ofReal (n * I) ≤
      ENNReal.ofReal (insertionDefect d s c β ρ N x) + ENNReal.ofReal (lam ^ 2 * n * (A₀ + B₀)) := by
    rw [hDe, ← hRint, ← lintegral_add_right _ hRm, ← hT]
    exact setLIntegral_mono' measurableSet_Ioc fun t ht => (hpt t ht).2
  have hErr0 : 0 ≤ lam ^ 2 * n * (A₀ + B₀) := by positivity
  have hnI0 : 0 ≤ n * I := mul_nonneg hn0 hI0
  rw [← ENNReal.ofReal_add hnI0 hErr0] at hup
  rw [← ENNReal.ofReal_add hD0 hErr0] at hlo
  have h1 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hup
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlo
  have e : n * (β / N) ^ 2 * ((K₁ + K₂ * Real.sqrt (1 + |Real.log (β / N)|) +
      K₃ * Real.sqrt (deltaN d s N) * (1 + |Real.log (β / N)|)) + (K₂ + K₃ * Real.sqrt (deltaN d s N))) =
      lam ^ 2 * n * (A₀ + B₀) := by
    simp only [hA₀, hB₀, ha, hlam]; ring
  show |insertionDefect d s c β ρ N x - n * ∫ y, taylorH ((β / N) * gPlus d s c (x - y)) ∂(withDensityReal ρ)| ≤
    n * (β / N) ^ 2 * _
  rw [e]
  exact abs_le.2 ⟨by linarith, by linarith⟩

end HRS.ME.Unif

end
