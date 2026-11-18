import HRS.MS.Fp81S21WeightedMomentsS

/-!
# Higher-exponent single-law weighted field moments

The frozen `R2Wfm.round2_weighted_field_moments_proof` accepts every real
moment exponent `τ` with `1 ≤ τ`. Its spatial indices are independently
constrained by `d/2 + 2 < k` and `k + d/2 < m`. The choice `k = d + 3`
therefore supports both chart indices `(m, Pw) = (2*d+6, d+4)` and
`(2*d+8, d+2)` when `d ≥ 2`; the respective second margins are `d/2+3`
and `d/2+5`. The generic adapters below retain the exact corresponding
condition `d+3+d/2 < m` and `0 ≤ Pw`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

private theorem fp81s21_r2wfm_singleLaw_pair_tau
    (p : Parameters) {r : ℕ} {Pw M L C₀ c₀ pinf K : ℝ}
    (hPw : 0 ≤ Pw)
    (horder : (p.d : ℝ) + 3 + (p.d : ℝ) / 2 < (r : ℝ))
    (hc₀ : 0 < c₀) (hpinf : 1 < pinf) (τ : ℝ) (hτ : 1 ≤ τ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ρ : Euc p.d → ℝ,
      HRS.Whole.IsRound2Density p.d p.s M L ρ →
      HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ Pactual : Measure (EucConfig p.d N),
      HRS.Whole.HasR2ActualDensity p.s p.β pinf K
        (HRS.Whole.withDensityReal ρ) Pactual →
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (HRS.Whole.r2EmpDistr (HRS.Whole.withDensityReal ρ) X) ^ τ
        ∂Pactual) ≤ ENNReal.ofReal D ∧
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (fun f => HRS.Whole.r2CommDistr p.d p.s
          (HRS.Whole.withDensityReal ρ) X f -
          ∫ Y, HRS.Whole.r2CommDistr p.d p.s
            (HRS.Whole.withDensityReal ρ) Y f ∂Pactual) ^ τ
        ∂Pactual) ≤ ENNReal.ofReal D := by
  let pcommon : ℝ := min pinf 2
  let Kcommon : ℝ := max K 1
  have hpcommon : 1 < pcommon := lt_min hpinf (by norm_num)
  have hpcommon_pinf : pcommon ≤ pinf := min_le_left _ _
  have hpcommon_two : pcommon ≤ 2 := min_le_right _ _
  have hKleft : K ≤ Kcommon := le_max_left _ _
  have hKright : 1 ≤ Kcommon := le_max_right _ _
  have hdR : (2 : ℝ) ≤ p.d := by exact_mod_cast p.hd
  have horderCast : ((p.d + 3 : ℕ) : ℝ) + (p.d : ℝ) / 2 < (r : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using horder
  have hdensityFamily := HRS.MS.R2Wfm.round2_weighted_field_moments_proof
    (d := p.d) p.hd p.s p.hs0 p.hs M L C₀ c₀ p.β pcommon Kcommon
    Pw p.hβ hpcommon hPw (p.d + 3) r (by
      push_cast
      nlinarith [hdR]) horderCast τ hτ
  obtain ⟨Cwfm, hCwfm⟩ := hdensityFamily.1
  let D : ℝ := max Cwfm 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨D, hD, ?_⟩
  intro ρ hρ hG N hN Pactual hactual

  let μ : Measure (Euc p.d) := HRS.Whole.withDensityReal ρ
  let Q : ∀ n : ℕ, Measure (EucConfig p.d n) := fun n =>
    HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel p.d p.s) n p.β μ
  obtain ⟨Cnorm, hCnorm, hnormalizer⟩ := HRS.MS.R2Mt.s92_normalizer_bounds
    p.hd p.hs0 p.hs M L p.β (2 * p.β) p.hβ (by nlinarith [p.hβ])
  have hQprob : ∀ n : ℕ, 2 ≤ n → IsProbabilityMeasure (Q n) := by
    intro n hn
    have hW := (hnormalizer ρ hρ n hn p.β
      ⟨le_rfl, by nlinarith [p.hβ]⟩).1
    letI : IsProbabilityMeasure μ := HRS.MS.R2Mt.s92_isProb_mu hρ.prob
    change IsProbabilityMeasure
      (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel p.d p.s) n p.β μ)
    exact HRS.MS.R2Mt.s92_isProb_Q hW

  let P : ∀ n : ℕ, Measure (EucConfig p.d n) := fun n =>
    if h : n = N then h.symm ▸ Pactual else Q n
  have hfamily : ∀ n : ℕ, 2 ≤ n →
      HRS.Whole.HasR2ActualDensity p.s p.β pcommon Kcommon μ (P n) := by
    intro n hn
    by_cases hEq : n = N
    · subst n
      simp only [P, dif_pos rfl]
      letI : IsProbabilityMeasure (Q N) := hQprob N hN
      refine ⟨hactual.1, hactual.2.1, ?_⟩
      have hmono :
          eLpNorm (fun X => ((Pactual.rnDeriv (Q N)) X).toReal)
              (ENNReal.ofReal pcommon) (Q N) ≤
            eLpNorm (fun X => ((Pactual.rnDeriv (Q N)) X).toReal)
              (ENNReal.ofReal pinf) (Q N) :=
        eLpNorm_le_eLpNorm_of_exponent_le
          (ENNReal.ofReal_le_ofReal hpcommon_pinf)
      exact (hmono.trans hactual.2.2).trans
        (ENNReal.ofReal_le_ofReal hKleft)
    · simp only [P, dif_neg hEq]
      letI : IsProbabilityMeasure (Q n) := hQprob n hn
      have hself := S99.s99_actual (Q n) rfl
      refine ⟨hself.1, hself.2.1, ?_⟩
      have hmono :
          eLpNorm (fun X => ((Q n).rnDeriv (Q n) X).toReal)
              (ENNReal.ofReal pcommon) (Q n) ≤
            eLpNorm (fun X => ((Q n).rnDeriv (Q n) X).toReal)
              (ENNReal.ofReal 2) (Q n) :=
        eLpNorm_le_eLpNorm_of_exponent_le
          (ENNReal.ofReal_le_ofReal hpcommon_two)
      exact (hmono.trans hself.2.2).trans
        (ENNReal.ofReal_le_ofReal hKright)

  have hbound := hCwfm ρ hρ hG P hfamily
  have hAtN := hbound () N hN
  have hEmpActual :
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (HRS.Whole.r2EmpDistr μ X) ^ τ ∂Pactual) ≤
          ENNReal.ofReal Cwfm := by
    calc
      _ ≤ ∫⁻ X, (HRS.Whole.r2NegSobNorm r Pw
          (HRS.Whole.r2EmpDistr μ X) ^ τ +
        HRS.Whole.r2NegSobNorm r Pw
          (HRS.Whole.r2CommDistr p.d p.s μ X) ^ τ) ∂Pactual := by
            apply lintegral_mono
            intro X
            exact le_add_of_nonneg_right (by positivity)
      _ ≤ ENNReal.ofReal Cwfm := by simpa [P, μ] using hAtN.1
  have hcommActual :
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (fun f => HRS.Whole.r2CommDistr p.d p.s μ X f -
          ∫ Y, HRS.Whole.r2CommDistr p.d p.s μ Y f ∂Pactual) ^ τ
        ∂Pactual) ≤ ENNReal.ofReal Cwfm := by
    calc
      _ ≤ ∫⁻ X,
          (HRS.Whole.r2NegSobNorm r Pw
              (fun f => HRS.Whole.r2EmpDistr μ X f -
                ∫ Y, HRS.Whole.r2EmpDistr μ Y f ∂Pactual) ^ τ +
            HRS.Whole.r2NegSobNorm r Pw
              (fun f => HRS.Whole.r2CommDistr p.d p.s μ X f -
                ∫ Y, HRS.Whole.r2CommDistr p.d p.s μ Y f ∂Pactual) ^ τ)
          ∂Pactual := by
            apply lintegral_mono
            intro X
            exact le_add_of_nonneg_left (by positivity)
      _ ≤ ENNReal.ofReal Cwfm := by simpa [P, μ] using hAtN.2
  refine ⟨?_, ?_⟩
  · calc
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
          (HRS.Whole.r2EmpDistr (HRS.Whole.withDensityReal ρ) X) ^ τ
          ∂Pactual) ≤ ENNReal.ofReal Cwfm := by simpa [μ] using hEmpActual
      _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · calc
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
          (fun f => HRS.Whole.r2CommDistr p.d p.s
            (HRS.Whole.withDensityReal ρ) X f -
            ∫ Y, HRS.Whole.r2CommDistr p.d p.s
              (HRS.Whole.withDensityReal ρ) Y f ∂Pactual) ^ τ
          ∂Pactual) ≤ ENNReal.ofReal Cwfm := by simpa [μ] using hcommActual
      _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- Higher-exponent empirical single-law bound. It exposes the raw
empirical clause of `R2WeightedFieldBound` with moment exponent `τ`. -/
theorem fp81s21_emp_r2wfm_singleLaw_tau
    (p : Parameters) {r : ℕ} {Pw M L C₀ c₀ pinf K : ℝ}
    (hPw : 0 ≤ Pw)
    (horder : (p.d : ℝ) + 3 + (p.d : ℝ) / 2 < (r : ℝ))
    (hc₀ : 0 < c₀) (hpinf : 1 < pinf) (τ : ℝ) (hτ : 1 ≤ τ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ρ : Euc p.d → ℝ,
      HRS.Whole.IsRound2Density p.d p.s M L ρ →
      HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ Pactual : Measure (EucConfig p.d N),
      HRS.Whole.HasR2ActualDensity p.s p.β pinf K
        (HRS.Whole.withDensityReal ρ) Pactual →
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (HRS.Whole.r2EmpDistr (HRS.Whole.withDensityReal ρ) X) ^ τ
        ∂Pactual) ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hbounds⟩ := fp81s21_r2wfm_singleLaw_pair_tau
    p hPw horder hc₀ hpinf τ hτ
  exact ⟨D, hD, fun ρ hρ hG N hN Pactual hactual =>
    (hbounds ρ hρ hG N hN Pactual hactual).1⟩

/-- Higher-exponent exactly centered quadratic single-law bound. It exposes
the centered commutator clause of `R2WeightedFieldBound` with exponent `τ`. -/
theorem fp81s21_quad_r2wfm_singleLaw_tau
    (p : Parameters) {r : ℕ} {Pw M L C₀ c₀ pinf K : ℝ}
    (hPw : 0 ≤ Pw)
    (horder : (p.d : ℝ) + 3 + (p.d : ℝ) / 2 < (r : ℝ))
    (hc₀ : 0 < c₀) (hpinf : 1 < pinf) (τ : ℝ) (hτ : 1 ≤ τ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ρ : Euc p.d → ℝ,
      HRS.Whole.IsRound2Density p.d p.s M L ρ →
      HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ Pactual : Measure (EucConfig p.d N),
      HRS.Whole.HasR2ActualDensity p.s p.β pinf K
        (HRS.Whole.withDensityReal ρ) Pactual →
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (fun f => HRS.Whole.r2CommDistr p.d p.s
          (HRS.Whole.withDensityReal ρ) X f -
          ∫ Y, HRS.Whole.r2CommDistr p.d p.s
            (HRS.Whole.withDensityReal ρ) Y f ∂Pactual) ^ τ
        ∂Pactual) ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hbounds⟩ := fp81s21_r2wfm_singleLaw_pair_tau
    p hPw horder hc₀ hpinf τ hτ
  exact ⟨D, hD, fun ρ hρ hG N hN Pactual hactual =>
    (hbounds ρ hρ hG N hN Pactual hactual).2⟩

#print axioms HRS.Fp81.S21.fp81s21_emp_r2wfm_singleLaw_tau
#print axioms HRS.Fp81.S21.fp81s21_quad_r2wfm_singleLaw_tau

end HRS.Fp81.S21

end
