import HRS.MS.Fp81S21WeightedMoments8
import HRS.MS.R2SeAux1

/-!
# Single-law adapter for R2Wfm's indexed-family premise

The Wfm producer chooses its moment constant before one entire family of
configuration laws. For the selected count use the actual law; at every other
count use the matching canonical Gibbs law. The actual-law exponent is
reduced to `min pinf 2`, and both density constants are enlarged to
`max K 1`, so the family has one common pair of density parameters.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- At one fixed reference density, R2Wfm's first raw-field clause supplies a
uniform lower-integral bound for the empirical negative Sobolev norm under any
selected actual law with the stated density data. The auxiliary family uses
the canonical Gibbs law at all other particle counts.

The producer parameters are `b = p.β`, density exponent
`min pinf 2`, density constant `max K 1`, weight `Pw = d + 2`,
orders `k = d + 3`, `m = 2d + 8`, and moment exponent `r = 2`.
The output constant is chosen before the density and family. At the selected
count the family member is `Pactual`; at every other count it is the
canonical Gibbs law for the same reference density. -/
theorem fp81s21_emp_r2wfm_singleLaw
    (p : Parameters) {M L C₀ c₀ pinf K : ℝ}
    (hc₀ : 0 < c₀) (hpinf : 1 < pinf)
    : ∃ D : ℝ, 0 ≤ D ∧ ∀ ρ : Euc p.d → ℝ,
      HRS.Whole.IsRound2Density p.d p.s M L ρ →
      HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ Pactual : Measure (EucConfig p.d N),
      HRS.Whole.HasR2ActualDensity p.s p.β pinf K
        (HRS.Whole.withDensityReal ρ) Pactual →
      (∫⁻ X, HRS.Whole.r2NegSobNorm (2 * p.d + 8)
        ((p.d : ℝ) + 2)
        (HRS.Whole.r2EmpDistr (HRS.Whole.withDensityReal ρ) X) ^ (2 : ℝ)
        ∂Pactual) ≤ ENNReal.ofReal D := by
  let pcommon : ℝ := min pinf 2
  let Kcommon : ℝ := max K 1
  have hpcommon : 1 < pcommon := lt_min hpinf (by norm_num)
  have hpcommon_pinf : pcommon ≤ pinf := min_le_left _ _
  have hpcommon_two : pcommon ≤ 2 := min_le_right _ _
  have hKleft : K ≤ Kcommon := le_max_left _ _
  have hKright : 1 ≤ Kcommon := le_max_right _ _
  have hdR : (2 : ℝ) ≤ p.d := by exact_mod_cast p.hd

  have hdensityFamily := HRS.MS.R2Wfm.round2_weighted_field_moments_proof
    (d := p.d) p.hd p.s p.hs0 p.hs M L C₀ c₀ p.β pcommon Kcommon
    ((p.d : ℝ) + 2) p.hβ hpcommon (by positivity)
    (p.d + 3) (2 * p.d + 8) (by
      push_cast
      nlinarith [hdR]) (by
      push_cast
      nlinarith [hdR]) (2 : ℝ) (by norm_num)
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
  have hEmp := (hbound () N hN).1
  have hEmpActual :
      (∫⁻ X, HRS.Whole.r2NegSobNorm (2 * p.d + 8)
        ((p.d : ℝ) + 2)
        (HRS.Whole.r2EmpDistr μ X) ^ (2 : ℝ) ∂Pactual) ≤
          ENNReal.ofReal Cwfm := by
    calc
      _ ≤ ∫⁻ X, (HRS.Whole.r2NegSobNorm (2 * p.d + 8)
          ((p.d : ℝ) + 2)
          (HRS.Whole.r2EmpDistr μ X) ^ (2 : ℝ) +
        HRS.Whole.r2NegSobNorm (2 * p.d + 8)
          ((p.d : ℝ) + 2)
          (HRS.Whole.r2CommDistr p.d p.s μ X) ^ (2 : ℝ)) ∂Pactual := by
            apply lintegral_mono
            intro X
            exact le_add_of_nonneg_right (by positivity)
      _ ≤ ENNReal.ofReal Cwfm := by simpa [P, μ] using hEmp
  calc
    (∫⁻ X, HRS.Whole.r2NegSobNorm (2 * p.d + 8)
        ((p.d : ℝ) + 2)
        (HRS.Whole.r2EmpDistr
          (HRS.Whole.withDensityReal ρ) X) ^ (2 : ℝ) ∂Pactual)
        ≤ ENNReal.ofReal Cwfm := by simpa [μ] using hEmpActual
    _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (le_max_left _ _)

#print axioms HRS.Fp81.S21.fp81s21_emp_r2wfm_singleLaw

end HRS.Fp81.S21
