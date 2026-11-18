import HRS.MS.Fp81S21WeightedMoments9
import HRS.MS.Fp81S21WeightedMomentsC

/-!
# Audit and generalized R2Wfm single-law adapters for the strong chart

Audit against the compiled W1N declarations:
* `fp81s21_emp_r2wfm_singleLaw` (WeightedMoments9) and
  `fp81s21_quad_r2wfm_singleLaw` (WeightedMomentsC) hard-wire
  `r = 2*d+8`, `Pw = d+2`, and use `k=d+3`, `m=2*d+8`, moment exponent
  `2`. Their conclusions are at those same fixed `r,Pw`.
* `fp81s21_quad_config_rep` (WeightedMomentsB),
  `fp81s21_particle_eta_momentRep` (WeightedMoments10),
  `fp81s21_particle_quad_momentRep` (WeightedMomentsC2), and
  `fp81s21_particle_momentReps` (WeightedMomentsC3) also fix
  `(r,Pw)=(2*d+8,d+2)`. The two particle first-moment corollaries inherit
  those indices.
* Already generic in `(r,Pw)` are `fp81s21_emp_config_rep`, with
  `d/2 < r`, `0 <= Pw`, and `d < 2*Pw`; `fp81s21_measurable_riesz`,
  with `d < 2*Pw`; and `fp81s21_rep_secondMoment`, which takes an arbitrary
  chart and its comparison and moment bounds.

The R2Wfm proof producer requires `d>=2`, `0<=s<d/2`, `b>0`, density
exponent `p_int>1`, `Pw>=0`, `d/2+2<k`, `k+d/2<m`, and moment exponent
`tau>=1`. The adapters choose `b=p.beta`, `p_int=min pinf 2`, `k=d+3`,
`m=r`, and `tau=2`. Thus their explicit order condition is
`d+3+d/2<r`. At the strong chart, `r=2*d+6`, and
`r-(d+3+d/2)=d/2+3>0` for `d>=2`; also
`(d+3)-(d/2+2)=d/2+1>0` and `2>=1`.

`s102_Z_fluct` needs `d>=1`, `Pw>=0`, `d/2<r`, and an integrable
reference weight `jbracket^Pw`. `s102_Z_quad` needs the stronger
`d/2+2<r`, the same nonnegative weight, its kernel bound, row and double
integrability, and integrability of `s102_Env (s102_gk s Pw)` under the
configuration law. `s102_gk_int` and `s102_Env_bound` require `Pw>=0`;
the latter also requires the stated round-two density, Gaussian upper bound,
`beta>0`, `p_int>1`, and actual-density hypothesis. The strong weight
`Pw=d+4` is nonnegative. The Gaussian envelope still integrates every
polynomial weight, and the generalized configuration producer below invokes
these bounds at `d+4` directly.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

private theorem fp81s21_r2wfm_singleLaw_pair_gen
    (p : Parameters) {r : ℕ} {Pw M L C₀ c₀ pinf K : ℝ}
    (hPw : 0 ≤ Pw)
    (horder : (p.d : ℝ) + 3 + (p.d : ℝ) / 2 < (r : ℝ))
    (hc₀ : 0 < c₀) (hpinf : 1 < pinf) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ρ : Euc p.d → ℝ,
      HRS.Whole.IsRound2Density p.d p.s M L ρ →
      HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ Pactual : Measure (EucConfig p.d N),
      HRS.Whole.HasR2ActualDensity p.s p.β pinf K
        (HRS.Whole.withDensityReal ρ) Pactual →
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (HRS.Whole.r2EmpDistr (HRS.Whole.withDensityReal ρ) X) ^ (2 : ℝ)
        ∂Pactual) ≤ ENNReal.ofReal D ∧
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (fun f => HRS.Whole.r2CommDistr p.d p.s
          (HRS.Whole.withDensityReal ρ) X f -
          ∫ Y, HRS.Whole.r2CommDistr p.d p.s
            (HRS.Whole.withDensityReal ρ) Y f ∂Pactual) ^ (2 : ℝ)
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
      nlinarith [hdR]) horderCast (2 : ℝ) (by norm_num)
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
        (HRS.Whole.r2EmpDistr μ X) ^ (2 : ℝ) ∂Pactual) ≤
          ENNReal.ofReal Cwfm := by
    calc
      _ ≤ ∫⁻ X, (HRS.Whole.r2NegSobNorm r Pw
          (HRS.Whole.r2EmpDistr μ X) ^ (2 : ℝ) +
        HRS.Whole.r2NegSobNorm r Pw
          (HRS.Whole.r2CommDistr p.d p.s μ X) ^ (2 : ℝ)) ∂Pactual := by
            apply lintegral_mono
            intro X
            exact le_add_of_nonneg_right (by positivity)
      _ ≤ ENNReal.ofReal Cwfm := by simpa [P, μ] using hAtN.1
  have hcommActual :
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (fun f => HRS.Whole.r2CommDistr p.d p.s μ X f -
          ∫ Y, HRS.Whole.r2CommDistr p.d p.s μ Y f ∂Pactual) ^ (2 : ℝ)
        ∂Pactual) ≤ ENNReal.ofReal Cwfm := by
    calc
      _ ≤ ∫⁻ X,
          (HRS.Whole.r2NegSobNorm r Pw
              (fun f => HRS.Whole.r2EmpDistr μ X f -
                ∫ Y, HRS.Whole.r2EmpDistr μ Y f ∂Pactual) ^ (2 : ℝ) +
            HRS.Whole.r2NegSobNorm r Pw
              (fun f => HRS.Whole.r2CommDistr p.d p.s μ X f -
                ∫ Y, HRS.Whole.r2CommDistr p.d p.s μ Y f ∂Pactual) ^ (2 : ℝ))
          ∂Pactual := by
            apply lintegral_mono
            intro X
            exact le_add_of_nonneg_left (by positivity)
      _ ≤ ENNReal.ofReal Cwfm := by simpa [P, μ] using hAtN.2
  refine ⟨?_, ?_⟩
  · calc
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
          (HRS.Whole.r2EmpDistr (HRS.Whole.withDensityReal ρ) X) ^ (2 : ℝ)
          ∂Pactual) ≤ ENNReal.ofReal Cwfm := by simpa [μ] using hEmpActual
      _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · calc
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
          (fun f => HRS.Whole.r2CommDistr p.d p.s
            (HRS.Whole.withDensityReal ρ) X f -
            ∫ Y, HRS.Whole.r2CommDistr p.d p.s
              (HRS.Whole.withDensityReal ρ) Y f ∂Pactual) ^ (2 : ℝ)
          ∂Pactual) ≤ ENNReal.ofReal Cwfm := by simpa [μ] using hcommActual
      _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- Generalized empirical single-law adapter for any R2Wfm-admissible
`(r,Pw)`: `Pw>=0` and `d+3+d/2<r`. -/
theorem fp81s21_emp_r2wfm_singleLaw_gen
    (p : Parameters) {r : ℕ} {Pw M L C₀ c₀ pinf K : ℝ}
    (hPw : 0 ≤ Pw)
    (horder : (p.d : ℝ) + 3 + (p.d : ℝ) / 2 < (r : ℝ))
    (hc₀ : 0 < c₀) (hpinf : 1 < pinf) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ρ : Euc p.d → ℝ,
      HRS.Whole.IsRound2Density p.d p.s M L ρ →
      HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ Pactual : Measure (EucConfig p.d N),
      HRS.Whole.HasR2ActualDensity p.s p.β pinf K
        (HRS.Whole.withDensityReal ρ) Pactual →
      (∫⁻ X, HRS.Whole.r2NegSobNorm r Pw
        (HRS.Whole.r2EmpDistr (HRS.Whole.withDensityReal ρ) X) ^ (2 : ℝ)
        ∂Pactual) ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hbounds⟩ := fp81s21_r2wfm_singleLaw_pair_gen
    p hPw horder hc₀ hpinf
  exact ⟨D, hD, fun ρ hρ hG N hN Pactual hactual =>
    (hbounds ρ hρ hG N hN Pactual hactual).1⟩

/-- Generalized exactly centered quadratic single-law adapter for any
R2Wfm-admissible `(r,Pw)`. -/
theorem fp81s21_quad_r2wfm_singleLaw_gen
    (p : Parameters) {r : ℕ} {Pw M L C₀ c₀ pinf K : ℝ}
    (hPw : 0 ≤ Pw)
    (horder : (p.d : ℝ) + 3 + (p.d : ℝ) / 2 < (r : ℝ))
    (hc₀ : 0 < c₀) (hpinf : 1 < pinf) :
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
            (HRS.Whole.withDensityReal ρ) Y f ∂Pactual) ^ (2 : ℝ)
        ∂Pactual) ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hbounds⟩ := fp81s21_r2wfm_singleLaw_pair_gen
    p hPw horder hc₀ hpinf
  exact ⟨D, hD, fun ρ hρ hG N hN Pactual hactual =>
    (hbounds ρ hρ hG N hN Pactual hactual).2⟩

#print axioms HRS.Fp81.S21.fp81s21_emp_r2wfm_singleLaw_gen
#print axioms HRS.Fp81.S21.fp81s21_quad_r2wfm_singleLaw_gen

end HRS.Fp81.S21

end
