import HRS.MS.Fp81S21InitialStein2
import HRS.MS.S21F_S00

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS.Whole
open HRS (Euc MemCb)
open HRS.MS.R26T3

/-- The first exact Stein identity at the actual initial preparation law.

`S47Feat` supplies the corrector and its generator identity. The observable itself is required in
`MemCb 1`, since `S47Feat` does not assert that the observable is measurable or bounded. -/
theorem initial_stein_pairEnergy
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ) {N : ℕ} (hN : 2 ≤ N)
    {φ χ : Euc p.d → ℝ} {Bχ : ℝ}
    (hχ : S47.S47Feat p.d p.s (R.ρ 0) p.γ φ χ Bχ)
    (hφ : MemCb 1 φ)
    {F : EucConfig p.d N → ℝ} (hF : ContDiff ℝ 1 F) {BF DF : ℝ}
    (hBF : ∀ X, |F X| ≤ BF) (hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ DF) :
    ∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) φ -
        HRS.Whole.pair (r26t3_marg R N) φ) * F X
        ∂(r26t3_Q R N) =
      (p.γ * N)⁻¹ *
        (∫ X, fderiv ℝ F X (fun i => gradient χ (X i)) ∂(r26t3_Q R N)) -
      ∫ X, (pairEnergy (commutatorKernel p.d p.s (gradient χ)) X (r26t3_mu R 0) -
        ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient χ)) Y (r26t3_mu R 0)
          ∂(r26t3_Q R N)) * F X ∂(r26t3_Q R N) := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    have hd2 : (p.d : ℝ) / 2 ≤ (p.d : ℝ) := by nlinarith
    exact lt_of_lt_of_le p.hs hd2
  have hq : 0 < p.a * p.β := mul_pos p.ha p.hβ
  have hφm : Measurable φ := hφ.1.continuous.measurable
  obtain ⟨Bφ, hBφsup⟩ := hφ.2 0 (by omega)
  have hBφ : ∀ x, |φ x| ≤ Bφ := fun x => by
    have hx := hBφsup (Set.mem_range_self x)
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hx
  obtain ⟨c0, hstar⟩ := S47.s47_star p.hd p.hs0 hsd hγ E.reference
    hχ.smooth hχ.B1 hχ.B2 hχ.corr
  have hstein := S47.s47_stein_id p.hd p.hs0 hsd hq hγ hN E.reference
    (E.static N hN) hχ.smooth hχ.B1 hχ.B2 hφm (Bφ := Bφ) hBφ hstar
    hF (BF := BF) hBF (DF := DF) hDF
  have hν : S47.s47_nu p.d p.s (R.ρ 0) p.γ N = r26t3_marg R N := by
    change HRS.Whole.firstMarginal (S47.s47_P p.d p.s (R.ρ 0) p.γ N) =
      HRS.Whole.firstMarginal (r26t3_Q R N)
    rw [E.law_eq N]
  have hsteinRp :
      ∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) φ -
          HRS.Whole.pair (S47.s47_nu p.d p.s (R.ρ 0) p.γ N) φ) * F X
          ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N) =
      ∫ X, S45.s45_Rp (r26t3_mu R 0)
            (S47.s47_nu p.d p.s (R.ρ 0) p.γ N)
            (S47.s47_P p.d p.s (R.ρ 0) p.γ N)
            (commutatorKernel p.d p.s (gradient χ)) X * F X
            ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N) +
          (p.γ * N)⁻¹ *
            (∫ X, fderiv ℝ F X (fun i => gradient χ (X i))
              ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N)) := by
    simpa only [S45.s45_Rp, r26t3_mu] using hstein
  have henergy : ∀ X : EucConfig p.d N,
      S45.s45_Rp (r26t3_mu R 0)
          (S47.s47_nu p.d p.s (R.ρ 0) p.γ N)
          (S47.s47_P p.d p.s (R.ρ 0) p.γ N)
          (commutatorKernel p.d p.s (gradient χ)) X =
        -(pairEnergy (commutatorKernel p.d p.s (gradient χ)) X (r26t3_mu R 0) -
          ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient χ)) Y (r26t3_mu R 0)
            ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N)) := by
    intro X
    exact fp81s21_s47_Rp_eq p.hd p.hs0 hsd E.reference hN (E.static N hN)
      hχ.smooth hχ.B2 X
  have hsteinEnergy :
      ∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) φ -
          HRS.Whole.pair (S47.s47_nu p.d p.s (R.ρ 0) p.γ N) φ) * F X
          ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N) =
        (p.γ * N)⁻¹ *
          (∫ X, fderiv ℝ F X (fun i => gradient χ (X i))
            ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N)) -
        ∫ X, (pairEnergy (commutatorKernel p.d p.s (gradient χ)) X (r26t3_mu R 0) -
          ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient χ)) Y (r26t3_mu R 0)
            ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N)) * F X
            ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N) := by
    calc
      _ = ∫ X, S45.s45_Rp (r26t3_mu R 0)
            (S47.s47_nu p.d p.s (R.ρ 0) p.γ N)
            (S47.s47_P p.d p.s (R.ρ 0) p.γ N)
            (commutatorKernel p.d p.s (gradient χ)) X * F X
            ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N) +
          (p.γ * N)⁻¹ *
            (∫ X, fderiv ℝ F X (fun i => gradient χ (X i))
              ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N)) := hsteinRp
      _ = (p.γ * N)⁻¹ *
            (∫ X, fderiv ℝ F X (fun i => gradient χ (X i))
              ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N)) -
          ∫ X, (pairEnergy (commutatorKernel p.d p.s (gradient χ)) X (r26t3_mu R 0) -
            ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient χ)) Y (r26t3_mu R 0)
              ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N)) * F X
              ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N) := by
        simp_rw [henergy, neg_mul, integral_neg]
        ring
  rw [← hν, ← E.law_eq N]
  simpa only [r26t3_mu] using hsteinEnergy

#print axioms initial_stein_pairEnergy

end HRS.Fp81.S21

end
