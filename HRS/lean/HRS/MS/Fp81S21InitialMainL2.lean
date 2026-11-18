import HRS.MS.Fp81S21InitialThird5
import HRS.MS.Fp81S21InitialULim3
import HRS.MS.Fp81S21InitialCoord2

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-!
## SOL31 packet 25b-3: the actual-law ℓ² Edgeworth expansion

Thermal-to-actual-law dictionary for `s99_main_l2`:
* `S46.s46_P` and `S46.s46_nu` become `r26t3_Q R N` and
  `r26t3_marg R N`; these are probability measures for `N ≥ 2` by
  `InitialSteinEnv.static` and `S99.s99_nu_prob`.
* The Gaussian covariance is susceptibility at `r26t3_mu R 0`; unfolding
  `fp81s21_initialCf` gives the covariance interface required by
  `fp81s21_initial_D1`.
* Thermal `Aterm`, `Bterm`, `Alim`, `Qk`, and `kap3` are replaced by
  their `fp81s21_initial_*` counterparts.

The reusable pieces already ported are the actual-law `D1` identity,
`initial_ULimA/B`, `initial_limit_ident`, and the actual response vector and
third-series identity. This file packages the common Gaussian Stein solution;
the next file applies `D1`, identifies its scaled terms, and assembles the
uniform expansion.
-/

/-- Package the Gaussian Stein solution for a C⁵ test whose derivatives through order five
are bounded by one. The Stein class records the derivative bounds of the solution; the
equation is in the integral form consumed by the actual-law `D1` identity. -/
theorem fp81s21_initial_stein_package
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {φ : ℕ → Euc p.d → ℝ}
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (φ i) (φ j)))
    {Φ : SeqL2 → ℝ} (hΦ : ContDiff ℝ 5 Φ)
    (hb : ∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1) :
    ∃ f : SeqL2 → ℝ, SteinCl f ∧
      (∀ x, ∫ z, iteratedFDeriv ℝ 2 f x ![z, z] ∂G - fderiv ℝ f x x =
        Φ x - ∫ z, Φ z ∂G) ∧
      (∀ v : Fin 3 → SeqL2,
        ∫ z, iteratedFDeriv ℝ 3 Φ z v ∂G =
          -3 * ∫ z, iteratedFDeriv ℝ 3 f z v ∂G) := by
  have hGauss : HRS.IsCenteredGaussian (HRS.law G (id : SeqL2 → SeqL2)) := by
    have hid : HRS.law G (id : SeqL2 → SeqL2) = G := by
      unfold HRS.law
      exact Measure.map_id
    rw [hid]
    exact hG.1
  let hMem : HRS.MemCb 5 Φ :=
    ⟨hΦ, fun j hj => ⟨1, by
      rintro _ ⟨x, rfl⟩
      exact hb j hj x⟩⟩
  obtain ⟨-, hf5, hfb⟩ :=
    HRS.stein_bounds G (id : SeqL2 → SeqL2) aemeasurable_id hGauss Φ hMem
  let f : SeqL2 → ℝ := HRS.steinSolution G (id : SeqL2 → SeqL2) Φ
  have hf : SteinCl f := by
    refine ⟨hf5, fun i hi1 hi5 z => ?_⟩
    change ‖iteratedFDeriv ℝ i
        (HRS.steinSolution G (id : SeqL2 → SeqL2) Φ) z‖ ≤ 1
    refine (hfb i hi1 hi5 z).trans ?_
    have hsup : (⨆ y, ‖iteratedFDeriv ℝ i Φ y‖) ≤ 1 :=
      ciSup_le fun y => hb i hi5 y
    have hi : ((i : ℝ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by exact_mod_cast hi1)
    have h0 : 0 ≤ ⨆ y, ‖iteratedFDeriv ℝ i Φ y‖ :=
      Real.iSup_nonneg fun _ => norm_nonneg _
    calc
      ((i : ℝ))⁻¹ * ⨆ y, ‖iteratedFDeriv ℝ i Φ y‖ ≤ 1 * 1 :=
        mul_le_mul hi hsup h0 zero_le_one
      _ = 1 := one_mul 1
  refine ⟨f, hf, ?_, ?_⟩
  · intro x
    simpa only [f, HRS.covarianceContraction, id] using
      (HRS.stein_equation G (id : SeqL2 → SeqL2) aemeasurable_id
        hGauss Φ hMem x)
  · intro v
    have hthird := HRS.stein_third_derivative G
      (id : SeqL2 → SeqL2) aemeasurable_id hGauss Φ hMem v
    change (∫ z, iteratedFDeriv ℝ 3
        (HRS.steinSolution G (id : SeqL2 → SeqL2) Φ) z v ∂G) =
      -(1 / 3) * ∫ z, iteratedFDeriv ℝ 3 Φ z v ∂G at hthird
    rw [show (fun z => iteratedFDeriv ℝ 3
        (HRS.steinSolution G (id : SeqL2 → SeqL2) Φ) z v) =
        (fun z => iteratedFDeriv ℝ 3 f z v) from rfl] at hthird
    linarith

#print axioms fp81s21_initial_stein_package

end HRS.Fp81.S21

end
