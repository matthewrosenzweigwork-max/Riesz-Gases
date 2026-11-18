import HRS.MC.QRAsm
import HRS.MC.QRPHd

/-! # Lemma 7.12 `HRS.Sec7.quadratic_relaxation`: final assembly from the proved pieces (sorry-free; `qrs_assembly_proof` applied to the `_proof` theorems). -/

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.MC.QRSpec.Asm
open HRS.Sec7
variable {d : ℕ}

theorem quadratic_relaxation_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∀ p : ℝ, 1 ≤ p → ∃ C c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r),
        IsCenteredGaussianWithCov r (P.map Y₀)
          (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) →
        IsCenteredGaussianWithCov r (P.map Ys₀)
          (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) →
        IndepFun Y₀ Ys₀ P →
        (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ r R.D.invβ T Y₀ η) →
        (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) r R.D.invβ T Ys₀ ηs) →
        IsSameNoise R.D R.ρ (fun _ => R.ρβ) r P Y₀ Ys₀ η ηs →
        ∀ B Bs : ℝ → Ω → NegSobolev d r,
          (∀ t, Measurable (B t)) → (∀ t, Measurable (Bs t)) →
          (∀ t : ℝ, 0 ≤ t → IsWickQuadraticField R.D.s P (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) →
          (∀ t : ℝ, 0 ≤ t → IsWickQuadraticField R.D.s P (fun ω => ηs t ω) (withDensityReal R.ρβ) (Bs t)) →
          ∀ t : ℝ, 0 ≤ t →
            eLpNorm (fun ω => B t ω - Bs t ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C * Real.exp (-c * t)) := 
  qrs_assembly_proof R r hr (HRS.MC.L2C6a.l2c6a_proof R r hr) (HRS.MC.L2C6b.l2c6b_proof R r hr)
    (HRS.MC.L2C6c.l2c6c_proof R r hr) (@HRS.MC.L2C7.l2c7_proof) (@HRS.MC.WCI.wci_proof)
    (HRS.MC.QRSpec.Marg.qrs_gauss_marginals_proof R r hr)
    (HRS.MC.QRSpec.Hd.qrs_hd_commutator_tail_proof R.D.s R.D.hs0 R.hs R.hd)
    HRS.MC.QRSpec.Chaos.qrs_chaos_lp_lim_proof HRS.MC.QRSpec.GaussEr.qrs_gauss_er_proof

example := (@quadratic_relaxation_proof : type_of% @HRS.Sec7.quadratic_relaxation)

end HRS.MC.QRSpec.Asm
end
