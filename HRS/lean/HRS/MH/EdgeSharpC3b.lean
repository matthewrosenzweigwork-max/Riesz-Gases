import HRS.MH.EdgeSharpB
import HRS.MH.EdgeSharpC3a

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS HRS.Main

variable {d : ℕ}

theorem crossCov_eq_nu_integral {m q T' : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussian ν)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hmeas : Measurable Z₀) (hlaw : law P' Z₀ = ν)
    (hsol : IsLinearFluctuationSolution P' D ρ m q T' Z₀ Z) {r : ℝ} (hr : r ∈ Set.Icc 0 T')
    {ψ φ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) (hφ : Torus.IsSmooth φ)
    (hf : Torus.IsSmooth (propagator D ρ 0 r ψ)) :
    ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z 0 ω) φ ∂P' =
      ∫ F, NegSobolev.eval F (propagator D ρ 0 r ψ) * NegSobolev.eval F φ ∂ν := by
  obtain ⟨hind, hXL2, hX0⟩ := gaussianPart_one D ρ P' Z₀ Z hsol hr hψ
  obtain ⟨Lf, hLf⟩ := exists_evalCLM (d := d) m _ hf
  obtain ⟨Lφ, hLφ⟩ := exists_evalCLM (d := d) m φ hφ
  set X : Ω' → ℝ := fun ω => NegSobolev.eval (Z r ω) ψ - NegSobolev.eval (Z₀ ω) (propagator D ρ 0 r ψ)
    with hXdef
  have hA : MemLp (fun ω => Lf (Z₀ ω)) 2 P' := memLp_two_clm ν hν Lf P' Z₀ hmeas hlaw
  have hB : MemLp (fun ω => Lφ (Z₀ ω)) 2 P' := memLp_two_clm ν hν Lφ P' Z₀ hmeas hlaw
  have hXB : IndepFun X (fun ω => Lφ (Z₀ ω)) P' :=
    hind.comp measurable_id Lφ.continuous.measurable
  have h1 : ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z 0 ω) φ ∂P' =
      ∫ ω, (X ω + Lf (Z₀ ω)) * Lφ (Z₀ ω) ∂P' := by
    refine integral_congr_ae ?_
    filter_upwards [hsol.init] with ω h0
    rw [h0, hLf, hLφ, hXdef]
    ring
  have hint1 : Integrable (fun ω => X ω * Lφ (Z₀ ω)) P' := hXL2.integrable_mul hB
  have hint2 : Integrable (fun ω => Lf (Z₀ ω) * Lφ (Z₀ ω)) P' := hA.integrable_mul hB
  have h2 : ∫ ω, (X ω + Lf (Z₀ ω)) * Lφ (Z₀ ω) ∂P' =
      ∫ ω, X ω * Lφ (Z₀ ω) ∂P' + ∫ ω, Lf (Z₀ ω) * Lφ (Z₀ ω) ∂P' := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [add_mul]
  have h3 : ∫ ω, X ω * Lφ (Z₀ ω) ∂P' = 0 := by
    have := hXB.integral_mul_eq_mul_integral hXL2.aestronglyMeasurable hB.aestronglyMeasurable
    have h0 : ∫ ω, X ω ∂P' = 0 := hX0
    calc ∫ ω, X ω * Lφ (Z₀ ω) ∂P' = (∫ ω, X ω ∂P') * ∫ ω, Lφ (Z₀ ω) ∂P' := this
      _ = 0 := by rw [h0, zero_mul]
  have h4 : ∫ ω, Lf (Z₀ ω) * Lφ (Z₀ ω) ∂P' = ∫ F, Lf F * Lφ F ∂ν := by
    rw [← hlaw]
    exact (integral_map hmeas.aemeasurable
      ((Lf.continuous.mul Lφ.continuous).aestronglyMeasurable)).symm
  have h5 : ∫ F, Lf F * Lφ F ∂ν =
      ∫ F, NegSobolev.eval F (propagator D ρ 0 r ψ) * NegSobolev.eval F φ ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun F => ?_)
    simp only [hLf, hLφ]
  rw [h1, h2, h3, zero_add, h4, h5]

end HRS.MH.EdgeSharp
