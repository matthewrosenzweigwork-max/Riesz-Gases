import HRS.MH.WpSpec

/-!
# P3a: `HRS.MH.Wp.gff_initial_term_eq_lintegral`

Steps 1 and 2 of the proof of `HRS.GF.gff_initial_term_eq` (GFFinal2.lean:16), with the order `p > 0` kept general
and no finiteness hypothesis; step 3 (Bochner integral to `lintegral`) is not needed.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.WpP

open HRS HRS.GF HRS.Uniform HRS.Uniform.Kot

theorem gff_initial_term_eq_lintegral_proof :
    type_of% @HRS.MH.Wp.gff_initial_term_eq_lintegral := by
  intro d S N Ω Ω₁ mΩ mΩ₁ P P₁ π₁ hπ₁ X₀ X hX0 hX₀m η₀ η' hη₀ hη' hlaw hγm p hp
  set Gf : Config d N × NegSobolev d (S.γ : ℝ) → ℝ≥0∞ := fun z =>
    ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical z.1) (withDensityReal (S.ρ N 0)) - z.2‖ₑ ^ p with hGf
  have hGfm : Measurable Gf := by
    refine Measurable.pow_const ?_ p
    exact (((gf_measurable_ofMeasureDiff_proof (S.γ : ℝ) hγm (withDensityReal (S.ρ N 0))).comp measurable_fst).const_smul
      (S.κ N) |>.sub measurable_snd).enorm
  have hA := AN_nonneg S N
  -- step 1
  have h1 : ∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) (fun t ω => X t (π₁ ω)) (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ^ p ∂P₁ =
      ENNReal.ofReal (AN S N) ^ p * ∫⁻ ω, Gf (X₀ (π₁ ω), η' ω) ∂P₁ := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
    refine lintegral_congr_ae ?_
    filter_upwards [hπ₁.quasiMeasurePreserving.ae hX0] with ω hω
    simp only [flucProc, hGf, Real.toNNReal_zero, hω, sigN_eq S N]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← smul_smul, ← smul_sub, enorm_smul, Real.enorm_eq_ofReal hA]
  -- step 2
  have h2 : ∫⁻ ω, Gf (X₀ (π₁ ω), η' ω) ∂P₁ = ∫⁻ ω, Gf (X₀ ω, η₀ ω) ∂P := by
    have hm1 : AEMeasurable (fun ω' => (X₀ (π₁ ω'), η' ω')) P₁ :=
      (hX₀m.comp_quasiMeasurePreserving hπ₁.quasiMeasurePreserving).prodMk hη'.aemeasurable
    have hm2 : AEMeasurable (fun ω => (X₀ ω, η₀ ω)) P := hX₀m.prodMk hη₀.aemeasurable
    rw [← lintegral_map' hGfm.aemeasurable hm1, ← lintegral_map' hGfm.aemeasurable hm2, hlaw]
  rw [h1, h2, ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hp.le), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end HRS.MH.WpP
