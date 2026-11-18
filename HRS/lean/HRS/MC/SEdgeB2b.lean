import HRS.MC.SEdgeB2a
import HRS.Dynamics.InitialData
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.Parametrix.PXFIDAuxK

/-!
# Packet B2b: `h_v ∈ L²(μ ⊗ μ)` (relocated proof of `sed_B2b_hs`)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B2b

open HRS.Sec7

variable {d : ℕ} {s : ℝ}

theorem sed_B2b_hs_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j)) :
    Integrable (fun z : Torus d × Torus d => Q66.q66_hv d s v z.1 z.2 ^ 2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  haveI := isProb_withDensityReal hρ.density
  obtain ⟨B, c, -, hB⟩ := HRS.MC.SEdge.B2a.b2a_main hd hs0 hs hv
  obtain ⟨Λ, -, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  have hg2 := HRS.periodicRiesz_sq_integrable hd hs0 hs ρ hρ.density Λ hΛ
  -- continuity facts: each coordinate `v j` is continuous
  have hvm : ∀ j, Measurable (v j) := fun j =>
    (PoleCavityAux.continuous_of_lift'
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (v j)) from hv j).continuous).measurable
  have hhm : Measurable (fun z : Torus d × Torus d => Q66.q66_hv d s v z.1 z.2) := by
    unfold Q66.q66_hv
    refine Finset.measurable_sum _ fun k _ => ?_
    refine Measurable.mul ((hvm k).comp measurable_fst |>.sub ((hvm k).comp measurable_snd)) ?_
    have := (HRS.KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)
    exact (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable.comp this
  have hdom : Integrable (fun z : Torus d × Torus d =>
      2 * B ^ 2 * (periodicRiesz d s (z.1 - z.2) ^ 2) + 2 * B ^ 2 * c ^ 2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    (hg2.const_mul _).add (integrable_const _)
  refine hdom.mono' (hhm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [HRS.Parx.PXFID.ae_ne_prod (by omega) hρ.density] with z hz
  have h1 := hB z.1 z.2 hz
  rw [Real.norm_eq_abs, abs_pow]
  calc |Q66.q66_hv d s v z.1 z.2| ^ 2 ≤ (B * (periodicRiesz d s (z.1 - z.2) + c)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = B ^ 2 * (periodicRiesz d s (z.1 - z.2) + c) ^ 2 := by ring
    _ ≤ 2 * B ^ 2 * (periodicRiesz d s (z.1 - z.2) ^ 2) + 2 * B ^ 2 * c ^ 2 := by
        nlinarith [sq_nonneg B, mul_nonneg (sq_nonneg B) (sq_nonneg (periodicRiesz d s (z.1 - z.2) - c))]


end HRS.MC.SEdge.B2b
