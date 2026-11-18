import HRS.Main.Rel513RieszB

/-!
# HRS.Main.Rel513RieszC -- packet rel513, part 3: measurability of `stationaryRemainder`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ}

theorem rel513_firstMarginal_finite {N : ℕ} (P : Measure (Config d N)) [IsFiniteMeasure P] :
    IsFiniteMeasure (firstMarginal P) := by
  unfold firstMarginal
  split_ifs
  · infer_instance
  · infer_instance

theorem rel513_sfinite_mu (ρ : Torus d → ℝ) : SFinite (withDensityReal ρ) := by
  unfold withDensityReal; infer_instance

theorem stationaryRemainder_measurable_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρβ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (N : ℕ) (hN : 2 ≤ N) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    Measurable (stationaryRemainder d s β V ρβ N φ) := by
  have hN1 : 1 ≤ N := by omega
  have hZ := canonicalPartition_pos_riesz_proof hd hs0 hsd β hβ V hV hN1
  haveI := canonicalGibbs_isProbability_proof (periodicRiesz d s) V N β hZ
  haveI : IsFiniteMeasure (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) :=
    rel513_firstMarginal_finite _
  haveI : SFinite (withDensityReal ρβ) := rel513_sfinite_mu ρβ
  have hm : Measurable (Function.uncurry
      (commKernel (periodicRieszGrad d s) (Torus.grad φ))) :=
    rel513_measurable_comm hsd (rel513_grad_continuous hφ)
  have hHμ := Quad.measurable_Hc hm (withDensityReal ρβ)
  have hHm := Quad.measurable_Hc hm (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β))
  unfold stationaryRemainder
  simp only [rel513_integral_empirical]
  refine Measurable.sub (Measurable.const_mul (Measurable.sub ?_ measurable_const) _)
    (Measurable.const_mul (Measurable.sub ?_ measurable_const) _)
  · exact Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      (hHμ.sub hHm).comp (measurable_pi_apply i)) _
  · unfold modulatedEnergy
    refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
    · exact Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
        Finset.measurable_sum _ fun j _ => Quad.measurable_h_pair hm i j) _
    · exact Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
        hHm.comp (measurable_pi_apply i)) _

example := (@stationaryRemainder_measurable_proof : type_of% @stationaryRemainder_measurable)

end HRS.Main

end
