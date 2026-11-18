import HRS.Main.ThermLinPlan2
import HRS.Main.ThermLinAux1

/-!
# THERMLIN2 packet Ly, part 1: `tl2_xi_law` (D1)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- D1: the initial law `N(0, C_β)` of the stationary field, with finite second moment. -/
theorem tl2_xi_law_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ γ : Measure (NegSobolev d m), IsProbabilityMeasure γ ∧
      IsCenteredGaussianWithCov m γ (susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β) ∧
      (∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂γ) < ⊤ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hcont : Continuous ρβ := HRS.StaticLimitAux.continuous_of_smooth hsm
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hΛ : ∀ x, ρβ x ≤ ρβ x0 := fun x => hx0 (Set.mem_univ x)
  have h0' : ∀ n : Lattice d, 0 ≤ rieszCoeff d S.s n := fun n => by
    by_cases hn : n = 0
    · simp [rieszCoeff, hn]
    · exact (rieszCoeff_pos S.hd S.hs0 S.hsd n hn).le
  obtain ⟨g', hgg, hS⟩ := HRS.ResponseAux.setup_of_kernel (integral_periodicRiesz S.hd S.hs0 S.hsd).1
    (rieszCoeff d S.s) h0'
    (HRS.ResponseAux.hcoef_of_funFourierCoeff (periodicRiesz_fourierCoeff S.hd S.hs0 S.hsd))
    h.1 hΛ
  obtain ⟨γ, hγp, hγc⟩ := HRS.ThermLin.thermlin_exists_gauss_kernel hS hgg S.hβ.le m
    (by linarith)
  refine ⟨γ, hγp, hγc, ?_⟩
  haveI := hγc.1.1
  have hmem : MemLp id 2 γ := ProbabilityTheory.IsGaussian.memLp_two_id
  have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    hmem.eLpNorm_lt_top
  simpa using h2

/-- Ties the proof to the frozen statement. -/
example := (@tl2_xi_law_proof : type_of% @tl2_xi_law)

end HRS.ThermLin.Plan2
