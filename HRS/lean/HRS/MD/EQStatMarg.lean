import HRS.Main.EqMargU4

/-!
# EQ-STATIC-U, part 4b: the Gibbs marginal in `L²`, uniform in `β ∈ [β₋,β₊]` and `ρ ≤ Λ₀`

Verbatim copy of `HRS.EqMarg.eqmarg_marginal_unif` (`HRS/Main/EqMargFinal.lean`), whose module also imports the frozen
Theorem 2.9 statement file; copied here so that the packet files depend on `EqMargU4` only.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace MD

namespace EQStat

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.EqMarg

variable {d : ℕ} {s : ℝ}

/-- Uniform version of `firstMarginal_density_L2` (Proposition 4.2, full-law part). -/
theorem eqstat_marginal_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ0) → ∀ N : ℕ, 2 ≤ N →
      firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
            (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1) 2
            (withDensityReal ρ) ≤ ENNReal.ofReal (C * deltaN d s N) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨C, hC0, hCU⟩ := eqmarg_L2_all hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Mp, hMp1, hMpU⟩ := eqmarg_pDens_bounds hd hs0 hsd βm βp hβm hββ Λ0
  refine ⟨C, hC0, fun β hβ1 hβ2 ρ hρ hΛ N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hC := hCU β hβ1 hβ2 ρ hρ hΛ
  have hMp := hMpU β hβ1 hβ2 ρ hρ hΛ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn (lam := β / ((n + 1 : ℕ) : ℝ)) rfl
  have hae := rnDeriv_pi_eq hd hs0 hsd hρ hlam hln
  rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (n + 1) (Nat.succ_pos n)]
  refine ⟨?_, ?_⟩
  · rw [firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln]
    exact withDensity_absolutelyContinuous _ _
  · have hN' : 2 ≤ n + 1 := hN
    have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
    have hp0 := pDens_pos hd hs0 hsd hρ hlam hln
    have hz : ∀ y, |pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1| ≤ Mp := by
      intro y
      have h1 := hp0 y
      have h2 := (hMp (n + 1) hN' y).2
      simp only [Nat.add_sub_cancel] at h2
      rw [abs_le]; constructor <;> linarith
    have hmem : MemLp (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1)
        2 (withDensityReal ρ) :=
      MemLp.of_bound (hpm.sub measurable_const).aestronglyMeasurable Mp (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hz y)
    rw [eLpNorm_congr_ae (g := fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n
      (β / ((n + 1 : ℕ) : ℝ)) β y - 1) (hae.mono fun y hy => by simp only [hy])]
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hA := hC n hn (β / ((n + 1 : ℕ) : ℝ)) rfl
    have hδ0 : 0 ≤ deltaN d s (n + 1) := by
      have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
      exact (inv_nonneg.2 hN0.le).trans this
    have e : ∫ y, ‖pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1‖ ^
        (2 : ENNReal).toReal ∂(withDensityReal ρ) =
        ∫ y, (pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1) ^ 2
          ∂(withDensityReal ρ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [e]
    have h3 : (2 : ENNReal).toReal⁻¹ = 1 / 2 := by simp
    rw [h3, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.2 ⟨mul_nonneg hC0 hδ0, hA⟩


end EQStat

end MD

end HRS

end
