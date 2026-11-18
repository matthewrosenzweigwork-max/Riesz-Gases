import HRS.Main.Rel513RieszE

/-!
# HRS.Main.Rel513RieszF -- packet rel513, part 6: the first marginal against `μ`

For `Q_{N,β}(μ)` (`N ≥ 2`): the first marginal `m_N` is a probability measure with
`m_N ≤ M_p μ`, `m_N ≪ μ` and `‖dm_N/dμ - 1‖_{L²(μ)} ≤ C δ_N`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ} {s : ℝ}

open HRS.MarginalAux HRS.PoleCavityAux

theorem rel513_marginal_facts (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ Mp CF : ℝ, 1 ≤ Mp ∧ 0 ≤ CF ∧ ∀ N : ℕ, 2 ≤ N →
      IsProbabilityMeasure (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))) ∧
      firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        ENNReal.ofReal Mp • withDensityReal ρ ∧
      firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪ withDensityReal ρ ∧
      eLpNorm (fun y => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
            (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1) 2
            (withDensityReal ρ) ≤ ENNReal.ofReal (CF * deltaN d s N) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨CF, hCF⟩ := firstMarginal_density_L2 hd hs0 hsd β hβ ρ hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  refine ⟨Mp, max CF 0, hMp1, le_max_right _ _, fun N hN => ⟨?_, ?_, (hCF N hN).1, ?_⟩⟩
  · have hN0 : 0 < N := by omega
    have hlam : 0 ≤ β / (N : ℝ) := by positivity
    have : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) := by
      rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ N hN0]
      exact cavity_isProb hd hs0 hsd β hρ N (β / N) hlam
    exact Quad.isProb_firstMarginal (by omega) _
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hn : 0 < n := by omega
    obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn (lam := β / ((n + 1 : ℕ) : ℝ)) rfl
    rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (n + 1) (Nat.succ_pos n),
      firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln]
    refine Measure.le_iff'.2 fun A => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    have hm : Measurable fun x => ENNReal.ofReal
        (pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x) :=
      ENNReal.measurable_ofReal.comp (measurable_pDens hd hs0 hsd hρ hlam hln)
    rw [withDensity_apply' _ A]
    calc ∫⁻ a in A, ENNReal.ofReal
          (pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β a)
          ∂(withDensityReal ρ)
        ≤ ∫⁻ _ in A, ENNReal.ofReal Mp ∂(withDensityReal ρ) := by
          refine lintegral_mono fun a => ENNReal.ofReal_le_ofReal ?_
          have h2 := (hMp (n + 1) hN a).2
          simpa only [Nat.add_sub_cancel] using h2
      _ = ENNReal.ofReal Mp * withDensityReal ρ A := setLIntegral_const _ _
  · refine (hCF N hN).2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hδ0 : 0 ≤ deltaN d s N := (Quad.deltaN_pos hd hs0 hsd (by omega : 1 ≤ N)).le
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0

end HRS.Main

end
