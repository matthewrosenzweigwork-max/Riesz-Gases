import HRS.MS.R2InterpAux80
import HRS.MS.R2MtAux2
import HRS.MS.R2ChaosAux14

/-!
# S10.2 (worker S10R), part 81 (packet F5a): `L¹` bounds of the pair energy of bounded kernels along one particle law

For a law `P₀` of `N ≥ 2` particles with `HasR2ActualDensity`, the quantities `N F_N^h` and its `P₀`-centering are integrable with a uniform `L¹` bound,
for every bounded pair kernel `h` (S9.2, single-`N` form `s92_F_bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_integrable_of_eLpNorm_one {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f P) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : eLpNorm f (ENNReal.ofReal 1) P ≤ ENNReal.ofReal C) :
    Integrable f P ∧ ∫ x, ‖f x‖ ∂P ≤ C := by
  rw [ENNReal.ofReal_one] at hC
  have hlt : eLpNorm f 1 P < ⊤ := lt_of_le_of_lt hC ENNReal.ofReal_lt_top
  have hint : Integrable f P := ⟨hf, by rw [hasFiniteIntegral_iff_enorm]; rwa [eLpNorm_one_eq_lintegral_enorm hf] at hlt⟩
  refine ⟨hint, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm hf] at hC
  calc ∫ x, ‖f x‖ ∂P = (∫⁻ x, ‖f x‖ₑ ∂P).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _) hf.norm]
        simp only [ofReal_norm]
    _ ≤ C := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hC
        rwa [ENNReal.toReal_ofReal hC0] at this

/-- **F5a** (single law, bounded kernel): `N F_N^h` and its centering are integrable with a uniform `L¹` bound. -/
theorem s102_comm_L1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L β p K B : ℝ) (hβ : 0 < β)
    (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ N : ℕ, 2 ≤ N →
      ∀ P₀ : Measure (EucConfig d N), HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) P₀ →
      ∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
        (Integrable (fun X : EucConfig d N => (N : ℝ) * pairEnergy h X (HRS.Whole.withDensityReal ρ)) P₀ ∧
          ∫ X, ‖(N : ℝ) * pairEnergy h X (HRS.Whole.withDensityReal ρ)‖ ∂P₀ ≤ C) ∧
        (Integrable (fun X : EucConfig d N => (N : ℝ) * (pairEnergy h X (HRS.Whole.withDensityReal ρ) -
            ∫ Y, pairEnergy h Y (HRS.Whole.withDensityReal ρ) ∂P₀)) P₀ ∧
          ∫ X, ‖(N : ℝ) * (pairEnergy h X (HRS.Whole.withDensityReal ρ) -
            ∫ Y, pairEnergy h Y (HRS.Whole.withDensityReal ρ) ∂P₀)‖ ∂P₀ ≤ C) := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.R2Mt.s92_F_bound hd hs0 hs M L β p K B 1 hβ hp le_rfl
  refine ⟨C, hC0, fun ρ hρ N hN P₀ hP h hh => ?_⟩
  haveI := HRS.MS.R2Mt.s92_isProb_mu hρ.prob
  obtain ⟨h1, h2⟩ := hC ρ hρ h hh N hN P₀ hP
  have hm : Measurable (fun X : EucConfig d N => pairEnergy h X (HRS.Whole.withDensityReal ρ)) :=
    HRS.MS.Wr.wr9_measurable_pairEnergy hh.measurable
  exact ⟨s102_integrable_of_eLpNorm_one (hm.const_mul _).aestronglyMeasurable hC0 h1,
    s102_integrable_of_eLpNorm_one ((hm.sub_const _).const_mul _).aestronglyMeasurable hC0 h2⟩

end HRS.MS.R2Interp

end
