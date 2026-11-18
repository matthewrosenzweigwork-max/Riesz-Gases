import HRS.MS.R2InterpAux71

/-!
# S10.2 (worker S102), part 72: `S102Lin` and `S102Std` for the thermal quadratic coefficient
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ}

theorem s102_lin_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (m T : ℝ) (hT : 0 ≤ T) :
    S102Lin ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) m T := by
  intro u t hu hut htT φ ψ c hφ hψ
  obtain ⟨f, hf⟩ := s102_combo_schwartz m hφ
  obtain ⟨g, hg⟩ := s102_combo_schwartz m hψ
  have ht : t ∈ Set.Icc (0 : ℝ) T := ⟨hu.trans hut, htT⟩
  have := s102_propagator_comb hd hs0 hs ha hβ hρ hT f g c ht (r := u) ⟨hu, hut⟩
  rw [hf, hg] at this
  have e : φ + c • ψ = fun x => φ x + c * ψ x := by funext x; simp
  rw [e]
  funext x
  have h2 := congrFun this x
  simpa using h2

theorem s102_std_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (m T : ℝ) (hT : 0 ≤ T) {r : ℕ}
    {c : MultiIndex d → ℝ} (hD : S101Data ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) m T r c) :
    S102Std ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) m T r c := by
  have hpd : HRS.Whole.IsProbDensity ρ := hρ.2.1
  refine ⟨hD, ?_, fun v => rfl, ?_, fun x => hpd.nonneg x, ?_⟩
  · show 0 ≤ β⁻¹
    exact (inv_pos.2 hβ).le
  · exact Integrable.of_integral_ne_zero (f := ρ) (by rw [hpd.integral_one]; exact one_ne_zero)
  · intro α t ht
    obtain ⟨f, hf⟩ := s102_osc_schwartz m α
    have := s102_exists_adjoint hd hs0 hs ha hβ hρ hT f ht
    rw [hf] at this
    exact this

end HRS.MS.R2Interp

end
