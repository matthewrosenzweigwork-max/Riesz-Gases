import HRS.Sections.Sec5
import HRS.Stochastic.DualityProof
import HRS.Stochastic.BDG
import HRS.Sections.Q40bAux2
import HRS.Sections.Q40bAux3
import HRS.Sections.Q40bAux5

/-!
# Packet Q40b, part 7: `L¹` bound of the commutator forcing from the entropy hypothesis

`q40b_hL1`: `sup_{r ≤ t} E|F_N^{h_{∇U^{r,t}φ}}(X^r, μ^r)| < ∞` (Proposition 5.5 with the Donsker–Varadhan
inequality, `q40b_forcing_L1`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

section L1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem q40b_hL1 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {t : ℝ} (ht : 0 ≤ t)
    {φ : Torus d → ℝ} {F : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution htr.dyn ρ t φ F)
    (hN : 2 ≤ N) {ℱ : Filtration ℝ mΩ} {X : ℝ≥0 → Ω → Config d N}
    (hXm : ∀ r : ℝ≥0, Measurable (X r)) (hprog : IsProgressive ℱ (ofNNRealTime X)) {H₁ : ℝ}
    (hent : ∀ r ∈ Set.Icc (0 : ℝ) t, relEntropy (P.map (X r.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r))) ≤ ENNReal.ofReal H₁) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ r ∈ Set.Icc (0 : ℝ) t, ∫⁻ ω, ‖Fm d s F ρ X r ω‖ₑ ∂P ≤ K := by
  obtain ⟨c₀, hc₀, Λ, hΛ⟩ := q40b_rho_bounds (by omega) htr
  obtain ⟨M, hM⟩ := q40b_unif_D2 hF
  have hM0 : ∀ r ∈ Set.Icc (0 : ℝ) t, IsLipschitzVF (max M 0) (Torus.grad (F r)) := fun r hr =>
    q40b_grad_lip (hF.c2 r hr) (fun y => (hM r hr y).trans (le_max_left _ _))
  obtain ⟨C, hC⟩ := q40b_forcing_L1 hd htr.hs0 htr.hsd htr.hβ hc₀ Λ (le_max_right M 0)
  refine ⟨ENNReal.ofReal C * (ENNReal.ofReal H₁ + ENNReal.ofReal (N * deltaN d s N)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩),
    fun r hr => ?_⟩
  have hρP : ∀ r ∈ Set.Icc (0 : ℝ) t, IsProbDensity (ρ r) := fun r hr => (hΛ r hr.1).1
  have hΨ := q40b_Psi_meas (N := N) (s := s) ht htr.hsd hF.isC12Test (q40b_jointCont (by omega) htr t) hρP
  have hgm : Measurable (fun x : Config d N => modulatedEnergy (commKernel (periodicRieszGrad d s)
      (Torus.grad (F r))) x (withDensityReal (ρ r))) := by
    have := hΨ.comp (measurable_prodMk_left (x := r) (β := Config d N))
    convert this using 1
    funext x
    simp only [Function.comp, clampTI_of_mem hr]
  set ν : Measure (Config d N) := P.map (X r.toNNReal) with hν
  have hKL : relEntropy ν (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r))) < ⊤ :=
    lt_of_le_of_lt (hent r hr) ENNReal.ofReal_lt_top
  have hmain := hC (ρ r) (hΛ r hr.1).1 (hΛ r hr.1).2.1 (hΛ r hr.1).2.2.1 (hΛ r hr.1).2.2.2
    (Torus.grad (F r)) (hM0 r hr) N hN ν inferInstance hKL
  have hconv : ∫⁻ ω, ENNReal.ofReal (N * |Fm d s F ρ X r ω|) ∂P =
      ∫⁻ x, ENNReal.ofReal (N * |modulatedEnergy (commKernel (periodicRieszGrad d s)
        (Torus.grad (F r))) x (withDensityReal (ρ r))|) ∂ν := by
    rw [hν, lintegral_map _ (hXm _)]
    · rfl
    · exact (ENNReal.measurable_ofReal.comp (measurable_const.mul hgm.abs))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  calc ∫⁻ ω, ‖Fm d s F ρ X r ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal (N * |Fm d s F ρ X r ω|) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [abs_nonneg (Fm d s F ρ X r ω)])
    _ = _ := hconv
    _ ≤ ENNReal.ofReal C * (relEntropy ν (modulatedGibbs (periodicRiesz d s) N β
          (withDensityReal (ρ r))) + ENNReal.ofReal (N * deltaN d s N)) := hmain
    _ ≤ _ := by gcongr; exact hent r hr

end L1

end HRS.Q40b
