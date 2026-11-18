import HRS.Sections.AdjKGlueAux5
import HRS.Main.GFB1Aux2

/-!
# ADJK-GLUE, part 6: the per-system bundle for `dynamic_convergence`

For a smooth positive trajectory, `m > d + 4` and a horizon `T > 0`, one dual evolution `Vev` (with uniform bound) and constants
`Cz, Cr` such that every particle system on `[0,T]` (filtered, finite entropy) carries a measurable continuous version `Z` of the
stochastic convolution of its martingale, with the BCONV bounds, the B2 bound for the integrated forcing, and the mild identity B3.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkg_sys (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) + 4 < m) {T : ℝ} (hT : 0 < T) {j : ℕ} (hj : (d : ℝ) + 2 ≤ j)
    (hjm : (j : ℝ) + 2 ≤ m) {m₂ : ℝ} (hm₂ : (d : ℝ) + 2 < m₂) :
    ∃ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m, IsDualEvolution htr.dyn ρ m Vev ∧
      (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') ∧
      ∃ CL : ℝ, 0 ≤ CL ∧ (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ CL) ∧
      ∃ Cz Cr : ℝ, 0 ≤ Cz ∧ 0 ≤ Cr ∧ ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          IsParticleSystem P htr.dyn T X₀ W X →
          (∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
            IsFilteredSolution P ℱ W' W X) →
          relEntropy (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
          ∃ Z : ℝ → Ω → NegSobolev d m, (∀ t, Measurable (Z t)) ∧
            (∀ ω, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) ∧
            ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, adjkEnergy (j : ℝ) m (Z t ω) ∂P ≤ ENNReal.ofReal Cz ∧
            (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∫⁻ ω, ‖Z t ω - Z s ω‖ₑ ^ (4 : ℝ) ∂P ≤ ENNReal.ofReal (Cz * |t - s| ^ 2)) ∧
            ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (∑' k : NonzeroLattice d,
                ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m₂) *
                  evolvingForcingCoord htr.dyn ρ X k t ω ^ 2)) ^ (1 / 2 : ℝ) ∂P ≤
              ENNReal.ofReal (Cr * entropyScale d s N (P.map X₀)
                (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N) ∧
            ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
              NegSobolev.fourierCoeff (etaE m (X t.toNNReal ω) (withDensityReal (ρ t))) k =
                NegSobolev.fourierCoeff (Vev t 0 (etaE m (X 0 ω) (withDensityReal (ρ 0)))) k +
                  NegSobolev.fourierCoeff (Z t ω) k + evolvingForcingCoord htr.dyn ρ X k t ω := by
  classical
  obtain ⟨Vev, hdual, hplain, hB1⟩ := adjk_evolution_moment_proof hd htr m 2 le_rfl
  obtain ⟨Cr3, cr3, hCr3, hcr3, Vev3, hdual3, -, hdec3, -⟩ := adjk_evolution_along_trajectory hd htr m
  have hCL : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr3 := by
    intro u t hu hut
    rw [adjkg_dual_eq hdual hdual3 hu hut]
    refine (hdec3 u t hu hut).trans ?_
    have : Real.exp (-cr3 * (t - u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  obtain ⟨CT, hCT0, hCTmain⟩ := hB1 T hT
  obtain ⟨Cb, hCb0, hCb⟩ := adjk_conv_kolmogorov_proof hd htr j hj m hjm T hT
  obtain ⟨Cr, hCr0, hCR⟩ := adjk_remainder_L1_proof hd htr m₂ hm₂ T hT
  refine ⟨Vev, hdual, hplain, Cr3, hCr3.le, hCL, Cb, Cr, hCb0, hCr0, ?_⟩
  intro N hN Ω mΩ P hP X₀ W X hX hF hfin
  obtain ⟨ℱ, W', hFs⟩ := hF
  have hm2 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨M, hM, hMid⟩ := adjk_particle_martingale_proof hd htr m hm2 T hT hN P X₀ W X hX ℱ W' hFs
  obtain ⟨Z₀, hZ₀, hZ₀c, hZ₀m, -⟩ := hCTmain Ω P ℱ 0 T le_rfl hT le_rfl M
    (fun r ω => covForm m β⁻¹ (empirical (X r.toNNReal ω))) (by rwa [zero_add])
  simp only [zero_add] at hZ₀ hZ₀c hZ₀m
  obtain ⟨Z, hZm, hZc, hZeq⟩ := GF.gf_measurable_modification_proof P T Z₀ hZ₀c hZ₀m
  have hZ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t) :=
    fun t ht => GF.isStochConv_congr_ae (hZ₀ t ht) (hZeq t ht).symm
  have hNpos : 0 < N := by omega
  obtain ⟨hb1, hb2⟩ := hCb Ω P ℱ (fun r ω => empirical (X r.toNNReal ω))
    (fun r ω => empirical_isProbabilityMeasure hNpos _) M hM Vev hdual hplain Z hZ
    (Filter.Eventually.of_forall hZc) hZm
  obtain ⟨-, hR⟩ := hCR N hN P X₀ W X hX ⟨ℱ, W', hFs⟩ hfin
  have h3 := adjk_mild_decomposition_proof hd htr m hm2 T hT hN P X₀ W X hX ℱ W' hFs M hM hMid Vev hdual
    Z hZ (fun t _ => (hZm t).aemeasurable) (Filter.Eventually.of_forall hZc)
  exact ⟨Z, hZm, hZc, hb1, hb2, hR, h3⟩

end HRS.AdjK
