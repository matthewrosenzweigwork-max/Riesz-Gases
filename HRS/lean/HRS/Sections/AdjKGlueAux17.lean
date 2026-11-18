import HRS.Sections.AdjKGlueAux16

/-!
# ADJK-GLUE, part 17: `dynamic_convergence` (Proposition 5.4, last paragraph), assembled
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

theorem adjkg_dynamic_convergence (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : S.IsSolutionOn htr.dyn T)
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hfin : ∀ n, relEntropy ((S.P n).map (S.X₀ n))
      (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) ≠ ⊤)
    (hB : Tendsto (fun n : ℕ => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
          Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0))
    (m : ℝ) (hm : (d : ℝ) + 4 < m)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η₀ : Ω' → NegSobolev d m)
    (hlaw : MeasureTheory.TendstoInDistribution
      (fun n ω => etaE m (S.X₀ n ω) (withDensityReal (ρ 0))) atTop η₀ S.P P')
    (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P' htr.dyn ρ m β⁻¹ T η₀ Y) :
    MeasureTheory.TendstoInDistribution
      (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ)) (S.X n) ρ ω) atTop
      (toPath m T Y) S.P P' := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmd2 : (d : ℝ) / 2 < m := by linarith
  have hm2 : (d : ℝ) < 2 * m := by linarith
  rcases hT.eq_or_lt with hT0 | hTpos
  · -- the case `T = 0`
    subst hT0
    let cst : NegSobolev d m → PathSpace d m 0 := fun z =>
      (⟨fun _ => z, continuous_const⟩ : C(Set.Icc (0 : ℝ) 0, NegSobolev d m))
    have hcst : Continuous cst := by
      show Continuous (ContinuousMap.const (Set.Icc (0 : ℝ) 0) :
        NegSobolev d m → C(Set.Icc (0 : ℝ) 0, NegSobolev d m))
      exact ContinuousMap.continuous_const'
    have hconv0 := hlaw.continuous_comp hcst
    have hzero : ∀ t : Set.Icc (0 : ℝ) 0, (t : ℝ) = 0 := fun t => le_antisymm t.2.2 t.2.1
    refine hconv0.congr (fun n => ?_) ?_
    · filter_upwards [adjkg_hcont hd htr le_rfl hmd2 S hS n, (hS n).sol.init] with ω hcω hi
      refine ContinuousMap.ext fun t => ?_
      show etaE m (S.X₀ n ω) (withDensityReal (ρ 0)) =
        (flucPath m 0 (Real.sqrt ((n + 2 : ℕ) : ℝ)) (S.X n) ρ ω).at' t
      rw [adjkg_flucPath_at m 0 _ (S.X n) ρ ω hcω t]
      simp only [hzero t, Real.toNNReal_zero, hi]
      rfl
    · filter_upwards [hY.cont, hY.init] with ω' hc hi
      have hc' : Continuous fun t : Set.Icc (0 : ℝ) 0 => Y t ω' := continuousOn_iff_continuous_restrict.1 hc
      refine ContinuousMap.ext fun t => ?_
      show η₀ ω' = (toPath m 0 Y ω').at' t
      rw [adjkg_toPath_at m 0 Y ω' hc' t, hzero t, hi]
  · -- `T > 0`
    have hΦ : ∀ n, AEMeasurable (fun ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ)) (S.X n) ρ ω)
        (S.P n) := fun n =>
      adjk_flucPath_aemeasurable_proof hd htr m hmd2 T hT (by omega : 2 ≤ n + 2) (S.P n) (S.X₀ n)
        (S.W n) (S.X n) (hS n)
    have hΨ : AEMeasurable (toPath m T Y) P' :=
      adjk_toPath_aemeasurable_proof P' m T Y hY.meas hY.cont
    have htight := adjkg_tight hd htr hTpos S hS hSF hfin hB hm hlaw
    exact adjk_convergence_of_tight_fidi_proof m T hT S.P
      (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ)) (S.X n) ρ ω) P' (toPath m T Y) hΦ hΨ
      htight (fun p ts hts φ hφ => adjkg_fdd hd htr hT S hS hSF hfin hB hmd2 hlaw hY p ts hts φ hφ)

end HRS.AdjK
