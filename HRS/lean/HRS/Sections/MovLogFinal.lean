import HRS.Sections.MovLogAux1

/-!
# MOVLOG: Lemma 5.8 `moving_log_moment` (`M:P:lem:moving-moments`), relocated proof

Chain plan: header of `MovLogAux1.lean`.  Sorried MOV declarations reached through `mov_lp_bound`: see the axiom check.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

theorem moving_log_moment_proof (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀) :
    ∃ pInf C : ℝ, 1 < pInf ∧ 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        (∀ T : ℝ, 0 ≤ T → IsParticleSystem P htr.dyn T X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        ∀ t : ℝ, 0 ≤ t →
          P.map (X t.toNNReal) ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)) ∧
          eLpNorm ((P.map (X t.toNNReal)).rnDeriv
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))))
            (ENNReal.ofReal pInf) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) ≤
          ENNReal.ofReal (Real.exp (C * logMomentScale d s N p₀ (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c₀, Λ₂, hc₀, hunif⟩ := movT_traj_uniform_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ
    htr.V_smooth htr.init htr.global
  obtain ⟨Λ₁, hΛ₁, L, hLl, hLi, hLlip, hLint⟩ := MovLog.movlog_L hd htr
  obtain ⟨pInf, C₁, hp, hC₁, H⟩ := mov_lp_bound hd1 htr.hs0 htr.hsd β β htr.hβ c₀ hc₀ Λ₂ p₀ hp₀ Λ₁ hΛ₁
  refine ⟨pInf, C₁, hp, hC₁, fun N hN Ω _ P _ X₀ W X hps hfilt hac hfin t ht => ?_⟩
  have hQ : ∀ r : ℝ, movT_Q (periodicRiesz d s) htr.dyn N ρ r =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r)) :=
    fun r => movT_Q_eq_beta (D := htr.dyn) (β := β) (by simp [IsSmoothPositiveTrajectory.dyn, PDE.mfData]) N ρ r
  have hMov : MovHyp P htr.dyn N t ρ X₀ W X :=
    ⟨MovLog.movlog_traj htr t, (hps t ht).brownian, (hps t ht).indep, (hps t ht).sol, hfilt⟩
  obtain ⟨ρt, hρt⟩ := (MovLog.movlog_traj htr t).classical
  obtain ⟨ℓ, hℓ, hLℓ⟩ := hLl t
  rw [← hQ 0] at hac hfin
  have key := H N hN P X₀ W X hMov hρt rfl
    (by simp [IsSmoothPositiveTrajectory.dyn, PDE.mfData])
    (fun r hr x => (hunif r hr.1).1 x) (fun r hr => (hunif r hr.1).2) L ⟨ℓ, hℓ, hLℓ⟩ (hLi t)
    (hLlip t) (hLint t) hac hfin t ⟨ht, le_rfl⟩
  rw [hQ t, hQ 0] at key
  exact key

example := (@moving_log_moment_proof : type_of% @HRS.moving_log_moment)

end HRS

end
