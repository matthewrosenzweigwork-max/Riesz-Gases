import HRS.Sections.MovLogAux4

/-!
# MOVLOG: Lemma 5.8 `moving_pair_moments` (`M:P:lem:moving-moments`, second assertion), relocated proof

Core for `D > 0`: `MovLog.movlog_pair_core` (`MovLogAux4.lean`); `D = 0` by letting `D → 0⁺` (a kernel with `|h| ≤ 0` off the
diagonal satisfies `|h| ≤ ε w` for every `ε > 0` because `w ≥ 0` off the diagonal... in fact `w ≥ 1`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

theorem moving_pair_moments_proof (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀) (cstar : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        (∀ T : ℝ, 0 ≤ T → IsParticleSystem P htr.dyn T X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        ∀ (D : ℝ), 0 ≤ D → ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) →
          (∀ x y, h x y = h y x) →
          (∀ x y, x ≠ y → |h x y| ≤ D * (periodicRiesz d s (x - y) + cstar)) →
          ∀ t : ℝ, 0 ≤ t →
            eLpNorm (fun ω => (N : ℝ) * modulatedEnergy h (X t.toNNReal ω) (withDensityReal (ρ t)))
              (ENNReal.ofReal r) P ≤
            ENNReal.ofReal (C * D * logMomentScale d s N p₀ (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) := by
  obtain ⟨C, hC, H⟩ := MovLog.movlog_pair_core hd htr p₀ hp₀ cstar hw r hr
  refine ⟨C, hC, fun N hN Ω _ P _ X₀ W X hps hfilt hac hfin D hD h hm hsym hdom t ht => ?_⟩
  rcases hD.eq_or_lt with h0 | hpos
  · subst h0
    set J : ℝ := logMomentScale d s N p₀ (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hJ
    have key : ∀ ε : ℝ, 0 < ε → eLpNorm (fun ω => (N : ℝ) *
        modulatedEnergy h (X t.toNNReal ω) (withDensityReal (ρ t))) (ENNReal.ofReal r) P ≤
        ENNReal.ofReal (C * ε * J) := fun ε hε =>
      H N hN P X₀ W X hps hfilt hac hfin ε hε h hm hsym (fun x y hxy => by
        have := hdom x y hxy
        have h1 := hw (x - y) (sub_ne_zero.2 hxy)
        rw [zero_mul] at this
        have h2 : 0 ≤ ε * (periodicRiesz d s (x - y) + cstar) := by nlinarith
        exact this.trans h2) t ht
    have tend : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε * J)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (ENNReal.ofReal (C * 0 * J))) :=
      ((ENNReal.continuous_ofReal.tendsto _).comp
        ((((continuous_const.mul continuous_id).mul continuous_const).tendsto 0))).mono_left
        nhdsWithin_le_nhds
    exact ge_of_tendsto tend (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  · exact H N hN P X₀ W X hps hfilt hac hfin D hpos h hm hsym hdom t ht

example := (@moving_pair_moments_proof : type_of% @HRS.moving_pair_moments)

end HRS

end
