import HRS.Sections.DynEntAux1

/-!
# DYNENT: Theorem 5.4 `dynamic_entropy` (final, statement verbatim)

Chain plan: header of `DynEntAux1.lean`.

`#print axioms HRS.dynamic_entropy_proof` shows `sorryAx` only through these sorried MOV declarations (all reached via
`mov_ent_ineq` / `movT_entropy_gronwall`): `movT_traj_bounds`, `movT_source_exp`, `movT_pressure_two_sided_C2`,
`movT_cond_narrow`, `movT_cond_hyp`, `movT_reg_ineq`, `movT_lp_init_limsup`, `movT_source_exp_uniform`,
`movT_lp_reg_bound`, `movT_regSeq_exists`, `movT_Q_tendsto_weak`, `movT_source_limit_bdd`, `movT_init_tendsto`,
`movT_cond_entropy_limit`, `movT_source_limit_cond` (frozen MovSpec copies; relocated `_proof`s exist for some).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

theorem dynamic_entropy_proof (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          relEntropy (P.map (X t.toNNReal))
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) +
            relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ => withDensityReal (ρ t)) ≤
          ENNReal.ofReal (C * entropyScale d s N (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) := by
  have hd1 : 1 ≤ d := by omega
  have htr' : MovTraj htr.dyn T ρ :=
    movT_traj_of_global_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init htr.global T
  obtain ⟨c₀, Λ₂, hc₀, hb⟩ :=
    movT_traj_uniform_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init htr.global
  obtain ⟨C₁, hC₁0, hC₁⟩ := movT_entropy_bound htr'
  obtain ⟨C₂, hC₂0, hC₂⟩ := dynent_product_bound hd1 htr' hc₀ (fun r hr x => (hb r hr.1).1 x)
    (fun r hr => (hb r hr.1).2)
  refine ⟨2 * C₁ + C₂ * (1 + C₁), by positivity, ?_⟩
  intro N hN Ω _ P _ X₀ W X hP hfilt hfin t ht
  have e : ∀ r, movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ r =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r)) := fun r =>
    movT_Q_eq_beta (g := periodicRiesz d s) rfl N ρ r
  have hMov : MovHyp P htr.dyn N T ρ X₀ W X :=
    movT_hyp_of_parts htr' hP.brownian hP.indep hP.sol hfilt
  have hfin' : relEntropy (P.map X₀) (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ 0) ≠ ⊤ := by
    rw [e]; exact hfin
  obtain ⟨hfinT, hbd⟩ := hC₁ N hN P X₀ W X hMov hfin' t ht
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff (hP.sol.adapted _).aemeasurable).2 inferInstance
  obtain ⟨hprodfin, hprodle⟩ := hC₂ N hN t ht (P.map (X t.toNNReal)) inferInstance hfinT
  rw [e] at hfinT hbd hprodle
  set B : ℝ := entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hB
  have hbd' : (relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal ≤ C₁ * B := by
    rw [e 0] at hbd; exact hbd
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN htr.hs0 N (by omega)
  have hH0 : 0 ≤ (relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))).toReal := ENNReal.toReal_nonneg
  have hBge : (N : ℝ) * deltaN d s N ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hB1 : 1 ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hHq0 := ENNReal.toReal_nonneg (a := relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))))
  have hp0 := ENNReal.toReal_nonneg (a := relEntropy (P.map (X t.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ t)))
  rw [← ENNReal.ofReal_toReal hfinT, ← ENNReal.ofReal_toReal hprodfin,
    ← ENNReal.ofReal_add hHq0 hp0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpr : (relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal ≤
      (relEntropy (P.map (X t.toNNReal))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal +
      C₂ * ((N : ℝ) * deltaN d s N + (relEntropy (P.map (X t.toNNReal))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal) := hprodle
  nlinarith [mul_le_mul_of_nonneg_left hBge hC₂0, mul_le_mul_of_nonneg_left hbd' hC₂0, hC₁0]

example := (@dynamic_entropy_proof : type_of% @HRS.dynamic_entropy)

end HRS

end
