import HRS.MS.MovEntAux4

/-!
# S6.6, packet P4: clause (2) from the entropy bound, and the preparation entropies

* `s66_particle_bounds`: `MovParticleBounds` for a particle process whose laws satisfy `H(f_t|Q_t) ≤ ofReal(C₁ N δ_N)` for all `t ≥ 0`
  (`C` independent of `ρ, N, P, X`, `C₀ ≥ 1`).
* `s66_prep_entropy`: for the preparations `MovPrepared γ` (iid, or `Q_{N,γ}(μ⁰)`): `H(f|Q_{N,β}(μ⁰)) ≤ ofReal(C₄ N δ_N)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

theorem s66_measurable_secondMoment {N : ℕ} : Measurable (fun Z : EucConfig d N => movSecondMoment Z) := by
  unfold movSecondMoment
  fun_prop

theorem s66_particle_bounds (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M L E c₁ β C₁ : ℝ)
    (hβ : 0 < β) (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ → Euc d → ℝ, S66Fam d s ρ M L E c₁ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → EucConfig d N), (∀ t, Measurable (X t)) →
      (∀ t : ℝ, 0 ≤ t → relEntropy (P.map (X t.toNNReal))
          (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ t))) ≤ ENNReal.ofReal (C₁ * N * deltaN d s N)) →
      ∀ (q C₀ : ℝ), 1 ≤ C₀ → MovParticleBounds d s q β C₀ C ρ N P X := by
  obtain ⟨C, hC0, hC⟩ := s66_bounds_at hd hs0 hsd M L E c₁ β C₁ hβ hc₁ hC₁
  refine ⟨C, hC0, ?_⟩
  intro ρ hρ N hN Ω _ P _ X hX hH q C₀ hC₀ t ht
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    inferInstance
  obtain ⟨a1, a2, a3, a4, a5⟩ := hC (ρ t) (hρ.prob t ht) (hρ.bound t ht) (hρ.logm t ht)
    (hρ.expm t ht) N hN (P.map (X t.toNNReal)) inferInstance (hH t ht)
  refine ⟨a1, a2, a3, a4 C₀ hC₀, ?_⟩
  rw [← lintegral_map (s66_measurable_secondMoment (N := N)).ennreal_ofReal (hX _)]
  exact a5

theorem s66_prep_entropy (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M L β γ : ℝ)
    (hβ : 0 < β) (hγ : 0 ≤ γ) :
    ∃ C₄ : ℝ, ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (wd ρ) L) → ∀ N : ℕ, 2 ≤ N →
      ∀ f : Measure (EucConfig d N), MovPrepared d s N γ (wd ρ) f →
        relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ)) ≤
          ENNReal.ofReal (C₄ * N * deltaN d s N) := by
  set b₀ : ℝ := if 0 < γ then γ else 1 with hb₀
  have hb₀pos : 0 < b₀ := by
    rw [hb₀]; split_ifs with h
    · exact h
    · exact one_pos
  obtain ⟨C₄, hC₄⟩ := HRS.MS.Wr.euclidean_preparations_bounds_proof hd hs0 hsd M L β b₀ hβ hb₀pos
  refine ⟨C₄, fun ρ hρ hM hL N hN f hf => ?_⟩
  have h := hC₄ ρ hρ hM hL N hN
  rcases hf with ⟨hγ0, rfl⟩ | ⟨hγp, rfl⟩
  · exact le_self_add.trans h
  · have : b₀ = γ := by rw [hb₀, if_pos hγp]
    rw [this] at h
    exact le_add_self.trans h

end HRS.MS.MovEnt

end
