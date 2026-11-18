import HRS.MS.S113X2A3d

/-!
# S11.3 X2 part A3e: assembly: `Law(X_t) ≪ Q^t` and `L¹(Q^t)` convergence of the killed ratios, for every `t ≥ 0`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

/-- **Removal of the localization.**  Let `D_n = s113a_domain d N n` and `χ_n` measurable with values in `[0,1]`,
`χ_n(X₀) → 1` a.s.  Let `Q t` be σ-finite reference measures with `Q 0 ≫ P∘X₀⁻¹` and such that Lebesgue measure on the
collision-free set is dominated by `Q t` (`Q t A = 0 → |A ∖ collisions| = 0`).  With `ν_n(t)` the killed law (at time `t`),
for every `t ≥ 0`: `Law(X_t) ≪ Q t`, `dν_n(t)/dQ t ≤ dLaw(X_t)/dQ t` a.e., and `dν_n(t)/dQ t → dLaw(X_t)/dQ t` in `L¹(Q t)`. -/
theorem s113a_removal_of_localization {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (Q : ℝ → Measure (EucConfig d N)) [∀ t, SigmaFinite (Q t)]
    (hQ : ∀ t, 0 ≤ t → ∀ A, MeasurableSet A → Q t A = 0 → volume (A ∩ (eucCollisionSet d N)ᶜ) = 0)
    (hinit : P.map X₀ ≪ Q 0)
    (chi : ℕ → EucConfig d N → ℝ) (hchi : ∀ n, Measurable (chi n)) (hchi0 : ∀ n z, 0 ≤ chi n z)
    (hchi1 : ∀ n z, chi n z ≤ 1)
    (hlim : ∀ᵐ ζ ∂P, Tendsto (fun n => chi n (X₀ ζ)) atTop (𝓝 1)) {t : ℝ} (ht : 0 ≤ t) :
    P.map (X t.toNNReal) ≪ Q t ∧
    (∀ n, ∀ᵐ x ∂(Q t),
      (((s113a_killedLaw P (s113a_domain d N n) X₀ X (chi n) t.toNNReal).rnDeriv (Q t)) x).toReal ≤
        (((P.map (X t.toNNReal)).rnDeriv (Q t)) x).toReal) ∧
    Tendsto (fun n => ∫⁻ x, ‖(((s113a_killedLaw P (s113a_domain d N n) X₀ X (chi n) t.toNNReal).rnDeriv (Q t)) x).toReal -
        (((P.map (X t.toNNReal)).rnDeriv (Q t)) x).toReal‖ₑ ∂(Q t)) atTop (𝓝 0) := by
  have hsol := hX.sol 0
  have hXt : Measurable (X t.toNNReal) := hsol.adapted _
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) := (Measure.isProbabilityMeasure_map_iff hXt.aemeasurable).2 inferInstance
  haveI hfin : ∀ n, IsFiniteMeasure (s113a_killedLaw P (s113a_domain d N n) X₀ X (chi n) t.toNNReal) :=
    fun n => s113a_killedLaw_finite P _ X₀ X (chi n) (hchi1 n) _
  have hle : ∀ n, s113a_killedLaw P (s113a_domain d N n) X₀ X (chi n) t.toNNReal ≤ P.map (X t.toNNReal) :=
    fun n => s113a_killedLaw_le P _ X₀ X (chi n) (hchi1 n) _ hXt
  have hmass := s113a_killedLaw_mass_tendsto hX (s113a_domain d N) (s113a_domain_isOpen d N)
    (s113a_domain_mono d N) (s113a_domain_iUnion d N) chi hchi hchi1 hchi0 hlim t.toNNReal
  have hac : ∀ n, s113a_killedLaw P (s113a_domain d N n) X₀ X (chi n) t.toNNReal ≪ Q t := by
    intro n
    rcases ht.eq_or_lt with h0 | hpos
    · subst h0
      have h1 : P.map (X (0 : ℝ).toNNReal) = P.map X₀ := by
        rw [Real.toNNReal_zero]
        exact Measure.map_congr (hsol.init)
      exact (Measure.absolutelyContinuous_of_le (h1 ▸ hle n)).trans hinit
    · exact s113a_killed_ac hβ hX _ (s113a_domain_isOpen d N n) (s113a_domain_subset_free d N n) (chi n)
        (hchi n) (hchi0 n) (hchi1 n) hpos (hQ t ht)
  obtain ⟨hμQ, hL1⟩ := s113a_L1_of_mass hle hmass hac
  refine ⟨hμQ, fun n => ?_, hL1⟩
  filter_upwards [s113a_rnDeriv_mono (Q := Q t) (hle n), Measure.rnDeriv_lt_top (P.map (X t.toNNReal)) (Q t)]
    with x h1 h2
  exact ENNReal.toReal_mono h2.ne h1

end HRS.MS.S113X2

end
