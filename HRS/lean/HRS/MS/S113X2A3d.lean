import HRS.MS.S113X2A3c

/-!
# S11.3 X2 part A3d: **removal of the localization**: `Law(X_t) ≪ Q^t` and `L¹(Q^t)` convergence of the killed ratios
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

/-- The killed law at a positive time is absolutely continuous with respect to any reference measure
charging every Lebesgue-positive set of the collision-free space. -/
theorem s113a_killed_ac {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s q β : ℝ} (hβ : 0 < β)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D) (hfree : D ⊆ (eucCollisionSet d N)ᶜ)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1) {t : ℝ} (ht : 0 < t)
    {Q : Measure (EucConfig d N)}
    (hQ : ∀ A, MeasurableSet A → Q A = 0 → volume (A ∩ (eucCollisionSet d N)ᶜ) = 0) :
    s113a_killedLaw P D X₀ X chi t.toNNReal ≪ Q := by
  obtain ⟨f, -, -, -, -, hdens, -⟩ := s113a_killed_interior_density hβ (T := t + 1) (by linarith) hX D hD hfree
    chi hchi hchi0 hchi1
  have hvol : s113a_killedLaw P D X₀ X chi t.toNNReal ≪ volume := by
    rw [hdens t ⟨ht, by linarith⟩]
    exact withDensity_absolutelyContinuous _ _
  have hcompl := s113a_killedLaw_compl P D hD X₀ X chi t.toNNReal ((hX.sol 0).adapted _)
  intro A hA
  obtain ⟨B, hAB, hBm, hQB⟩ := exists_measurable_superset_of_null hA
  refine measure_mono_null hAB ?_
  have h1 : volume (B ∩ (eucCollisionSet d N)ᶜ) = 0 := hQ B hBm hQB
  have h2 : s113a_killedLaw P D X₀ X chi t.toNNReal (B ∩ (eucCollisionSet d N)ᶜ) = 0 := hvol h1
  have hsub : B ∩ eucCollisionSet d N ⊆ Dᶜ := fun x hx hxD => hfree hxD hx.2
  have h3 : s113a_killedLaw P D X₀ X chi t.toNNReal (B ∩ eucCollisionSet d N) = 0 :=
    measure_mono_null hsub hcompl
  refine nonpos_iff_eq_zero.1 ?_
  calc s113a_killedLaw P D X₀ X chi t.toNNReal B
      ≤ s113a_killedLaw P D X₀ X chi t.toNNReal (B ∩ (eucCollisionSet d N)ᶜ) +
        s113a_killedLaw P D X₀ X chi t.toNNReal (B ∩ eucCollisionSet d N) := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro x hx
        by_cases h : x ∈ eucCollisionSet d N
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl ⟨hx, h⟩
    _ = 0 := by rw [h2, h3, add_zero]

end HRS.MS.S113X2

end
