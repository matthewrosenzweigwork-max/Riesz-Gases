import HRS.MC.Q714HILaw

/-!
# Packet HI (row 7.14): `haar_invariance_proof`

Dynamic Haar invariance, `m_N^t = dx` (TeX L9488-9492): the law of the Haar-started (more precisely `Q_{N,β₀}(dx)`-started)
homogeneous flow is invariant under diagonal translations (`hi_law_shift`), hence every one-particle marginal is Haar measure.
Tie: `HRS/MC/Q714HITie.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.HI

open HRS HRS.Sec7

variable {d N : ℕ}

/-- A translation invariant probability measure on the torus is Haar measure. -/
theorem hi_haar_of_invariant (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
    (hinv : ∀ a : Torus d, ν.map (fun x : Torus d => x + a) = ν) : ν = volume := by
  haveI : Measure.IsAddLeftInvariant ν := ⟨fun a => by
    have e : (fun x : Torus d => a + x) = fun x => x + a := funext fun x => add_comm a x
    rw [e]
    exact hinv a⟩
  have hc := Measure.isAddInvariant_eq_smul_of_compactSpace ν (volume : Measure (Torus d))
  have hmass := congrArg (fun ν : Measure (Torus d) => ν Set.univ) hc
  have hc1 : ν.addHaarScalarFactor (volume : Measure (Torus d)) = 1 := by
    simpa using hmass.symm
  rw [hc, hc1, one_smul]

theorem hi_meanEmpirical_volume (hN : 1 ≤ N) (μ : Measure (Config d N)) [IsProbabilityMeasure μ]
    (hinv : ∀ θ : Torus d, μ.map (shiftC θ) = μ) : meanEmpirical μ = volume := by
  have hmi : ∀ i : Fin N, μ.map (fun X : Config d N => X i) = volume := by
    intro i
    refine hi_haar_of_invariant _ (fun a => ?_)
    have hcomp : ((fun x : Torus d => x + a) ∘ (fun X : Config d N => X i)) =
        (fun X : Config d N => X i) ∘ (shiftC a) := rfl
    rw [Measure.map_map (measurable_add_const a) (measurable_pi_apply i), hcomp,
      ← Measure.map_map (measurable_pi_apply i) (measurable_shiftC a), hinv a]
  rw [meanEmpirical_eq_sum]
  simp only [hmi, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top N),
    one_smul]

/-- **HI (dynamic Haar invariance)**, relocated proof; statement copied verbatim from `Q714Spec.lean`. -/
theorem haar_invariance_proof (hd : 2 ≤ d) {s β β₀ : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hβ : 0 < β) (hβ₀ : 0 < β₀)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 1 ≤ N) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization D P (modulatedGibbs (periodicRiesz d s) N β₀ volume) X₀ W X) :
    ∀ t : ℝ, 0 ≤ t → meanEmpirical (P.map (X t.toNNReal)) = volume := by
  intro t _
  obtain ⟨hDs, hDM, hDV, hDβ⟩ := hD
  have hd1 : 1 ≤ d := by omega
  have hsd : s < (d : ℝ) := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hg : Measurable (periodicRiesz d s) := CoercAux.measurable_periodicRiesz_one hd1 hs0 hsd
  have hQ0inv : ∀ θ : Torus d,
      (modulatedGibbs (periodicRiesz d s) N β₀ (volume : Measure (Torus d))).map (shiftC θ) =
        modulatedGibbs (periodicRiesz d s) N β₀ (volume : Measure (Torus d)) := fun θ =>
    haar_gibbs_shift_invariant hg hN β₀ θ
  have hac : modulatedGibbs (periodicRiesz d s) N β₀ (volume : Measure (Torus d)) ≪
      (volume : Measure (Config d N)) := by
    unfold modulatedGibbs
    exact (withDensity_absolutelyContinuous _ _).smul_left _
  have hQ0 : ∀ᵐ Y ∂(modulatedGibbs (periodicRiesz d s) N β₀ (volume : Measure (Torus d))),
      Y ∉ collisionSet d N := hac.ae_le (Q84d.q84d_ae_not_collision hd1)
  have hlaw : ∀ θ : Torus d, (P.map (X t.toNNReal)).map (shiftC θ) = P.map (X t.toNNReal) := fun θ =>
    hi_law_shift hd hN D hDM hDV P _ hQ0 hQ0inv X₀ W X hreal t.toNNReal θ
  exact hi_meanEmpirical_volume hN _ hlaw

end HRS.MC.Q714.HI
