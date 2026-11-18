import HRS.MS.S113X2C8

/-!
# S11.3 X2 wiring (worker S11W), C9: the bundle of the killed density for one domain and horizon

`s113c_qmin`: the moving reference is bounded below on the compact domain, uniformly on `[0,T]`.
`s113c_bundle`: given the Liouville bound `ν_t ≤ B dx` for `t ∈ [0,T]` and the `C²` reference `q̃` of the core QREG on `closure D`:
a family `u_t` of densities of the killed laws with `u_t/q_t ≤ Z` and, for every absolutely continuous `p > 1` on `[0,T]`,
the integrated one-sided chain inequality (`s113c_chain_conf`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory intervalIntegral
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)

variable {d N : ℕ}

theorem s113c_qmin {s β : ℝ} {ρ : ℝ → Euc d → ℝ} {T : ℝ} {K : Set (EucConfig d N)} (hK : IsCompact K)
    {qt : ℝ → s113b_E (N * d) → ℝ} {G' : Set (s113b_E (N * d))} (hQ : s113c_QReg d N s β ρ T K qt G') :
    ∃ qmin : ℝ, 0 < qmin ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ K, qmin ≤ movQDensity d s β N (ρ t) x := by
  have hKE : IsCompact (Jc d N ⁻¹' K) := ((Jc d N).toHomeomorph.isCompact_preimage).2 hK
  obtain ⟨qm, hqm, hle⟩ := (isCompact_Icc.prod hKE).exists_forall_le' (a := 0)
    (f := fun z : ℝ × s113b_E (N * d) => qt z.1 z.2) hQ.smooth.continuous.continuousOn
    (fun z hz => hQ.pos _ hz.1 _)
  refine ⟨qm, hqm, fun t ht x hx => ?_⟩
  set z := (Jc d N).symm x with hz
  have hzK : z ∈ Jc d N ⁻¹' K := by simpa [hz] using hx
  have h1 := hle (t, z) ⟨ht, hzK⟩
  have h2 := hQ.match_ t ⟨ht.1, by linarith [ht.2]⟩ z (hQ.subset z (by simpa [hz] using hx))
  have h3 : Jc d N z = x := (Jc d N).apply_symm_apply x
  rw [h3] at h2
  rw [← h2]
  exact h1

theorem s113c_bundle {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D) (hDc : IsCompact (closure D))
    (hDfree : closure D ⊆ (eucCollisionSet d N)ᶜ)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi) (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    (hinit : P.map X₀ ≪ (volume : Measure (EucConfig d N)))
    {T : ℝ} (hT : 0 < T) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) T, s113a_killedLaw P D X₀ X chi t.toNNReal ≤ ENNReal.ofReal B • volume)
    {ρ : ℝ → Euc d → ℝ} {qt : ℝ → s113b_E (N * d) → ℝ} {G' : Set (s113b_E (N * d))}
    (hQ : s113c_QReg d N s β ρ T (closure D) qt G') :
    ∃ (u : ℝ → EucConfig d N → ℝ) (Z : ℝ), 0 ≤ Z ∧ (∀ t x, 0 ≤ u t x) ∧ (∀ t, Measurable (u t)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x / movQDensity d s β N (ρ t) x ≤ Z) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, s113a_killedLaw P D X₀ X chi t.toNNReal =
        volume.withDensity (fun x => ENNReal.ofReal (u t x))) ∧
      ∀ p : ℝ → ℝ, AbsolutelyContinuousOnInterval p 0 T → (∀ t ∈ Set.Icc (0 : ℝ) T, 1 < p t) →
        IntervalIntegrable (s113c_Gc d s q β N ρ u p) volume 0 T ∧
        ∀ s' t : ℝ, 0 ≤ s' → s' ≤ t → t ≤ T →
          s113c_Mc d s β N ρ u p t - s113c_Mc d s β N ρ u p s' ≤ ∫ τ in s'..t, s113c_Gc d s q β N ρ u p τ := by
  obtain ⟨u, hu0, hum, huD, huB, hdens⟩ := s113c_density_family hβ hX D hD (hDfree.trans' subset_closure) chi hchi hchi0
    hchi1 hinit hT hB0 hB
  obtain ⟨qmin, hqmin, hqle⟩ := s113c_qmin hDc hQ
  refine ⟨u, B / qmin, by positivity, hu0, fun t => hum.comp (measurable_prodMk_left (x := t)), ?_, hdens, ?_⟩
  · intro t ht x
    by_cases hx : x ∈ D
    · exact div_le_div₀ hB0 (huB t x) hqmin (hqle t ht x (subset_closure hx))
    · rw [huD t x hx, zero_div]; positivity
  · intro p hp hp1
    exact s113c_chain_conf hβ hX D hD hDc hDfree chi hchi hchi0 hchi1 hT u hu0 hum huD huB hdens hQ hp hp1

end HRS.MS.S113X2C

end
