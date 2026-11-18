import HRS.Sections.ScrnAux28

/-!
# Packet SCRN, part 29: the covariation discrepancy `E ∫ ‖Σ - Σ̄‖_{S₁}`

`scrn_G_facts`: the completed positive energy `G_r = (F_N(X^r) + o_N)_+` (time clamped) is jointly measurable,
integrable with `E G_r ≤ o_N`.  `scrn_cov_entry`: the entries of `Σ - Σ̄` are `2β⁻¹ (μ_N^r(χ) - ∫χ)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

open HRS.Main.A8P HRS.Uniform

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem scrn_jensen_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Ω → ℝ) (hGm : Measurable G) (hG0 : ∀ᵐ ω ∂P, 0 ≤ G ω) (hGi : Integrable G P) :
    Integrable (fun ω => Real.sqrt (G ω)) P ∧ ∫ ω, Real.sqrt (G ω) ∂P ≤ Real.sqrt (∫ ω, G ω ∂P) := by
  have hum : Measurable fun ω => Real.sqrt (G ω) := hGm.sqrt
  have hsq : (fun ω => Real.sqrt (G ω) ^ 2) =ᵐ[P] G := by
    filter_upwards [hG0] with ω hω using Real.sq_sqrt hω
  have hint2 : Integrable (fun ω => Real.sqrt (G ω) ^ 2) P := hGi.congr hsq.symm
  have hmem : MemLp (fun ω => Real.sqrt (G ω)) 2 P :=
    (memLp_two_iff_integrable_sq hum.aestronglyMeasurable).2 hint2
  have hu1 : Integrable (fun ω => Real.sqrt (G ω)) P := hmem.integrable one_le_two
  refine ⟨hu1, ?_⟩
  have hv := variance_nonneg (fun ω => Real.sqrt (G ω)) P
  rw [variance_eq_sub hmem] at hv
  have h1 : ∫ ω, Real.sqrt (G ω) ∂P ≤ |∫ ω, Real.sqrt (G ω) ∂P| := le_abs_self _
  refine h1.trans (Real.abs_le_sqrt ?_)
  have e : P[(fun ω => Real.sqrt (G ω)) ^ 2] = ∫ ω, G ω ∂P := integral_congr_ae hsq
  rw [e] at hv
  linarith

/-- The pointwise form of the entries of `Σ - Σ̄`. -/
theorem scrn_cov_entry {Ω : Type*} {N p : ℕ} (hN : 1 ≤ N) (D : DynData d)
    (ts : Fin p → ℝ) (f : Fin p → ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) (r : ℝ) (ω : Ω)
    (a b : Fin p) :
    killedCovMatrix (fun a => scrnPhi D (Real.sqrt N) (ts a) (f a) X) ts r ω a b -
      scrnSig ts (scrnGc ts f) (2 * D.invβ) r a b =
    if 0 ≤ r ∧ r < min (ts a) (ts b) then
      2 * D.invβ * (∫ x, inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x)
          ∂(empirical (X (Real.toNNReal r) ω)) -
        ∫ x, inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x)) else 0 := by
  have h := a8p_cov_entry_eq hN D (Real.sqrt N) ts f X (fun _ _ => (1 : ℝ)) r ω a b
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hc : 2 * (Real.sqrt N ^ 2 * D.invβ / N) = 2 * D.invβ := by
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]; field_simp
  rw [hc] at h
  have hs : a8pSigBar ts (a8pG ts f) (fun _ _ => (1 : ℝ)) (2 * D.invβ) r a b =
      scrnSig ts (scrnGc ts f) (2 * D.invβ) r a b := by
    unfold a8pSigBar scrnSig
    simp [a8pG, scrnGc]
  rw [← hs]
  simp only [mul_one] at h
  exact h

/-- The completed positive energy `G_r = (F_N(X^r) + o_N)_+` along the flow. -/
theorem scrn_G_facts (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hfl : ScrnFlow d hs0 hsd β hβ N P X₀ W X)
    {ℱ : MeasureTheory.Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {C₀ Cq : ℝ} (hcom : A8CommSpec d s C₀ Cq)
    {Tm : ℝ} (hTm0 : 0 < Tm) :
    ∃ G : ℝ → Ω → ℝ, (Measurable fun q : ℝ × Ω => G q.1 q.2) ∧ (∀ r ω, 0 ≤ G r ω) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) Tm, Integrable (G r) P) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) Tm, ∫ ω, G r ω ∂P ≤ oN d s C₀ N) ∧
      (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) Tm,
        0 ≤ rieszEnergy d s (X (Real.toNNReal r) ω) (volume : Measure (Torus d)) + oN d s C₀ N ∧
        rieszEnergy d s (X (Real.toNNReal r) ω) (volume : Measure (Torus d)) + oN d s C₀ N ≤ G r ω) := by
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  set o : ℝ := oN d s C₀ N with ho
  have hsolT := hfl.sol Tm hTm0.le
  have hEn : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω => rieszEnergy d s (X t.toNNReal ω) (volume : Measure (Torus d))) P ∧
      ∫ ω, rieszEnergy d s (X t.toNNReal ω) (volume : Measure (Torus d)) ∂P ≤ 0 := fun t ht =>
    scrn_energy_bound hd hs0 hsd β hβ hN P X₀ W X hfl.brownian hfl.indep hfl.law hfl.sol hfl.filt t ht
  have hFmeas : Measurable (fun Y : Config d N => rieszEnergy d s Y (volume : Measure (Torus d))) := by
    obtain ⟨hm, -⟩ := movf_energy_facts hd1 hs0 hsd scrn_isProbDensity_one continuous_const hN0 (N := N)
    rw [scrn_withDensityReal_one] at hm
    exact hm
  have hρ := scrn_isProbDensity_one (d := d)
  set G : ℝ → Ω → ℝ := fun r ω => max (rieszEnergy d s (X (Real.toNNReal (Q54c.clampT Tm r)) ω)
    (volume : Measure (Torus d)) + o) 0 with hG
  have hnoc : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ Tm → X t ω ∉ collisionSet d N := hsolT.no_collision
  have hpos : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) Tm,
      0 ≤ rieszEnergy d s (X (Real.toNNReal r) ω) (volume : Measure (Torus d)) + o := by
    filter_upwards [hnoc] with ω hω r hr
    have hcoll : X (Real.toNNReal r) ω ∉ collisionSet d N := hω _ (by
      rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
    have h := (hcom 1 le_rfl N hN (fun _ => (1 : ℝ)) hρ (fun _ => le_rfl) _ hcoll).1
    rw [scrn_withDensityReal_one, scrn_oNΛ_one] at h
    exact h
  refine ⟨G, ?_, fun r ω => le_max_right _ _, ?_, ?_, ?_⟩
  · exact ((hFmeas.comp (scrn_progressive_meas ℱ X hF.progressive hTm0.le)).add_const o).max
      measurable_const
  · intro r hr
    have hr0 : 0 ≤ Q54c.clampT Tm r := (Q54c.clampT_mem hTm0.le r).1
    exact ((hEn _ hr0).1.add (integrable_const o)).pos_part
  · intro r hr
    have hcl := Q54c.clampT_mem hTm0.le r
    have hae : G r =ᵐ[P] fun ω => rieszEnergy d s (X (Real.toNNReal (Q54c.clampT Tm r)) ω)
        (volume : Measure (Torus d)) + o := by
      filter_upwards [hpos] with ω hω
      simp only [hG]
      exact max_eq_left (hω _ hcl)
    rw [integral_congr_ae hae, integral_add (hEn _ hcl.1).1 (integrable_const o)]
    have := (hEn _ hcl.1).2
    simp only [integral_const, probReal_univ, one_smul]
    linarith
  · filter_upwards [hpos] with ω hω r hr
    refine ⟨hω r hr, ?_⟩
    simp only [hG, Q54c.clampT_of_mem hr]
    exact le_max_left _ _

end HRS
