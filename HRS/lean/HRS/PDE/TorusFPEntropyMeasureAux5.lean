import HRS.PDE.TorusFPEntropyMeasureAux4

/-!
# D3-b, Aux5: the tilted reference measure `q = d1_gibbsMeasure κ (U - κψ)` and entropy relative to it

Helpers `d3b_*`.  `q = P.tilted ψ` (Mathlib's exponential tilting of `P = d1_gibbsMeasure κ U`), and for a
probability measure `μ`: `H(μ|P.tilted ψ) = H(μ|P) - ∫ψ dμ + log ∫ e^ψ dP`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

/-- `d1_gibbsMeasure κ (U - κψ)` is the exponential tilt of `d1_gibbsMeasure κ U` by `ψ`. -/
theorem d3b_tilt_eq {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {ψ : Torus n → ℝ}
    (hψ : Continuous ψ) :
    d1_gibbsMeasure κ (d3_tiltPot κ U ψ) = (d1_gibbsMeasure κ U).tilted ψ := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  obtain ⟨Zr, hZr⟩ : ∃ Zr : ℝ≥0∞, Zr = ∫⁻ x, ENNReal.ofReal (d1_gibbsWeight κ U x) := ⟨_, rfl⟩
  have hrawU : d1_gibbsRaw κ U Set.univ = Zr := by
    rw [hZr]; unfold d1_gibbsRaw; rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hPdef : d1_gibbsMeasure κ U = Zr⁻¹ • d1_gibbsRaw κ U := by rw [hZr]; rfl
  have h1 : Zr⁻¹ * Zr = 1 := by
    have := measure_univ (μ := d1_gibbsMeasure κ U)
    rwa [hPdef, Measure.smul_apply, smul_eq_mul, hrawU] at this
  have hZ0 : Zr ≠ 0 := by intro h; rw [h] at h1; simp at h1
  have hZt : Zr ≠ ⊤ := by intro h; rw [h] at h1; simp at h1
  have hrawP : d1_gibbsRaw κ U = Zr • d1_gibbsMeasure κ U := by
    rw [hPdef, smul_smul, ENNReal.mul_inv_cancel hZ0 hZt, one_smul]
  have hmU : Measurable fun x => ENNReal.ofReal (d1_gibbsWeight κ U x) :=
    (d1c_gibbs_continuous hU).measurable.ennreal_ofReal
  have hg : Measurable fun x => ENNReal.ofReal (Real.exp (ψ x)) :=
    (Real.continuous_exp.comp hψ).measurable.ennreal_ofReal
  have hw : ∀ x, d1_gibbsWeight κ (d3_tiltPot κ U ψ) x = d1_gibbsWeight κ U x * Real.exp (ψ x) := by
    intro x
    unfold d1_gibbsWeight d3_tiltPot
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hrawV : d1_gibbsRaw κ (d3_tiltPot κ U ψ) =
      (d1_gibbsRaw κ U).withDensity fun x => ENNReal.ofReal (Real.exp (ψ x)) := by
    unfold d1_gibbsRaw
    rw [← withDensity_mul _ hmU hg]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (d1c_gibbs_nonneg κ U x), hw x]
  set Φ : Measure (Torus n) := (d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (Real.exp (ψ x))
    with hΦ
  have hrawV' : d1_gibbsRaw κ (d3_tiltPot κ U ψ) = Zr • Φ := by
    rw [hrawV, hrawP, withDensity_smul_measure]
  have hΦuniv : Φ Set.univ = ENNReal.ofReal (∫ x, Real.exp (ψ x) ∂(d1_gibbsMeasure κ U)) :=
    d3a_mass_eq (Real.continuous_exp.comp hψ) (fun x => (Real.exp_pos _).le)
  have hI : 0 < ∫ x, Real.exp (ψ x) ∂(d1_gibbsMeasure κ U) :=
    integral_exp_pos (d3a_hint _ (Real.continuous_exp.comp hψ))
  have hZv : (∫⁻ x, ENNReal.ofReal (d1_gibbsWeight κ (d3_tiltPot κ U ψ) x)) = Zr * Φ Set.univ := by
    have : d1_gibbsRaw κ (d3_tiltPot κ U ψ) Set.univ =
        ∫⁻ x, ENNReal.ofReal (d1_gibbsWeight κ (d3_tiltPot κ U ψ) x) := by
      unfold d1_gibbsRaw; rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← this, hrawV']; simp
  have hΦ0 : Φ Set.univ ≠ 0 := by rw [hΦuniv]; simpa using hI
  have hΦt : Φ Set.univ ≠ ⊤ := by rw [hΦuniv]; exact ENNReal.ofReal_ne_top
  have hcancel : (Zr * Φ Set.univ)⁻¹ * Zr = (Φ Set.univ)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hZ0) (Or.inl hZt)]
    calc Zr⁻¹ * (Φ Set.univ)⁻¹ * Zr = (Zr⁻¹ * Zr) * (Φ Set.univ)⁻¹ := by ring
      _ = _ := by rw [h1, one_mul]
  have hq : d1_gibbsMeasure κ (d3_tiltPot κ U ψ) = (Φ Set.univ)⁻¹ • Φ := by
    unfold d1_gibbsMeasure
    rw [hZv, hrawV', smul_smul, hcancel]
  rw [hq, hΦuniv, Measure.tilted, hΦ, ← withDensity_smul _ hg]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_inv_of_pos hI, ← ENNReal.ofReal_mul (inv_nonneg.2 hI.le), div_eq_inv_mul]

/-- Entropy relative to a tilted probability measure (forward direction). -/
theorem d3b_klDiv_tilted_fwd {P : Measure (Torus n)} [IsProbabilityMeasure P] {ψ : Torus n → ℝ}
    (hψ : Continuous ψ) {μ : Measure (Torus n)} [IsProbabilityMeasure μ] (h : relEntropy μ P ≠ ⊤) :
    relEntropy μ (P.tilted ψ) ≠ ⊤ ∧
      (relEntropy μ (P.tilted ψ)).toReal =
        (relEntropy μ P).toReal - ∫ x, ψ x ∂μ + Real.log (∫ x, Real.exp (ψ x) ∂P) := by
  have hexp : Integrable (fun x => Real.exp (ψ x)) P := d3a_hint P (Real.continuous_exp.comp hψ)
  haveI : IsProbabilityMeasure (P.tilted ψ) := isProbabilityMeasure_tilted hexp
  have hkl := InformationTheory.klDiv_ne_top_iff.1 h
  have hac' : μ ≪ P.tilted ψ := hkl.1.trans (absolutelyContinuous_tilted hexp)
  have hfμ : Integrable ψ μ := d3a_hint μ hψ
  have hint' := integrable_llr_tilted_right hkl.1 hfμ hkl.2 hexp
  refine ⟨InformationTheory.klDiv_ne_top hac' hint', ?_⟩
  unfold relEntropy
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac' (by simp),
    InformationTheory.toReal_klDiv_of_measure_eq hkl.1 (by simp)]
  exact integral_llr_tilted_right hkl.1 hfμ hexp hkl.2

/-- Finiteness of the entropy is the same for `P` and `P.tilted ψ`. -/
theorem d3b_klDiv_tilted_iff {P : Measure (Torus n)} [IsProbabilityMeasure P] {ψ : Torus n → ℝ}
    (hψ : Continuous ψ) {μ : Measure (Torus n)} [IsProbabilityMeasure μ] :
    relEntropy μ (P.tilted ψ) ≠ ⊤ ↔ relEntropy μ P ≠ ⊤ := by
  refine ⟨fun h => ?_, fun h => (d3b_klDiv_tilted_fwd hψ h).1⟩
  have hexp : Integrable (fun x => Real.exp (ψ x)) P := d3a_hint P (Real.continuous_exp.comp hψ)
  haveI : IsProbabilityMeasure (P.tilted ψ) := isProbabilityMeasure_tilted hexp
  have := (d3b_klDiv_tilted_fwd (P := P.tilted ψ) (ψ := -ψ) hψ.neg h).1
  rwa [tilted_neg_same hexp] at this

end HRS
