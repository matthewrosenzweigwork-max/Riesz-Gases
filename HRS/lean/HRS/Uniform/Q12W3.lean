import HRS.Uniform.Q12W2

/-!
# Q12, part W3: the density of a smeared measure
-/

noncomputable section

open HRS MeasureTheory Filter Topology
open HRS.CoercAux
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- The density `z ↦ ∫ K_t(z - y) dν(y)` of `ν * K_t`. -/
def smearDens (d : ℕ) (t : ℝ) (ν : Measure (Torus d)) (z : Torus d) : ℝ :=
  ∫ y, heatK d t (z - y) ∂ν

lemma q12_continuous_kernel {t : ℝ} (ht : 0 < t) :
    Continuous fun p : Torus d × Torus d => heatK d t (p.1 - p.2) :=
  (continuous_heatK ht).comp (continuous_fst.sub continuous_snd)

lemma q12_ofReal_smearDens {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
    (z : Torus d) :
    ENNReal.ofReal (smearDens d t ν z) = ∫⁻ y, ENNReal.ofReal (heatK d t (z - y)) ∂ν := by
  unfold smearDens
  have hint : Integrable (fun y => heatK d t (z - y)) ν :=
    ((continuous_heatK ht).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => heatK_nonneg ht _)

lemma q12_smearM_eq {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    smearM d t ν = withDensityReal (smearDens d t ν) := by
  haveI := q12_kerMeasure_prob (d := d) ht
  ext A hA
  have hm : Measurable fun p : Torus d × Torus d => p.1 + p.2 := by fun_prop
  unfold smearM withDensityReal
  rw [Measure.map_apply hm hA, withDensity_apply _ hA]
  rw [Measure.prod_apply (hm hA)]
  -- inner measure
  have hinner : ∀ y : Torus d, kerMeasure d t (Prod.mk y ⁻¹' ((fun p : Torus d × Torus d => p.1 + p.2) ⁻¹' A)) =
      ∫⁻ z in A, ENNReal.ofReal (heatK d t (z - y)) := by
    intro y
    have hB : MeasurableSet (Prod.mk y ⁻¹' ((fun p : Torus d × Torus d => p.1 + p.2) ⁻¹' A)) :=
      measurable_prodMk_left (hm hA)
    unfold kerMeasure
    rw [withDensity_apply _ hB]
    have e1 : ∫⁻ ξ in Prod.mk y ⁻¹' ((fun p : Torus d × Torus d => p.1 + p.2) ⁻¹' A),
        ENNReal.ofReal (heatK d t ξ) =
        ∫⁻ ξ, A.indicator (fun z => ENNReal.ofReal (heatK d t (z - y))) (y + ξ) := by
      rw [← lintegral_indicator hB]
      refine lintegral_congr fun ξ => ?_
      by_cases h : y + ξ ∈ A
      · have h' : ξ ∈ Prod.mk y ⁻¹' ((fun p : Torus d × Torus d => p.1 + p.2) ⁻¹' A) := h
        simp [Set.indicator_of_mem h, Set.indicator_of_mem h']
      · have h' : ξ ∉ Prod.mk y ⁻¹' ((fun p : Torus d × Torus d => p.1 + p.2) ⁻¹' A) := h
        simp [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    rw [e1, lintegral_add_left_eq_self (μ := (volume : Measure (Torus d)))
      (A.indicator (fun z => ENNReal.ofReal (heatK d t (z - y)))) y, lintegral_indicator hA]
  simp_rw [hinner]
  have hmeas : Measurable (Function.uncurry fun (y z : Torus d) => ENNReal.ofReal (heatK d t (z - y))) := by
    have : Continuous (Function.uncurry fun (y z : Torus d) => heatK d t (z - y)) :=
      (continuous_heatK ht).comp (continuous_snd.sub continuous_fst)
    exact this.measurable.ennreal_ofReal
  rw [lintegral_lintegral_swap (hmeas.aemeasurable)]
  refine lintegral_congr fun z => ?_
  rw [q12_ofReal_smearDens ht ν z]


lemma q12_smearDens_nonneg {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) (z : Torus d) :
    0 ≤ smearDens d t ν z :=
  integral_nonneg fun y => heatK_nonneg ht _

lemma q12_continuous_smearDens {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    Continuous (smearDens d t ν) := by
  have h := continuous_parametric_integral_of_continuous (μ := ν) (s := (Set.univ : Set (Torus d)))
    (f := fun (z y : Torus d) => heatK d t (z - y)) (q12_continuous_kernel ht) isCompact_univ
  have h' : Continuous fun x : Torus d => ∫ y, heatK d t (x - y) ∂ν := by
    simpa [Measure.restrict_univ] using h
  exact h'

/-- Fubini for the smeared density. -/
lemma q12_integral_smearDens_mul {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
    {G : Torus d → ℂ} (hG : Continuous G) :
    ∫ z, G z * (smearDens d t ν z : ℂ) = ∫ y, (∫ z, G z * (heatK d t (z - y) : ℂ)) ∂ν := by
  have e : ∀ z : Torus d, G z * (smearDens d t ν z : ℂ) = ∫ y, G z * (heatK d t (z - y) : ℂ) ∂ν := by
    intro z
    unfold smearDens
    rw [integral_const_mul, integral_complex_ofReal]
  simp_rw [e]
  have hc : Continuous (Function.uncurry fun (z y : Torus d) => G z * (heatK d t (z - y) : ℂ)) :=
    (hG.comp continuous_fst).mul (Complex.continuous_ofReal.comp (q12_continuous_kernel ht))
  have hint : Integrable (Function.uncurry fun (z y : Torus d) => G z * (heatK d t (z - y) : ℂ))
      ((volume : Measure (Torus d)).prod ν) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact integral_integral_swap hint

lemma q12_integral_kernel_shift {t : ℝ} (ht : 0 < t) (y : Torus d) :
    ∫ z, heatK d t (z - y) = 1 := by
  rw [integral_sub_right_eq_self (fun z => heatK d t z) y, integral_heatK ht]

lemma q12_integral_smearDens {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    ∫ z, smearDens d t ν z = 1 := by
  have h := q12_integral_smearDens_mul ht ν (G := fun _ => (1 : ℂ)) continuous_const
  simp only [one_mul] at h
  have h1 : ∀ y : Torus d, ∫ z, (heatK d t (z - y) : ℂ) = 1 := fun y => by
    rw [integral_complex_ofReal, q12_integral_kernel_shift ht y]; simp
  simp_rw [h1] at h
  rw [integral_complex_ofReal] at h
  simpa using h

lemma q12_isProbDensity_smearDens {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    IsProbDensity (smearDens d t ν) :=
  ⟨q12_smearDens_nonneg ht ν, (q12_continuous_smearDens ht ν).measurable, q12_integral_smearDens ht ν⟩

/-- The Fourier coefficient of a smeared measure. -/
lemma q12_fcoef_smearDens {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
    (k : Lattice d) :
    Torus.fcoef (smearDens d t ν) k =
      (Real.exp (-t * Lattice.enorm k ^ 2) : ℂ) * ∫ y, Torus.mode (-k) y ∂ν := by
  unfold Torus.fcoef
  rw [q12_integral_smearDens_mul ht ν (G := fun z => Torus.mode (-k) z) (Torus.continuous_mode _)]
  have h : ∀ y : Torus d, ∫ z, Torus.mode (-k) z * (heatK d t (z - y) : ℂ) =
      Torus.mode (-k) y * (Real.exp (-t * Lattice.enorm k ^ 2) : ℂ) := by
    intro y
    rw [← integral_add_left_eq_self (μ := (volume : Measure (Torus d)))
      (fun z => Torus.mode (-k) z * (heatK d t (z - y) : ℂ)) y]
    have e : ∀ ξ : Torus d, Torus.mode (-k) (y + ξ) * (heatK d t (y + ξ - y) : ℂ) =
        Torus.mode (-k) y * (Torus.mode (-k) ξ * (heatK d t ξ : ℂ)) := fun ξ => by
      rw [add_sub_cancel_left, Torus.mode_add_arg]; ring
    simp_rw [e]
    rw [integral_const_mul, q12_integral_mode_heatK ht k]
  simp_rw [h]
  rw [integral_mul_const, mul_comm]


lemma q12_integrable_of_isProbDensity {ρ : Torus d → ℝ} (h : IsProbDensity ρ) : Integrable ρ := by
  by_contra hn
  have := h.integral_one
  rw [integral_undef hn] at this
  norm_num at this

lemma q12_smearDens_ge {t : ℝ} (ht : 0 < t) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {m : ℝ}
    (hm : ∀ x, m ≤ ρ x) (z : Torus d) : m ≤ smearDens d t (withDensityReal ρ) z := by
  unfold smearDens withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul (hρ.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ.nonneg _)]
  have hKc : Continuous fun y : Torus d => heatK d t (z - y) :=
    (continuous_heatK ht).comp (continuous_const.sub continuous_id)
  have hK1 : ∫ y, heatK d t (z - y) = 1 := by
    haveI : (volume : Measure (Torus d)).IsNegInvariant :=
      MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
    rw [integral_sub_left_eq_self (fun y => heatK d t y) volume z, integral_heatK ht]
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hKc
  have hi1 : Integrable (fun y => ρ y * heatK d t (z - y)) :=
    (q12_integrable_of_isProbDensity hρ).mul_bdd hKc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa using hM y)
  have hi2 : Integrable (fun y : Torus d => m * heatK d t (z - y)) :=
    (hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul m
  calc m = ∫ y, m * heatK d t (z - y) := by rw [integral_const_mul, hK1, mul_one]
    _ ≤ ∫ y, ρ y * heatK d t (z - y) := integral_mono hi2 hi1 fun y =>
        mul_le_mul_of_nonneg_right (hm y) (heatK_nonneg ht _)

end HRS.Uniform.Q12
