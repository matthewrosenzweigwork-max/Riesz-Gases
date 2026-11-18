import HRS.MS.Fp81S21GaussianPhysicalPackage

/-! Packet 35, unit 8: unconditional assembly, with charts before all radii.
The six radii include source/canonical/quadratic selection, both physical
identifications, and unit 6's intersection of the D/J/Z-fourth moment radii.
Unit 5 has no further radius. All constants precede the shift; the retained
histories are used through unit 6's universal history clause. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Norm-preserving inclusion transports the four supplied integrabilities. -/
private theorem fp81s21_physical35_integrabilities
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D Z : Ω → B) (J : Ω → projTensor B 2)
    (hD : MemLp D 3 P) (hZ : MemLp Z 4 P) (hJ : MemLp J 2 P) :
    Integrable (fun ω => ‖D ω‖) P ∧
    Integrable (fun ω => ‖(J ω : TensorDual B 2)‖) P ∧
    Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P ∧
    Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P := by
  have hJmeas : AEStronglyMeasurable (fun ω => (J ω : TensorDual B 2)) P :=
    continuous_subtype_val.comp_aestronglyMeasurable hJ.aestronglyMeasurable
  have hJval : MemLp (fun ω => (J ω : TensorDual B 2)) 2 P := by
    refine MemLp.of_le (f := fun ω => (J ω : TensorDual B 2)) (g := J) hJ hJmeas ?_
    filter_upwards [] with ω
    exact le_of_eq rfl
  obtain ⟨hDi, hJi, hDmix, hJmix, _, _⟩ :=
    fp81s21_gaussian_correction_integral_certificate
      D Z (fun ω => (J ω : TensorDual B 2)) hD hZ hJval
  exact ⟨hDi, hJi, hDmix, hJmix⟩

/-- The physical Gaussian corrections, with all certificates on one source. -/
theorem fp81s21_gaussian_physical_package (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        Nonempty (fp81s21_Physical35 p R) := by
  let Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4) :=
    Classical.choice (physical_weighted_chart (by have := p.hd; omega)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) p.d]))
  let E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2) :=
    Classical.choice (physical_weighted_chart (by have := p.hd; omega)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) p.d]))
  obtain ⟨δs, hδs, hδshalf, hsrc⟩ := fp81s21_gaussian_source_retained p
  obtain ⟨εG, hεG, hεGlim, δg, hδg, _, hcanon⟩ :=
    fp81s21_gaussian_V2_G_physical p Es E
  obtain ⟨εB, hεB, hεBlim, δb, hδb, _, hquad⟩ :=
    fp81s21_quadraticPhysical31_exists p Es E
  obtain ⟨δD, hδD, _, hD⟩ := fp81s21_gaussian35_D_physical p Es E
  obtain ⟨δJ, hδJ, _, hJ⟩ := fp81s21_gaussian35_J_physical p E
  obtain ⟨δM, hδM, _, hM⟩ := fp81s21_gaussian35_moments p Es E
  refine ⟨min δs (min δg (min δb (min δD (min δJ δM)))),
    lt_min hδs (lt_min hδg (lt_min hδb (lt_min hδD (lt_min hδJ hδM)))),
    (min_le_left _ _).trans hδshalf, ?_⟩
  intro δ hδ hδle R
  have hle : δ ≤ δs ∧ δ ≤ δg ∧ δ ≤ δb ∧ δ ≤ δD ∧ δ ≤ δJ ∧ δ ≤ δM := by
    simpa only [le_min_iff] using hδle
  rcases hle with ⟨hs, hg, hb, hd, hj, hm⟩
  -- Localization constants precede even the retained probability space.
  obtain ⟨Cmix, cdec, hCmix, hcdec, hJbody⟩ := hJ δ hδ hj R
  letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
  obtain ⟨src⟩ := hsrc δ hδ hs R
  letI : IsProbabilityMeasure src.G0.P := src.G0.prob
  obtain ⟨_, _, _, _, MUG, hMUG, canon, _⟩ := hcanon δ hδ hg R
  obtain ⟨S⟩ := hquad δ hδ hb R
  let Q := fp81s21_gaussian35_selection_of_selected Es E src εG εB
    hεG hεGlim hεB hεBlim MUG hMUG canon S
  obtain ⟨cD, KD, cJ, KJ, MD, MJ, MZ, hcD, hKD, hcJ, hKJ, hMD, hMJ, hMZ,
      OD, OJ, hFamilies⟩ :=
    hM δ hδ hm R (hμ₀ := fp81s21_initialMeasure_isProbability p R)
      src εG εB MUG hMUG canon S
  have hMom := hFamilies.2 Q.UB Q.UG Q.hUB Q.hUG
  have hDP := fun (a : ℝ) (ha : 0 ≤ a) =>
    hD δ hδ hd R εB S src.G0 cD KD hcD.le hKD a ha (OD a ha) (Q.UB a ha) (Q.hUB a ha)
  have hJP := fun (a : ℝ) (ha : 0 ≤ a) =>
    hJbody src.G0.P (fp81s21_gaussian_embedFamily p Es E (canon.q src.G0)) MUG
      ((canon.payload src.G0).coefficients.weak_momentRep).1
      a ha cJ KJ hcJ.le hKJ (OJ a ha) (Q.UG a ha) (Q.hUG a ha)
  have hChaos := fp81s21_gaussian35_chaos p Es E R
    (fp81s21_initialMeasure_isProbability p R) src MUG εG εB
    (canon.q src.G0) (canon.payload src.G0) S cD KD cJ KJ OD OJ Q.UB Q.UG Q.hUB Q.hUG
  obtain ⟨hξmeas, hξae, hξstd⟩ := fp81s21_gaussian_source_measurable_coords_std src
  let D := fp81s21_physical35_D Q OD
  let J := fp81s21_physical35_J Q OJ
  let Z := r26t3_Zpath src.G0
  have hMom' : ∀ a : ℝ, 0 ≤ a →
      MemLp (D a) 3 src.G0.P ∧ (∫ ω, ‖D a ω‖ ^ 3 ∂src.G0.P) ≤ MD ∧
      MemLp (J a) 2 src.G0.P ∧ (∫ ω, ‖J a ω‖ ^ 2 ∂src.G0.P) ≤ MJ ∧
      MemLp (Z a) 4 src.G0.P ∧ (∫ ω, ‖Z a ω‖ ^ 4 ∂src.G0.P) ≤ MZ := hMom
  refine ⟨{
    tofp81s21_Gaussian35Selection := Q
    cD := cD, KD := KD, cJ := cJ, KJ := KJ, MD := MD, MJ := MJ, MZ := MZ
    Cmix := Cmix, cdec := cdec
    hcD := hcD, hKD := hKD, hcJ := hcJ, hKJ := hKJ
    hMD := hMD, hMJ := hMJ, hMZ := hMZ, hCmix := hCmix, hcdec := hcdec
    OD := OD, OJ := OJ
    source := ⟨hξstd, hξmeas, hξae⟩
    supplied_half_wick := (S.payload src.G0).1
    T_oscillator := (S.payload src.G0).2.1
    weighted := (fp81s21_gaussian35_source_agreement p Es E R
      (fp81s21_initialMeasure_isProbability p R) src MUG εG εB
      (canon.q src.G0) (canon.payload src.G0) S).1
    DPhysical := fun a ha => (hDP a ha).1
    DRegularity := fun a ha => (hDP a ha).2
    JPhysical := fun a ha => (hJP a ha).1
    JMeasure := fun a ha => (hJP a ha).2.1
    JRegularity := fun a ha => (hJP a ha).2.2.1
    symmetry := ?_
    chaos := ?_
    moments := hMom'
    integrabilities := fun a ha => fp81s21_physical35_integrabilities src.G0.P
      (D a) (Z a) (J a) (hMom' a ha).1 (hMom' a ha).2.2.2.2.1 (hMom' a ha).2.2.1
    mixed_bound := fp81s21_gaussian35_mixed_explicit src.G0.P D J Z MD MJ MZ hMom' }⟩
  · dsimp only
    intro a ha ω M
    simp only [fp81s21_physical35_J, dif_pos ha]
    exact (hJP a ha).2.2.2 (a + p.T) (add_nonneg ha p.hT.le) le_rfl ω M
  · dsimp only
    intro a ha
    simp only [fp81s21_physical35_D, fp81s21_physical35_J, dif_pos ha]
    exact hChaos a ha

#print axioms fp81s21_physical35_integrabilities
#print axioms fp81s21_gaussian_physical_package
end HRS.Fp81.S21
end
