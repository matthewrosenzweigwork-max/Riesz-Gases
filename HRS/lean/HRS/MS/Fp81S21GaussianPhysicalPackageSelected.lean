import HRS.MS.Fp81S21GaussianPhysicalPackage

/-! Physical Gaussian assembly on a supplied selection.

The charts precede the common radius; the trajectory and the supplied selection
follow it. The two chart equalities merely express that the record uses those
fixed charts. Equality of the entire parent record preserves ALL its fields:
Es, E, src, εG, εB, their four sign/convergence certificates, MUG and its sign,
canon, S, UG, UB, hUG and hUB. In particular no source, family, or history is
selected again. Only the physical operators, constants and certificates are new.

The proposed Rad notation is expanded into its existential-radius telescope to
stay within the audited import closure. No selection-existence radius is needed
because the selection is supplied. The physical identification and moment radii
are intersected before δ, R and Q. For packet 33, the constructor's εG is εAvg
and its εB is the retained εB; its canon and quadratic family remain literal
fields of the extension. The physical operators need not be packet 33's operators.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Norm-preserving inclusion transports the four supplied integrabilities. -/
private theorem fp81s21_physical35_selected_integrabilities
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

/-- Extend every supplied selection on the fixed charts, preserving its entire
parent record, while producing every clause of `Physical35`. -/
theorem fp81s21_gaussian_physical_package_selected
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Gaussian35Selection p R, Q.Es = Es → Q.E = E →
        ∃ P : fp81s21_Physical35 p R, P.tofp81s21_Gaussian35Selection = Q := by
  obtain ⟨δD, hδD, hδDhalf, hD⟩ := fp81s21_gaussian35_D_physical p Es E
  obtain ⟨δJ, hδJ, _, hJ⟩ := fp81s21_gaussian35_J_physical p E
  obtain ⟨δM, hδM, _, hM⟩ := fp81s21_gaussian35_moments p Es E
  refine ⟨min δD (min δJ δM), lt_min hδD (lt_min hδJ hδM),
    (min_le_left _ _).trans hδDhalf, ?_⟩
  intro δ hδ hδle R Q hEs hE
  have hle : δ ≤ δD ∧ δ ≤ δJ ∧ δ ≤ δM := by
    simpa only [le_min_iff] using hδle
  rcases hle with ⟨hd, hj, hm⟩
  subst Es E
  obtain ⟨Cmix, cdec, hCmix, hcdec, hJbody⟩ := hJ δ hδ hj R
  letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
  let src := Q.src
  letI : IsProbabilityMeasure src.G0.P := src.G0.prob
  let εG := Q.εG
  let εB := Q.εB
  let MUG := Q.MUG
  have hMUG : 0 ≤ MUG := Q.MUG_nonneg
  let canon := Q.canon
  let S := Q.S
  obtain ⟨cD, KD, cJ, KJ, MD, MJ, MZ, hcD, hKD, hcJ, hKJ, hMD, hMJ, hMZ,
      OD, OJ, hFamilies⟩ :=
    hM δ hδ hm R (hμ₀ := fp81s21_initialMeasure_isProbability p R)
      src εG εB MUG hMUG canon S
  have hMom := hFamilies.2 Q.UB Q.UG Q.hUB Q.hUG
  have hDP := fun (a : ℝ) (ha : 0 ≤ a) =>
    hD δ hδ hd R εB S src.G0 cD KD hcD.le hKD a ha (OD a ha) (Q.UB a ha) (Q.hUB a ha)
  have hJP := fun (a : ℝ) (ha : 0 ≤ a) =>
    hJbody src.G0.P (fp81s21_gaussian_embedFamily p Q.Es Q.E (canon.q src.G0)) MUG
      ((canon.payload src.G0).coefficients.weak_momentRep).1
      a ha cJ KJ hcJ.le hKJ (OJ a ha) (Q.UG a ha) (Q.hUG a ha)
  have hChaos := fp81s21_gaussian35_chaos p Q.Es Q.E R
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
    weighted := (fp81s21_gaussian35_source_agreement p Q.Es Q.E R
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
    integrabilities := fun a ha => fp81s21_physical35_selected_integrabilities src.G0.P
      (D a) (Z a) (J a) (hMom' a ha).1 (hMom' a ha).2.2.2.2.1 (hMom' a ha).2.2.1
    mixed_bound := fp81s21_gaussian35_mixed_explicit src.G0.P D J Z MD MJ MZ hMom' }, rfl⟩
  · dsimp only
    intro a ha ω M
    simp only [fp81s21_physical35_J, dif_pos ha]
    exact (hJP a ha).2.2.2 (a + p.T) (add_nonneg ha p.hT.le) le_rfl ω M
  · dsimp only
    intro a ha
    simp only [fp81s21_physical35_D, fp81s21_physical35_J, dif_pos ha]
    exact hChaos a ha


#print axioms fp81s21_physical35_selected_integrabilities
#print axioms fp81s21_gaussian_physical_package_selected
end HRS.Fp81.S21
end
