import HRS.Energy.Commutator.RenormRep

/-!
# Route S, packet S4: the slice force and the smeared charges satisfy the hypotheses of `RenormAlg`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- `|sgc j l z| ≤ M / (4π²)` away from the origin, uniformly in `l ≥ 0`. -/
theorem abs_sgc_bdd_away {l : ℝ} (hl : 0 ≤ l) {δ : ℝ} (hδ : 0 < δ) (j : Fin d) :
    ∃ B : ℝ, ∀ z : Torus d, δ ≤ KernelGrad.tdist z 0 → |SliceAux.sgc j l z| ≤ B := by
  obtain ⟨M, hM0, hMb⟩ := SliceAux.psiG_bound_unif (d := d) j hδ
  refine ⟨M / (4 * Real.pi ^ 2), fun z hz => ?_⟩
  set x := KernelGrad.centeredRep z with hx
  have hxz : Torus.mk x = z := KernelGrad.mk_centeredRep z
  have hxb : ∀ i, |x i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le z
  have hxn : δ ≤ ‖x‖ := by rw [hx, EnergyAux.norm_centeredRep_eq]; exact hz
  have hc : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp ((-(4 * Real.pi ^ 2)) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(4 * Real.pi ^ 2) < 0) 0).const_mul M
  have hval : ∫ t in Ioi (0 : ℝ), M * Real.exp ((-(4 * Real.pi ^ 2)) * t) = M / (4 * Real.pi ^ 2) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(4 * Real.pi ^ 2) < 0) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  unfold SliceAux.sgc
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hint ?_).trans (le_of_eq hval)
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := hMb x hxb hxn (4 * Real.pi ^ 2 * t) (by positivity)
  rw [hxz] at this
  calc Real.exp (-l * t) * |KernelAux.psiG j z (4 * Real.pi ^ 2 * t)|
      ≤ 1 * (M * Real.exp (-(4 * Real.pi ^ 2 * t))) := by
        refine mul_le_mul ?_ this (abs_nonneg _) zero_le_one
        rw [Real.exp_le_one_iff]; nlinarith
    _ = M * Real.exp ((-(4 * Real.pi ^ 2)) * t) := by rw [one_mul]; congr 2; ring

theorem sgv_bdd_away {l : ℝ} (hl : 0 ≤ l) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, ∀ z : Torus d, δ ≤ KernelGrad.tdist z 0 → ‖SliceAux.sgv l z‖ ≤ B := by
  choose B hB using fun j : Fin d => abs_sgc_bdd_away hl hδ j
  refine ⟨∑ j, B j, fun z hz => ?_⟩
  exact (SliceAux.norm_sgv_le l z).trans (Finset.sum_le_sum fun j _ => hB j z hz)


theorem sgv_integrable {l : ℝ} (hl : 0 ≤ l) : Integrable (SliceAux.sgv l : Torus d → Euc d) volume := by
  have hm : Measurable (SliceAux.sgv l : Torus d → Euc d) :=
    (SliceAux.measurable_sgv (d := d)).comp (measurable_const.prodMk measurable_id)
  refine Integrable.mono' (integrable_finsetSum (Finset.univ : Finset (Fin d))
    (fun j _ => (RoughKernel.integrable_sgc j hl).abs)) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  exact SliceAux.norm_sgv_le l z

theorem measurable_sgv_l (l : ℝ) : Measurable (SliceAux.sgv l : Torus d → Euc d) :=
  (SliceAux.measurable_sgv (d := d)).comp (measurable_const.prodMk measurable_id)

theorem hasFDerivAt_lift_sliceG {l : ℝ} (hl : 0 ≤ l) {y : Euc d} (hy : Torus.mk y ≠ 0) :
    HasFDerivAt (Torus.lift (sliceG d l))
      (∑ j, SliceAux.sgv l (Torus.mk y) j • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) y := by
  have h := SliceAux.hasFDerivAt_slice (d := d) hl hy
  exact h

theorem hasFDerivAt_lift_sliceGfull {l : ℝ} (hl : 0 ≤ l) {y : Euc d} (hy : Torus.mk y ≠ 0) :
    HasFDerivAt (Torus.lift (sliceGfull d l))
      (∑ j, SliceAux.sgv l (Torus.mk y) j • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) y :=
  (hasFDerivAt_lift_sliceG hl hy).add_const (1 / l)

theorem sliceGfull_bdd_away {l : ℝ} (hl : 0 ≤ l) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, ∀ z : Torus d, δ ≤ KernelGrad.tdist z 0 → |sliceGfull d l z| ≤ B := by
  obtain ⟨B, hB⟩ := EnergyAux.sliceG_bdd_away (d := d) hl hδ
  refine ⟨B + |1 / l|, fun z hz => ?_⟩
  unfold sliceGfull
  exact (abs_add_le _ _).trans (add_le_add (hB z hz) le_rfl)


/-! ### The translated charges -/

/-- The smeared charge of the slice `l > 0`, centred at `a`. -/
def chS (d : ℕ) (l η : ℝ) (a : Torus d) : Measure (Torus d) := (smearT d l η).map (fun y => y + a)

/-- The sphere charge of the Coulomb slice, centred at `a`. -/
def chC (d : ℕ) (η : ℝ) (a : Torus d) : Measure (Torus d) := (sphereT d η).map (fun y => y + a)

theorem chS_eq (d : ℕ) (l η : ℝ) (a : Torus d) : chS d l η a = (smearT d l η).map (fun y => y + a) := rfl

theorem isFiniteMeasure_chS (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d) :
    IsFiniteMeasure (chS d l η a) := by
  have := (smearT_structure hd hl hη hη2).1
  unfold chS; infer_instance

theorem isFiniteMeasure_chC (hd : 1 ≤ d) (η : ℝ) (a : Torus d) : IsFiniteMeasure (chC d η a) := by
  have := EnergyAux.isProbabilityMeasure_sphereT hd η
  unfold chC; infer_instance

theorem chS_supp (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d) :
    ∀ᵐ x ∂(chS d l η a), KernelGrad.tdist x a ≤ η := by
  unfold chS
  rw [show (fun y : Torus d => y + a) = ⇑(MeasurableEquiv.addRight a) from rfl,
    (MeasurableEquiv.addRight a).measurableEmbedding.ae_map_iff]
  filter_upwards [EnergyAux.ae_tdist_le hd hl hη hη2] with x hx
  show KernelGrad.tdist (x + a) a ≤ η
  rw [EnergyAux.tdist_def, add_sub_cancel_right]; exact hx

theorem chC_supp (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d) :
    ∀ᵐ x ∂(chC d η a), KernelGrad.tdist x a ≤ η := by
  unfold chC
  rw [show (fun y : Torus d => y + a) = ⇑(MeasurableEquiv.addRight a) from rfl,
    (MeasurableEquiv.addRight a).measurableEmbedding.ae_map_iff]
  filter_upwards [EnergyAux.ae_tdist_sphereT hd hη hη2] with x hx
  show KernelGrad.tdist (x + a) a ≤ η
  rw [EnergyAux.tdist_def, add_sub_cancel_right]; exact hx.le

theorem chS_newton (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d)
    {z : Torus d} (hz : η < KernelGrad.tdist z a) :
    ∫ x, sliceGfull d l (z - x) ∂(chS d l η a) = sliceGfull d l (z - a) + 0 := by
  have hz0 : z - a ≠ 0 := by
    refine EnergyAux.ne_zero_of_tdist_pos ?_
    rw [← EnergyAux.tdist_def]; linarith
  unfold chS
  rw [show (fun y : Torus d => y + a) = ⇑(MeasurableEquiv.addRight a) from rfl,
    (MeasurableEquiv.addRight a).measurableEmbedding.integral_map]
  have e : ∀ u : Torus d, sliceGfull d l (z - (MeasurableEquiv.addRight a) u) = sliceGfull d l ((z - a) - u) := by
    intro u
    show sliceGfull d l (z - (u + a)) = _
    congr 1; abel
  simp_rw [e]
  rw [sliceGfull_conv_smear hd hl hη hη2 (z - a) hz0]
  have hf : fTrunc d l η (z - a) = 0 := by
    refine (fTrunc_support hd hl hη hη2).2.1 _ ?_
    rw [EnergyAux.norm_centeredRep_eq, ← EnergyAux.tdist_def]; linarith
  rw [hf]; ring

theorem chC_newton (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d)
    {z : Torus d} (hz : η < KernelGrad.tdist z a) :
    ∫ x, sliceG d 0 (z - x) ∂(chC d η a) = sliceG d 0 (z - a) + η ^ 2 / (2 * d) := by
  have hz0 : z - a ≠ 0 := by
    refine EnergyAux.ne_zero_of_tdist_pos ?_
    rw [← EnergyAux.tdist_def]; linarith
  unfold chC
  rw [show (fun y : Torus d => y + a) = ⇑(MeasurableEquiv.addRight a) from rfl,
    (MeasurableEquiv.addRight a).measurableEmbedding.integral_map]
  have e : ∀ u : Torus d, sliceG d 0 (z - (MeasurableEquiv.addRight a) u) = sliceG d 0 ((z - a) - u) := by
    intro u
    show sliceG d 0 (z - (u + a)) = _
    congr 1; abel
  simp_rw [e]
  rw [sliceG0_conv_sphere hd hη hη2 (z - a) hz0]
  have hf : fTrunc0 d η (z - a) = 0 := by
    refine EnergyAux.fTrunc0_eq_zero hd hη ?_
    rw [← EnergyAux.tdist_def]; linarith
  rw [hf]; ring


theorem chS_repro (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d)
    {y : Torus d} (hy : η < KernelGrad.tdist y a) :
    ∫ x, SliceAux.sgv l (y - x) ∂(chS d l η a) = SliceAux.sgv l (y - a) := by
  haveI := isFiniteMeasure_chS hd hl hη hη2 a
  exact repro_of_newton (G := sliceGfull d l) (w := SliceAux.sgv l) (EnergyAux.measurable_sliceGfull l)
    (measurable_sgv_l l) (fun y hy => hasFDerivAt_lift_sliceGfull hl.le hy)
    (fun δ hδ => sliceGfull_bdd_away hl.le hδ) (fun δ hδ => sgv_bdd_away hl.le hδ) hη.le
    (chS_supp hd hl hη hη2 a) (fun z hz => chS_newton hd hl hη hη2 a hz) hy

theorem chC_repro (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d)
    {y : Torus d} (hy : η < KernelGrad.tdist y a) :
    ∫ x, SliceAux.sgv 0 (y - x) ∂(chC d η a) = SliceAux.sgv 0 (y - a) := by
  haveI := isFiniteMeasure_chC (by omega) η a
  exact repro_of_newton (G := sliceG d 0) (w := SliceAux.sgv 0) (EnergyAux.measurable_sliceG 0)
    (measurable_sgv_l 0) (fun y hy => hasFDerivAt_lift_sliceG le_rfl hy)
    (fun δ hδ => EnergyAux.sliceG_bdd_away le_rfl hδ) (fun δ hδ => sgv_bdd_away le_rfl hδ) hη.le
    (chC_supp (by omega) hη hη2 a) (fun z hz => chC_newton hd hη hη2 a hz) hy

end HRS.Commutator.Renorm
