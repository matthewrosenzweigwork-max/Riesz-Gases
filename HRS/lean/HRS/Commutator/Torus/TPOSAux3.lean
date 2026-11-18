import HRS.Commutator.Torus.TPOSAux2

/-!
# T-POS helpers, part 3: periodisation (unfolding `ℝ^d` integrals over the cell `(0,1]^d`)

`∫_{ℝ^d} F = ∫_{(0,1]^d} ∑_m F(y+m)` (Lebesgue and Bochner versions), the torus integral over the cell,
and for `perio f`: measurability, integrability, mean, Fourier coefficients.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- The cell `(0,1]^d`. -/
def tposCell0 (d : ℕ) : Set (Euc d) := {y | ∀ i, y i ∈ Set.Ioc (0 : ℝ) 1}

/-- The translated cell `m + (0,1]^d`. -/
def tposCell (m : Lattice d) : Set (Euc d) := {y | ∀ i, y i ∈ Set.Ioc (m i : ℝ) (m i + 1)}

lemma tpos_measurable_coord (i : Fin d) : Measurable (fun y : Euc d => y i) := by
  fun_prop

lemma tpos_measurableSet_cell0 : MeasurableSet (tposCell0 d) := by
  have : tposCell0 d = ⋂ i, (fun y : Euc d => y i) ⁻¹' Set.Ioc (0 : ℝ) 1 := by
    ext y; simp [tposCell0]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_Ioc.preimage (tpos_measurable_coord i)

lemma tpos_measurableSet_cell (m : Lattice d) : MeasurableSet (tposCell m) := by
  have : tposCell m = ⋂ i, (fun y : Euc d => y i) ⁻¹' Set.Ioc (m i : ℝ) (m i + 1) := by
    ext y; simp [tposCell]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_Ioc.preimage (tpos_measurable_coord i)

lemma tpos_toEuc_apply (m : Lattice d) (i : Fin d) : (Lattice.toEuc m) i = (m i : ℝ) := rfl

lemma tpos_add_apply (y z : Euc d) (i : Fin d) : (y + z) i = y i + z i := rfl

lemma tpos_cell_translate (m : Lattice d) (y : Euc d) :
    y + Lattice.toEuc m ∈ tposCell m ↔ y ∈ tposCell0 d := by
  simp only [tposCell0, tposCell, Set.mem_setOf_eq, Set.mem_Ioc, tpos_add_apply, tpos_toEuc_apply]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

lemma tpos_cell_disjoint : Pairwise (Function.onFun Disjoint (tposCell (d := d))) := by
  intro m m' hne
  rw [Function.onFun, Set.disjoint_left]
  intro y hy hy'
  apply hne
  funext i
  have h1 := hy i
  have h2 := hy' i
  have a1 : (m i : ℝ) < (m' i : ℝ) + 1 := lt_of_lt_of_le h1.1 h2.2
  have a2 : (m' i : ℝ) < (m i : ℝ) + 1 := lt_of_lt_of_le h2.1 h1.2
  have b1 : m i < m' i + 1 := by exact_mod_cast a1
  have b2 : m' i < m i + 1 := by exact_mod_cast a2
  omega

lemma tpos_cell_cover : (⋃ m : Lattice d, tposCell m) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨fun i => ⌈y i⌉ - 1, fun i => ?_⟩
  refine ⟨?_, ?_⟩
  · have := Int.ceil_lt_add_one (y i)
    push_cast
    linarith
  · have := Int.le_ceil (y i)
    push_cast
    linarith

lemma tpos_cell_preimage (m : Lattice d) :
    (fun y : Euc d => y + Lattice.toEuc m) ⁻¹' tposCell m = tposCell0 d := by
  ext y; exact tpos_cell_translate m y

lemma tpos_lintegral_cell (m : Lattice d) (G : Euc d → ℝ≥0∞) :
    ∫⁻ y in tposCell m, G y = ∫⁻ y in tposCell0 d, G (y + Lattice.toEuc m) := by
  have hmp : MeasurePreserving (fun y : Euc d => y + Lattice.toEuc m) volume volume :=
    measurePreserving_add_right volume _
  have hge : MeasurableEmbedding (fun y : Euc d => y + Lattice.toEuc m) :=
    (MeasurableEquiv.addRight (Lattice.toEuc m)).measurableEmbedding
  rw [← hmp.setLIntegral_comp_preimage_emb hge G (tposCell m), tpos_cell_preimage]

lemma tpos_integral_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : Lattice d)
    (G : Euc d → E) :
    ∫ y in tposCell m, G y = ∫ y in tposCell0 d, G (y + Lattice.toEuc m) := by
  have hmp : MeasurePreserving (fun y : Euc d => y + Lattice.toEuc m) volume volume :=
    measurePreserving_add_right volume _
  have hge : MeasurableEmbedding (fun y : Euc d => y + Lattice.toEuc m) :=
    (MeasurableEquiv.addRight (Lattice.toEuc m)).measurableEmbedding
  rw [← hmp.setIntegral_preimage_emb hge G (tposCell m), tpos_cell_preimage]

lemma tpos_lintegral_unfold (G : Euc d → ℝ≥0∞) :
    ∫⁻ y, G y = ∑' m : Lattice d, ∫⁻ y in tposCell0 d, G (y + Lattice.toEuc m) := by
  have h := lintegral_iUnion (μ := (volume : Measure (Euc d))) tpos_measurableSet_cell
    tpos_cell_disjoint G
  rw [tpos_cell_cover, Measure.restrict_univ] at h
  rw [h]
  exact tsum_congr fun m => tpos_lintegral_cell m G

lemma tpos_integral_unfold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Euc d → E} (hF : Integrable F) :
    ∫ y, F y = ∫ y in tposCell0 d, ∑' m : Lattice d, F (y + Lattice.toEuc m) := by
  have h1 : ∫ y, F y = ∑' m : Lattice d, ∫ y in tposCell m, F y := by
    have h := integral_iUnion (μ := (volume : Measure (Euc d))) (f := F) tpos_measurableSet_cell
      tpos_cell_disjoint (by rw [tpos_cell_cover]; exact hF.integrableOn)
    rw [tpos_cell_cover, Measure.restrict_univ] at h
    exact h
  have h2 : ∑' m : Lattice d, ∫⁻ y in tposCell0 d, ‖F (y + Lattice.toEuc m)‖ₑ ≠ ⊤ := by
    have := tpos_lintegral_unfold (fun y => ‖F y‖ₑ)
    rw [← this]
    exact hF.hasFiniteIntegral.ne
  have hm : ∀ m : Lattice d, AEStronglyMeasurable (fun y => F (y + Lattice.toEuc m))
      (volume.restrict (tposCell0 d)) := fun m =>
    (hF.1.comp_measurePreserving (measurePreserving_add_right volume (Lattice.toEuc m))).restrict
  rw [h1, integral_tsum hm h2]
  exact tsum_congr fun m => tpos_integral_cell m F

/-- The torus integral as an integral over the cell. -/
lemma tpos_torus_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Torus d → E) :
    ∫ x, G x = ∫ y in tposCell0 d, G (Torus.mk y) := by
  have h0 : ∫ x : Torus d, G x = ∫ (x : Fin d → ℝ) in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((fun _ => (0 : ℝ)) i) ((fun _ => (0 : ℝ)) i + 1)}, G fun i => ((x i : ℝ) : UnitAddCircle) := by
    rw [Torus.volume_eq_pi_haar]
    exact UnitAddTorus.integral_preimage G (fun _ => (0 : ℝ))
  rw [h0]
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have hge : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have := hmp.setIntegral_preimage_emb hge (fun v : Fin d → ℝ => G (fun i => ((v i : ℝ) : UnitAddCircle)))
    {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((fun _ => (0 : ℝ)) i) ((fun _ => (0 : ℝ)) i + 1)}
  simp only [zero_add] at this ⊢
  rw [← this]
  rfl

lemma tpos_torus_lintegral (G : Torus d → ℝ≥0∞) :
    ∫⁻ x, G x = ∫⁻ y in tposCell0 d, G (Torus.mk y) := by
  have h0 : ∫⁻ x : Torus d, G x = ∫⁻ (x : Fin d → ℝ) in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((fun _ => (0 : ℝ)) i) ((fun _ => (0 : ℝ)) i + 1)}, G fun i => ((x i : ℝ) : UnitAddCircle) := by
    rw [Torus.volume_eq_pi_haar]
    exact UnitAddTorus.lintegral_preimage G (fun _ => (0 : ℝ))
  rw [h0]
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have hge : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have := hmp.setLIntegral_comp_preimage_emb hge (fun v : Fin d → ℝ => G (fun i => ((v i : ℝ) : UnitAddCircle)))
    {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((fun _ => (0 : ℝ)) i) ((fun _ => (0 : ℝ)) i + 1)}
  simp only [zero_add] at this ⊢
  rw [← this]
  rfl

end HRS.Commutator.TorusNote
