import HRS.Energy.Commutator.RenormStjKernel

/-!
# Route S, packet STJ: the slice charges `chS` as `SliceCharges`, and their self energy
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

theorem chS_real_univ (l η : ℝ) (a : Torus d) : (chS d l η a).real univ = mass d l η := by
  unfold chS mass
  rw [measureReal_def, measureReal_def, Measure.map_apply (measurable_add_const a) MeasurableSet.univ,
    Set.preimage_univ]

theorem smearT_atomless (hd : 2 ≤ d) (l : ℝ) {η : ℝ} (hη : 0 < η) (x : Torus d) :
    smearT d l η {x} = 0 := by
  haveI : NullSingletonClass (smearEuc d l η) := ⟨fun z => smearEuc_singleton hd l η hη z⟩
  unfold smearT
  rw [Measure.map_apply Torus.continuous_mk.measurable (measurableSet_singleton x)]
  obtain ⟨y0, hy0⟩ : ∃ y0 : Euc d, Torus.mk y0 = x := ⟨Torus.rep x, Torus.mk_rep x⟩
  have hsub : (Torus.mk ⁻¹' {x} : Set (Euc d)) ⊆ Set.range fun m : Lattice d => y0 + Lattice.toEuc m := by
    intro y hy
    have hy' : Torus.mk y = Torus.mk y0 := by rw [hy0]; exact hy
    obtain ⟨m, hm⟩ := SliceAux.exists_lattice_of_mk_eq hy'
    exact ⟨m, hm.symm⟩
  exact Set.Countable.measure_zero ((Set.countable_range _).mono hsub) _

theorem chS_atom (hd : 2 ≤ d) (l : ℝ) {η : ℝ} (hη : 0 < η) (a x : Torus d) : chS d l η a {x} = 0 := by
  unfold chS
  rw [Measure.map_apply (measurable_add_const a) (measurableSet_singleton _)]
  have : (fun y : Torus d => y + a) ⁻¹' {x} = {x - a} := by
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact (eq_sub_iff_add_eq).symm
  rw [this]
  exact smearT_atomless hd l hη _

theorem chS_Gii (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d) :
    Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((chS d l η a).prod (chS d l η a)) := by
  haveI := isFiniteMeasure_chS hd hl hη hη2 a
  have hmeas : Measurable fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2) :=
    (EnergyAux.measurable_sliceGfull l).comp (measurable_fst.sub measurable_snd)
  have hmeas' : Measurable fun p : Torus d × Torus d => ENNReal.ofReal (sliceGfull d l (p.1 - p.2)) :=
    ENNReal.measurable_ofReal.comp hmeas
  have hfin : ∫⁻ p : Torus d × Torus d, ENNReal.ofReal (sliceGfull d l (p.1 - p.2))
      ∂((chS d l η a).prod (chS d l η a)) < ⊤ := by
    rw [lintegral_prod _ hmeas'.aemeasurable]
    unfold chS
    have := EnergyAux.lintegral_self_shift (d := d) (l := l) (smearT d l η) a
    simp only [] at this ⊢
    rw [this]
    exact (EnergyAux.lintegral_self_le hd hl hη hη2).trans_lt (EnergyAux.lintegral_smearT_g_lt_top hd hl hη hη2)
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => EnergyAux.sliceGfull_nonneg hl _)).mp hfin.ne

theorem sliceCharges_stj (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {N : ℕ} {X : Fin N → Torus d} {η : Fin N → ℝ}
    (hη : ∀ i, 0 < η i ∧ η i < 1 / 2) (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)) :
    SliceCharges l X η (fun i => chS d l (η i) (X i)) :=
  { η0 := fun i => (hη i).1
    fin := fun i => isFiniteMeasure_chS hd hl (hη i).1 (hη i).2 (X i)
    supp := fun i => chS_supp hd hl (hη i).1 (hη i).2 (X i)
    rep := fun i y hy => chS_repro hd hl (hη i).1 (hη i).2 (X i) hy
    sep := hdisj
    atom := fun h2 i x => chS_atom h2 l (hη i).1 (X i) x
    mass_le := fun i => by
      rw [chS_real_univ]; exact mass_le_one hd hl (hη i).1 (hη i).2
    neutral := fun h0 => absurd h0 hl.ne'
    Gii := fun i => chS_Gii hd hl (hη i).1 (hη i).2 (X i) }

/-! ### The self energy -/

theorem integral_sliceGfull_vol (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) :
    ∫ z : Torus d, sliceGfull d l z = 1 / l := by
  have h := EnergyAux.lintegral_sliceGfull hd hl
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => EnergyAux.sliceGfull_nonneg hl z)
    (EnergyAux.measurable_sliceGfull l).aestronglyMeasurable, h]
  exact ENNReal.toReal_ofReal (by positivity)

/-- the (mean-free) self energy `S_l(η) = ∬ G_l dσ dσ - m²/l` of `σ = σ_{l,η}` -/
def Self (d : ℕ) (l η : ℝ) : ℝ :=
  ∫ x, ∫ y, sliceGfull d l (x - y) ∂(smearT d l η) ∂(smearT d l η) - (mass d l η) ^ 2 / l

theorem quadForm_chS_eq (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d) :
    quadForm (fun x y => sliceGfull d l (x - y)) (chS d l η a)
      (ENNReal.ofReal ((chS d l η a).real Set.univ) • (volume : Measure (Torus d))) = Self d l η := by
  haveI := isFiniteMeasure_chS hd hl hη hη2 a
  have hm : (chS d l η a).real Set.univ = mass d l η := chS_real_univ l η a
  set m := mass d l η with hmdef
  have hm0 : 0 ≤ m := mass_nonneg d l η
  rw [hm]
  have hz : ∀ x : Torus d, ∫ y, sliceGfull d l (x - y) ∂(ENNReal.ofReal m • (volume : Measure (Torus d))) = m / l := by
    intro x
    rw [integral_smul_measure, ENNReal.toReal_ofReal hm0, smul_eq_mul,
      integral_sub_left_eq_self (fun z => sliceGfull d l z) volume x, integral_sliceGfull_vol hd hl]
    ring
  unfold quadForm
  simp_rw [hz]
  have hvol : (volume : Measure (Torus d)) univ = 1 := measure_univ
  rw [integral_const, integral_const]
  simp only [smul_eq_mul, Measure.real, Measure.smul_apply, hvol, mul_one, ENNReal.toReal_ofReal hm0]
  rw [show (chS d l η a univ).toReal = m from by rw [← hm]; rfl]
  unfold Self
  have emb := (MeasurableEquiv.addRight a).measurableEmbedding
  have e1 : (fun y : Torus d => y + a) = ⇑(MeasurableEquiv.addRight a) := rfl
  have key : ∀ x : Torus d, ∫ y, sliceGfull d l (x - y) ∂(chS d l η a) =
      ∫ y, sliceGfull d l (x - a - y) ∂(smearT d l η) := by
    intro x
    unfold chS
    rw [e1, emb.integral_map]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show sliceGfull d l (x - (y + a)) = _
    congr 1; abel
  have hlhs : ∫ x, ∫ y, sliceGfull d l (x - y) ∂(chS d l η a) ∂(chS d l η a) =
      ∫ x, ∫ y, sliceGfull d l (x - y) ∂(smearT d l η) ∂(smearT d l η) := by
    simp_rw [key]
    unfold chS
    rw [e1, emb.integral_map]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∫ y, sliceGfull d l (x + a - a - y) ∂(smearT d l η) = _
    simp
  rw [hlhs]
  field_simp
  ring

end HRS.Commutator.Stj
