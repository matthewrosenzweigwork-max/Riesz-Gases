import HRS.Torus.Sobolev

/-!
# LEIB-T helpers, part 1: integrals of periodic functions over large boxes

For `η > 0`, `M : ℕ` and `N = (M + 1/2)/η`, the box `(-N, N]^d ⊂ ℝ^d` is a union of `(2M+1)^d` translates (by
`η⁻¹ ℤ^d`) of the cell `η⁻¹ (-1/2, 1/2]^d`; hence for every measurable `Ψ : 𝕋^d → [0,∞]`
`∫_{(-N,N]^d} Ψ(mk(η y)) dy = (2N)^d ∫_{𝕋^d} Ψ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- The cell `m + (-1/2, 1/2]^d`. -/
def leibt_cell (m : Lattice d) : Set (Euc d) := {w | ∀ i, w i ∈ Ioc ((m i : ℝ) - 1 / 2) ((m i : ℝ) + 1 / 2)}

/-- The box `(-N, N]^d`. -/
def leibt_boxN (d : ℕ) (N : ℝ) : Set (Euc d) := {w | ∀ i, w i ∈ Ioc (-N) N}

lemma leibt_measurableSet_pi (a b : Fin d → ℝ) :
    MeasurableSet {w : Euc d | ∀ i, w i ∈ Ioc (a i) (b i)} := by
  have : {w : Euc d | ∀ i, w i ∈ Ioc (a i) (b i)} =
      (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun i : Fin d => Ioc (a i) (b i)) := by
    ext w; simp
  rw [this]
  exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

lemma leibt_measurableSet_cell (m : Lattice d) : MeasurableSet (leibt_cell m) :=
  leibt_measurableSet_pi _ _

lemma leibt_measurableSet_boxN (N : ℝ) : MeasurableSet (leibt_boxN d N) :=
  leibt_measurableSet_pi _ _

lemma leibt_mk_measurePreserving :
    MeasurePreserving (Torus.mk : Euc d → Torus d) (volume.restrict (leibt_cell 0)) volume := by
  have h1 := measurePreserving_pi (fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)))
    (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) (fun _ => UnitAddCircle.measurePreserving_mk (-1 / 2))
  rw [← Measure.restrict_pi_pi] at h1
  have h2 := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (s := Set.pi univ fun _ : Fin d => Ioc (-1 / 2 : ℝ) (-1 / 2 + 1))
    (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc)
  have hc : (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) =
      leibt_cell (0 : Lattice d) := by
    ext w
    simp only [mem_preimage, Set.mem_pi, mem_univ, forall_true_left, leibt_cell, mem_setOf_eq]
    refine forall_congr' fun i => ?_
    simp only [Pi.zero_apply, Int.cast_zero, zero_sub, zero_add, mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  rw [hc] at h2
  exact h1.comp h2

lemma leibt_cell_preimage (m : Lattice d) :
    (fun y : Euc d => y + Lattice.toEuc m) ⁻¹' leibt_cell m = leibt_cell 0 := by
  ext y
  simp only [mem_preimage, leibt_cell, mem_setOf_eq, PiLp.add_apply, Lattice.toEuc, Pi.zero_apply,
    Int.cast_zero, zero_sub, zero_add, mem_Ioc]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

lemma leibt_lintegral_cell (m : Lattice d) (Ψ : Torus d → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ y in leibt_cell m, Ψ (Torus.mk y) = ∫⁻ x, Ψ x := by
  have hmp : MeasurePreserving (fun y : Euc d => y + Lattice.toEuc m) volume volume :=
    measurePreserving_add_right volume _
  have hge : MeasurableEmbedding (fun y : Euc d => y + Lattice.toEuc m) :=
    (MeasurableEquiv.addRight (Lattice.toEuc m)).measurableEmbedding
  have h1 : ∫⁻ y in leibt_cell m, Ψ (Torus.mk y) =
      ∫⁻ y in leibt_cell 0, Ψ (Torus.mk (y + Lattice.toEuc m)) := by
    rw [← hmp.setLIntegral_comp_preimage_emb hge (fun y => Ψ (Torus.mk y)) (leibt_cell m),
      leibt_cell_preimage]
  rw [h1]
  have h2 : ∀ y : Euc d, Torus.mk (y + Lattice.toEuc m) = Torus.mk y := fun y => by
    rw [HRS.Torus.mk_add, HRS.Torus.mk_toEuc, add_zero]
  simp_rw [h2]
  have := leibt_mk_measurePreserving (d := d)
  rw [← this.lintegral_comp hΨ]

lemma leibt_cell_disjoint : Pairwise (Function.onFun Disjoint (leibt_cell (d := d))) := by
  intro m m' hne
  rw [Function.onFun, Set.disjoint_left]
  intro y hy hy'
  apply hne
  funext i
  have h1 := hy i
  have h2 := hy' i
  have a1 : (m i : ℝ) < (m' i : ℝ) + 1 := by linarith [h1.1, h2.2]
  have a2 : (m' i : ℝ) < (m i : ℝ) + 1 := by linarith [h2.1, h1.2]
  have b1 : m i < m' i + 1 := by exact_mod_cast a1
  have b2 : m' i < m i + 1 := by exact_mod_cast a2
  omega

lemma leibt_boxN_eq_biUnion (M : ℕ) :
    leibt_boxN d ((M : ℝ) + 1 / 2) =
      ⋃ m ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M : ℤ)) M), leibt_cell m := by
  ext w
  simp only [leibt_boxN, mem_setOf_eq, mem_iUnion, Fintype.mem_piFinset, Finset.mem_Icc, exists_prop]
  constructor
  · intro hw
    refine ⟨fun i => ⌈w i - 1 / 2⌉, fun i => ?_, fun i => ?_⟩
    · show -(M : ℤ) ≤ ⌈w i - 1 / 2⌉ ∧ ⌈w i - 1 / 2⌉ ≤ M
      have h1 := (hw i).1
      have h2 := (hw i).2
      have a1 := Int.le_ceil (w i - 1 / 2)
      have a2 := Int.ceil_lt_add_one (w i - 1 / 2)
      constructor
      · have : (-(M : ℝ) - 1 : ℝ) < (⌈w i - 1 / 2⌉ : ℝ) := by linarith
        have : -(M : ℤ) - 1 < ⌈w i - 1 / 2⌉ := by exact_mod_cast this
        omega
      · have : (⌈w i - 1 / 2⌉ : ℝ) < (M : ℝ) + 1 := by linarith
        have : ⌈w i - 1 / 2⌉ < (M : ℤ) + 1 := by exact_mod_cast this
        omega
    · show _ < w i ∧ w i ≤ _
      have a1 := Int.le_ceil (w i - 1 / 2)
      have a2 := Int.ceil_lt_add_one (w i - 1 / 2)
      constructor <;> linarith
  · rintro ⟨m, hm, hw⟩ i
    have h1 := (hm i).1
    have h2 := (hm i).2
    have h1' : (-(M : ℝ)) ≤ (m i : ℝ) := by exact_mod_cast h1
    have h2' : (m i : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
    have := hw i
    constructor <;> linarith [this.1, this.2]

lemma leibt_lintegral_box (M : ℕ) (Ψ : Torus d → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ y in leibt_boxN d ((M : ℝ) + 1 / 2), Ψ (Torus.mk y) =
      ENNReal.ofReal ((2 * (M : ℝ) + 1) ^ d) * ∫⁻ x, Ψ x := by
  classical
  rw [leibt_boxN_eq_biUnion]
  rw [lintegral_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun m _ => leibt_lintegral_cell m Ψ hΨ), Finset.sum_const,
      Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
    rw [this, ENNReal.ofReal_pow (by positivity)]
    congr 2
    rw [show (2 * (M : ℝ) + 1) = ((2 * M + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
    exact Nat.cast_pow _ _
  · intro m _ m' _ hne
    exact leibt_cell_disjoint hne
  · intro m _
    exact leibt_measurableSet_cell m


lemma leibt_boxN_preimage {η : ℝ} (hη : 0 < η) (M : ℕ) :
    leibt_boxN d (((M : ℝ) + 1 / 2) / η) = (fun y : Euc d => η • y) ⁻¹' leibt_boxN d ((M : ℝ) + 1 / 2) := by
  ext y
  simp only [leibt_boxN, mem_setOf_eq, mem_preimage, PiLp.smul_apply, smul_eq_mul, mem_Ioc]
  refine forall_congr' fun i => ?_
  rw [← neg_div, div_lt_iff₀ hη, le_div_iff₀ hη, mul_comm (y.ofLp i)]

lemma leibt_lintegral_boxN {η : ℝ} (hη : 0 < η) (M : ℕ) (Ψ : Torus d → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ y in leibt_boxN d (((M : ℝ) + 1 / 2) / η), Ψ (Torus.mk (η • y)) =
      ENNReal.ofReal ((2 * (((M : ℝ) + 1 / 2) / η)) ^ d) * ∫⁻ x, Ψ x := by
  set B := leibt_boxN d ((M : ℝ) + 1 / 2) with hB
  have hBm : MeasurableSet B := leibt_measurableSet_boxN _
  have hg : Measurable (fun y : Euc d => Ψ (Torus.mk y)) := hΨ.comp HRS.Torus.continuous_mk.measurable
  have hT : Measurable (fun y : Euc d => η • y) := measurable_const_smul η
  rw [leibt_boxN_preimage hη M]
  have h1 : ∫⁻ y in (fun y : Euc d => η • y) ⁻¹' B, Ψ (Torus.mk (η • y)) =
      ∫⁻ y, (B.indicator (fun z => Ψ (Torus.mk z))) (η • y) := by
    rw [← lintegral_indicator (hT hBm)]
    congr 1
  rw [h1, ← lintegral_map (hg.indicator hBm) hT, Measure.map_addHaar_smul volume hη.ne']
  rw [lintegral_smul_measure, lintegral_indicator hBm, leibt_lintegral_box M Ψ hΨ, smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity)]
  have : (2 * (M : ℝ) + 1) = 2 * ((M : ℝ) + 1 / 2) := by ring
  rw [this, mul_pow, mul_pow, div_pow]
  field_simp

end HRS.Commutator.TorusNote
