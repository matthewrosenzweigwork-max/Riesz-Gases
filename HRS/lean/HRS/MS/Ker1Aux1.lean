import HRS.Kernel.D1
import HRS.Kernel.GradSmooth
import HRS.Commutator.Torus.TEXTAux2

/-!
# MS-KER1, helper file 1: the torus / unit-cell dictionary
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

namespace HRS.MS.Ker1

variable {d : ℕ}

/-- The cell `(0,1]^d`. -/
def ker1_cell (d : ℕ) : Set (Euc d) := {w | ∀ i, w i ∈ Ioc (0 : ℝ) 1}

theorem ker1_measurableSet_cell : MeasurableSet (ker1_cell d) := by
  have : ker1_cell d = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) 1) := by
    ext w; simp [ker1_cell]
  rw [this]
  exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

theorem ker1_mk_mp :
    MeasurePreserving (Torus.mk : Euc d → Torus d) (volume.restrict (ker1_cell d)) volume := by
  have h1 := measurePreserving_pi (fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + 1)))
    (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) (fun _ => UnitAddCircle.measurePreserving_mk 0)
  rw [← Measure.restrict_pi_pi] at h1
  have h2 := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (s := Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) (0 + 1))
    (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc)
  have hc : (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) (0 + 1)) =
      ker1_cell d := by
    ext w; simp [ker1_cell]
  rw [hc] at h2
  exact h1.comp h2


/-- Integrals over the torus are integrals over the unit cell. -/
theorem ker1_integral_torus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Torus d → E) (hF : AEStronglyMeasurable F volume) :
    ∫ z, F z = ∫ y in ker1_cell d, F (Torus.mk y) := by
  have h := ker1_mk_mp (d := d)
  have h1 : ∫ z, F z = ∫ z, F z ∂(Measure.map (Torus.mk : Euc d → Torus d)
      (volume.restrict (ker1_cell d))) := by rw [h.map_eq]
  rw [h1]
  exact integral_map h.aemeasurable (by rw [h.map_eq]; exact hF)

theorem ker1_integrableOn_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Torus d → E} (hF : Integrable F) :
    IntegrableOn (fun y : Euc d => F (Torus.mk y)) (ker1_cell d) :=
  (ker1_mk_mp.integrable_comp hF.aestronglyMeasurable).2 hF


theorem ker1_mk_add (x y : Euc d) : Torus.mk (x + y) = Torus.mk x + Torus.mk y := by
  funext i; simp [Torus.mk]

theorem ker1_mk_neg (x : Euc d) : Torus.mk (-x) = -Torus.mk x := by
  funext i; simp [Torus.mk]

/-- A function of `mk` with integrable torus profile is integrable on each translated cell. -/
theorem ker1_integrableOn_shift_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Torus d → E} (hF : Integrable F) (a : Euc d) :
    IntegrableOn (fun y : Euc d => F (Torus.mk y))
      {x : Euc d | ∀ i, x i ∈ Ioc (a i) (a i + 1)} := by
  have hFa : Integrable (fun z => F (z + Torus.mk a)) := hF.comp_add_right (Torus.mk a)
  have h1 := ker1_integrableOn_cell hFa
  have hφ := (measurePreserving_add_right (volume : Measure (Euc d)) (-a)).restrict_preimage
    (ker1_measurableSet_cell (d := d))
  have hS : (fun x : Euc d => x + -a) ⁻¹' ker1_cell d =
      {x : Euc d | ∀ i, x i ∈ Ioc (a i) (a i + 1)} := by
    ext x
    simp only [ker1_cell, mem_preimage, mem_setOf_eq, PiLp.add_apply, PiLp.neg_apply, mem_Ioc]
    constructor <;> intro h i <;> have := h i <;> constructor <;> linarith [this.1, this.2]
  rw [hS] at hφ
  have h2 := (hφ.integrable_comp h1.aestronglyMeasurable).2 h1
  have heq : ((fun y : Euc d => F (Torus.mk y + Torus.mk a)) ∘ fun x : Euc d => x + -a) =
      fun y : Euc d => F (Torus.mk y) := by
    funext x
    simp only [Function.comp_apply]
    rw [← ker1_mk_add, neg_add_cancel_right]
  rw [heq] at h2
  exact h2

theorem ker1_locInt_comp_mk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Torus d → E} (hF : Integrable F) :
    LocallyIntegrable (fun y : Euc d => F (Torus.mk y)) volume := by
  intro x₀
  refine ⟨Metric.ball x₀ (1 / 2), Metric.ball_mem_nhds _ (by norm_num), ?_⟩
  refine (ker1_integrableOn_shift_cell hF (WithLp.toLp 2 fun i => x₀ i - 1 / 2)).mono_set ?_
  intro x hx i
  have h1 : |x i - x₀ i| ≤ ‖x - x₀‖ := by
    have := PiLp.norm_apply_le (x - x₀) i
    simpa [Real.norm_eq_abs] using this
  have h2 : ‖x - x₀‖ < 1 / 2 := by simpa [dist_eq_norm] using hx
  have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
  simp only [mem_Ioc]
  constructor <;> simp <;> linarith [h3.1, h3.2]


theorem ker1_locInt_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E}
    (hf : LocallyIntegrable f volume) {c : ℝ} (hc : c ≠ 0) :
    LocallyIntegrable (fun x => f (c • x)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hcK : IsCompact (c • K) := hK.image (continuous_const_smul c)
  have h1 : Integrable ((c • K).indicator f) volume :=
    (integrable_indicator_iff hcK.measurableSet).mpr (hf.integrableOn_isCompact hcK)
  have h2 := h1.comp_smul hc
  refine (integrable_indicator_iff hK.measurableSet).mp ?_
  convert h2 using 1
  funext x
  by_cases hx : x ∈ K
  · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((smul_mem_smul_set_iff₀ hc K x).2 hx)]
  · simp [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx ((smul_mem_smul_set_iff₀ hc K x).1 h))]


/-- The half-open box `[0,L)^d` (definitionally `HRS.Whole.AppendixALemmas.periodBox d L`). -/
def ker1_box (d : ℕ) (L : ℝ) : Set (Euc d) := {x | ∀ i, 0 ≤ x i ∧ x i < L}

theorem ker1_hyperplane_null (i : Fin d) (c : ℝ) : volume {x : Euc d | x i = c} = 0 := by
  have h := PiLp.volume_preserving_ofLp (Fin d)
  have h1 : {x : Euc d | x i = c} = (fun w : Euc d => w.ofLp) ⁻¹' {f : Fin d → ℝ | f i = c} := rfl
  have hm : MeasurableSet {f : Fin d → ℝ | f i = c} :=
    (measurableSet_singleton c).preimage (measurable_pi_apply i)
  rw [h1, h.measure_preimage hm.nullMeasurableSet]
  exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i c

theorem ker1_box_ae_cell : ker1_box d 1 =ᵐ[volume] ker1_cell d := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (t := ⋃ i : Fin d, {x : Euc d | x i = 0}) ?_
      (measure_iUnion_null fun i => ker1_hyperplane_null i 0)
    intro x ⟨hx, hx'⟩
    simp only [ker1_cell, mem_setOf_eq, mem_Ioc, not_forall, not_and, not_le] at hx hx'
    obtain ⟨i, hi⟩ := hx'
    simp only [mem_iUnion, mem_setOf_eq]
    refine ⟨i, ?_⟩
    have h1 := hx i
    by_contra hne
    have h0 : 0 < x i := lt_of_le_of_ne h1.1 (Ne.symm hne)
    linarith [hi h0, h1.2]
  · refine measure_mono_null (t := ⋃ i : Fin d, {x : Euc d | x i = 1}) ?_
      (measure_iUnion_null fun i => ker1_hyperplane_null i 1)
    intro x ⟨hx, hx'⟩
    simp only [ker1_box, mem_setOf_eq, not_forall, not_and, not_lt] at hx hx'
    obtain ⟨i, hi⟩ := hx'
    simp only [mem_iUnion, mem_setOf_eq]
    refine ⟨i, ?_⟩
    have h1 := hx i
    by_contra hne
    have := hi h1.1.le
    exact absurd (lt_of_le_of_ne h1.2 hne) (not_lt.2 this)

theorem ker1_setIntegral_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euc d → E)
    {L : ℝ} (hL : 0 < L) :
    ∫ x in ker1_box d L, f x = L ^ d • ∫ y in ker1_cell d, f (L • y) := by
  have hbox : ker1_box d L = L • ker1_box d 1 := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem₀ hL.ne']
    simp only [ker1_box, mem_setOf_eq, PiLp.smul_apply, smul_eq_mul]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mul_nonneg (inv_nonneg.2 hL.le) h1, by
        rw [inv_mul_lt_iff₀ hL]; linarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · exact (mul_nonneg_iff_of_pos_left (inv_pos.2 hL)).1 h1
      · rw [inv_mul_lt_iff₀ hL] at h2; linarith
  have h1 := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (volume : Measure (Euc d)) f
    (ker1_box d 1) hL
  rw [finrank_euclideanSpace_fin, ← hbox] at h1
  rw [setIntegral_congr_set ker1_box_ae_cell] at h1
  rw [h1, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]


/-- the section `Torus d → (0,1]^d` of `mk` -/
def ker1_r (z : Torus d) : Euc d :=
  WithLp.toLp 2 fun i => ((AddCircle.equivIoc (1 : ℝ) 0 (z i) : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ)

theorem ker1_mk_r (z : Torus d) : Torus.mk (ker1_r z) = z := by
  funext i
  simp only [Torus.mk, ker1_r]
  exact AddCircle.coe_equivIoc

theorem ker1_r_mem (z : Torus d) : ker1_r z ∈ ker1_cell d := by
  intro i
  have := (AddCircle.equivIoc (1 : ℝ) 0 (z i)).2
  simpa [ker1_r] using this

theorem ker1_r_mp :
    MeasurePreserving (ker1_r : Torus d → Euc d) volume (volume.restrict (ker1_cell d)) := by
  have h1 : MeasurePreserving (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => (0 : ℝ)))
      (volume : Measure (Torus d)) (Measure.comap Subtype.val volume) := by
    rw [Torus.volume_eq_pi_haar]
    exact UnitAddTorus.measurePreserving_equivPiIoc _
  have hs : MeasurableSet {x : Fin d → ℝ | ∀ i, x i ∈ Ioc ((fun _ : Fin d => (0 : ℝ)) i)
      ((fun _ : Fin d => (0 : ℝ)) i + 1)} := MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have h2 := measurePreserving_subtype_coe (μa := (volume : Measure (Fin d → ℝ))) hs
  have h3 := (PiLp.volume_preserving_toLp (Fin d)).restrict_preimage
    (s := ker1_cell d) ker1_measurableSet_cell
  have hc : (fun f : Fin d → ℝ => (WithLp.toLp 2 f : Euc d)) ⁻¹' ker1_cell d =
      {x : Fin d → ℝ | ∀ i, x i ∈ Ioc ((fun _ : Fin d => (0 : ℝ)) i)
      ((fun _ : Fin d => (0 : ℝ)) i + 1)} := by
    ext f; simp [ker1_cell]
  rw [hc] at h3
  exact h3.comp (h2.comp h1)


theorem ker1_descent (h : Euc d → ℝ) (hper : ∀ (x : Euc d) (n : Lattice d), h (x + Lattice.toEuc n) = h x)
    (hint : IntegrableOn h (ker1_cell d)) :
    ∃ G : Torus d → ℝ, Integrable G ∧ ∀ y : Euc d, G (Torus.mk y) = h y := by
  refine ⟨h ∘ ker1_r, ?_, fun y => ?_⟩
  · have hmp := ker1_r_mp (d := d)
    exact (hmp.integrable_comp hint.aestronglyMeasurable).2 hint
  · obtain ⟨m, hm⟩ := HRS.KernelGrad.exists_lattice_of_mk_eq (x := ker1_r (Torus.mk y)) (y := y)
      (ker1_mk_r (Torus.mk y))
    simp only [Function.comp_apply]
    rw [hm, hper]

theorem ker1_mode_mk (k : Lattice d) (y : Euc d) :
    Torus.mode k (Torus.mk y) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (k i : ℝ) * y i : ℝ) : ℂ)) := by
  unfold Torus.mode UnitAddTorus.mFourier
  show (∏ i : Fin d, fourier (k i) (((y i : ℝ)) : UnitAddCircle)) = _
  simp_rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem ker1_box_coeff {L : ℝ} (hL : 0 < L) (G : Torus d → ℝ) (hG : Integrable G) (k : Lattice d) :
    ∫ x in ker1_box d L, (G (Torus.mk (L⁻¹ • x)) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ((k i : ℝ) / L) * x i : ℝ) : ℂ))) =
      (L : ℂ) ^ d * ∫ z, Torus.mode (-k) z * (G z : ℂ) := by
  rw [ker1_setIntegral_box _ hL]
  have hint : AEStronglyMeasurable (fun z : Torus d => Torus.mode (-k) z * (G z : ℂ)) volume :=
    (hG.ofReal.bdd_mul (Torus.continuous_mode (-k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-k) x).le)).aestronglyMeasurable
  rw [ker1_integral_torus _ hint]
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  have : ∀ y : Euc d, ((G (Torus.mk (L⁻¹ • L • y)) : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ((k i : ℝ) / L) * (L • y) i : ℝ) : ℂ))) =
      Torus.mode (-k) (Torus.mk y) * (G (Torus.mk y) : ℂ) := by
    intro y
    have hsum : (∑ i, ((k i : ℝ) / L) * (L • y) i) = ∑ i, (k i : ℝ) * y i :=
      Finset.sum_congr rfl fun i _ => by
        simp only [PiLp.smul_apply, smul_eq_mul]; field_simp
    have e1 : (∑ i, (((-k) i : ℤ) : ℝ) * y i) = -(∑ i, (k i : ℝ) * y i) := by
      simp [Finset.sum_neg_distrib]
    rw [ker1_mode_mk, e1, hsum, inv_smul_smul₀ hL.ne', mul_comm]
    congr 2
    push_cast
    ring
  simp_rw [this]
  simp [Algebra.smul_def]

end HRS.MS.Ker1
