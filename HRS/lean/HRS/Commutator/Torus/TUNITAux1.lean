import HRS.Commutator.Torus.Defs
import HRS.Commutator.Torus.TENAux3

/-!
# T-UNIT-a helpers, part 1: generic signed-measure facts on `𝕋^d`

Prefix `tunit_`.  Torus analogue of `Whole/DECAux.lean`: linearity of `σ.int`, Fubini swap, pulling inner
products out of `σ.int`, the odd-kernel identity `𝒞_F(w,σ) = 2 σ.int (x ↦ ⟨w x, (F*σ)(x)⟩)`, and the
charge integral `ν.int f = N⁻¹ ∑ f(X_i) - ∫ ρ f` for measurable `f` with `ρ f` integrable.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

theorem tunit_bdd_integrable {α : Type*} [MeasurableSpace α] {m : Measure α} [IsFiniteMeasure m]
    {f : α → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

theorem tunit_int_sub_int (σ : SMT d) {f g : Torus d → ℝ}
    (hfp : Integrable f σ.pos) (hgp : Integrable g σ.pos)
    (hfn : Integrable f σ.neg) (hgn : Integrable g σ.neg) :
    σ.int (fun x => f x - g x) = σ.int f - σ.int g := by
  unfold SMT.int
  rw [integral_sub hfp hgp, integral_sub hfn hgn]
  ring

theorem tunit_int_neg_fun (σ : SMT d) (f : Torus d → ℝ) : σ.int (fun x => -f x) = -σ.int f := by
  unfold SMT.int
  simp only [integral_neg]
  ring

theorem tunit_param_measurable {μ : Measure (Torus d)} [SFinite μ] {J : Torus d → Torus d → ℝ}
    (hJ : Measurable (fun q : Torus d × Torus d => J q.1 q.2)) :
    Measurable (fun x => ∫ y, J x y ∂μ) :=
  (hJ.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem tunit_param_bound {μ : Measure (Torus d)} [IsFiniteMeasure μ] {J : Torus d → Torus d → ℝ}
    (C : ℝ) (hC : ∀ x y, ‖J x y‖ ≤ C) (x : Torus d) : ‖∫ y, J x y ∂μ‖ ≤ C * μ.real Set.univ :=
  norm_integral_le_of_norm_le_const (ae_of_all _ fun y => hC x y)

theorem tunit_param_integrable {μ ν : Measure (Torus d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {J : Torus d → Torus d → ℝ} (hJ : Measurable (fun q : Torus d × Torus d => J q.1 q.2)) (C : ℝ)
    (hC : ∀ x y, ‖J x y‖ ≤ C) : Integrable (fun x => ∫ y, J x y ∂ν) μ :=
  tunit_bdd_integrable (tunit_param_measurable (μ := ν) hJ) _ (tunit_param_bound (μ := ν) C hC)

/-- Expansion of the iterated signed integral of a bounded measurable kernel into four iterated integrals. -/
theorem tunit_int_expand (σ : SMT d) [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg]
    {J : Torus d → Torus d → ℝ} (hJ : Measurable (fun q : Torus d × Torus d => J q.1 q.2)) (C : ℝ)
    (hC : ∀ x y, ‖J x y‖ ≤ C) :
    σ.int (fun x => σ.int (fun y => J x y)) =
      (∫ x, ∫ y, J x y ∂σ.pos ∂σ.pos) - (∫ x, ∫ y, J x y ∂σ.neg ∂σ.pos)
        - (∫ x, ∫ y, J x y ∂σ.pos ∂σ.neg) + (∫ x, ∫ y, J x y ∂σ.neg ∂σ.neg) := by
  have i1 := tunit_param_integrable (μ := σ.pos) (ν := σ.pos) hJ C hC
  have i2 := tunit_param_integrable (μ := σ.pos) (ν := σ.neg) hJ C hC
  have i3 := tunit_param_integrable (μ := σ.neg) (ν := σ.pos) hJ C hC
  have i4 := tunit_param_integrable (μ := σ.neg) (ν := σ.neg) hJ C hC
  unfold SMT.int
  rw [integral_sub i1 i2, integral_sub i3 i4]
  ring

/-- Fubini swap for a bounded measurable kernel on a finite signed measure. -/
theorem tunit_int_int_swap (σ : SMT d) [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg]
    {J : Torus d → Torus d → ℝ} (hJ : Measurable (fun q : Torus d × Torus d => J q.1 q.2)) (C : ℝ)
    (hC : ∀ x y, ‖J x y‖ ≤ C) :
    σ.int (fun x => σ.int (fun y => J x y)) = σ.int (fun y => σ.int (fun x => J x y)) := by
  have hJ' : Measurable (fun q : Torus d × Torus d => (fun a b => J b a) q.1 q.2) :=
    hJ.comp measurable_swap
  have hC' : ∀ a b, ‖(fun a b => J b a) a b‖ ≤ C := fun a b => hC b a
  rw [tunit_int_expand σ hJ C hC, tunit_int_expand σ hJ' C hC']
  have sw : ∀ (m m' : Measure (Torus d)) [IsFiniteMeasure m] [IsFiniteMeasure m'],
      ∫ x, ∫ y, J x y ∂m' ∂m = ∫ y, ∫ x, J x y ∂m ∂m' := by
    intro m m' _ _
    exact integral_integral_swap (tunit_bdd_integrable (m := m.prod m') hJ C (fun q => hC q.1 q.2))
  simp only [sw σ.pos σ.pos, sw σ.pos σ.neg, sw σ.neg σ.pos, sw σ.neg σ.neg]
  ring

/-- Pulling a fixed vector out of a signed integral. -/
theorem tunit_int_inner (σ : SMT d) (c : Euc d) {g : Torus d → Euc d}
    (hgp : Integrable g σ.pos) (hgn : Integrable g σ.neg) :
    σ.int (fun y => inner ℝ c (g y)) = inner ℝ c (σ.intV g) := by
  unfold SMT.int SMT.intV
  rw [integral_inner hgp c, integral_inner hgn c, inner_sub_right]

/-- Oddness of the force turns `σ.intV (x ↦ F(x - y))` into `- σ.intV (z ↦ F(y - z))`. -/
theorem tunit_intV_odd (σ : SMT d) {F : Torus d → Euc d} (hF : ∀ z, F (-z) = -F z) (y : Torus d) :
    σ.intV (fun x => F (x - y)) = -σ.intV (fun z => F (y - z)) := by
  have h : (fun x => F (x - y)) = fun x => -(F (y - x)) := by
    funext x
    rw [← hF, neg_sub]
  rw [h]
  unfold SMT.intV
  simp only [integral_neg]
  abel

/-- The commutator kernel with a fixed `w` splits as a difference of two inner products. -/
theorem tunit_commKer_split (F : Torus d → Euc d) (w : Torus d → Euc d) (x y : Torus d) :
    commKernel F w x y = inner ℝ (w x) (F (x - y)) - inner ℝ (w y) (F (x - y)) := by
  unfold commKernel
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h, inner_sub_left]

set_option maxHeartbeats 1000000 in
/-- The odd-kernel identity: for a finite signed measure `σ`, a bounded odd force `F` and a bounded
`w`, `𝒞_F(w,σ) = 2 σ.int (x ↦ ⟨w x, (F*σ)(x)⟩)`. -/
theorem tunit_pair2_odd (σ : SMT d) [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg]
    {F : Torus d → Euc d} (hFm : Measurable F) (hF : ∀ z, F (-z) = -F z) (CF : ℝ)
    (hFb : ∀ z, ‖F z‖ ≤ CF) {w : Torus d → Euc d} (hwm : Measurable w) (Cw : ℝ)
    (hwb : ∀ x, ‖w x‖ ≤ Cw) :
    σ.pair2 (commKernel F w) =
      2 * σ.int (fun x => inner ℝ (w x) (σ.intV (fun y => F (x - y)))) := by
  have hCw : 0 ≤ Cw := (norm_nonneg _).trans (hwb 0)
  have hFx : Measurable (fun q : Torus d × Torus d => F (q.1 - q.2)) :=
    hFm.comp (measurable_fst.sub measurable_snd)
  set J1 : Torus d → Torus d → ℝ := fun x y => inner ℝ (w x) (F (x - y)) with hJ1
  set J2 : Torus d → Torus d → ℝ := fun x y => inner ℝ (w y) (F (x - y)) with hJ2
  have hJ1m : Measurable (fun q : Torus d × Torus d => J1 q.1 q.2) :=
    (hwm.comp measurable_fst).inner hFx
  have hJ2m : Measurable (fun q : Torus d × Torus d => J2 q.1 q.2) :=
    (hwm.comp measurable_snd).inner hFx
  have hb1 : ∀ x y, ‖J1 x y‖ ≤ Cw * CF := fun x y =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (hwb x) (hFb _) (norm_nonneg _) hCw)
  have hb2 : ∀ x y, ‖J2 x y‖ ≤ Cw * CF := fun x y =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (hwb y) (hFb _) (norm_nonneg _) hCw)
  have hm1 : ∀ x, Measurable (fun y => J1 x y) := fun x => hJ1m.comp measurable_prodMk_left
  have hm2 : ∀ x, Measurable (fun y => J2 x y) := fun x => hJ2m.comp measurable_prodMk_left
  have hFi : ∀ x, Measurable (fun y => F (x - y)) := fun x =>
    hFm.comp (measurable_const.sub measurable_id)
  have hFi' : ∀ y, Measurable (fun x => F (x - y)) := fun y =>
    hFm.comp (measurable_id.sub measurable_const)
  have hFbd : ∀ x y, ‖F (x - y)‖ ≤ CF := fun x y => hFb _
  have hI1 : ∀ x, Integrable (fun y => J1 x y) σ.pos ∧ Integrable (fun y => J1 x y) σ.neg :=
    fun x => ⟨tunit_bdd_integrable (m := σ.pos) (hm1 x) (Cw * CF) (hb1 x),
      tunit_bdd_integrable (m := σ.neg) (hm1 x) (Cw * CF) (hb1 x)⟩
  have hI2 : ∀ x, Integrable (fun y => J2 x y) σ.pos ∧ Integrable (fun y => J2 x y) σ.neg :=
    fun x => ⟨tunit_bdd_integrable (m := σ.pos) (hm2 x) (Cw * CF) (hb2 x),
      tunit_bdd_integrable (m := σ.neg) (hm2 x) (Cw * CF) (hb2 x)⟩
  have hJ1eq : ∀ x, σ.int (fun y => J1 x y) = inner ℝ (w x) (σ.intV (fun y => F (x - y))) :=
    fun x => tunit_int_inner σ (w x)
      (Integrable.of_bound (hFi x).aestronglyMeasurable CF (ae_of_all _ fun y => hFbd x y))
      (Integrable.of_bound (hFi x).aestronglyMeasurable CF (ae_of_all _ fun y => hFbd x y))
  have hJ2eq : ∀ y, σ.int (fun x => J2 x y) = -inner ℝ (w y) (σ.intV (fun z => F (y - z))) := by
    intro y
    rw [tunit_int_inner σ (w y)
      (Integrable.of_bound (hFi' y).aestronglyMeasurable CF (ae_of_all _ fun x => hFbd x y))
      (Integrable.of_bound (hFi' y).aestronglyMeasurable CF (ae_of_all _ fun x => hFbd x y)),
      tunit_intV_odd σ hF y, inner_neg_right]
  have hsub : ∀ x, σ.int (fun y => commKernel F w x y) =
      σ.int (fun y => J1 x y) - σ.int (fun y => J2 x y) := fun x => by
    simp only [tunit_commKer_split]
    exact tunit_int_sub_int σ (hI1 x).1 (hI2 x).1 (hI1 x).2 (hI2 x).2
  have hO1 : Integrable (fun x => σ.int (fun y => J1 x y)) σ.pos := by
    unfold SMT.int
    exact (tunit_param_integrable (μ := σ.pos) (ν := σ.pos) hJ1m _ hb1).sub
      (tunit_param_integrable (μ := σ.pos) (ν := σ.neg) hJ1m _ hb1)
  have hO1' : Integrable (fun x => σ.int (fun y => J1 x y)) σ.neg := by
    unfold SMT.int
    exact (tunit_param_integrable (μ := σ.neg) (ν := σ.pos) hJ1m _ hb1).sub
      (tunit_param_integrable (μ := σ.neg) (ν := σ.neg) hJ1m _ hb1)
  have hO2 : Integrable (fun x => σ.int (fun y => J2 x y)) σ.pos := by
    unfold SMT.int
    exact (tunit_param_integrable (μ := σ.pos) (ν := σ.pos) hJ2m _ hb2).sub
      (tunit_param_integrable (μ := σ.pos) (ν := σ.neg) hJ2m _ hb2)
  have hO2' : Integrable (fun x => σ.int (fun y => J2 x y)) σ.neg := by
    unfold SMT.int
    exact (tunit_param_integrable (μ := σ.neg) (ν := σ.pos) hJ2m _ hb2).sub
      (tunit_param_integrable (μ := σ.neg) (ν := σ.neg) hJ2m _ hb2)
  unfold SMT.pair2
  simp only [hsub]
  rw [tunit_int_sub_int σ hO1 hO2 hO1' hO2', tunit_int_int_swap σ hJ2m (Cw * CF) hb2]
  simp only [hJ1eq, hJ2eq, tunit_int_neg_fun]
  ring

/-! ### The charge integral for unbounded `f` -/

/-- `f ∈ L¹(withDensity (ofReal a))` from `a f ∈ L¹`. -/
theorem tunit_integrable_withDensity_pos {a f : Torus d → ℝ} (ha : Measurable a)
    (haf : Integrable (fun x => a x * f x)) :
    Integrable f (volume.withDensity fun x => ENNReal.ofReal (a x)) := by
  refine (integrable_withDensity_iff_integrable_smul' ha.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).2 ?_
  have : (fun x => (ENNReal.ofReal (a x)).toReal • f x) =
      {x | 0 < a x}.indicator (fun x => a x * f x) := by
    funext x
    by_cases h : 0 < a x
    · rw [Set.indicator_of_mem (show x ∈ {x | 0 < a x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
        max_eq_left h.le]
    · rw [Set.indicator_of_notMem (show x ∉ {x | 0 < a x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
        max_eq_right (not_lt.1 h), zero_mul]
  rw [this]
  exact haf.indicator (measurableSet_lt measurable_const ha)

/-- The charge `ν = μ_N - μ` integrates a measurable `f` with `ρ f ∈ L¹` as `N⁻¹ ∑ f(X_i) - ∫ ρ f`. -/
theorem tunit_charge_int {N : ℕ} (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) (hN : 1 ≤ N) (X : Config d N)
    (f : Torus d → ℝ) (hf : Measurable f) (hfρ : Integrable (fun x => ρ x * f x)) :
    (chargeT X ρ).int f = (1 / (N : ℝ)) * ∑ i, f (X i) - ∫ x, ρ x * f x := by
  have hρm := hρ.measurable
  have hN0 : 0 < N := by omega
  have := HRS.empirical_isProbabilityMeasure hN0 X
  have hIE : Integrable f (HRS.empirical X) := by
    unfold HRS.empirical
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (by exact_mod_cast hN0.ne'))
    exact integrable_finsetSum_measure.2 fun i _ => integrable_dirac (by simp)
  have hW1 : Integrable f (volume.withDensity fun x => ENNReal.ofReal (-ρ x)) :=
    tunit_integrable_withDensity_pos hρm.neg (by simpa using hfρ.neg)
  have hD := ten_int_ofDensity (fun x => -ρ x) f hρm.neg (by simpa using hfρ.neg)
  have hD' : ∫ x, f x ∂(volume.withDensity fun x => ENNReal.ofReal (-ρ x)) -
      ∫ x, f x ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) = -∫ x, ρ x * f x := by
    have h2 := hD
    unfold SMT.int SMT.ofDensity at h2
    simp only [neg_neg] at h2
    rw [h2, ← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have hE : ∫ x, f x ∂(HRS.empirical X) = (N : ℝ)⁻¹ * ∑ i, f (X i) :=
    HRS.pair_empirical hN0 X f
  unfold SMT.int chargeT
  rw [integral_add_measure hIE hW1, hE, one_div]
  linarith [hD']

end HRS.Commutator.TorusNote
