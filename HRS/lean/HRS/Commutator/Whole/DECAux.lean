import HRS.Commutator.Whole.Defs

/-!
# Packet CMX-DEC, helper file 1: generic signed-measure facts

Bounded measurable kernels on finite signed measures `σ = σ⁺ - σ⁻` (`SMeas`): linearity of `σ.int`,
Fubini swap, pulling inner products out of `σ.int`, and the odd-kernel identity
`𝒞_F(w,σ) = 2 σ.int (x ↦ ⟨w x, (F*σ)(x)⟩)` (`F` odd, `w` bounded).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.DEC

variable {d : ℕ}

theorem bdd_integrable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E]
    [SecondCountableTopology E] [BorelSpace E] {m : Measure α} [IsFiniteMeasure m]
    {f : α → E} (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

theorem int_sub_int (σ : SMeas d) {f g : Euc d → ℝ}
    (hfp : Integrable f σ.pos) (hgp : Integrable g σ.pos)
    (hfn : Integrable f σ.neg) (hgn : Integrable g σ.neg) :
    σ.int (fun x => f x - g x) = σ.int f - σ.int g := by
  unfold SMeas.int
  rw [integral_sub hfp hgp, integral_sub hfn hgn]
  ring

theorem int_neg_fun (σ : SMeas d) (f : Euc d → ℝ) : σ.int (fun x => -f x) = -σ.int f := by
  unfold SMeas.int
  simp only [integral_neg]
  ring

theorem param_measurable {μ : Measure (Euc d)} [SFinite μ] {J : Euc d → Euc d → ℝ}
    (hJ : Measurable (fun q : Euc d × Euc d => J q.1 q.2)) :
    Measurable (fun x => ∫ y, J x y ∂μ) :=
  (hJ.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem param_bound {μ : Measure (Euc d)} [IsFiniteMeasure μ] {J : Euc d → Euc d → ℝ} (C : ℝ)
    (hC : ∀ x y, ‖J x y‖ ≤ C) (x : Euc d) : ‖∫ y, J x y ∂μ‖ ≤ C * μ.real Set.univ :=
  norm_integral_le_of_norm_le_const (ae_of_all _ fun y => hC x y)

theorem param_integrable {μ ν : Measure (Euc d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {J : Euc d → Euc d → ℝ} (hJ : Measurable (fun q : Euc d × Euc d => J q.1 q.2)) (C : ℝ)
    (hC : ∀ x y, ‖J x y‖ ≤ C) : Integrable (fun x => ∫ y, J x y ∂ν) μ :=
  bdd_integrable (param_measurable (μ := ν) hJ) _ (param_bound (μ := ν) C hC)

/-- Expansion of the iterated signed integral of a bounded measurable kernel into four iterated
integrals (outer measure first). -/
theorem int_expand (σ : SMeas d) [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg]
    {J : Euc d → Euc d → ℝ} (hJ : Measurable (fun q : Euc d × Euc d => J q.1 q.2)) (C : ℝ)
    (hC : ∀ x y, ‖J x y‖ ≤ C) :
    σ.int (fun x => σ.int (fun y => J x y)) =
      (∫ x, ∫ y, J x y ∂σ.pos ∂σ.pos) - (∫ x, ∫ y, J x y ∂σ.neg ∂σ.pos)
        - (∫ x, ∫ y, J x y ∂σ.pos ∂σ.neg) + (∫ x, ∫ y, J x y ∂σ.neg ∂σ.neg) := by
  have i1 := param_integrable (μ := σ.pos) (ν := σ.pos) hJ C hC
  have i2 := param_integrable (μ := σ.pos) (ν := σ.neg) hJ C hC
  have i3 := param_integrable (μ := σ.neg) (ν := σ.pos) hJ C hC
  have i4 := param_integrable (μ := σ.neg) (ν := σ.neg) hJ C hC
  unfold SMeas.int
  rw [integral_sub i1 i2, integral_sub i3 i4]
  ring

/-- Fubini swap for a bounded measurable kernel on a finite signed measure. -/
theorem int_int_swap (σ : SMeas d) [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg]
    {J : Euc d → Euc d → ℝ} (hJ : Measurable (fun q : Euc d × Euc d => J q.1 q.2)) (C : ℝ)
    (hC : ∀ x y, ‖J x y‖ ≤ C) :
    σ.int (fun x => σ.int (fun y => J x y)) = σ.int (fun y => σ.int (fun x => J x y)) := by
  have hJ' : Measurable (fun q : Euc d × Euc d => (fun a b => J b a) q.1 q.2) :=
    hJ.comp measurable_swap
  have hC' : ∀ a b, ‖(fun a b => J b a) a b‖ ≤ C := fun a b => hC b a
  rw [int_expand σ hJ C hC, int_expand σ hJ' C hC']
  have sw : ∀ (m m' : Measure (Euc d)) [IsFiniteMeasure m] [IsFiniteMeasure m'],
      ∫ x, ∫ y, J x y ∂m' ∂m = ∫ y, ∫ x, J x y ∂m ∂m' := by
    intro m m' _ _
    exact integral_integral_swap (bdd_integrable (m := m.prod m') hJ C (fun q => hC q.1 q.2))
  simp only [sw σ.pos σ.pos, sw σ.pos σ.neg, sw σ.neg σ.pos, sw σ.neg σ.neg]
  ring

/-- Pulling a fixed vector out of a signed integral. -/
theorem int_inner (σ : SMeas d) (c : Euc d) {g : Euc d → Euc d}
    (hgp : Integrable g σ.pos) (hgn : Integrable g σ.neg) :
    σ.int (fun y => inner ℝ c (g y)) = inner ℝ c (σ.intV g) := by
  unfold SMeas.int SMeas.intV
  rw [integral_inner hgp c, integral_inner hgn c, inner_sub_right]

/-- Oddness of the force turns `σ.intV (x ↦ F(x - y))` into `- σ.intV (z ↦ F(y - z))`. -/
theorem intV_odd (σ : SMeas d) {F : Euc d → Euc d} (hF : ∀ z, F (-z) = -F z) (y : Euc d) :
    σ.intV (fun x => F (x - y)) = -σ.intV (fun z => F (y - z)) := by
  have h : (fun x => F (x - y)) = fun x => -(F (y - x)) := by
    funext x
    rw [← hF, neg_sub]
  rw [h]
  unfold SMeas.intV
  simp only [integral_neg]
  abel

/-- The commutator kernel with a fixed `w` splits as a difference of two inner products. -/
theorem commKer_split (F : Euc d → Euc d) (w : Euc d → Euc d) (x y : Euc d) :
    commKer F w x y = inner ℝ (w x) (F (x - y)) - inner ℝ (w y) (F (x - y)) := by
  unfold commKer
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h, inner_sub_left]

set_option maxHeartbeats 1000000 in
/-- The odd-kernel identity: for a finite signed measure `σ`, a bounded odd force `F` and a bounded
`w`, `𝒞_F(w,σ) = 2 σ.int (x ↦ ⟨w x, (F*σ)(x)⟩)`. -/
theorem pair2_odd (σ : SMeas d) [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg]
    {F : Euc d → Euc d} (hFm : Measurable F) (hF : ∀ z, F (-z) = -F z) (CF : ℝ)
    (hFb : ∀ z, ‖F z‖ ≤ CF) {w : Euc d → Euc d} (hwm : Measurable w) (Cw : ℝ)
    (hwb : ∀ x, ‖w x‖ ≤ Cw) :
    σ.pair2 (commKer F w) =
      2 * σ.int (fun x => inner ℝ (w x) (σ.intV (fun y => F (x - y)))) := by
  have hCw : 0 ≤ Cw := (norm_nonneg _).trans (hwb 0)
  have hFx : Measurable (fun q : Euc d × Euc d => F (q.1 - q.2)) :=
    hFm.comp (measurable_fst.sub measurable_snd)
  set J1 : Euc d → Euc d → ℝ := fun x y => inner ℝ (w x) (F (x - y)) with hJ1
  set J2 : Euc d → Euc d → ℝ := fun x y => inner ℝ (w y) (F (x - y)) with hJ2
  have hJ1m : Measurable (fun q : Euc d × Euc d => J1 q.1 q.2) :=
    (hwm.comp measurable_fst).inner hFx
  have hJ2m : Measurable (fun q : Euc d × Euc d => J2 q.1 q.2) :=
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
    fun x => ⟨bdd_integrable (m := σ.pos) (hm1 x) (Cw * CF) (hb1 x),
      bdd_integrable (m := σ.neg) (hm1 x) (Cw * CF) (hb1 x)⟩
  have hI2 : ∀ x, Integrable (fun y => J2 x y) σ.pos ∧ Integrable (fun y => J2 x y) σ.neg :=
    fun x => ⟨bdd_integrable (m := σ.pos) (hm2 x) (Cw * CF) (hb2 x),
      bdd_integrable (m := σ.neg) (hm2 x) (Cw * CF) (hb2 x)⟩
  have hJ1eq : ∀ x, σ.int (fun y => J1 x y) = inner ℝ (w x) (σ.intV (fun y => F (x - y))) :=
    fun x => int_inner σ (w x) (bdd_integrable (m := σ.pos) (hFi x) CF (hFbd x))
      (bdd_integrable (m := σ.neg) (hFi x) CF (hFbd x))
  have hJ2eq : ∀ y, σ.int (fun x => J2 x y) = -inner ℝ (w y) (σ.intV (fun z => F (y - z))) := by
    intro y
    rw [int_inner σ (w y) (bdd_integrable (m := σ.pos) (hFi' y) CF (fun x => hFbd x y))
      (bdd_integrable (m := σ.neg) (hFi' y) CF (fun x => hFbd x y)), intV_odd σ hF y,
      inner_neg_right]
  have hsub : ∀ x, σ.int (fun y => commKer F w x y) =
      σ.int (fun y => J1 x y) - σ.int (fun y => J2 x y) := fun x => by
    simp only [commKer_split]
    exact int_sub_int σ (hI1 x).1 (hI2 x).1 (hI1 x).2 (hI2 x).2
  have hO1 : Integrable (fun x => σ.int (fun y => J1 x y)) σ.pos := by
    unfold SMeas.int
    exact (param_integrable (μ := σ.pos) (ν := σ.pos) hJ1m _ hb1).sub
      (param_integrable (μ := σ.pos) (ν := σ.neg) hJ1m _ hb1)
  have hO1' : Integrable (fun x => σ.int (fun y => J1 x y)) σ.neg := by
    unfold SMeas.int
    exact (param_integrable (μ := σ.neg) (ν := σ.pos) hJ1m _ hb1).sub
      (param_integrable (μ := σ.neg) (ν := σ.neg) hJ1m _ hb1)
  have hO2 : Integrable (fun x => σ.int (fun y => J2 x y)) σ.pos := by
    unfold SMeas.int
    exact (param_integrable (μ := σ.pos) (ν := σ.pos) hJ2m _ hb2).sub
      (param_integrable (μ := σ.pos) (ν := σ.neg) hJ2m _ hb2)
  have hO2' : Integrable (fun x => σ.int (fun y => J2 x y)) σ.neg := by
    unfold SMeas.int
    exact (param_integrable (μ := σ.neg) (ν := σ.pos) hJ2m _ hb2).sub
      (param_integrable (μ := σ.neg) (ν := σ.neg) hJ2m _ hb2)
  unfold SMeas.pair2
  simp only [hsub]
  rw [int_sub_int σ hO1 hO2 hO1' hO2', int_int_swap σ hJ2m (Cw * CF) hb2]
  simp only [hJ1eq, hJ2eq, int_neg_fun]
  ring

end HRS.Commutator.Whole.DEC
