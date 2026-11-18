import HRS.MC.S7E1Aux2

/-!
# Packet `s7_E1_variance_sandwich`, file 3: the canonical centring of an `L^2` kernel

For measurable `h in L^2(mu x mu)` (`mu` a probability measure) the canonical centring
`h° = canonicalCenter mu h` is measurable, in `L^2(mu x mu)`, doubly centred (in each variable, a.e.), and has
the same coefficients `iint h° e_i e_j = iint h e_i e_j` against centred `e_i, e_j`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.E1Aux3

open HRS HRS.Sec7

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}

theorem e1c_meas {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h)) :
    Measurable (Function.uncurry (canonicalCenter μ h)) := by
  unfold canonicalCenter
  have t2 : Measurable (fun p : Torus d × Torus d => ∫ y', h p.1 y' ∂μ) := by
    have : StronglyMeasurable (fun x : Torus d => ∫ y', h x y' ∂μ) :=
      (hm.stronglyMeasurable : StronglyMeasurable (Function.uncurry h)).integral_prod_right
    exact this.measurable.comp measurable_fst
  have t3 : Measurable (fun p : Torus d × Torus d => ∫ x', h x' p.2 ∂μ) := by
    have h' : StronglyMeasurable (Function.uncurry fun y x' => h x' y) :=
      (hm.comp measurable_swap).stronglyMeasurable
    have : StronglyMeasurable (fun y : Torus d => ∫ x', h x' y ∂μ) := h'.integral_prod_right
    exact this.measurable.comp measurable_snd
  exact ((hm.sub t2).sub t3).add measurable_const

/-- the row average of an `L^2` kernel is in `L^2` -/
theorem e1c_row_memLp {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (hL2 : MemLp (Function.uncurry h) 2 (μ.prod μ)) : MemLp (fun x => ∫ y, h x y ∂μ) 2 μ := by
  have Ksq : Integrable (fun z : Torus d × Torus d => h z.1 z.2 ^ 2) (μ.prod μ) := hL2.integrable_sq
  have hsm : StronglyMeasurable (fun x : Torus d => ∫ y', h x y' ∂μ) :=
    (hm.stronglyMeasurable : StronglyMeasurable (Function.uncurry h)).integral_prod_right
  refine (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).2 ?_
  have gint : Integrable (fun x => ∫ y, h x y ^ 2 ∂μ) μ := Ksq.integral_prod_left
  refine gint.mono' (hsm.aestronglyMeasurable.pow 2) ?_
  filter_upwards [Ksq.prod_right_ae] with x hx
  have hrow : MemLp (h x) 2 μ :=
    (memLp_two_iff_integrable_sq (hm.comp measurable_prodMk_left).aestronglyMeasurable).2 hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact E1Aux2.e1b_sq_int_le hrow

theorem e1c_col_memLp {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (hL2 : MemLp (Function.uncurry h) 2 (μ.prod μ)) : MemLp (fun y => ∫ x, h x y ∂μ) 2 μ := by
  have hm' : Measurable (Function.uncurry fun y x => h x y) := hm.comp measurable_swap
  have hL2' : MemLp (Function.uncurry fun y x => h x y) 2 (μ.prod μ) := by
    have := hL2.comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    exact this
  exact e1c_row_memLp (h := fun y x => h x y) hm' hL2'

theorem e1c_cc_eq (h : Torus d → Torus d → ℝ) (x y : Torus d) :
    canonicalCenter μ h x y = h x y - (∫ y', h x y' ∂μ) - (∫ x', h x' y ∂μ) +
      ∫ x', ∫ y', h x' y' ∂μ ∂μ := rfl

theorem e1c_memLp {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (hL2 : MemLp (Function.uncurry h) 2 (μ.prod μ)) :
    MemLp (Function.uncurry (canonicalCenter μ h)) 2 (μ.prod μ) := by
  have hr := (e1c_row_memLp hm hL2).comp_fst μ
  have hc := (e1c_col_memLp hm hL2).comp_snd μ
  have := ((hL2.sub hr).sub hc).add (memLp_const (∫ x', ∫ y', h x' y' ∂μ ∂μ))
  refine this.ae_eq (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.uncurry, e1c_cc_eq, Pi.add_apply, Pi.sub_apply]

theorem e1c_row_zero {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (hL2 : MemLp (Function.uncurry h) 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, ∫ y, canonicalCenter μ h x y ∂μ = 0 := by
  have hint : Integrable (Function.uncurry h) (μ.prod μ) := hL2.integrable one_le_two
  have hcint : Integrable (fun y => ∫ x', h x' y ∂μ) μ := (e1c_col_memLp hm hL2).integrable one_le_two
  filter_upwards [hint.prod_right_ae] with x hx
  have hx' : Integrable (fun y => h x y) μ := hx
  have i1 : Integrable (fun y => h x y - ∫ y', h x y' ∂μ) μ := hx'.sub (integrable_const _)
  have i2 : Integrable (fun y => h x y - (∫ y', h x y' ∂μ) - ∫ x', h x' y ∂μ) μ := i1.sub hcint
  simp only [e1c_cc_eq]
  rw [integral_add i2 (integrable_const _), integral_sub i1 hcint, integral_sub hx' (integrable_const _)]
  have hsw : ∫ y, ∫ x', h x' y ∂μ ∂μ = ∫ x', ∫ y', h x' y' ∂μ ∂μ :=
    (integral_integral_swap (f := fun x' y => h x' y) hint).symm
  simp [hsw]

theorem e1c_col_zero {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (hL2 : MemLp (Function.uncurry h) 2 (μ.prod μ)) :
    ∀ᵐ y ∂μ, ∫ x, canonicalCenter μ h x y ∂μ = 0 := by
  have hint : Integrable (Function.uncurry h) (μ.prod μ) := hL2.integrable one_le_two
  have hrint : Integrable (fun x => ∫ y', h x y' ∂μ) μ := (e1c_row_memLp hm hL2).integrable one_le_two
  filter_upwards [hint.prod_left_ae] with y hy
  have hy' : Integrable (fun x => h x y) μ := hy
  have i1 : Integrable (fun x => h x y - ∫ y', h x y' ∂μ) μ := hy'.sub hrint
  have i2 : Integrable (fun x => h x y - (∫ y', h x y' ∂μ) - ∫ x', h x' y ∂μ) μ :=
    i1.sub (integrable_const _)
  simp only [e1c_cc_eq]
  rw [integral_add i2 (integrable_const _), integral_sub i1 (integrable_const _), integral_sub hy' hrint]
  simp

theorem e1c_coef (he : IsONBL2Zero μ e) {h : Torus d → Torus d → ℝ}
    (hm : Measurable (Function.uncurry h)) (hL2 : MemLp (Function.uncurry h) 2 (μ.prod μ)) (i j : ℕ) :
    ∫ x, ∫ y, canonicalCenter μ h x y * e i x * e j y ∂μ ∂μ = ∫ x, ∫ y, h x y * e i x * e j y ∂μ ∂μ := by
  have hW : MemLp (fun z : Torus d × Torus d => e i z.1 * e j z.2) 2 (μ.prod μ) :=
    E0b.e0b_tensor_memLp (he.memLp i) (he.memLp j)
  have hcc := e1c_memLp (μ := μ) hm hL2
  set r : Torus d → ℝ := fun x => ∫ y, h x y ∂μ with hr
  set c : Torus d → ℝ := fun y => ∫ x, h x y ∂μ with hc
  set I : ℝ := ∫ x', ∫ y', h x' y' ∂μ ∂μ with hI
  have hrm : MemLp r 2 μ := e1c_row_memLp hm hL2
  have hcm : MemLp c 2 μ := e1c_col_memLp hm hL2
  have iA : Integrable (fun z : Torus d × Torus d => h z.1 z.2 * (e i z.1 * e j z.2)) (μ.prod μ) :=
    hL2.integrable_mul hW
  have i1 : Integrable (fun x => r x * e i x) μ := hrm.integrable_mul (he.memLp i)
  have i2 : Integrable (fun y => c y * e j y) μ := hcm.integrable_mul (he.memLp j)
  have iei : Integrable (e i) μ := (he.memLp i).integrable one_le_two
  have iej : Integrable (e j) μ := (he.memLp j).integrable one_le_two
  have iU1 : Integrable (fun z : Torus d × Torus d => (r z.1 * e i z.1) * e j z.2) (μ.prod μ) :=
    i1.mul_prod iej
  have iU2 : Integrable (fun z : Torus d × Torus d => e i z.1 * (c z.2 * e j z.2)) (μ.prod μ) :=
    iei.mul_prod i2
  have iU3 : Integrable (fun z : Torus d × Torus d => I * (e i z.1 * e j z.2)) (μ.prod μ) :=
    (hW.integrable one_le_two).const_mul I
  have iCC : Integrable (fun z : Torus d × Torus d =>
      canonicalCenter μ h z.1 z.2 * (e i z.1 * e j z.2)) (μ.prod μ) := hcc.integrable_mul hW
  have key : ∀ z : Torus d × Torus d, canonicalCenter μ h z.1 z.2 * (e i z.1 * e j z.2) =
      h z.1 z.2 * (e i z.1 * e j z.2) - (r z.1 * e i z.1) * e j z.2 -
        e i z.1 * (c z.2 * e j z.2) + I * (e i z.1 * e j z.2) := by
    intro z; simp only [e1c_cc_eq, hr, hc, hI]; ring
  have z1 : ∫ z : Torus d × Torus d, (r z.1 * e i z.1) * e j z.2 ∂(μ.prod μ) = 0 := by
    rw [integral_prod_mul (fun x => r x * e i x) (e j), he.centered j, mul_zero]
  have z2 : ∫ z : Torus d × Torus d, e i z.1 * (c z.2 * e j z.2) ∂(μ.prod μ) = 0 := by
    rw [integral_prod_mul (e i) (fun y => c y * e j y), he.centered i, zero_mul]
  have z3 : ∫ z : Torus d × Torus d, I * (e i z.1 * e j z.2) ∂(μ.prod μ) = 0 := by
    rw [integral_const_mul, integral_prod_mul (e i) (e j), he.centered i, zero_mul, mul_zero]
  have hmain : ∫ z : Torus d × Torus d, canonicalCenter μ h z.1 z.2 * (e i z.1 * e j z.2) ∂(μ.prod μ) =
      ∫ z : Torus d × Torus d, h z.1 z.2 * (e i z.1 * e j z.2) ∂(μ.prod μ) := by
    have j1 : Integrable (fun z : Torus d × Torus d => h z.1 z.2 * (e i z.1 * e j z.2) -
        (r z.1 * e i z.1) * e j z.2) (μ.prod μ) := iA.sub iU1
    have j2 : Integrable (fun z : Torus d × Torus d => h z.1 z.2 * (e i z.1 * e j z.2) -
        (r z.1 * e i z.1) * e j z.2 - e i z.1 * (c z.2 * e j z.2)) (μ.prod μ) := j1.sub iU2
    simp_rw [key]
    rw [integral_add j2 iU3, integral_sub j1 iU2, integral_sub iA iU1, z1, z2, z3]
    ring
  have l1 := integral_prod _ iCC
  have l2 := integral_prod _ iA
  have e1 : ∀ x, ∫ y, canonicalCenter μ h x y * e i x * e j y ∂μ =
      ∫ y, canonicalCenter μ h x y * (e i x * e j y) ∂μ := fun x =>
    integral_congr_ae (Filter.Eventually.of_forall fun y => mul_assoc _ _ _)
  have e2 : ∀ x, ∫ y, h x y * e i x * e j y ∂μ = ∫ y, h x y * (e i x * e j y) ∂μ := fun x =>
    integral_congr_ae (Filter.Eventually.of_forall fun y => mul_assoc _ _ _)
  simp_rw [e1, e2]
  rw [← l1, ← l2]
  exact hmain

/-- Parseval: `sum_{ij} H_ij^2 = ||h°||^2`. -/
theorem e1c_parseval (he : IsONBL2Zero μ e) {h : Torus d → Torus d → ℝ}
    (hm : Measurable (Function.uncurry h)) (hL2 : MemLp (Function.uncurry h) 2 (μ.prod μ)) :
    HasSum (fun p : ℕ × ℕ => (∫ x, ∫ y, h x y * e p.1 x * e p.2 y ∂μ ∂μ) ^ 2)
      (∫ z : Torus d × Torus d, canonicalCenter μ h z.1 z.2 ^ 2 ∂(μ.prod μ)) := by
  have := E1Aux2.e1b_parseval2 he (e1c_meas (μ := μ) hm) (e1c_memLp hm hL2) (e1c_row_zero hm hL2)
    (e1c_col_zero hm hL2)
  simpa only [e1c_coef he hm hL2] using this

end HRS.MC.Sec7.E1Aux3

end
