import HRS.MS.ThmDefs

/-!
# THM-3 (part 1): scalar facts, integrability of the energy integrands on `C_M`, midpoint inequality

Infrastructure for `HRS.MS.Thm.exists_min_Cset` (file `ThmMinAux2.lean`).  Helper lemmas are prefixed `t3_`.

Statement adjustments relative to the sketch (see `docs/THM_REVIEW_NOTES.md`): `1 ≤ M` and `0 < β` are assumed;
all integrals of `G` on `C_M` are genuine (never the junk value `0`): `ρ log (ρ / r)` is bounded by `M² r`, and the
energy integrand is dominated by `M² K r r`, which is integrable on the product by (K1).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-! ### Scalar facts for `t ↦ t log t` -/

lemma t3_mul_log_lower {t : ℝ} (ht : 0 ≤ t) : -1 ≤ t * Real.log t := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]; simp
  · have h1 := Real.one_sub_inv_le_log_of_pos h
    have h2 : t * (1 - t⁻¹) = t - 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 ht]

lemma t3_mul_log_upper {t M : ℝ} (ht : 0 ≤ t) (htM : t ≤ M) : t * Real.log t ≤ M ^ 2 := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]; simp; nlinarith
  · have h1 := Real.log_le_sub_one_of_pos h
    nlinarith [mul_le_mul_of_nonneg_left h1 ht]

lemma t3_mul_log_abs {t M : ℝ} (hM : 1 ≤ M) (ht : 0 ≤ t) (htM : t ≤ M) : |t * Real.log t| ≤ M ^ 2 := by
  rw [abs_le]
  exact ⟨by nlinarith [t3_mul_log_lower ht], t3_mul_log_upper ht htM⟩

/-- `ψ(t) = t log t - t²/(2M)` is convex on `[0, M]` (its second derivative is `1/t - 1/M ≥ 0`). -/
lemma t3_psi_convex {M : ℝ} (_hM : 0 < M) :
    ConvexOn ℝ (Set.Icc 0 M) (fun t : ℝ => t * Real.log t - t ^ 2 / (2 * M)) := by
  have hderiv : ∀ t : ℝ, t ≠ 0 →
      HasDerivAt (fun t : ℝ => t * Real.log t - t ^ 2 / (2 * M)) (Real.log t + 1 - t / M) t := by
    intro t ht
    have h1 := Real.hasDerivAt_mul_log ht
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / (2 * M)) (t / M) t := by
      have := ((hasDerivAt_pow 2 t).div_const (2 * M))
      convert this using 1
      norm_num
      ring
    exact h1.sub h2
  have hint : interior (Set.Icc (0 : ℝ) M) = Set.Ioo 0 M := interior_Icc
  refine convexOn_of_deriv2_nonneg (convex_Icc 0 M) ?_ ?_ ?_ ?_
  · exact (Real.continuous_mul_log.sub ((continuous_pow 2).div_const _)).continuousOn
  · intro t ht
    rw [hint] at ht
    exact (hderiv t ht.1.ne').differentiableAt.differentiableWithinAt
  · rw [hint]
    have heq : ∀ t ∈ Set.Ioo (0 : ℝ) M,
        deriv (fun t : ℝ => t * Real.log t - t ^ 2 / (2 * M)) t = Real.log t + 1 - t / M :=
      fun t ht => (hderiv t ht.1.ne').deriv
    intro t ht
    have hd : DifferentiableAt ℝ (fun t : ℝ => Real.log t + 1 - t / M) t :=
      (((Real.differentiableAt_log ht.1.ne').add_const 1).sub (differentiableAt_id.div_const M))
    refine (hd.differentiableWithinAt).congr (fun y hy => heq y hy) (heq t ht)
  · rw [hint]
    intro t ht
    have heq : (deriv (fun t : ℝ => t * Real.log t - t ^ 2 / (2 * M))) =ᶠ[nhds t]
        fun t => Real.log t + 1 - t / M := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy using (hderiv y hy.1.ne').deriv
    have h3 : HasDerivAt (fun t : ℝ => Real.log t + 1 - t / M) (t⁻¹ - 1 / M) t := by
      have := ((Real.hasDerivAt_log ht.1.ne').add_const 1).sub ((hasDerivAt_id t).div_const M)
      convert this using 1
      ext y; simp
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [heq.deriv_eq, h3.deriv]
    have : 1 / M ≤ t⁻¹ := by
      rw [one_div]; exact inv_anti₀ ht.1 ht.2.le
    linarith

/-- Strong convexity of `t log t` on `[0, M]`:
`φ((a+b)/2) ≤ (φ a + φ b)/2 - (a-b)²/(8M)`. -/
lemma t3_phi_strong {M a b : ℝ} (hM : 0 < M) (ha0 : 0 ≤ a) (haM : a ≤ M) (hb0 : 0 ≤ b) (hbM : b ≤ M) :
    (a + b) / 2 * Real.log ((a + b) / 2) ≤
      (a * Real.log a + b * Real.log b) / 2 - (a - b) ^ 2 / (8 * M) := by
  have h := (t3_psi_convex hM).2 (show a ∈ Set.Icc 0 M from ⟨ha0, haM⟩)
    (show b ∈ Set.Icc 0 M from ⟨hb0, hbM⟩) (show (0:ℝ) ≤ 1 / 2 by norm_num)
    (show (0:ℝ) ≤ 1 / 2 by norm_num) (show (1:ℝ) / 2 + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  have e : (1 / 2 : ℝ) * a + 1 / 2 * b = (a + b) / 2 := by ring
  rw [e] at h
  have e2 : (a - b) ^ 2 / (8 * M) = ((a ^ 2 / (2 * M)) / 2 + (b ^ 2 / (2 * M)) / 2
      - ((a + b) / 2) ^ 2 / (2 * M)) := by
    field_simp; ring
  rw [e2]
  linarith

/-! ### Integrability of the energy integrands under (K1) -/

section Setting

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B : ℝ}

lemma t3_r_integrable (hS : ThmSetting K r B) : Integrable r := by
  by_contra h
  have := hS.r_prob.integral_one
  rw [integral_undef h] at this
  norm_num at this

lemma t3_W_integrable (hS : ThmSetting K r B) :
    Integrable (fun p : Euc d × Euc d => K p.1 p.2 * r p.1 * r p.2)
      ((volume : Measure (Euc d)).prod volume) := by
  have hr : Measurable r := hS.r_prob.measurable
  have hK : Measurable (fun p : Euc d × Euc d => K p.1 p.2) := hS.meas
  have hmeas : Measurable (fun p : Euc d × Euc d => K p.1 p.2 * r p.1 * r p.2) :=
    (hK.mul (hr.comp measurable_fst)).mul (hr.comp measurable_snd)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · refine Filter.Eventually.of_forall fun x => ?_
    have := ((hS.k1 x).1).const_mul (r x)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  · refine Integrable.mono' ((t3_r_integrable hS).mul_const B) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact hmeas.aestronglyMeasurable.norm.integral_prod_right'
    · have h1 : ∀ y, ‖K x y * r x * r y‖ = r x * (K x y * r y) := fun y => by
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hS.nonneg x y) (hS.r_pos x).le) (hS.r_pos y).le)]
        ring
      simp only [h1]
      rw [integral_const_mul]
      have h2 : 0 ≤ ∫ y, K x y * r y := integral_nonneg fun y => mul_nonneg (hS.nonneg x y) (hS.r_pos y).le
      rw [Real.norm_of_nonneg (mul_nonneg (hS.r_pos x).le h2)]
      exact mul_le_mul_of_nonneg_left (hS.k1 x).2 (hS.r_pos x).le

lemma t3_prod_integrable (hS : ThmSetting K r B) {f h : Euc d → ℝ} (hf : Measurable f) (hh : Measurable h)
    {C C' : ℝ} (hfb : ∀ x, |f x| ≤ C * r x) (hhb : ∀ x, |h x| ≤ C' * r x) :
    Integrable (fun p : Euc d × Euc d => K p.1 p.2 * f p.1 * h p.2)
      ((volume : Measure (Euc d)).prod volume) := by
  have hK : Measurable (fun p : Euc d × Euc d => K p.1 p.2) := hS.meas
  have hmeas : Measurable (fun p : Euc d × Euc d => K p.1 p.2 * f p.1 * h p.2) :=
    (hK.mul (hf.comp measurable_fst)).mul (hh.comp measurable_snd)
  refine Integrable.mono' ((t3_W_integrable hS).const_mul (C * C')) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  have hk := hS.nonneg p.1 p.2
  have hC : 0 ≤ C := by
    have := (abs_nonneg (f p.1)).trans (hfb p.1)
    exact nonneg_of_mul_nonneg_left this (hS.r_pos p.1)
  have hC' : 0 ≤ C' := by
    have := (abs_nonneg (h p.2)).trans (hhb p.2)
    exact nonneg_of_mul_nonneg_left this (hS.r_pos p.2)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hk]
  calc K p.1 p.2 * |f p.1| * |h p.2| ≤ K p.1 p.2 * (C * r p.1) * (C' * r p.2) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb p.1) hk) (hhb p.2) (abs_nonneg _)
          (mul_nonneg hk (mul_nonneg hC (hS.r_pos _).le))
    _ = C * C' * (K p.1 p.2 * r p.1 * r p.2) := by ring

lemma t3_pairE_eq {f h : Euc d → ℝ}
    (hint : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * f p.1 * h p.2)
      ((volume : Measure (Euc d)).prod volume)) :
    pairE K f h = ∫ p : Euc d × Euc d, K p.1 p.2 * f p.1 * h p.2 ∂((volume : Measure (Euc d)).prod volume) := by
  unfold pairE
  exact (integral_prod _ hint).symm

lemma t3_pairE_nonneg {f h : Euc d → ℝ} (hK : ∀ x y, 0 ≤ K x y) (hf : ∀ x, 0 ≤ f x) (hh : ∀ x, 0 ≤ h x) :
    0 ≤ pairE K f h :=
  integral_nonneg fun x => integral_nonneg fun y => mul_nonneg (mul_nonneg (hK x y) (hf x)) (hh y)

end Setting

/-! ### The class `C_M`: integrability of the free-energy integrands -/

section CsetFacts

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B M : ℝ}

lemma t3_Cset_integrable (hS : ThmSetting K r B) {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset r M) : Integrable ρ :=
  ((t3_r_integrable hS).const_mul M).mono' hρ.1.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hρ.1.nonneg x)]; exact hρ.2 x)

lemma t3_Cset_abs {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset r M) (x : Euc d) : |ρ x| ≤ M * r x := by
  rw [abs_of_nonneg (hρ.1.nonneg x)]; exact hρ.2 x

lemma t3_Cset_le_ratio (hS : ThmSetting K r B) {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset r M) (x : Euc d) :
    ρ x / r x ≤ M := by
  rw [div_le_iff₀ (hS.r_pos x)]; exact hρ.2 x

lemma t3_ent_eq (hS : ThmSetting K r B) (ρ : Euc d → ℝ) (x : Euc d) :
    ρ x * Real.log (ρ x / r x) = r x * ((ρ x / r x) * Real.log (ρ x / r x)) := by
  have := (hS.r_pos x).ne'
  field_simp

lemma t3_ent_abs (hS : ThmSetting K r B) (hM : 1 ≤ M) {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset r M) (x : Euc d) :
    |ρ x * Real.log (ρ x / r x)| ≤ M ^ 2 * r x := by
  rw [t3_ent_eq hS, abs_mul, abs_of_pos (hS.r_pos x), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (t3_mul_log_abs hM (div_nonneg (hρ.1.nonneg x) (hS.r_pos x).le) (t3_Cset_le_ratio hS hρ x))
    (hS.r_pos x).le

lemma t3_ent_integrable (hS : ThmSetting K r B) (hM : 1 ≤ M) {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset r M) :
    Integrable (fun x => ρ x * Real.log (ρ x / r x)) := by
  have hr : Measurable r := hS.r_prob.measurable
  have hm : Measurable (fun x => ρ x * Real.log (ρ x / r x)) :=
    hρ.1.measurable.mul (Real.measurable_log.comp (hρ.1.measurable.div hr))
  exact ((t3_r_integrable hS).const_mul (M ^ 2)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact t3_ent_abs hS hM hρ x)

lemma t3_relEnt_ge (hS : ThmSetting K r B) (hM : 1 ≤ M) {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset r M) :
    -1 ≤ relEnt ρ r := by
  have h1 : ∫ x, -r x ≤ ∫ x, ρ x * Real.log (ρ x / r x) := by
    refine integral_mono (t3_r_integrable hS).neg (t3_ent_integrable hS hM hρ) fun x => ?_
    rw [t3_ent_eq hS]
    have := t3_mul_log_lower (div_nonneg (hρ.1.nonneg x) (hS.r_pos x).le)
    nlinarith [hS.r_pos x]
  rw [integral_neg, hS.r_prob.integral_one] at h1
  exact h1

lemma t3_pairE_integrable (hS : ThmSetting K r B) {ρ₁ ρ₂ : Euc d → ℝ} (h₁ : ρ₁ ∈ Cset r M)
    (h₂ : ρ₂ ∈ Cset r M) :
    Integrable (fun p : Euc d × Euc d => K p.1 p.2 * ρ₁ p.1 * ρ₂ p.2)
      ((volume : Measure (Euc d)).prod volume) :=
  t3_prod_integrable hS h₁.1.measurable h₂.1.measurable (t3_Cset_abs h₁) (t3_Cset_abs h₂)

lemma t3_G_ge (hS : ThmSetting K r B) (hM : 1 ≤ M) {β : ℝ} (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : ρ ∈ Cset r M) : -β⁻¹ ≤ Gfun K r β ρ := by
  unfold Gfun
  have h1 := t3_relEnt_ge hS hM hρ
  have h2 := t3_pairE_nonneg hS.nonneg hρ.1.nonneg hρ.1.nonneg
  have h3 : -β⁻¹ ≤ β⁻¹ * relEnt ρ r := by
    have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hβ.le)
    linarith
  linarith

/-- Midpoint of two elements of `C_M`. -/
lemma t3_mid_mem (hS : ThmSetting K r B) {ρ₁ ρ₂ : Euc d → ℝ} (h₁ : ρ₁ ∈ Cset r M) (h₂ : ρ₂ ∈ Cset r M) :
    (fun x => (ρ₁ x + ρ₂ x) / 2) ∈ Cset r M := by
  have hM0 : 0 ≤ M := by
    have := (hS.r_pos 0).le
    by_contra hneg
    rw [not_le] at hneg
    have := h₁.2 0
    have := h₁.1.nonneg 0
    nlinarith [hS.r_pos 0]
  refine ⟨⟨fun x => by have := h₁.1.nonneg x; have := h₂.1.nonneg x; positivity,
    (h₁.1.measurable.add h₂.1.measurable).div_const 2, ?_⟩, fun x => ?_⟩
  · rw [integral_div, integral_add (t3_Cset_integrable hS h₁) (t3_Cset_integrable hS h₂),
      h₁.1.integral_one, h₂.1.integral_one]
    norm_num
  · have := h₁.2 x
    have := h₂.2 x
    linarith

lemma t3_pt_mid {ρ₁ ρ₂ s : ℝ} (hM : 0 < M) (hs : 0 < s) (h1 : 0 ≤ ρ₁) (h1' : ρ₁ ≤ M * s) (h2 : 0 ≤ ρ₂)
    (h2' : ρ₂ ≤ M * s) :
    (ρ₁ + ρ₂) / 2 * Real.log (((ρ₁ + ρ₂) / 2) / s) ≤
      (ρ₁ * Real.log (ρ₁ / s) + ρ₂ * Real.log (ρ₂ / s)) / 2 - (ρ₁ - ρ₂) ^ 2 / (8 * M * s) := by
  have ha : ρ₁ / s ≤ M := by rw [div_le_iff₀ hs]; exact h1'
  have hb : ρ₂ / s ≤ M := by rw [div_le_iff₀ hs]; exact h2'
  have h := mul_le_mul_of_nonneg_left
    (t3_phi_strong hM (div_nonneg h1 hs.le) ha (div_nonneg h2 hs.le) hb) hs.le
  have e1 : (ρ₁ / s + ρ₂ / s) / 2 = ((ρ₁ + ρ₂) / 2) / s := by ring
  rw [e1] at h
  have hs' := hs.ne'
  have hM' := hM.ne'
  have eL : s * (((ρ₁ + ρ₂) / 2) / s * Real.log (((ρ₁ + ρ₂) / 2) / s)) =
      (ρ₁ + ρ₂) / 2 * Real.log (((ρ₁ + ρ₂) / 2) / s) := by field_simp
  have eR : s * ((ρ₁ / s * Real.log (ρ₁ / s) + ρ₂ / s * Real.log (ρ₂ / s)) / 2 -
      (ρ₁ / s - ρ₂ / s) ^ 2 / (8 * M)) =
      (ρ₁ * Real.log (ρ₁ / s) + ρ₂ * Real.log (ρ₂ / s)) / 2 - (ρ₁ - ρ₂) ^ 2 / (8 * M * s) := by
    field_simp
  rw [eL, eR] at h
  exact h

end CsetFacts

/-! ### Midpoint inequality -/

section Midpoint

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B M : ℝ}

/-- The squared weighted `L²` distance `∫ (ρ₁ - ρ₂)² / r`. -/
def t3D (r ρ₁ ρ₂ : Euc d → ℝ) : ℝ := ∫ x, (ρ₁ x - ρ₂ x) ^ 2 / r x

lemma t3_D_integrable (hS : ThmSetting K r B) {ρ₁ ρ₂ : Euc d → ℝ} (h₁ : ρ₁ ∈ Cset r M)
    (h₂ : ρ₂ ∈ Cset r M) : Integrable (fun x => (ρ₁ x - ρ₂ x) ^ 2 / r x) := by
  have hr : Measurable r := hS.r_prob.measurable
  have hm : Measurable (fun x => (ρ₁ x - ρ₂ x) ^ 2 / r x) :=
    ((h₁.1.measurable.sub h₂.1.measurable).pow_const 2).div hr
  refine ((t3_r_integrable hS).const_mul (M ^ 2)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hrx := hS.r_pos x
  have a1 := h₁.1.nonneg x
  have a2 := h₂.1.nonneg x
  have b1 := h₁.2 x
  have b2 := h₂.2 x
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hrx.le), div_le_iff₀ hrx]
  have : |ρ₁ x - ρ₂ x| ≤ M * r x := by
    rw [abs_le]; constructor <;> nlinarith
  have h2 := sq_le_sq' (neg_le_of_abs_le this) (le_of_abs_le this)
  nlinarith

lemma t3_D_nonneg {ρ₁ ρ₂ : Euc d → ℝ} (hr : ∀ x, 0 < r x) : 0 ≤ t3D r ρ₁ ρ₂ :=
  integral_nonneg fun x => div_nonneg (sq_nonneg _) (hr x).le

lemma t3_relEnt_mid (hS : ThmSetting K r B) (hM : 1 ≤ M) {ρ₁ ρ₂ : Euc d → ℝ} (h₁ : ρ₁ ∈ Cset r M)
    (h₂ : ρ₂ ∈ Cset r M) :
    relEnt (fun x => (ρ₁ x + ρ₂ x) / 2) r ≤
      (relEnt ρ₁ r + relEnt ρ₂ r) / 2 - t3D r ρ₁ ρ₂ / (8 * M) := by
  have hM0 : 0 < M := by linarith
  have hmid := t3_mid_mem hS h₁ h₂
  have i1 := t3_ent_integrable hS hM h₁
  have i2 := t3_ent_integrable hS hM h₂
  have iD := t3_D_integrable hS h₁ h₂
  have iR : Integrable (fun x => (ρ₁ x * Real.log (ρ₁ x / r x) + ρ₂ x * Real.log (ρ₂ x / r x)) / 2
      - (1 / (8 * M)) * ((ρ₁ x - ρ₂ x) ^ 2 / r x)) :=
    ((i1.add i2).div_const 2).sub (iD.const_mul _)
  have hle : ∫ x, (fun x => (ρ₁ x + ρ₂ x) / 2) x * Real.log ((fun x => (ρ₁ x + ρ₂ x) / 2) x / r x) ≤
      ∫ x, ((ρ₁ x * Real.log (ρ₁ x / r x) + ρ₂ x * Real.log (ρ₂ x / r x)) / 2
      - (1 / (8 * M)) * ((ρ₁ x - ρ₂ x) ^ 2 / r x)) := by
    refine integral_mono (t3_ent_integrable hS hM hmid) iR fun x => ?_
    have := t3_pt_mid hM0 (hS.r_pos x) (h₁.1.nonneg x) (h₁.2 x) (h₂.1.nonneg x) (h₂.2 x)
    have e : (ρ₁ x - ρ₂ x) ^ 2 / (8 * M * r x) = (1 / (8 * M)) * ((ρ₁ x - ρ₂ x) ^ 2 / r x) := by
      have := (hS.r_pos x).ne'
      field_simp
    simp only
    rw [← e]
    exact this
  have ha : Integrable (fun x => (ρ₁ x * Real.log (ρ₁ x / r x) + ρ₂ x * Real.log (ρ₂ x / r x)) / 2) :=
    (i1.add i2).div_const 2
  have hb : Integrable (fun x => (1 / (8 * M)) * ((ρ₁ x - ρ₂ x) ^ 2 / r x)) := iD.const_mul _
  have hval : ∫ x, ((ρ₁ x * Real.log (ρ₁ x / r x) + ρ₂ x * Real.log (ρ₂ x / r x)) / 2
      - (1 / (8 * M)) * ((ρ₁ x - ρ₂ x) ^ 2 / r x)) =
      (relEnt ρ₁ r + relEnt ρ₂ r) / 2 - t3D r ρ₁ ρ₂ / (8 * M) := by
    rw [integral_sub ha hb, integral_div, integral_add i1 i2, integral_const_mul]
    unfold relEnt t3D
    ring
  unfold relEnt at hle ⊢
  rw [hval] at hle
  exact hle

lemma t3_diff_prod_integrable (hS : ThmSetting K r B) {ρ₁ ρ₂ : Euc d → ℝ} (h₁ : ρ₁ ∈ Cset r M)
    (h₂ : ρ₂ ∈ Cset r M) :
    Integrable (fun p : Euc d × Euc d => K p.1 p.2 * (ρ₁ p.1 - ρ₂ p.1) * (ρ₁ p.2 - ρ₂ p.2))
      ((volume : Measure (Euc d)).prod volume) := by
  have hm : Measurable (fun x => ρ₁ x - ρ₂ x) := h₁.1.measurable.sub h₂.1.measurable
  have hb : ∀ x, |ρ₁ x - ρ₂ x| ≤ M * r x := fun x => by
    have a1 := h₁.1.nonneg x
    have a2 := h₂.1.nonneg x
    have b1 := h₁.2 x
    have b2 := h₂.2 x
    rw [abs_le]; constructor <;> linarith
  exact t3_prod_integrable hS (f := fun x => ρ₁ x - ρ₂ x) (h := fun x => ρ₁ x - ρ₂ x) hm hm hb hb

lemma t3_pairE_mid (hS : ThmSetting K r B) {ρ₁ ρ₂ : Euc d → ℝ} (h₁ : ρ₁ ∈ Cset r M)
    (h₂ : ρ₂ ∈ Cset r M) :
    pairE K (fun x => (ρ₁ x + ρ₂ x) / 2) (fun x => (ρ₁ x + ρ₂ x) / 2) +
        pairE K (fun x => ρ₁ x - ρ₂ x) (fun x => ρ₁ x - ρ₂ x) / 4 =
      (pairE K ρ₁ ρ₁ + pairE K ρ₂ ρ₂) / 2 := by
  have hmid := t3_mid_mem hS h₁ h₂
  have i11 := t3_pairE_integrable hS h₁ h₁
  have i22 := t3_pairE_integrable hS h₂ h₂
  have imm := t3_pairE_integrable hS hmid hmid
  have idd := t3_diff_prod_integrable hS h₁ h₂
  have e : ∫ p : Euc d × Euc d, (K p.1 p.2 * ((ρ₁ p.1 + ρ₂ p.1) / 2) * ((ρ₁ p.2 + ρ₂ p.2) / 2) +
      K p.1 p.2 * (ρ₁ p.1 - ρ₂ p.1) * (ρ₁ p.2 - ρ₂ p.2) / 4) ∂((volume : Measure (Euc d)).prod volume) =
      ∫ p : Euc d × Euc d, (K p.1 p.2 * ρ₁ p.1 * ρ₁ p.2 + K p.1 p.2 * ρ₂ p.1 * ρ₂ p.2) / 2
        ∂((volume : Measure (Euc d)).prod volume) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => by simp only; ring)
  rw [integral_add imm (idd.div_const 4), integral_div, integral_div, integral_add i11 i22] at e
  rw [t3_pairE_eq imm, t3_pairE_eq idd, t3_pairE_eq i11, t3_pairE_eq i22]
  exact e

lemma t3_G_mid (hS : ThmSetting K r B) (hM : 1 ≤ M) {β : ℝ} (hβ : 0 < β) {ρ₁ ρ₂ : Euc d → ℝ}
    (h₁ : ρ₁ ∈ Cset r M) (h₂ : ρ₂ ∈ Cset r M) :
    Gfun K r β (fun x => (ρ₁ x + ρ₂ x) / 2) ≤
      (Gfun K r β ρ₁ + Gfun K r β ρ₂) / 2 - t3D r ρ₁ ρ₂ / (8 * M * β) := by
  have hM0 : 0 < M := by linarith
  have hr := t3_relEnt_mid hS hM h₁ h₂
  have hp := t3_pairE_mid hS h₁ h₂
  have iDD := (t3_diff_prod_integrable hS h₁ h₂).abs
  have hk2 : 0 ≤ pairE K (fun x => ρ₁ x - ρ₂ x) (fun x => ρ₁ x - ρ₂ x) := by
    refine hS.k2 (fun x => ρ₁ x - ρ₂ x) ((t3_Cset_integrable hS h₁).sub (t3_Cset_integrable hS h₂))
      iDD ?_
    rw [integral_sub (t3_Cset_integrable hS h₁) (t3_Cset_integrable hS h₂), h₁.1.integral_one,
      h₂.1.integral_one]
    norm_num
  unfold Gfun
  have e1 := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hβ.le)
  have e2 : β⁻¹ * (t3D r ρ₁ ρ₂ / (8 * M)) = t3D r ρ₁ ρ₂ / (8 * M * β) := by
    field_simp
  rw [mul_sub, e2] at e1
  nlinarith

end Midpoint

end HRS.MS.Thm

end
