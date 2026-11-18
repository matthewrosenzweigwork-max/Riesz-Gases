import HRS.Commutator.Whole.XNRSAux9

/-!
# Packet X-NRS, part 10: from the `z`-form to the `(x,y)`-form

Product-integrability on `ℝ^d × ℝ^d` for functions dominated by `a(x) G(x-y)` or `a(y) G(x-y)`, and
the identification
`∫ K(z) ∫ (h(x)-h(x-z)) ψ(x) dx dz = ∫_y ∫_x ψ(x)(h(x)-h(y)) K(x-y) dx dy`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xint_xy1 {a G : Euc d → ℝ} (ha : Integrable a) (hG : Integrable G) :
    Integrable (fun p : Euc d × Euc d => a p.1 * G (p.1 - p.2)) (volume.prod volume) := by
  have h1 : Integrable (fun q : Euc d × Euc d => a q.1 * G (-q.2)) (volume.prod volume) :=
    Integrable.mul_prod (f := a) (g := fun w => G (-w)) ha (hG.comp_neg)
  have hmp := measurePreserving_prod_sub (volume : Measure (Euc d)) (volume : Measure (Euc d))
  have := hmp.integrable_comp_of_integrable h1
  refine this.congr (Eventually.of_forall fun p => ?_)
  simp [neg_sub]

lemma xint_xy2 {a G : Euc d → ℝ} (ha : Integrable a) (hG : Integrable G) :
    Integrable (fun p : Euc d × Euc d => a p.2 * G (p.1 - p.2)) (volume.prod volume) := by
  have h1 : Integrable (fun q : Euc d × Euc d => a q.1 * G q.2) (volume.prod volume) :=
    Integrable.mul_prod (f := a) (g := G) ha hG
  have hmp := measurePreserving_prod_sub_swap (volume : Measure (Euc d)) (volume : Measure (Euc d))
  exact hmp.integrable_comp_of_integrable h1

lemma integrable_xK_shift {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) :
    Integrable (xK d σ δ) := (xKer_xK hσ hδ).integrable


theorem xsc_AB {K : Euc d → ℝ} (hK : XKer K) (h ψ : 𝓢(Euc d, ℂ)) :
    ∫ z, ((K z : ℝ) : ℂ) * (∫ x, (h x - h (x - z)) * ψ x) =
      ∫ y, ∫ x, ψ x * ((h x - h y) * ((K (x - y) : ℝ) : ℂ)) := by
  obtain ⟨M, hM0, hM⟩ := xhbdd h
  -- integrability of Ψ on the product
  have hΨ : Integrable (Function.uncurry fun x y : Euc d =>
      ψ x * ((h x - h y) * ((K (x - y) : ℝ) : ℂ))) (volume.prod volume) := by
    have hb := xint_xy1 (a := fun x => 2 * M * ‖ψ x‖) (G := K)
      ((ψ.integrable.norm).const_mul (2 * M)) hK.integrable
    refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Continuous (fun p : Euc d × Euc d =>
          ψ p.1 * ((h p.1 - h p.2) * ((K (p.1 - p.2) : ℝ) : ℂ))) := by
        refine (ψ.continuous.comp continuous_fst).mul ?_
        refine ((h.continuous.comp continuous_fst).sub (h.continuous.comp continuous_snd)).mul ?_
        exact Complex.continuous_ofReal.comp (hK.cont.comp (continuous_fst.sub continuous_snd))
      exact this.aestronglyMeasurable
    · show ‖ψ p.1 * ((h p.1 - h p.2) * ((K (p.1 - p.2) : ℝ) : ℂ))‖ ≤ 2 * M * ‖ψ p.1‖ * K (p.1 - p.2)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hK.nonneg _)]
      have h1 : ‖h p.1 - h p.2‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hM p.1, hM p.2])
      have h2 := hK.nonneg (p.1 - p.2)
      have h3 := norm_nonneg (ψ p.1)
      nlinarith [mul_nonneg h3 h2, mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)]
  -- integrability of S on the product (x,z)
  have hS : Integrable (Function.uncurry fun x z : Euc d =>
      ((K z : ℝ) : ℂ) * (ψ x * (h x - h (x - z)))) (volume.prod volume) := by
    have hb : Integrable (fun p : Euc d × Euc d => ‖ψ p.1‖ * (2 * M * K p.2)) (volume.prod volume) :=
      Integrable.mul_prod (f := fun x => ‖ψ x‖) (g := fun z => 2 * M * K z) ψ.integrable.norm
        (hK.integrable.const_mul _)
    refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Continuous (fun p : Euc d × Euc d =>
          ((K p.2 : ℝ) : ℂ) * (ψ p.1 * (h p.1 - h (p.1 - p.2)))) := by
        refine (Complex.continuous_ofReal.comp (hK.cont.comp continuous_snd)).mul ?_
        refine (ψ.continuous.comp continuous_fst).mul ?_
        exact (h.continuous.comp continuous_fst).sub (h.continuous.comp (continuous_fst.sub continuous_snd))
      exact this.aestronglyMeasurable
    · show ‖((K p.2 : ℝ) : ℂ) * (ψ p.1 * (h p.1 - h (p.1 - p.2)))‖ ≤ ‖ψ p.1‖ * (2 * M * K p.2)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hK.nonneg _)]
      have h1 : ‖h p.1 - h (p.1 - p.2)‖ ≤ 2 * M :=
        (norm_sub_le _ _).trans (by linarith [hM p.1, hM (p.1 - p.2)])
      have h2 := hK.nonneg p.2
      have h3 := norm_nonneg (ψ p.1)
      nlinarith [mul_nonneg h3 h2, mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)]
  have e1 : ∀ x : Euc d, ∫ y, ψ x * ((h x - h y) * ((K (x - y) : ℝ) : ℂ)) =
      ∫ z, ((K z : ℝ) : ℂ) * (ψ x * (h x - h (x - z))) := by
    intro x
    have := integral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
      (fun y => ψ x * ((h x - h y) * ((K (x - y) : ℝ) : ℂ))) x
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sub_sub_cancel]
    ring
  have e2 : ∫ y, ∫ x, ψ x * ((h x - h y) * ((K (x - y) : ℝ) : ℂ)) =
      ∫ x, ∫ y, ψ x * ((h x - h y) * ((K (x - y) : ℝ) : ℂ)) :=
    (integral_integral_swap hΨ).symm
  rw [e2]
  simp_rw [e1]
  rw [integral_integral_swap hS]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  ring


lemma xint_sq_bdd (h : 𝓢(Euc d, ℂ)) : Integrable (fun x : Euc d => ‖h x‖ ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := xhbdd h
  refine (h.integrable.norm.const_mul M).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (h.continuous.norm.pow 2).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    calc ‖h x‖ ^ 2 = ‖h x‖ * ‖h x‖ := sq _
      _ ≤ M * ‖h x‖ := by nlinarith [hM x, norm_nonneg (h x)]

lemma xsq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_sub_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]

/-- the energy integrand is integrable on the product. -/
lemma xe_int {K : Euc d → ℝ} (hK : XKer K) (h : 𝓢(Euc d, ℂ)) :
    Integrable (Function.uncurry fun x y : Euc d => ‖h x - h y‖ ^ 2 * K (x - y)) (volume.prod volume) := by
  have hb1 := xint_xy1 (a := fun x => 2 * ‖h x‖ ^ 2) (G := K) ((xint_sq_bdd h).const_mul 2) hK.integrable
  have hb2 := xint_xy2 (a := fun x => 2 * ‖h x‖ ^ 2) (G := K) ((xint_sq_bdd h).const_mul 2) hK.integrable
  refine (hb1.add hb2).mono' ?_ (Eventually.of_forall fun p => ?_)
  · have : Continuous (fun p : Euc d × Euc d => ‖h p.1 - h p.2‖ ^ 2 * K (p.1 - p.2)) := by
      refine (((h.continuous.comp continuous_fst).sub (h.continuous.comp continuous_snd)).norm.pow 2).mul ?_
      exact hK.cont.comp (continuous_fst.sub continuous_snd)
    exact this.aestronglyMeasurable
  · show ‖‖h p.1 - h p.2‖ ^ 2 * K (p.1 - p.2)‖ ≤
      2 * ‖h p.1‖ ^ 2 * K (p.1 - p.2) + 2 * ‖h p.2‖ ^ 2 * K (p.1 - p.2)
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hK.nonneg _))]
    have h1 := xsq_le (h p.1) (h p.2)
    have h2 := hK.nonneg (p.1 - p.2)
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem xE_eq {K : Euc d → ℝ} (hK : XKer K) (h : 𝓢(Euc d, ℂ)) :
    ∫ y, ∫ x, ‖h x - h y‖ ^ 2 * K (x - y) = ∫ ξ, 2 * xmK K ξ * ‖𝓕 h ξ‖ ^ 2 := by
  rw [← xenergyK hK h]
  have hE := xe_int hK h
  have e2 : ∫ y, ∫ x, ‖h x - h y‖ ^ 2 * K (x - y) = ∫ x, ∫ y, ‖h x - h y‖ ^ 2 * K (x - y) :=
    (integral_integral_swap hE).symm
  have e1 : ∀ x : Euc d, ∫ y, ‖h x - h y‖ ^ 2 * K (x - y) = ∫ z, K z * ‖h x - h (x - z)‖ ^ 2 := by
    intro x
    have := integral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
      (fun y => ‖h x - h y‖ ^ 2 * K (x - y)) x
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sub_sub_cancel]
    ring
  have hS : Integrable (Function.uncurry fun x z : Euc d => K z * ‖h x - h (x - z)‖ ^ 2)
      (volume.prod volume) := by
    have hb1 : Integrable (fun p : Euc d × Euc d => (2 * ‖h p.1‖ ^ 2) * K p.2) (volume.prod volume) :=
      Integrable.mul_prod (f := fun x => 2 * ‖h x‖ ^ 2) (g := K) ((xint_sq_bdd h).const_mul 2) hK.integrable
    have hb2 : Integrable (fun p : Euc d × Euc d => (2 * ‖h (p.1 - p.2)‖ ^ 2) * K p.2)
        (volume.prod volume) :=
      (measurePreserving_sub_prod (volume : Measure (Euc d)) (volume : Measure (Euc d))).integrable_comp_of_integrable hb1
    refine (hb1.add hb2).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Continuous (fun p : Euc d × Euc d => K p.2 * ‖h p.1 - h (p.1 - p.2)‖ ^ 2) := by
        refine (hK.cont.comp continuous_snd).mul ?_
        exact (((h.continuous.comp continuous_fst).sub (h.continuous.comp (continuous_fst.sub continuous_snd))).norm.pow 2)
      exact this.aestronglyMeasurable
    · show ‖K p.2 * ‖h p.1 - h (p.1 - p.2)‖ ^ 2‖ ≤ 2 * ‖h p.1‖ ^ 2 * K p.2 + 2 * ‖h (p.1 - p.2)‖ ^ 2 * K p.2
      rw [Real.norm_of_nonneg (mul_nonneg (hK.nonneg _) (by positivity))]
      have h1 := xsq_le (h p.1) (h (p.1 - p.2))
      have h2 := hK.nonneg p.2
      nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  rw [e2]
  simp_rw [e1]
  rw [integral_integral_swap hS]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_const_mul]

end HRS.Commutator.Whole.XNRS
