import Mathlib

/-!
# S8.2 observed-time layer, packet T8A.C11: cavity logarithm derivative including the right endpoint zero

For `S ≥ 0` integrable, the map `u ↦ log ∫ exp(-u S)` has right derivative `-∫ S e^{-tS} / ∫ e^{-tS}` at every `t ≥ 0`
(within `Ici 0`; also two-sided for `t > 0`).  Proof by the slope characterisation and dominated convergence, using
that `u ↦ exp(-u y)` is `y`-Lipschitz on `[0, ∞)` for `y ≥ 0`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_c11_hasDerivAt (u y : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-v * y)) (Real.exp (-u * y) * (-y)) u := by
  have h : HasDerivAt (fun v : ℝ => -v * y) (-y) u := by
    simpa using ((hasDerivAt_id u).neg.mul_const y)
  exact h.exp

theorem r26t8a_c11_lip {y : ℝ} (hy : 0 ≤ y) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.exp (-s * y) - Real.exp (-t * y)| ≤ y * |s - t| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun v : ℝ => Real.exp (-v * y)) (C := y)
    (s := Set.Ici (0 : ℝ)) (x := t) (y := s)
    (fun v _ => (r26t8a_c11_hasDerivAt v y).differentiableAt)
    (fun v hv => by
      rw [(r26t8a_c11_hasDerivAt v y).deriv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hy,
        abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-v * y) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hv.out, hy])
      nlinarith [Real.exp_pos (-v * y)])
    (convex_Ici 0) ht hs
  simpa [Real.norm_eq_abs] using this

theorem r26t8a_log_laplace_derivative {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (S : E → ℝ)
    (hS : Measurable S) (hS0 : ∀ x, 0 ≤ S x) (hSi : Integrable S P) :
    ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt
      (fun u => Real.log (∫ x, Real.exp (-u*S x) ∂P))
      (-(∫ x, S x * Real.exp (-t*S x) ∂P) / (∫ x, Real.exp (-t*S x) ∂P))
      (Set.Ici 0) t := by
  intro t ht
  have hem : ∀ u : ℝ, Measurable fun x => Real.exp (-u * S x) := fun u =>
    (measurable_const.mul hS).exp
  have hint : ∀ u : ℝ, 0 ≤ u → Integrable (fun x => Real.exp (-u * S x)) P := fun u hu =>
    Integrable.of_bound (C := 1) (hem u).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith [hS0 x]))
  have hZpos : 0 < ∫ x, Real.exp (-t * S x) ∂P := by
    refine (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) (hint t ht)).2 ?_
    have : Function.support (fun x => Real.exp (-t * S x)) = Set.univ := by
      ext x; simp [Real.exp_pos]
    rw [this]; simp
  have hderiv : HasDerivWithinAt (fun u => ∫ x, Real.exp (-u * S x) ∂P)
      (-(∫ x, S x * Real.exp (-t * S x) ∂P)) (Set.Ici 0) t := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hlim : Tendsto (fun s => ∫ x, (s - t)⁻¹ * (Real.exp (-s * S x) - Real.exp (-t * S x)) ∂P)
        (𝓝[Set.Ici 0 \ {t}] t) (𝓝 (∫ x, -(S x * Real.exp (-t * S x)) ∂P)) := by
      refine tendsto_integral_filter_of_dominated_convergence S ?_ ?_ hSi ?_
      · exact Eventually.of_forall fun s =>
          (measurable_const.mul ((hem s).sub (hem t))).aestronglyMeasurable
      · refine eventually_nhdsWithin_of_forall fun s hs => Eventually.of_forall fun x => ?_
        have hs0 : 0 ≤ s := hs.1
        have hst : s - t ≠ 0 := sub_ne_zero.2 hs.2
        rw [Real.norm_eq_abs, abs_mul, abs_inv]
        have := r26t8a_c11_lip (hS0 x) hs0 ht
        have hpos : 0 < |s - t| := abs_pos.2 hst
        rw [inv_mul_le_iff₀ hpos]
        linarith
      · refine Eventually.of_forall fun x => ?_
        have h1 := (hasDerivAt_iff_tendsto_slope.1 (r26t8a_c11_hasDerivAt t (S x))).mono_left
          (nhdsWithin_mono t (fun y (hy : y ∈ Set.Ici (0:ℝ) \ {t}) => hy.2))
        have h2 := h1.congr (fun s => by rw [slope_def_module, smul_eq_mul])
        have e : Real.exp (-t * S x) * (-S x) = -(S x * Real.exp (-t * S x)) := by ring
        rw [e] at h2
        exact h2
    rw [integral_neg] at hlim
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    have hs0 : 0 ≤ s := hs.1
    rw [slope_def_module, smul_eq_mul, ← integral_sub (hint s hs0) (hint t ht), ← integral_const_mul]
  exact hderiv.log hZpos.ne'

end HRS.MS.R26T8A
