import Mathlib

/-!
# S8.2 observed-time layer, packet T8A.C02: one-factor conditional density change

For a bounded probability density `k` (with respect to a probability measure `mu`) and a nonnegative cost `r` with
`∫ r ≤ A`, the exponentially tilted normalised density differs from `k` pointwise by at most
`K (1 - exp(-t r x)) + K² t A`, since `k e/Z - k = (k e/Z)(1 - Z) - k (1 - e)` and `0 ≤ 1 - Z = ∫ k (1 - e) ≤ K t A`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_one_factor_change {E : Type*} [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu] (k r : E → ℝ) (K A t : ℝ)
    (hK : 0≤K) (hA : 0≤A) (ht : 0≤t) (hk : Measurable k) (hr : Measurable r)
    (hk0 : ∀ x, 0≤k x) (hkB : ∀ x, k x≤K) (hk1 : ∫ x, k x ∂mu=1)
    (hr0 : ∀ x, 0≤r x) (hri : Integrable r mu) (hrA : ∫ x, r x ∂mu≤A)
    (hZ : 0<∫ x, k x*Real.exp (-t*r x) ∂mu)
    (hkB' : ∀ x, k x*Real.exp (-t*r x)/(∫ y, k y*Real.exp (-t*r y) ∂mu)≤K) :
    ∀ x, |k x*Real.exp (-t*r x)/(∫ y, k y*Real.exp (-t*r y) ∂mu)-k x|≤
      K*(1-Real.exp (-t*r x))+K^2*t*A := by
  intro x
  set Z : ℝ := ∫ y, k y * Real.exp (-t * r y) ∂mu with hZdef
  have he0 : ∀ y, 0 ≤ t * r y := fun y => mul_nonneg ht (hr0 y)
  have hepos : ∀ y, 0 < Real.exp (-t * r y) := fun y => Real.exp_pos _
  have hele : ∀ y, Real.exp (-t * r y) ≤ 1 := fun y =>
    Real.exp_le_one_iff.2 (by nlinarith [he0 y])
  have hem : Measurable fun y => Real.exp (-t * r y) := (measurable_const.mul hr).exp
  have hbd : ∀ g : E → ℝ, Measurable g → (∀ y, |g y| ≤ K) → Integrable g mu := fun g hg hb =>
    Integrable.of_bound hg.aestronglyMeasurable K
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb y)
  have hkint : Integrable k mu := hbd k hk fun y => by rw [abs_of_nonneg (hk0 y)]; exact hkB y
  have hkeint : Integrable (fun y => k y * Real.exp (-t * r y)) mu := hbd _ (hk.mul hem) fun y => by
    rw [abs_of_nonneg (mul_nonneg (hk0 y) (hepos y).le)]
    calc k y * Real.exp (-t * r y) ≤ K * 1 := mul_le_mul (hkB y) (hele y) (hepos y).le hK
      _ = K := mul_one K
  have hdint : Integrable (fun y => k y * (1 - Real.exp (-t * r y))) mu :=
    hbd _ (hk.mul (measurable_const.sub hem)) fun y => by
      rw [abs_of_nonneg (mul_nonneg (hk0 y) (by linarith [hele y]))]
      calc k y * (1 - Real.exp (-t * r y)) ≤ K * 1 :=
            mul_le_mul (hkB y) (by linarith [hepos y]) (by linarith [hele y]) hK
        _ = K := mul_one K
  have h1Z : 1 - Z = ∫ y, k y * (1 - Real.exp (-t * r y)) ∂mu := by
    have : (fun y => k y * (1 - Real.exp (-t * r y))) =
        fun y => k y - k y * Real.exp (-t * r y) := by funext y; ring
    rw [this, integral_sub hkint hkeint, hk1]
  have hd0 : 0 ≤ 1 - Z := by
    rw [h1Z]
    exact integral_nonneg fun y => mul_nonneg (hk0 y) (by linarith [hele y])
  have hdle : 1 - Z ≤ K * t * A := by
    rw [h1Z]
    calc ∫ y, k y * (1 - Real.exp (-t * r y)) ∂mu ≤ ∫ y, K * t * r y ∂mu := by
          refine integral_mono hdint (hri.const_mul (K * t)) fun y => ?_
          have h1 : 1 - Real.exp (-t * r y) ≤ t * r y := by
            have := Real.add_one_le_exp (-(t * r y))
            have e : -t * r y = -(t * r y) := by ring
            rw [e]; linarith
          calc k y * (1 - Real.exp (-t * r y)) ≤ K * (t * r y) :=
                mul_le_mul (hkB y) h1 (by linarith [hele y]) hK
            _ = K * t * r y := by ring
      _ = K * t * ∫ y, r y ∂mu := integral_const_mul _ _
      _ ≤ K * t * A := mul_le_mul_of_nonneg_left hrA (mul_nonneg hK ht)
  have hkt : 0 ≤ k x * Real.exp (-t * r x) / Z :=
    div_nonneg (mul_nonneg (hk0 x) (hepos x).le) hZ.le
  have key : k x * Real.exp (-t * r x) / Z - k x =
      (k x * Real.exp (-t * r x) / Z) * (1 - Z) - k x * (1 - Real.exp (-t * r x)) := by
    field_simp
    ring
  rw [key]
  have hA1 : (k x * Real.exp (-t * r x) / Z) * (1 - Z) ≤ K * (K * t * A) :=
    mul_le_mul (hkB' x) hdle hd0 hK
  have hA2 : 0 ≤ (k x * Real.exp (-t * r x) / Z) * (1 - Z) := mul_nonneg hkt hd0
  have hB1 : k x * (1 - Real.exp (-t * r x)) ≤ K * (1 - Real.exp (-t * r x)) :=
    mul_le_mul_of_nonneg_right (hkB x) (by linarith [hele x])
  have hB2 : 0 ≤ k x * (1 - Real.exp (-t * r x)) := mul_nonneg (hk0 x) (by linarith [hele x])
  rw [abs_le]
  constructor <;> nlinarith [hA1, hA2, hB1, hB2]

end HRS.MS.R26T8A
