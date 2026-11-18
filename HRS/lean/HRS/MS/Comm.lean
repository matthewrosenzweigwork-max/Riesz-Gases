import HRS.Whole.Static
import HRS.Whole.MovtrAux4

/-!
# MS-COMM: the commutator kernel of a Lipschitz field is in the S3.3 and S3.5 kernel classes

Proves `HRS.Whole.commutatorKernel_isBounded` (S3.3, `B = sΛ`, `0 < s`) and
`HRS.Whole.commutatorKernel_log_isBounded` (S3.5, `B = Λ`, `s = 0`) as
`commutatorKernel_isBounded_proof` and `commutatorKernel_log_isBounded_proof`.

Mathematics: `h(x,y) = ⟨v(x)-v(y), ∇g(x-y)⟩`.
* symmetry: `∇g` is odd off the origin (explicit formula `movtr_rieszKernelGrad_eq`), and
  `h(x,x) = 0` because `v(x)-v(x) = 0`;
* measurability: `v` is continuous, `∇g` is measurable (`movtr_rieszKernelGrad_measurable`);
* bound: `|h| ≤ Λ‖z‖·‖∇g(z)‖` with `‖∇g(z)‖ = σ‖z‖^{-s-1}` (`movtr_rieszKernelGrad_norm`);
  for `s > 0` this gives `|h| ≤ sΛ‖z‖^{-s}`; for `s = 0` it gives `|h| ≤ Λ`, and the
  log kernel `K(x,y) = -log‖x-y‖ + ℓ(x) + ℓ(y)` is nonnegative because
  `‖x-y‖² ≤ (1+‖x‖²)(1+‖y‖²)` (the difference is `(‖x‖‖y‖-1)² + 2(‖x‖‖y‖+⟨x,y⟩) ≥ 0`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Comm

open HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- The force is odd off the origin. -/
lemma comm_grad_odd {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s (-z) = -rieszKernelGrad d s z := by
  rw [movtr_rieszKernelGrad_eq s (neg_ne_zero.mpr hz), movtr_rieszKernelGrad_eq s hz,
    norm_neg, smul_neg]

/-- Symmetry of the commutator kernel. -/
lemma comm_symm (v : Euc d → Euc d) (x y : Euc d) :
    commutatorKernel d s v x y = commutatorKernel d s v y x := by
  by_cases hxy : x = y
  · subst hxy; rfl
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  unfold commutatorKernel
  rw [show y - x = -(x - y) by abel, comm_grad_odd hz, inner_neg_right,
    ← neg_sub (v x) (v y), inner_neg_left, neg_neg]

/-- Measurability of the commutator kernel on the product space. -/
lemma comm_meas (v : Euc d → Euc d) (hv : Measurable v) :
    Measurable fun p : Euc d × Euc d => commutatorKernel d s v p.1 p.2 := by
  unfold commutatorKernel
  exact ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).inner
    ((movtr_rieszKernelGrad_measurable (d := d) s).comp (measurable_fst.sub measurable_snd))

/-- The Lipschitz bound `‖v x - v y‖ ≤ Λ‖x - y‖`. -/
lemma comm_lip {Λ : NNReal} {v : Euc d → Euc d} (hv : LipschitzWith Λ v) (x y : Euc d) :
    ‖v x - v y‖ ≤ (Λ : ℝ) * ‖x - y‖ := by
  have := hv.dist_le_mul x y
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- The bound for `s > 0`: `|h| ≤ sΛ(1 + |x-y|^{-s})`, off the diagonal. -/
lemma comm_bound_pos (hs0 : 0 < s) (Λ : NNReal) (v : Euc d → Euc d)
    (hv : LipschitzWith Λ v) (x y : Euc d) (hxy : x ≠ y) :
    |commutatorKernel d s v x y| ≤ s * (Λ : ℝ) * (1 + rieszWeight s (x - y)) := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
  have hs : s ≠ 0 := hs0.ne'
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := NNReal.coe_nonneg Λ
  have hw : rieszWeight s (x - y) = ‖x - y‖ ^ (-s) := by simp [rieszWeight, hs]
  have hG : ‖rieszKernelGrad d s (x - y)‖ = s * ‖x - y‖ ^ (-s - 1) := by
    rw [movtr_rieszKernelGrad_norm s hs0.le hz]
    simp [movtr_sigma, hs]
  have hpow : ‖x - y‖ ^ (-s) = ‖x - y‖ ^ (-s - 1) * ‖x - y‖ := by
    rw [← Real.rpow_add_one hzpos.ne']
    congr 1
    ring
  have key : |commutatorKernel d s v x y| ≤ s * (Λ : ℝ) * ‖x - y‖ ^ (-s) := by
    unfold commutatorKernel
    calc |inner ℝ (v x - v y) (rieszKernelGrad d s (x - y))|
        ≤ ‖v x - v y‖ * ‖rieszKernelGrad d s (x - y)‖ := abs_real_inner_le_norm _ _
      _ ≤ ((Λ : ℝ) * ‖x - y‖) * (s * ‖x - y‖ ^ (-s - 1)) :=
          mul_le_mul (comm_lip hv x y) hG.le (norm_nonneg _) (by positivity)
      _ = s * (Λ : ℝ) * ‖x - y‖ ^ (-s) := by rw [hpow]; ring
  rw [hw]
  have hsΛ : 0 ≤ s * (Λ : ℝ) := mul_nonneg hs0.le hΛ
  rw [mul_add, mul_one]
  linarith [key]

/-- Nonnegativity of the spherical log kernel `K(x,y) = -log|x-y| + ℓ(x) + ℓ(y)`. -/
lemma comm_log_nonneg (x y : Euc d) : 0 ≤ sphericalLogKernel x y := by
  by_cases hxy : x = y
  · subst hxy
    unfold sphericalLogKernel logWeight
    have h1 : 0 ≤ Real.log (1 + ‖x‖ ^ 2) := Real.log_nonneg (by have := sq_nonneg ‖x‖; linarith)
    simp only [sub_self, norm_zero, Real.log_zero, neg_zero, zero_add]
    linarith
  have hc : ‖x - y‖ ^ 2 ≤ (1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
    have h1 := norm_sub_sq_real x y
    have h2 : -(‖x‖ * ‖y‖) ≤ inner ℝ x y := by
      have := abs_real_inner_le_norm x y
      linarith [neg_abs_le (inner ℝ x y)]
    nlinarith [sq_nonneg (‖x‖ * ‖y‖ - 1)]
  have hpos1 : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hpos2 : 0 < 1 + ‖y‖ ^ 2 := by positivity
  have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h1 : Real.log (‖x - y‖ ^ 2) ≤ Real.log ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) :=
    Real.log_le_log (by positivity) hc
  rw [Real.log_pow, Real.log_mul hpos1.ne' hpos2.ne'] at h1
  unfold sphericalLogKernel logWeight
  push_cast at h1
  linarith

/-- The bound for `s = 0`: `|h| ≤ Λ(1 + K)`, off the diagonal. -/
lemma comm_bound_log (Λ : NNReal) (v : Euc d → Euc d)
    (hv : LipschitzWith Λ v) (x y : Euc d) (hxy : x ≠ y) :
    |commutatorKernel d 0 v x y| ≤ (Λ : ℝ) * (1 + sphericalLogKernel x y) := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := NNReal.coe_nonneg Λ
  have hG : ‖rieszKernelGrad d 0 (x - y)‖ = ‖x - y‖⁻¹ := by
    rw [movtr_rieszKernelGrad_norm 0 le_rfl hz]
    norm_num [movtr_sigma, Real.rpow_neg_one]
  have key : |commutatorKernel d 0 v x y| ≤ (Λ : ℝ) := by
    unfold commutatorKernel
    calc |inner ℝ (v x - v y) (rieszKernelGrad d 0 (x - y))|
        ≤ ‖v x - v y‖ * ‖rieszKernelGrad d 0 (x - y)‖ := abs_real_inner_le_norm _ _
      _ ≤ ((Λ : ℝ) * ‖x - y‖) * ‖x - y‖⁻¹ :=
          mul_le_mul (comm_lip hv x y) hG.le (norm_nonneg _) (by positivity)
      _ = (Λ : ℝ) := by rw [mul_assoc, mul_inv_cancel₀ hzpos.ne', mul_one]
  have hK := comm_log_nonneg (d := d) x y
  rw [mul_add, mul_one]
  linarith [key, mul_nonneg hΛ hK]

/-- Theorem S3.3 commutator class membership (proof). -/
theorem commutatorKernel_isBounded_proof (hs0 : 0 < s) (Λ : ℝ≥0) (v : Euc d → Euc d)
    (hv : LipschitzWith Λ v) : IsBoundedPairKernel s (s * Λ) (commutatorKernel d s v) :=
  ⟨comm_meas v hv.continuous.measurable, comm_symm v,
    fun x y hxy => comm_bound_pos hs0 Λ v hv x y hxy⟩

/-- Theorem S3.5 commutator class membership (proof). -/
theorem commutatorKernel_log_isBounded_proof (hd : 1 ≤ d) (Λ : ℝ≥0) (v : Euc d → Euc d)
    (hv : LipschitzWith Λ v) : IsLogBoundedPairKernel Λ (commutatorKernel d 0 v) :=
  ⟨comm_meas (s := 0) v hv.continuous.measurable, comm_symm v,
    fun x y hxy => comm_bound_log Λ v hv x y hxy⟩

example := (@commutatorKernel_isBounded_proof : type_of% @HRS.Whole.commutatorKernel_isBounded)
example := (@commutatorKernel_log_isBounded_proof :
  type_of% @HRS.Whole.commutatorKernel_log_isBounded)

end HRS.MS.Comm
