import HRS.Main.GFB3Aux2
import HRS.Main.GFSpec2

/-!
# Packet GFB3, part 3: the trace-duality identity for the covariance difference
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform

variable {d : ℕ}

/-- `B(u, v) = ∑_i ε_i ⟨e_i, u⟩⟨f_i, v⟩` as a bounded bilinear form. -/
def gfb3_B {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {n : ℕ}
    (e f : Fin n → H) (ε : Fin n → ℝ) : H →L[ℝ] H →L[ℝ] ℝ :=
  ∑ i, ε i • (innerSL ℝ (e i)).smulRight (innerSL ℝ (f i))

lemma gfb3_B_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {n : ℕ}
    (e f : Fin n → H) (ε : Fin n → ℝ) (u v : H) :
    gfb3_B e f ε u v = ∑ i, ε i * (inner ℝ (e i) u * inner ℝ (f i) v) := by
  unfold gfb3_B
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, mul_comm, mul_left_comm]

lemma gfb3_B_norm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {n : ℕ}
    (e f : Fin n → H) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) : ‖gfb3_B e f ε‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [one_mul, gfb3_B_apply]
  have hu : ∑ i, (inner ℝ (e i) u) ^ 2 ≤ ‖u‖ ^ 2 := by
    have := he.sum_inner_products_le (s := Finset.univ) (x := u)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hv : ∑ i, (inner ℝ (f i) v) ^ 2 ≤ ‖v‖ ^ 2 := by
    have := hf.sum_inner_products_le (s := Finset.univ) (x := v)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have h1 : |∑ i, ε i * (inner ℝ (e i) u * inner ℝ (f i) v)| ≤
      ∑ i, |inner ℝ (e i) u| * |inner ℝ (f i) v| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul]
    calc |ε i| * (|inner ℝ (e i) u| * |inner ℝ (f i) v|) ≤ 1 * (|inner ℝ (e i) u| * |inner ℝ (f i) v|) :=
          mul_le_mul_of_nonneg_right (hε i) (by positivity)
      _ = _ := one_mul _
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |inner ℝ (e i) u|)
    (fun i => |inner ℝ (f i) v|)
  simp only [sq_abs] at h2
  have h3 : (∑ i, |inner ℝ (e i) u| * |inner ℝ (f i) v|) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    calc _ ≤ _ := h2
      _ ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 :=
        mul_le_mul hu hv (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have h4 : ∑ i, |inner ℝ (e i) u| * |inner ℝ (f i) v| ≤ ‖u‖ * ‖v‖ :=
    le_of_sq_le_sq (by simpa using h3) (by positivity)
  exact (Real.norm_eq_abs _ ▸ h1.trans h4)

lemma gfb3_family_cov {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] {n : ℕ} (e f : Fin n → NegSobolev d γ) (ε : Fin n → ℝ) :
    ∑ i, ε i * covForm γ q μ (e i) (f i) = 2 * q * ∫ x, gfb3_F γ (gfb3_B e f ε) x ∂μ := by
  have hcc : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q := Real.mul_self_sqrt (by positivity)
  have hcont : ∀ (i : Fin n) (j : Fin d) (u : NegSobolev d γ), Continuous fun a =>
      inner ℝ (bVec γ j a) u := fun i j u =>
    (HRS.Uniform.Q14.q14_continuous_bVec hγ j).inner continuous_const
  have hint : ∀ (i : Fin n) (j : Fin d), Integrable (fun a =>
      inner ℝ (bVec γ j a) (e i) * inner ℝ (bVec γ j a) (f i)) μ := fun i j =>
    ((hcont i j (e i)).mul (hcont i j (f i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ (i : Fin n) (j : Fin d) (a : Torus d),
      inner ℝ (Real.sqrt (2 * q) • bVec γ j a) (e i) * inner ℝ (Real.sqrt (2 * q) • bVec γ j a) (f i) =
        2 * q * (inner ℝ (bVec γ j a) (e i) * inner ℝ (bVec γ j a) (f i)) := by
    intro i j a
    simp only [inner_smul_left, conj_trivial]
    linear_combination (inner ℝ (bVec γ j a) (e i) * inner ℝ (bVec γ j a) (f i)) * hcc
  have hF : ∀ a, gfb3_F γ (gfb3_B e f ε) a =
      ∑ j : Fin d, ∑ i : Fin n, ε i * (inner ℝ (bVec γ j a) (e i) * inner ℝ (bVec γ j a) (f i)) := by
    intro a
    unfold gfb3_F
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gfb3_B_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (e i), real_inner_comm (f i)]
  simp_rw [HRS.Uniform.Q14.q14_covForm_apply hγ hq μ, hpt]
  simp_rw [hF]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ fun i _ => (hint i j).const_mul _)]
  simp_rw [integral_finset_sum _ (fun i _ => (hint i _).const_mul _)]
  simp_rw [integral_const_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end HRS.GF
