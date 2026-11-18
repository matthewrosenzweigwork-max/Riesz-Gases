import HRS.MS.S82UG3

/-!
# S8.2 A04 (S82U), part 4: `u4Env p q ∈ L²(canonicalP)`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82

section master
variable {d N : ℕ}

lemma u4_Env_meas (p q : ℝ) : Measurable (u4Env (d := d) (N := N) p q) := by
  unfold u4Env
  refine ((measurable_const.add measurable_norm).pow_const p).mul ?_
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  exact measurable_const.add (((measurable_pi_apply i).sub (measurable_pi_apply j)).norm.pow_const _)

lemma u4_single_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (hf : ∀ i, 1 ≤ f i) (i : ι) :
    f i ≤ ∏ j, f j := by
  have := Finset.prod_le_prod_of_subset_of_one_le₀ (f := f) (s := {i}) (t := Finset.univ)
    (Finset.subset_univ _) (fun j _ => by linarith [hf j]) (fun j _ _ => hf j)
  simpa using this

lemma u4_one_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ j, f j := by
  have := Finset.prod_le_prod_of_subset_of_one_le₀ (f := f) (s := ∅) (t := Finset.univ)
    (Finset.empty_subset _) (fun j _ => by linarith [hf j]) (fun j _ _ => hf j)
  simpa using this

lemma u4_one_add_norm_le (hN : 0 < N) (X : EucConfig d N) : 1 + ‖X‖ ≤ ∏ i, (1 + ‖X i‖) := by
  have h1 : ∀ i, 1 ≤ 1 + ‖X i‖ := fun i => by linarith [norm_nonneg (X i)]
  have h2 : ∀ i, 1 + ‖X i‖ ≤ ∏ j, (1 + ‖X j‖) := fun i =>
    u4_single_le_prod (fun j => 1 + ‖X j‖) h1 i
  have h3 : ‖X‖ ≤ (∏ j, (1 + ‖X j‖)) - 1 := by
    refine (pi_norm_le_iff_of_nonneg ?_).2 fun i => ?_
    · have : 1 ≤ ∏ j, (1 + ‖X j‖) := u4_one_le_prod (fun j => 1 + ‖X j‖) h1
      linarith
    · linarith [h2 i]
  linarith

theorem u4_env_L2 (hd : 2 ≤ d) (hN : 0 < N) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Integrable (fun X => (u4Env p q X) ^ 2) (canonicalP d N a beta) := by
  obtain ⟨Kc, hKc, hpole⟩ := u4_pole_prod hd hN hq hbeta
  have hc : 0 < beta * a / 2 := by positivity
  have h1 : Integrable (fun z : Euc d => (1 + ‖z‖) ^ (2 * p) * Real.exp (-(beta * a / 2) * ‖z‖ ^ 2)) :=
    u4_gauss_int1 hd hc (by linarith)
  have h2 : Integrable (fun X : EucConfig d N => ∏ i, ((1 + ‖X i‖) ^ (2 * p) *
      Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2))) (volume : Measure (EucConfig d N)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin N => (volume : Measure (Euc d)))
      (f := fun _ z => (1 + ‖z‖) ^ (2 * p) * Real.exp (-(beta * a / 2) * ‖z‖ ^ 2)) (fun _ => h1)
    simpa [volume_pi] using this
  refine u4_int_of_w hd ha hbeta ?_
  refine Integrable.mono' (h2.const_mul Kc)
    ((u4_w_meas d N a beta).mul ((u4_Env_meas p q).pow_const 2)).aestronglyMeasurable ?_
  have hae : ∀ᵐ X ∂(volume : Measure (EucConfig d N)), X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using u4_coll_null (by omega) N
  filter_upwards [hae] with X hX
  have hw0 : 0 ≤ u4w d N a beta X := by unfold u4w; exact (Real.exp_pos _).le
  have hE0 : 0 ≤ (u4Env p q X) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 hE0)]
  -- rewrite the envelope square
  have hsq : (u4Env p q X) ^ 2 = (1 + ‖X‖) ^ (2 * p) *
      ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q)) ^ 2 := by
    unfold u4Env
    rw [mul_pow, ← Finset.prod_pow]
    congr 1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [norm_nonneg X])]
      congr 1; push_cast; ring
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_pow]
  have hweight : u4w d N a beta X = (∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) *
      Real.exp (-(beta / N) * u4Sp X) := by
    unfold u4w
    rw [u4_H_eq hd a X, ← Real.exp_sum, ← Real.exp_add]
    congr 1
    have : ∑ i, -(beta * a / 2) * ‖X i‖ ^ 2 = -beta * ∑ i, confinement a (X i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold confinement; ring
    rw [this]; ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hSp := u4_Sp_nonneg X
  have hexp : Real.exp (beta / (2 * N) * u4Sp X) * Real.exp (-(beta / N) * u4Sp X) ≤ 1 := by
    rw [← Real.exp_add]
    refine Real.exp_le_one_iff.2 ?_
    have : beta / (2 * N) * u4Sp X + -(beta / N) * u4Sp X = -(beta / (2 * N)) * u4Sp X := by
      field_simp; ring
    rw [this]
    have : 0 ≤ beta / (2 * N) := by positivity
    nlinarith
  have hnorm : (1 + ‖X‖) ^ (2 * p) ≤ ∏ i, (1 + ‖X i‖) ^ (2 * p) := by
    rw [Real.finsetProd_rpow _ _ (fun i _ => by linarith [norm_nonneg (X i)])]
    exact Real.rpow_le_rpow (by linarith [norm_nonneg X]) (u4_one_add_norm_le hN X) (by linarith)
  have hpr := hpole X hX
  have hpr0 : 0 ≤ ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q)) ^ 2 :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by positivity
  have hEn0 : 0 ≤ (1 + ‖X‖) ^ (2 * p) := Real.rpow_nonneg (by linarith [norm_nonneg X]) _
  have hG0 : 0 ≤ ∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2) := Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have hP0 : 0 ≤ ∏ i, (1 + ‖X i‖) ^ (2 * p) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by linarith [norm_nonneg (X i)]) _
  rw [hsq, hweight]
  have hprod : (∏ i, ((1 + ‖X i‖) ^ (2 * p) * Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2))) =
      (∏ i, (1 + ‖X i‖) ^ (2 * p)) * ∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2) := Finset.prod_mul_distrib
  rw [hprod]
  have hE1 := Real.exp_pos (-(beta / N) * u4Sp X)
  calc (∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) * Real.exp (-(beta / N) * u4Sp X) *
        ((1 + ‖X‖) ^ (2 * p) * ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q)) ^ 2)
      ≤ (∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) * Real.exp (-(beta / N) * u4Sp X) *
        ((∏ i, (1 + ‖X i‖) ^ (2 * p)) * (Kc * Real.exp (beta / (2 * N) * u4Sp X))) := by
        gcongr
    _ = Kc * (((∏ i, (1 + ‖X i‖) ^ (2 * p)) * ∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) *
          (Real.exp (beta / (2 * N) * u4Sp X) * Real.exp (-(beta / N) * u4Sp X))) := by ring
    _ ≤ Kc * (((∏ i, (1 + ‖X i‖) ^ (2 * p)) * ∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) * 1) := by
        gcongr
    _ = Kc * ((∏ i, (1 + ‖X i‖) ^ (2 * p)) * ∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) := by ring

end master

end HRS.MS.S82U
