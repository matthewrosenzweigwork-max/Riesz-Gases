import HRS.MS.FinNoiseAux16
import HRS.MS.SpecAux3

/-!
# S8.6 `finite_noise`: eigenbasis of a trace-class form bounded below by a positive diagonal form (S86)

* `s86_rankone_compact`, `s86_formOp_compact`: the operator `formOp C` of a trace-class form is compact (norm-convergent
  sum of rank-one operators from `IsTraceClassCov.exists_decomp'`).
* `s86_form_eigenbasis`: if moreover `C ≥ c D₀` with `D₀` diagonal (positive weights) in a Hilbert basis, then `C` is
  diagonal in some Hilbert basis with positive eigenvalues (`s8p_compact_selfadjoint_basis`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS HRS.HilbertCLTAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem s86_rankone_compact (a b : H) :
    IsCompactOperator ((innerSL ℝ a).smulRight b : H →L[ℝ] H) := by
  refine (isCompactOperator_iff_image_closedBall_subset_compact
    (((innerSL ℝ a).smulRight b : H →L[ℝ] H) : H →ₗ[ℝ] H) (r := 1) one_pos).2
    ⟨(fun t : ℝ => t • b) '' Icc (-‖a‖) ‖a‖,
    (isCompact_Icc.image (continuous_id.smul continuous_const)), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  refine ⟨inner ℝ a x, ⟨?_, ?_⟩, rfl⟩
  · have := abs_real_inner_le_norm a x
    have h2 : |inner ℝ a x| ≤ ‖a‖ := this.trans (by nlinarith [norm_nonneg a, norm_nonneg x])
    linarith [(abs_le.1 h2).1]
  · have := abs_real_inner_le_norm a x
    have h2 : |inner ℝ a x| ≤ ‖a‖ := this.trans (by nlinarith [norm_nonneg a, norm_nonneg x])
    linarith [(abs_le.1 h2).2]

variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem s86_formOp_compact {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    IsCompactOperator (formOp C) := by
  obtain ⟨ℓ, hs, hℓ⟩ := hC.exists_decomp'
  set R : ℕ → H →L[ℝ] H := fun j => (innerSL ℝ (ℓ j)).smulRight (ℓ j) with hR
  have hRn : ∀ j, ‖R j‖ ≤ ‖ℓ j‖ ^ 2 := fun j => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    simp only [hR, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul,
      Real.norm_eq_abs]
    calc |inner ℝ (ℓ j) x| * ‖ℓ j‖ ≤ ‖ℓ j‖ * ‖x‖ * ‖ℓ j‖ :=
          mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
      _ = ‖ℓ j‖ ^ 2 * ‖x‖ := by ring
  have hsum : Summable R :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun j => norm_nonneg _) hRn hs)
  have hval : ∑' j, R j = formOp C := by
    refine ContinuousLinearMap.ext fun x => ?_
    refine ext_inner_right ℝ fun y => ?_
    have h1 : HasSum (fun j => R j x) ((∑' j, R j) x) :=
      (hsum.hasSum.map (ContinuousLinearMap.apply ℝ H x) (ContinuousLinearMap.apply ℝ H x).continuous)
    have h2 : HasSum (fun j => inner ℝ y (R j x)) (inner ℝ y ((∑' j, R j) x)) := by
      simpa using h1.mapL (innerSL ℝ y)
    have h3 : HasSum (fun j => inner ℝ y (R j x)) (C x y) := by
      have := hℓ x y
      convert this using 2 with j
      simp [hR, inner_smul_right, real_inner_comm]
    rw [inner_formOp, real_inner_comm]
    exact h2.unique h3
  have hlim : Tendsto (fun n => ∑ j ∈ Finset.range n, R j) atTop (𝓝 (formOp C)) := by
    rw [← hval]; exact hsum.hasSum.tendsto_sum_nat
  refine isCompactOperator_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  induction n with
  | zero => simpa using isCompactOperator_zero
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact ih.add (s86_rankone_compact _ _)

theorem s86_form_eigenbasis {C D₀ : H →L[ℝ] H →L[ℝ] ℝ} {κ : Type*} (e : HilbertBasis κ ℝ H)
    (dd : κ → ℝ) (hdd : ∀ i, 0 < dd i) (hD₀e : ∀ i y, D₀ (e i) y = dd i * inner ℝ (e i : H) y)
    {c : ℝ} (hc : 0 < c) (hcD : ∀ x, c * D₀ x x ≤ C x x) (hC : IsTraceClassCov C) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ H) (lam : ι → ℝ), (∀ i, 0 < lam i) ∧
      ∀ i y, C (b i) y = lam i * inner ℝ (b i : H) y := by
  have hsymm : ((formOp C : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric := fun x y => by
    show inner ℝ (formOp C x) y = inner ℝ x (formOp C y)
    rw [inner_formOp, real_inner_comm, inner_formOp, hC.symm]
  have hpos : ∀ x, 0 ≤ ⟪x, formOp C x⟫ := fun x => by
    rw [real_inner_comm, inner_formOp]; exact hC.nonneg x
  have hinj : Function.Injective (formOp C) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h0 : C x x = 0 := by rw [← inner_formOp, hx]; simp
    have hD : D₀ x x ≤ 0 := by
      have := hcD x
      rw [h0] at this
      nlinarith
    have hrep : HasSum (fun i => inner ℝ (e i : H) x • (e i : H)) x := by
      simpa [HilbertBasis.repr_apply_apply] using e.hasSum_repr x
    have h1 := hrep.mapL (D₀.flip x)
    simp only [ContinuousLinearMap.flip_apply, map_smul, hD₀e, smul_eq_mul] at h1
    have hz : ∀ i, inner ℝ (e i : H) x = 0 := fun i => by
      have hnn : ∀ j, 0 ≤ inner ℝ (e j : H) x * (dd j * inner ℝ (e j : H) x) := fun j => by
        have : inner ℝ (e j : H) x * (dd j * inner ℝ (e j : H) x) =
            dd j * inner ℝ (e j : H) x ^ 2 := by ring
        rw [this]; exact mul_nonneg (hdd j).le (sq_nonneg _)
      have := le_hasSum h1 i (fun j _ => hnn j)
      have h2 : dd i * inner ℝ (e i : H) x ^ 2 ≤ 0 := by
        have e2 : inner ℝ (e i : H) x * (dd i * inner ℝ (e i : H) x) =
            dd i * inner ℝ (e i : H) x ^ 2 := by ring
        rw [← e2]; exact this.trans hD
      have h3 : inner ℝ (e i : H) x ^ 2 ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        nlinarith [hdd i]
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h3 (sq_nonneg _))
    have h4 : HasSum (fun i => inner ℝ (e i : H) x • (e i : H)) 0 := by
      simpa [hz] using hasSum_zero
    exact (h4.unique hrep).symm
  obtain ⟨ι, b, lam, hlam, hb, -⟩ := HRS.MS.Spec.s8p_compact_selfadjoint_basis (formOp C)
    (s86_formOp_compact hC) hsymm hpos hinj
  refine ⟨ι, b, lam, hlam, fun i y => ?_⟩
  rw [← inner_formOp, hb i, inner_smul_left]
  simp

end HRS.MS.FinNoise
