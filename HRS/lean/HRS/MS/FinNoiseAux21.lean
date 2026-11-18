import HRS.MS.FinNoiseAux20
import HRS.MS.FinNoiseAux17

/-!
# S8.6 `finite_noise`: Hilbert-Schmidt calculus, part 2 (S86, for Araki-Yamagami)

* `s86_hs2_basis`: `hs2` does not depend on the Hilbert basis.
* `s86_hs_compact`: a Hilbert-Schmidt operator is compact.
* `s86_diag_op`: for weights `w` with `∑ w < ∞` the diagonal operator `∑ w_j ⟨e_j,·⟩ e_j` (compact, positive, injective
  when `w > 0`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

theorem s86_hs2_basis {ι κ : Type*} (b : HilbertBasis ι ℝ K) (e : HilbertBasis κ ℝ K)
    (A : K →L[ℝ] K) : hs2 b A = hs2 e A := by
  have h1 : ∀ j, ENNReal.ofReal (‖A (b j)‖ ^ 2) =
      ∑' k, ENNReal.ofReal (inner ℝ (b j : K) (ContinuousLinearMap.adjoint A (e k)) ^ 2) := fun j => by
    have := hasSum_inner_sq e (A (b j))
    rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) this.summable]
    refine tsum_congr fun k => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  have h2 : ∀ k, ENNReal.ofReal (‖ContinuousLinearMap.adjoint A (e k)‖ ^ 2) =
      ∑' j, ENNReal.ofReal (inner ℝ (b j : K) (ContinuousLinearMap.adjoint A (e k)) ^ 2) := fun k => by
    have := hasSum_inner_sq b (ContinuousLinearMap.adjoint A (e k))
    rw [← this.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) this.summable]
    refine tsum_congr fun j => ?_
    rw [real_inner_comm]
  have : hs2 b A = hs2 e (ContinuousLinearMap.adjoint A) := by
    unfold hs2
    simp_rw [h1, h2]
    exact ENNReal.tsum_comm
  rw [this, ← s86_hs2_adjoint]

theorem s86_finsum_rankone_compact {ι : Type*} (F : Finset ι) (a b : ι → K) :
    IsCompactOperator ⇑(∑ j ∈ F, ((innerSL ℝ (a j)).smulRight (b j) : K →L[ℝ] K)) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero
  | insert j F hj ih =>
    rw [Finset.sum_insert hj]
    exact (s86_rankone_compact _ _).add ih

theorem s86_amgm (u v t : ℝ) (ht : 0 < t) : |u| * v * 2 ≤ t * u ^ 2 + v ^ 2 / t := by
  have h : t * u ^ 2 + v ^ 2 / t - |u| * v * 2 = (t * |u| - v) ^ 2 / t := by
    have : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    rw [this]
    field_simp
    ring
  have : 0 ≤ (t * |u| - v) ^ 2 / t := by positivity
  linarith

theorem s86_tail_bound {ι : Type*} (e : HilbertBasis ι ℝ K) (A : K →L[ℝ] K)
    (hAs : Summable fun j => ‖A (e j)‖ ^ 2) (F : Finset ι) (x : K) {t : ℝ} (ht : 0 < t) :
    ‖A x - ∑ j ∈ F, inner ℝ (e j : K) x • A (e j)‖ ≤
      (t * ‖x‖ ^ 2 + (∑' j : {j // j ∉ F}, ‖A (e j.1)‖ ^ 2) / t) / 2 := by
  classical
  have hu : HasSum (fun j => inner ℝ (e j : K) x ^ 2) (‖x‖ ^ 2) := by
    have := hasSum_inner_sq e x
    convert this using 2 with n
    rw [real_inner_comm]
  have hv : HasSum (fun j => inner ℝ (e j : K) x • A (e j)) (A x) := by
    have h1 := (e.hasSum_repr x).mapL A
    convert h1 using 2 with j
    simp [HilbertBasis.repr_apply_apply]
  set g : ι → ℝ := fun j => (t * inner ℝ (e j : K) x ^ 2 + ‖A (e j)‖ ^ 2 / t) / 2 with hg
  have hgs : Summable g := ((hu.summable.mul_left t).add (hAs.div_const t)).div_const 2
  have hnv : ∀ j, ‖inner ℝ (e j : K) x • A (e j)‖ ≤ g j := fun j => by
    rw [norm_smul, Real.norm_eq_abs, hg]
    simp only
    have h1 : 0 ≤ |inner ℝ (e j : K) x| := abs_nonneg _
    have h2 : 0 ≤ ‖A (e j)‖ := norm_nonneg _
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have := s86_amgm (inner ℝ (e j : K) x) ‖A (e j)‖ t ht
    linarith
  have hnorm : Summable fun j => ‖inner ℝ (e j : K) x • A (e j)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnv hgs
  have hsplit := hv.summable.sum_add_tsum_subtype_compl F
  rw [hv.tsum_eq] at hsplit
  have h1 : A x - ∑ j ∈ F, inner ℝ (e j : K) x • A (e j) =
      ∑' j : {j // j ∉ F}, inner ℝ (e j.1 : K) x • A (e j.1) := by
    rw [← hsplit]; abel
  rw [h1]
  have hsubn : Summable (fun j : {j // j ∉ F} => ‖inner ℝ (e j.1 : K) x • A (e j.1)‖) :=
    hnorm.subtype _
  have hsubg : Summable (fun j : {j // j ∉ F} => g j.1) := hgs.subtype _
  have step1 := norm_tsum_le_tsum_norm hsubn
  have step2 := hsubn.tsum_le_tsum (fun j : {j // j ∉ F} => hnv j.1) hsubg
  have hsu : Summable (fun j : {j // j ∉ F} => inner ℝ (e j.1 : K) x ^ 2) := hu.summable.subtype _
  have hsA : Summable (fun j : {j // j ∉ F} => ‖A (e j.1)‖ ^ 2) := hAs.subtype _
  have e2 : ∑' j : {j // j ∉ F}, g j.1 = (t * ∑' j : {j // j ∉ F}, inner ℝ (e j.1 : K) x ^ 2 +
      (∑' j : {j // j ∉ F}, ‖A (e j.1)‖ ^ 2) / t) / 2 := by
    simp only [hg]
    rw [tsum_div_const, (hsu.mul_left t).tsum_add (hsA.div_const t), tsum_mul_left, tsum_div_const]
  have e3 : ∑' j : {j // j ∉ F}, inner ℝ (e j.1 : K) x ^ 2 ≤ ‖x‖ ^ 2 := by
    have h := hu.summable.sum_add_tsum_subtype_compl F
    rw [hu.tsum_eq] at h
    have h0 : 0 ≤ ∑ j ∈ F, inner ℝ (e j : K) x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have := mul_le_mul_of_nonneg_left e3 ht.le
  linarith

theorem s86_hs_compact {ι : Type*} (e : HilbertBasis ι ℝ K) {A : K →L[ℝ] K} (hA : hs2 e A ≠ ⊤) :
    IsCompactOperator A := by
  classical
  have hAs := s86_hs2_summable e hA
  set AF : Finset ι → (K →L[ℝ] K) := fun F =>
    ∑ j ∈ F, (innerSL ℝ (e j : K)).smulRight (A (e j)) with hAF
  have hAFx : ∀ F x, AF F x = ∑ j ∈ F, inner ℝ (e j : K) x • A (e j) := fun F x => by
    simp [hAF, ContinuousLinearMap.sum_apply]
  have hlim : Tendsto AF atTop (𝓝 A) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have htail := ENNReal.tendsto_tsum_compl_atTop_zero hA
    have hev := htail.eventually (gt_mem_nhds
      (show (0 : ℝ≥0∞) < ENNReal.ofReal ((ε / 2) ^ 2) from ENNReal.ofReal_pos.2 (by positivity)))
    filter_upwards [hev] with F hF
    have hτ : ∑' j : {j // j ∉ F}, ‖A (e j.1)‖ ^ 2 < (ε / 2) ^ 2 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hAs.subtype _)] at hF
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hF
    have hτ0 : 0 ≤ ∑' j : {j // j ∉ F}, ‖A (e j.1)‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
    rw [dist_eq_norm]
    have hbound : ‖AF F - A‖ ≤ ε / 2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have ht : 0 < ε / (2 * ‖x‖) := by positivity
      have h := s86_tail_bound e A hAs F x ht
      rw [sub_apply, hAFx, norm_sub_rev]
      refine h.trans ?_
      set τ := ∑' j : {j // j ∉ F}, ‖A (e j.1)‖ ^ 2 with hτdef
      have e1 : ε / (2 * ‖x‖) * ‖x‖ ^ 2 = ε * ‖x‖ / 2 := by field_simp
      have e2 : τ / (ε / (2 * ‖x‖)) ≤ ε * ‖x‖ / 2 := by
        rw [div_div_eq_mul_div, div_le_iff₀ hε]
        have : τ * (2 * ‖x‖) ≤ (ε / 2) ^ 2 * (2 * ‖x‖) :=
          mul_le_mul_of_nonneg_right hτ.le (by positivity)
        nlinarith
      rw [e1]
      linarith
    linarith [hbound]
  refine isCompactOperator_of_tendsto hlim (Eventually.of_forall fun F => ?_)
  exact s86_finsum_rankone_compact F _ _

end HRS.MS.FinNoise
