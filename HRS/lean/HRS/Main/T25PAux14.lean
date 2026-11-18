import HRS.Main.T25PAux13
import HRS.Uniform.Q48cCov

/-!
# T25P, part 14: the trace norm of a bilinear form is at most the `ℓ¹` norm of its matrix entries
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The rank-one form `x, y ↦ ⟨u,x⟩⟨v,y⟩`. -/
def t25pRank1 (u v : H) : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ u).smulRight (innerSL ℝ v)

theorem t25pRank1_apply (u v x y : H) : t25pRank1 u v x y = inner ℝ u x * inner ℝ v y := by
  simp [t25pRank1]

theorem t25pRank1_norm_le {u v : H} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖t25pRank1 u v‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  simp only [t25pRank1_apply, one_mul]
  calc ‖inner ℝ u x * inner ℝ v y‖ = ‖inner ℝ u x‖ * ‖inner ℝ v y‖ := norm_mul _ _
    _ ≤ (‖u‖ * ‖x‖) * (‖v‖ * ‖y‖) :=
        mul_le_mul (norm_inner_le_norm u x) (norm_inner_le_norm v y) (norm_nonneg _)
          (by positivity)
    _ ≤ (1 * ‖x‖) * (1 * ‖y‖) := by gcongr
    _ = ‖x‖ * ‖y‖ := by ring

set_option maxHeartbeats 1600000 in
theorem t25p_traceNormForm_le_entries {ι : Type*} (b : HilbertBasis ι ℝ H) (Q : H →L[ℝ] H →L[ℝ] ℝ)
    (hs : Summable fun p : ι × ι => |Q (b p.1) (b p.2)|) :
    traceNormForm Q ≤ ∑' p : ι × ι, |Q (b p.1) (b p.2)| := by
  classical
  have hb1 : ∀ i, ‖(b i : H)‖ = 1 := fun i => b.orthonormal.norm_eq_one i
  -- expansion of `Q x y` in the basis (no `tsum` in the operator-norm space)
  have hev : ∀ x y : H, Q x y = ∑' p : ι × ι, Q (b p.1) (b p.2) * (inner ℝ (b p.1 : H) x * inner ℝ (b p.2 : H) y) := by
    intro x y
    have hrep : ∀ z : H, HasSum (fun i => inner ℝ (b i : H) z • (b i : H)) z := fun z => by
      simpa [HilbertBasis.repr_apply_apply] using b.hasSum_repr z
    have hQx : HasSum (fun i => inner ℝ (b i : H) x * Q (b i) y) (Q x y) := by
      have h1 := (Q.hasSum (hrep x))
      have h2 := (ContinuousLinearMap.apply ℝ ℝ y).hasSum h1
      simpa using h2
    have hg : ∀ i : ι, HasSum (fun j : ι => Q (b i) (b j) * (inner ℝ (b i : H) x * inner ℝ (b j : H) y))
        (inner ℝ (b i : H) x * Q (b i) y) := by
      intro i
      have h1 := ((Q (b i)).hasSum (hrep y))
      have h2 := h1.mul_left (inner ℝ (b i : H) x)
      convert h2 using 2 with j
      simp only [Function.comp, map_smul, smul_eq_mul]
      ring
    have hfs : Summable fun p : ι × ι => Q (b p.1) (b p.2) * (inner ℝ (b p.1 : H) x * inner ℝ (b p.2 : H) y) := by
      refine Summable.of_norm_bounded (hs.mul_right (‖x‖ * ‖y‖)) (fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
      · have := abs_real_inner_le_norm (b p.1 : H) x
        rwa [hb1, one_mul] at this
      · have := abs_real_inner_le_norm (b p.2 : H) y
        rwa [hb1, one_mul] at this
    exact hQx.unique (hfs.hasSum.prod_fiberwise hg)
  -- the variational bound
  have h0 : 0 ≤ ∑' p : ι × ι, |Q (b p.1) (b p.2)| := tsum_nonneg fun _ => abs_nonneg _
  refine Real.iSup_le (fun p => ?_) h0
  obtain ⟨⟨n, e, f⟩, he, hf⟩ := p
  simp only
  have hia : ∀ (i : Fin n) (k : ι), |inner ℝ (b k : H) (e i)| ≤ 1 := fun i k => by
    have := abs_real_inner_le_norm (b k : H) (e i)
    rw [hb1 k, he.norm_eq_one i, one_mul] at this
    exact this
  have hib : ∀ (i : Fin n) (l : ι), |inner ℝ (b l : H) (f i)| ≤ 1 := fun i l => by
    have := abs_real_inner_le_norm (b l : H) (f i)
    rw [hb1 l, hf.norm_eq_one i, one_mul] at this
    exact this
  have hsum_i : ∀ i : Fin n, Summable fun p : ι × ι =>
      |Q (b p.1) (b p.2)| * (|inner ℝ (b p.1 : H) (e i)| * |inner ℝ (b p.2 : H) (f i)|) := by
    intro i
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hs
    calc |Q (b p.1) (b p.2)| * (|inner ℝ (b p.1 : H) (e i)| * |inner ℝ (b p.2 : H) (f i)|)
        ≤ |Q (b p.1) (b p.2)| * (1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hia i p.1) (hib i p.2) (abs_nonneg _) zero_le_one)
            (abs_nonneg _)
      _ = _ := by ring
  have h1 : ∀ i : Fin n, |Q (e i) (f i)| ≤ ∑' p : ι × ι,
      |Q (b p.1) (b p.2)| * (|inner ℝ (b p.1 : H) (e i)| * |inner ℝ (b p.2 : H) (f i)|) := by
    intro i
    rw [hev]
    have := norm_tsum_le_tsum_norm (f := fun p : ι × ι =>
      Q (b p.1) (b p.2) * (inner ℝ (b p.1 : H) (e i) * inner ℝ (b p.2 : H) (f i))) (by
        simpa [norm_mul, Real.norm_eq_abs, mul_assoc] using hsum_i i)
    simpa [norm_mul, Real.norm_eq_abs, mul_assoc] using this
  have hbess : ∀ k l : ι, ∑ i : Fin n, |inner ℝ (b k : H) (e i)| * |inner ℝ (b l : H) (f i)| ≤ 1 := by
    intro k l
    have hA : ∑ i : Fin n, |inner ℝ (b k : H) (e i)| ^ 2 ≤ 1 := by
      have := he.sum_inner_products_le (b k : H) (s := Finset.univ)
      rw [hb1 k] at this
      refine le_trans (le_of_eq ?_) (this.trans (by norm_num))
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, real_inner_comm]
    have hB : ∑ i : Fin n, |inner ℝ (b l : H) (f i)| ^ 2 ≤ 1 := by
      have := hf.sum_inner_products_le (b l : H) (s := Finset.univ)
      rw [hb1 l] at this
      refine le_trans (le_of_eq ?_) (this.trans (by norm_num))
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, real_inner_comm]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin n => |inner ℝ (b k : H) (e i)|)
      (fun i : Fin n => |inner ℝ (b l : H) (f i)|)
    have hS0 : 0 ≤ ∑ i : Fin n, |inner ℝ (b k : H) (e i)| * |inner ℝ (b l : H) (f i)| :=
      Finset.sum_nonneg fun i _ => by positivity
    have hS2 : (∑ i : Fin n, |inner ℝ (b k : H) (e i)| * |inner ℝ (b l : H) (f i)|) ^ 2 ≤ 1 := by
      refine hcs.trans ?_
      nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => sq_nonneg |inner ℝ (b k : H) (e i)|),
        Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => sq_nonneg |inner ℝ (b l : H) (f i)|)]
    nlinarith
  calc ∑ i : Fin n, |Q (e i) (f i)|
      ≤ ∑ i : Fin n, ∑' p : ι × ι,
          |Q (b p.1) (b p.2)| * (|inner ℝ (b p.1 : H) (e i)| * |inner ℝ (b p.2 : H) (f i)|) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = ∑' p : ι × ι, ∑ i : Fin n,
          |Q (b p.1) (b p.2)| * (|inner ℝ (b p.1 : H) (e i)| * |inner ℝ (b p.2 : H) (f i)|) :=
        (Summable.tsum_finsetSum fun i _ => hsum_i i).symm
    _ ≤ ∑' p : ι × ι, |Q (b p.1) (b p.2)| := by
        refine Summable.tsum_le_tsum (fun p => ?_) (summable_sum fun i _ => hsum_i i) hs
        rw [← Finset.mul_sum]
        calc |Q (b p.1) (b p.2)| * ∑ i : Fin n, |inner ℝ (b p.1 : H) (e i)| * |inner ℝ (b p.2 : H) (f i)|
            ≤ |Q (b p.1) (b p.2)| * 1 := mul_le_mul_of_nonneg_left (hbess p.1 p.2) (abs_nonneg _)
          _ = _ := mul_one _

end HRS.T25P
