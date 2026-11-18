import HRS.MS.R26T8AL3e

/-!
# S8.2 observed-time layer, generic lemma L3 (final assembly)

`r26t8a_l3`: for `c` smooth with bounded iterated derivatives and `v` `SobSmooth`, `c · v` is `SobSmooth` and
`sobolevNormE m (c·v) ≤ C_m · sobolevNormE m v` for every natural `m` (constant `C_m` independent of `v`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.Whole.Q09A LineDeriv

variable {d : ℕ}

theorem r26t8a_l3f_top (i : Fin d) (c v : Euc d → ℝ) (hc : ContDiff ℝ ∞ c) (Bc : ℕ → ℝ)
    (hBc : ∀ k (x : Euc d), ‖iteratedFDeriv ℝ k c x‖ ≤ Bc k)
    (hv : r26t8a_SobSmooth v) (m : ℕ) :
    ∫ x, ((r26t8a_l3_D i)^[m] (fun y => c y * v y) x) ^ 2 ≤
      ((m : ℝ) + 1) * (∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2) *
        sobolevNormSq (m : ℝ) v := by
  have hmemv : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) v := hv.2 m
  have hf : ∀ k ∈ Finset.range (m + 1), ∫ x, ((r26t8a_l3_D i)^[m - k] v x) ^ 2 ≤ sobolevNormSq (m : ℝ) v := by
    intro k hk
    have hL2 : MemLp ((r26t8a_l3_D i)^[m - k] v) 2 volume := ((r26t8a_l3_sob_iter v hv i (m - k)).2 0).1
    rw [← r26t8a_l3d_sob0 _ hL2]
    have h1 := r26t8a_l3_pure_bound v hv i (m - k) 0
    have h2 : sobolevNormSq ((0 + (m - k) : ℕ) : ℝ) v ≤ sobolevNormSq (m : ℝ) v :=
      r26t8a_l3d_sq_mono (by exact_mod_cast (by omega : 0 + (m - k) ≤ m)) v hmemv
    simpa using h1.trans h2
  have hpt : ∀ x, ((r26t8a_l3_D i)^[m] (fun y => c y * v y) x) ^ 2 ≤
      ((m : ℝ) + 1) * ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2 *
        ((r26t8a_l3_D i)^[m - k] v x) ^ 2 := by
    intro x
    have hp := r26t8a_l3e_pw i c v hc Bc hBc hv m x
    have hsum : |(r26t8a_l3_D i)^[m] (fun y => c y * v y) x| ≤
        ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) * |(r26t8a_l3_D i)^[m - k] v x| :=
      hp.trans (le_of_eq (Finset.sum_congr rfl fun k _ => by ring))
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1))
      (f := fun k => ((m.choose k : ℝ) * |Bc k|) * |(r26t8a_l3_D i)^[m - k] v x|)
    rw [Finset.card_range] at hcs
    have hsq : ((r26t8a_l3_D i)^[m] (fun y => c y * v y) x) ^ 2 =
        |(r26t8a_l3_D i)^[m] (fun y => c y * v y) x| ^ 2 := (sq_abs _).symm
    have hcs' : (∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) * |(r26t8a_l3_D i)^[m - k] v x|) ^ 2 ≤
        ((m : ℝ) + 1) * ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2 *
          ((r26t8a_l3_D i)^[m - k] v x) ^ 2 := by
      refine hcs.trans (le_of_eq ?_)
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow, sq_abs, mul_pow]
    rw [hsq]
    exact (pow_le_pow_left₀ (abs_nonneg _) hsum 2).trans hcs'
  have hint : ∀ k ∈ Finset.range (m + 1), Integrable (fun x => ((m.choose k : ℝ) * |Bc k|) ^ 2 *
      ((r26t8a_l3_D i)^[m - k] v x) ^ 2) volume := by
    intro k _
    have hL2 : MemLp ((r26t8a_l3_D i)^[m - k] v) 2 volume := ((r26t8a_l3_sob_iter v hv i (m - k)).2 0).1
    exact (hL2.integrable_sq).const_mul _
  have hI : Integrable (fun x => ((m : ℝ) + 1) * ∑ k ∈ Finset.range (m + 1),
      ((m.choose k : ℝ) * |Bc k|) ^ 2 * ((r26t8a_l3_D i)^[m - k] v x) ^ 2) volume :=
    (integrable_finset_sum _ hint).const_mul _
  calc ∫ x, ((r26t8a_l3_D i)^[m] (fun y => c y * v y) x) ^ 2
      ≤ ∫ x, ((m : ℝ) + 1) * ∑ k ∈ Finset.range (m + 1),
          ((m.choose k : ℝ) * |Bc k|) ^ 2 * ((r26t8a_l3_D i)^[m - k] v x) ^ 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hI
          (Eventually.of_forall hpt)
    _ = ((m : ℝ) + 1) * ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2 *
          ∫ x, ((r26t8a_l3_D i)^[m - k] v x) ^ 2 := by
        rw [integral_const_mul, integral_finset_sum _ hint]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [integral_const_mul]
    _ ≤ ((m : ℝ) + 1) * (∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2) *
          sobolevNormSq (m : ℝ) v := by
        have hsumle : ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2 *
            ∫ x, ((r26t8a_l3_D i)^[m - k] v x) ^ 2 ≤
            (∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2) * sobolevNormSq (m : ℝ) v := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hf k hk) (sq_nonneg _)
        have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
        calc ((m : ℝ) + 1) * ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2 *
              ∫ x, ((r26t8a_l3_D i)^[m - k] v x) ^ 2
            ≤ ((m : ℝ) + 1) * ((∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2) *
                sobolevNormSq (m : ℝ) v) := mul_le_mul_of_nonneg_left hsumle hm1
          _ = ((m : ℝ) + 1) * (∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * |Bc k|) ^ 2) *
                sobolevNormSq (m : ℝ) v := by ring

end HRS.MS.R26T8A

end
