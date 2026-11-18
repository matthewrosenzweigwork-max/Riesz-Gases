import HRS.MS.MainRdPathAux9

/-!
# S.A.9, packet P3d: domination, boundedness and decay of the tail function

* `sa9_mriG_le`: `∑_ℓ ofReal (mriG m ψ_ℓ x) ≤ sa9_Gt`;
* `sa9_Gt_meas`, `sa9_Gt_le`: measurability and the uniform bound `sa9_Cdim · K²`;
* `sa9_Gt_tendsto`: pointwise decay in `Lc`;
* `sa9_cellsum_tendsto`: the weighted cell integrals of the tail function tend to `0` (dominated convergence).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit

variable {d : ℕ}

theorem sa9_mriG_le (h : ℕ → mhn_Hc d) (Cf : WholeCoeff d) (t : ℝ) (m Lc : ℕ) (x : Euc d) :
    ∑' l, ENNReal.ofReal (mriG m (propagatorW Cf 0 t (mhn_phi (h (l + Lc)))) x) ≤ sa9_Gt h Cf t m Lc x := by
  unfold sa9_Gt
  have hpt : ∀ l, ENNReal.ofReal (mriG m (propagatorW Cf 0 t (mhn_phi (h (l + Lc)))) x) ≤
      ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) * ∑ idx : Fin i → Fin d,
        ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h (l + Lc)))) x) ^ 2) := by
    intro l
    unfold mriG
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (ENNReal.ofReal_le_ofReal (mri_norm_iter_sq i _ x)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg fun idx _ => by positivity]
  calc ∑' l, ENNReal.ofReal (mriG m (propagatorW Cf 0 t (mhn_phi (h (l + Lc)))) x)
      ≤ ∑' l, ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) * ∑ idx : Fin i → Fin d,
        ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h (l + Lc)))) x) ^ 2) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) * ∑ idx : Fin i → Fin d,
        ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h (l + Lc)))) x) ^ 2) := by
        rw [Summable.tsum_finsetSum fun i _ => ENNReal.summable]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum fun idx _ => ENNReal.summable]

section Props

variable {q m : ℕ} {T K : ℝ} {Cf : WholeCoeff d}

theorem sa9_prop_lin (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) Cf T K) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) :
    (∀ a b : mhn_Hc d, propagatorW Cf 0 t (mhn_phi (a + b)) =
      propagatorW Cf 0 t (mhn_phi a) + propagatorW Cf 0 t (mhn_phi b)) ∧
    (∀ (c : ℝ) (a : mhn_Hc d), propagatorW Cf 0 t (mhn_phi (c • a)) = c • propagatorW Cf 0 t (mhn_phi a)) :=
  ⟨fun a b => by rw [mri_phi_add, mri_prop_add hadj ht0 htT (mhn_isSobolevTest_phi _ a) (mhn_isSobolevTest_phi _ b)],
   fun c a => by rw [mri_phi_smul, mri_prop_smul hadj ht0 htT (mhn_isSobolevTest_phi _ a)]⟩

theorem sa9_Gt_meas (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) Cf T K) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) (h : ℕ → mhn_Hc d) (Lc : ℕ) : Measurable (sa9_Gt h Cf t m Lc) := by
  unfold sa9_Gt
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' : i ≤ m + 1 := by have := Finset.mem_range.1 hi; omega
  refine Measurable.const_mul (Finset.measurable_sum _ fun idx _ => ?_) _
  refine Measurable.ennreal_tsum fun l => ?_
  have hc := (hadj 0 t le_rfl ht0 htT _ (mhn_isSobolevTest_phi ((q : ℕ) : ℝ) (h (l + Lc)))).2.1
  exact ENNReal.measurable_ofReal.comp ((sa9_partial_cont (hc.of_le (by exact_mod_cast hi')) idx).measurable.pow_const 2)

theorem sa9_tsum_le (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) Cf T K)
    (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {i : ℕ} (hi : i ≤ m + 1) (idx : Fin i → Fin d) (x : Euc d)
    (Lc : ℕ) :
    ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h (l + Lc)))) x) ^ 2) ≤
      ENNReal.ofReal (K ^ 2) := by
  obtain ⟨hadd, hsmul⟩ := sa9_prop_lin hadj ht0 htT
  have hcd : ∀ a : mhn_Hc d, ContDiff ℝ i (propagatorW Cf 0 t (mhn_phi a)) := fun a =>
    ((hadj 0 t le_rfl ht0 htT _ (mhn_isSobolevTest_phi _ a)).2.1).of_le (by exact_mod_cast hi)
  have hb : ∀ n, ∑ l ∈ Finset.range n, (partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h l))) x) ^ 2 ≤ K ^ 2 :=
    fun n => sa9_bessel h hP (propagatorW Cf 0 t) idx x hadd hsmul hcd (C := K) (fun g =>
      (hadj 0 t le_rfl ht0 htT _ (mhn_isSobolevTest_phi _ g)).2.2.2 i hi idx x |>.trans' (le_refl _)) n
  calc ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h (l + Lc)))) x) ^ 2)
      ≤ ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h l))) x) ^ 2) :=
        ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective Lc)
          (fun l => ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h l))) x) ^ 2))
    _ ≤ ENNReal.ofReal (K ^ 2) := by
        rw [ENNReal.tsum_eq_iSup_nat]
        refine iSup_le fun n => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => sq_nonneg _]
        exact ENNReal.ofReal_le_ofReal (hb n)

theorem sa9_Gt_le (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) Cf T K) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (Lc : ℕ) (x : Euc d) :
    sa9_Gt h Cf t m Lc x ≤ ENNReal.ofReal (sa9_Cdim d m * K ^ 2) := by
  rw [← sa9_const_sum]
  unfold sa9_Gt
  exact Finset.sum_le_sum fun i hi => mul_le_mul' le_rfl (Finset.sum_le_sum fun idx _ =>
    sa9_tsum_le hadj h hP ht0 htT (by have := Finset.mem_range.1 hi; omega) idx x Lc)

theorem sa9_Gt_tendsto (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) Cf T K) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (x : Euc d) :
    Tendsto (fun Lc => sa9_Gt h Cf t m Lc x) atTop (𝓝 0) := by
  unfold sa9_Gt
  have : (0 : ℝ≥0∞) = ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) * ∑ idx : Fin i → Fin d, 0 := by
    simp
  rw [this]
  refine tendsto_finset_sum _ fun i hi => ?_
  refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_finset_sum _ fun idx _ => ?_
  have hi' : i ≤ m + 1 := by have := Finset.mem_range.1 hi; omega
  exact ENNReal.tendsto_sum_nat_add (fun l => ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h l))) x) ^ 2))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by
      simpa using ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective 0)
        (fun l => ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h l))) x) ^ 2)) |>.trans
        (sa9_tsum_le hadj h hP ht0 htT hi' idx x 0)))

end Props

end HRS.MS.MainRdPath
