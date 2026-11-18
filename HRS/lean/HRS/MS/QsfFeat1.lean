import HRS.MS.QsfBound1

/-!
# S4.5 packet B5 (part): conjuncts 1 and 2 of `StaticFieldConclusion`

For a summable feature family (`∑ cbNorm J φ_j < ∞`) and a probability measure `ν`:

* `s45_feature_memℓp`: for EVERY configuration the feature coordinates `√N(μ_N(φ_j) - ν(φ_j))` lie in `ℓ²`
  (so the junk value `SeqL2.ofSeq = 0` is never used);
* `s45_feature_measurable`: `featureVec φ ν : (ℝ^d)^N → ℓ²` is measurable (limit of its finite truncations).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s45_feature_bound (hN : 1 ≤ N) {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : ∀ j, MemCb J (φ j))
    {ν : Measure (Euc d)} [IsProbabilityMeasure ν] (X : EucConfig d N) (j : ℕ) :
    |Real.sqrt N * (pair (empirical X) (φ j) - pair ν (φ j))| ≤ 2 * Real.sqrt N * cbNorm J (φ j) := by
  have hb : ∀ x, |φ j x| ≤ cbNorm J (φ j) := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ j) x
    rwa [Real.norm_eq_abs] at this
  have h1 := s45_abs_pair_empirical_le hN hb X
  have h2 : |pair ν (φ j)| ≤ cbNorm J (φ j) :=
    HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hb x)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt N * |pair (empirical X) (φ j) - pair ν (φ j)|
      ≤ Real.sqrt N * (|pair (empirical X) (φ j)| + |pair ν (φ j)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt N * (2 * cbNorm J (φ j)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem s45_feature_memℓp (hN : 1 ≤ N) {J : ℕ} {φ : ℕ → Euc d → ℝ}
    (hφ : HRS.Whole.IsSummableFeatureFamily J φ) {ν : Measure (Euc d)} [IsProbabilityMeasure ν]
    (X : EucConfig d N) :
    Memℓp (fun j => Real.sqrt N * (pair (empirical X) (φ j) - pair ν (φ j))) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hs : Summable fun j => (2 * Real.sqrt N * cbNorm J (φ j)) ^ 2 :=
    s45_summable_sq (fun j => by have := HRS.MS.Tc5.tc5_cb_nonneg (d := d) J (φ j); positivity)
      (hφ.2.mul_left _)
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (s45_feature_bound hN hφ.1 (ν := ν) X j) 2

theorem s45_coord_ofSeq {c : ℕ → ℝ} (h : Memℓp c 2) (j : ℕ) : SeqL2.coord (SeqL2.ofSeq c) j = c j := by
  simp [SeqL2.ofSeq, h, SeqL2.coord]

/-- The element `a e_j` of `ℓ²`. -/
def s45_e1 (j : ℕ) (a : ℝ) : SeqL2 := lp.single (E := fun _ : ℕ => ℝ) 2 j a

theorem s45_e1_eq (j : ℕ) (a : ℝ) : s45_e1 j a = a • s45_e1 j 1 := by
  unfold s45_e1
  have := lp.single_smul (E := fun _ : ℕ => ℝ) (p := 2) j a (1 : ℝ)
  rw [smul_eq_mul, mul_one] at this
  exact this

theorem s45_feature_measurable (hN : 1 ≤ N) {J : ℕ} {φ : ℕ → Euc d → ℝ}
    (hφ : HRS.Whole.IsSummableFeatureFamily J φ) {ν : Measure (Euc d)} [IsProbabilityMeasure ν] :
    Measurable (featureVec φ ν : EucConfig d N → SeqL2) := by
  set c : ℕ → EucConfig d N → ℝ := fun j X =>
    Real.sqrt N * (pair (empirical X) (φ j) - pair ν (φ j)) with hc
  have hcm : ∀ j, Measurable (c j) := fun j =>
    measurable_const.mul ((s45_measurable_pair_empirical hN (hφ.1 j).1.continuous.measurable).sub
      measurable_const)
  have hgm : ∀ n : ℕ, Measurable (fun X : EucConfig d N =>
      ∑ j ∈ Finset.range n, s45_e1 j (c j X)) := by
    intro n
    refine Finset.measurable_sum _ fun j _ => ?_
    rw [show (fun X : EucConfig d N => s45_e1 j (c j X)) = fun X => c j X • s45_e1 j 1 from
      funext fun X => s45_e1_eq j (c j X)]
    exact (hcm j).smul_const _
  refine measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.2 fun X => ?_)
  have hmem := s45_feature_memℓp hN hφ (ν := ν) X
  have hs := lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by simp)
    (show lp (fun _ : ℕ => ℝ) 2 from featureVec φ ν X)
  have heq : (fun j : ℕ => s45_e1 j (c j X)) = fun j => lp.single (E := fun _ : ℕ => ℝ) 2 j
      ((show lp (fun _ : ℕ => ℝ) 2 from featureVec φ ν X) j) := by
    funext j
    unfold s45_e1
    congr 1
    exact (s45_coord_ofSeq hmem j).symm
  have ht := hs.tendsto_sum_nat
  rw [← heq] at ht
  exact ht

end S45

end
