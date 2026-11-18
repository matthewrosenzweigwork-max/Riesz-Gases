import HRS.MS.R2SeAux2

/-!
# S9.9 `r2_static_edgeworth`, packet 3: the feature vector as a `C¹` series in `ℓ²`

Worker S99, namespace `S99`.  For a summable feature family `φ` (`IsSummableFeatureFamily J φ`, `J ≥ 1`) and a probability measure `ν`
the feature vector `W = featureVec φ ν : (ℝ^d)^N → ℓ²` is the series `∑' j, s45_Yi N (φ j) (pair ν (φ j)) • e_j`
(`s99_W_hasSum`); it is `C¹` with derivative `X ↦ ∑' l, (s45_L N (φ l) X).smulRight e_l` (`s99_W_hasFDerivAt`, `s99_W_contDiff`) and
bounded: `‖W X‖ ≤ 2√N ∑_j cbNorm J φ_j`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The `j`-th term `Y_j e_j` of the feature series. -/
def Wterm (N : ℕ) (φ : ℕ → Euc d → ℝ) (c : ℕ → ℝ) (j : ℕ) (X : EucConfig d N) : SeqL2 :=
  s45_Yi N (φ j) (c j) X • s45_e1 j 1

theorem s99_e1_norm (j : ℕ) : ‖s45_e1 j (1 : ℝ)‖ = 1 := by
  have h := lp.norm_single (E := fun _ : ℕ => ℝ) (p := (2 : ℝ≥0∞)) (by norm_num) j (1 : ℝ)
  unfold s45_e1
  exact h.trans norm_one

theorem s99_Wterm_norm (φ : ℕ → Euc d → ℝ) (c : ℕ → ℝ) (j : ℕ) (X : EucConfig d N) :
    ‖Wterm N φ c j X‖ = |s45_Yi N (φ j) (c j) X| := by
  unfold Wterm
  rw [norm_smul, s99_e1_norm, mul_one, Real.norm_eq_abs]

/-- The feature vector is the series of its terms. -/
theorem s99_W_hasSum (hN : 1 ≤ N) {J : ℕ} {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily J φ) {ν : Measure (Euc d)} [IsProbabilityMeasure ν]
    (X : EucConfig d N) :
    HasSum (fun j => Wterm N φ (fun j => pair ν (φ j)) j X) (featureVec φ ν X) := by
  have hmem := s45_feature_memℓp hN hφ (ν := ν) X
  have hs := lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by simp)
    (show lp (fun _ : ℕ => ℝ) 2 from featureVec φ ν X)
  have heq : (fun j : ℕ => Wterm N φ (fun j => pair ν (φ j)) j X) = fun j =>
      lp.single (E := fun _ : ℕ => ℝ) 2 j ((show lp (fun _ : ℕ => ℝ) 2 from featureVec φ ν X) j) := by
    funext j
    unfold Wterm
    rw [← s45_e1_eq]
    unfold s45_e1
    congr 1
    show s45_Yi N (φ j) (pair ν (φ j)) X = _
    exact (s45_coord_ofSeq hmem j).symm
  rw [heq]
  exact hs

theorem s99_Wterm_bound (hN : 1 ≤ N) {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : ∀ j, MemCb J (φ j))
    {ν : Measure (Euc d)} [IsProbabilityMeasure ν] (X : EucConfig d N) (j : ℕ) :
    ‖Wterm N φ (fun j => pair ν (φ j)) j X‖ ≤ 2 * Real.sqrt N * cbNorm J (φ j) := by
  rw [s99_Wterm_norm]
  exact s45_feature_bound hN hφ (ν := ν) X j

theorem s99_L_opNorm (hN : 1 ≤ N) {ψ : Euc d → ℝ} {D : ℝ} (hD : ∀ x, ‖fderiv ℝ ψ x‖ ≤ D)
    (X : EucConfig d N) : ‖s45_L N ψ X‖ ≤ Real.sqrt N * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [Real.norm_eq_abs]
  have := s45_L_bound hD hN X w
  linarith

theorem s99_Wterm_hasFDerivAt (hN : 1 ≤ N) {φ : ℕ → Euc d → ℝ} (hφ : ∀ j, Differentiable ℝ (φ j))
    (c : ℕ → ℝ) (j : ℕ) (X : EucConfig d N) :
    HasFDerivAt (Wterm N φ c j) ((s45_L N (φ j) X).smulRight (s45_e1 j (1 : ℝ))) X :=
  (s45_Yi_hasFDerivAt hN (hφ j) (c j) X).smul_const _

theorem s99_Wterm_fderiv_norm (hN : 1 ≤ N) {J : ℕ} (hJ : 1 ≤ J) {φ : ℕ → Euc d → ℝ}
    (hφ : ∀ j, MemCb J (φ j)) (j : ℕ) (X : EucConfig d N) :
    ‖(s45_L N (φ j) X).smulRight (s45_e1 j (1 : ℝ))‖ ≤ Real.sqrt N * cbNorm J (φ j) := by
  refine (ContinuousLinearMap.norm_smulRight_apply _ _).le.trans ?_
  rw [s99_e1_norm, mul_one]
  exact s99_L_opNorm hN (fun x => s45_cb_deriv_le hJ (hφ j) x) X

/-- The feature vector is `C¹` with the termwise derivative. -/
theorem s99_W_hasFDerivAt (hN : 1 ≤ N) {J : ℕ} (hJ : 1 ≤ J) {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily J φ) {ν : Measure (Euc d)} [IsProbabilityMeasure ν]
    (X : EucConfig d N) :
    HasFDerivAt (fun X : EucConfig d N => featureVec φ ν X)
      (∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))) X := by
  have hfeq : (fun X : EucConfig d N => featureVec φ ν X) =
      fun X => ∑' j, Wterm N φ (fun j => pair ν (φ j)) j X :=
    funext fun X => ((s99_W_hasSum hN hφ X).tsum_eq).symm
  rw [hfeq]
  have hu : Summable fun j => Real.sqrt N * cbNorm J (φ j) := hφ.2.mul_left _
  exact hasFDerivAt_tsum hu (fun j Y => s99_Wterm_hasFDerivAt hN (fun j => (hφ.1 j).1.differentiable
    (by exact_mod_cast (by omega : J ≠ 0))) _ j Y) (fun j Y => s99_Wterm_fderiv_norm hN hJ hφ.1 j Y)
    (x₀ := X) (s99_W_hasSum hN hφ X).summable X

theorem s99_W_contDiff (hN : 1 ≤ N) {J : ℕ} (hJ : 1 ≤ J) {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily J φ) {ν : Measure (Euc d)} [IsProbabilityMeasure ν] :
    ContDiff ℝ 1 (fun X : EucConfig d N => featureVec φ ν X) := by
  have hfeq : (fun X : EucConfig d N => featureVec φ ν X) =
      fun X => ∑' j, Wterm N φ (fun j => pair ν (φ j)) j X :=
    funext fun X => ((s99_W_hasSum hN hφ X).tsum_eq).symm
  rw [hfeq]
  have hcd : ∀ j, ContDiff ℝ 1 (Wterm N φ (fun j => pair ν (φ j)) j : EucConfig d N → SeqL2) := fun j =>
    (s45_Yi_contDiff hN ((hφ.1 j).1.of_le (by exact_mod_cast hJ)) _).smul contDiff_const
  refine contDiff_tsum (N := 1) (v := fun k j => if k = 0 then 2 * Real.sqrt N * cbNorm J (φ j)
    else Real.sqrt N * cbNorm J (φ j)) hcd ?_ ?_
  · intro k hk
    by_cases h0 : k = 0
    · simp only [h0, ite_true]; exact (hφ.2.mul_left _)
    · simp only [h0, ite_false]; exact hφ.2.mul_left _
  · intro k j X hk
    have hk1 : k ≤ 1 := by exact_mod_cast hk
    interval_cases k
    · simp only [norm_iteratedFDeriv_zero, ite_true]
      exact s99_Wterm_bound hN hφ.1 X j
    · simp only [one_ne_zero, ite_false]
      rw [norm_iteratedFDeriv_one, (s99_Wterm_hasFDerivAt hN (fun j => (hφ.1 j).1.differentiable
        (by exact_mod_cast (by omega : J ≠ 0))) _ j X).fderiv]
      exact s99_Wterm_fderiv_norm hN hJ hφ.1 j X

end S99

end
