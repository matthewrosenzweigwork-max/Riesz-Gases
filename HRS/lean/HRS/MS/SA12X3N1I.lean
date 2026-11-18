import HRS.MS.SA12X3N1H

/-!
# S.A.12 N1/N2 (SA12X3), part I: derivatives of a `C_c^∞` test function are mean-zero test functions
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x3n_integral_D1 {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i : Fin d) :
    ∫ x, D1 i ψ x = 0 := by
  have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
  have hD : Integrable (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) volume := by
    have : Continuous (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact this.integrable_of_hasCompactSupport
      ((hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) (by simp))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := fun _ : Euc d => (1 : ℝ)) (g := ψ) (v := EuclideanSpace.single i (1 : ℝ))
    (by simp) (by simpa using hD) (by simpa using hψi) (fun x _ => differentiableAt_const _)
    (fun x _ => (hψ.differentiable one_ne_zero) x)
  simpa [D1] using h

theorem sa12x3n_D1_data {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (i : Fin d) :
    ContDiff ℝ ∞ (D1 i f) ∧ HasCompactSupport (D1 i f) ∧ tsupport (D1 i f) ⊆ tsupport f ∧ ∫ x, D1 i f x = 0 := by
  refine ⟨(hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, D1_supp hfc i, ?_,
    sa12x3n_integral_D1 (hf.of_le (by simp)) hfc i⟩
  have h1 : D1 i f = (fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) ∘ fderiv ℝ f := rfl
  rw [h1]
  exact (tsupport_comp_subset (by simp) _).trans (tsupport_fderiv_subset ℝ)

theorem sa12x3n_test_data {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∃ R B : ℝ, 1 ≤ R ∧ 0 ≤ B ∧
      (∀ i : Fin d, Continuous (D1 i ψ) ∧ tsupport (D1 i ψ) ⊆ closedBall 0 R ∧ ∫ x, D1 i ψ x = 0 ∧
        ∀ u, |D1 i ψ u| ≤ B) ∧
      (∀ i j : Fin d, Continuous (D1 j (D1 i ψ)) ∧ tsupport (D1 j (D1 i ψ)) ⊆ closedBall 0 R ∧
        ∫ x, D1 j (D1 i ψ) x = 0 ∧ ∀ u, |D1 j (D1 i ψ) u| ≤ B) := by
  obtain ⟨R0, hR0⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R : ℝ := max R0 1 with hR
  have hts : tsupport ψ ⊆ closedBall (0 : Euc d) R :=
    hR0.trans (closedBall_subset_closedBall (le_max_left _ _))
  have h1 := fun i => sa12x3n_D1_data hψ hψc i
  have h2 := fun i j => sa12x3n_D1_data (h1 i).1 (h1 i).2.1 j
  have hb1 : ∀ i, ∃ b : ℝ, ∀ u, |D1 i ψ u| ≤ b := fun i => by
    obtain ⟨b, hb⟩ := ((h1 i).1.continuous).bounded_above_of_compact_support (h1 i).2.1
    exact ⟨b, fun u => by simpa [Real.norm_eq_abs] using hb u⟩
  have hb2 : ∀ i j, ∃ b : ℝ, ∀ u, |D1 j (D1 i ψ) u| ≤ b := fun i j => by
    obtain ⟨b, hb⟩ := ((h2 i j).1.continuous).bounded_above_of_compact_support (h2 i j).2.1
    exact ⟨b, fun u => by simpa [Real.norm_eq_abs] using hb u⟩
  choose b1 hb1 using hb1
  choose b2 hb2 using hb2
  refine ⟨R, ∑ i, |b1 i| + ∑ i, ∑ j, |b2 i j|, le_max_right _ _, by positivity, fun i => ?_, fun i j => ?_⟩
  · refine ⟨(h1 i).1.continuous, ((h1 i).2.2.1).trans hts, (h1 i).2.2.2, fun u => ?_⟩
    have : |b1 i| ≤ ∑ i, |b1 i| := Finset.single_le_sum (f := fun i => |b1 i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
    have : (0 : ℝ) ≤ ∑ i, ∑ j, |b2 i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [hb1 i u, le_abs_self (b1 i)]
  · refine ⟨(h2 i j).1.continuous, ((h2 i j).2.2.1).trans (((h1 i).2.2.1).trans hts), (h2 i j).2.2.2, fun u => ?_⟩
    have : |b2 i j| ≤ ∑ j, |b2 i j| := Finset.single_le_sum (f := fun j => |b2 i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
    have : ∑ j, |b2 i j| ≤ ∑ i, ∑ j, |b2 i j| := Finset.single_le_sum (f := fun i => ∑ j, |b2 i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have : (0 : ℝ) ≤ ∑ i, |b1 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [hb2 i j u, le_abs_self (b2 i j)]

end HRS.MH.AdjointRd.Phase2SA12Construction
