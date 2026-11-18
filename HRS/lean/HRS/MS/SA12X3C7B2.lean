import HRS.MS.SA12X3C7B1

/-!
# S.A.12 C7 (SA12X3), part B2: tuple partials of the smooth-kernel term

For `k_L(u) = ∂_i q(L⁻¹u)` and a continuous `g` with `tsupport g ⊆ B(c,ρ)`: for `x ∈ B(c,ρ)` and `|idx| = n ≤ m`,
`|∂^idx_x ∫ k_L(x-y) g(y) dy| ≤ Kk ∫ |g|` with `Kk` independent of `L ≥ 1`, `i`, `c`, `g`.
(The kernel is cut off by a bump equal to `1` on `B(0,2ρ)`; the derivative then falls on the cut kernel by B1.)
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_pd_congr_open {f₁ f : Euc d → ℝ} {s : Set (Euc d)} (hs : IsOpen s) (h : EqOn f₁ f s) {n : ℕ}
    (idx : Fin n → Fin d) {x : Euc d} (hx : x ∈ s) : partialDeriv idx f₁ x = partialDeriv idx f x := by
  unfold partialDeriv
  have h1 := iteratedFDerivWithin_congr (𝕜 := ℝ) h hx n
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hs hx, iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hs hx] at h1
  rw [h1]

/-- The jets of the scaled kernel `u ↦ ∂_i q(L⁻¹ u)` are bounded by those of `q` on the ball of radius `r`. -/
theorem sa12x3_kernel_jets {q : Euc d → ℝ} (hq : ContDiff ℝ ∞ q) (m : ℕ) (r : ℝ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (L : ℝ), 1 ≤ L → ∀ (e : Euc d), ‖e‖ ≤ 1 → ∀ j ≤ m, ∀ u : Euc d, ‖u‖ ≤ r →
      ‖iteratedFDeriv ℝ j (fun u => fderiv ℝ q (L⁻¹ • u) e) u‖ ≤ Q := by
  have h : ∀ j : ℕ, ∃ Qj : ℝ, 0 ≤ Qj ∧ ∀ v : Euc d, ‖v‖ ≤ r → ‖iteratedFDeriv ℝ (j + 1) q v‖ ≤ Qj := by
    intro j
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) r).exists_bound_of_continuousOn
      ((hq.continuous_iteratedFDeriv (m := j + 1) (sa12x2_le_top _)).continuousOn)
    exact ⟨max C 0, le_max_right _ _, fun v hv => (hC v (by simpa using hv)).trans (le_max_left _ _)⟩
  choose Qj hQ0 hQj using h
  refine ⟨∑ j ∈ Finset.range (m + 1), Qj j, Finset.sum_nonneg fun j _ => hQ0 j, ?_⟩
  intro L hL e he j hj u hu
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  set A : Euc d →L[ℝ] Euc d := L⁻¹ • ContinuousLinearMap.id ℝ (Euc d) with hA
  have hAx : ∀ u, A u = L⁻¹ • u := fun u => by simp [hA]
  have hAn : ‖A‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
    rw [hAx, norm_smul, norm_inv, Real.norm_of_nonneg hL0.le]
    have : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
    nlinarith [norm_nonneg u]
  have hfd : ContDiff ℝ ∞ (fderiv ℝ q) := hq.fderiv_right (m := ∞) (by simp)
  have e1 : (fun u => fderiv ℝ q (L⁻¹ • u) e) = fun u => ((fderiv ℝ q) ∘ A) u e := by
    funext u; simp [Function.comp, hAx]
  rw [e1]
  have hcomp : ContDiff ℝ ∞ ((fderiv ℝ q) ∘ A) := hfd.comp A.contDiff
  have h2 := norm_iteratedFDeriv_clm_apply_const (c := e) (n := j) (x := u)
    (f := (fderiv ℝ q) ∘ A) (hcomp.contDiffAt) (by exact_mod_cast sa12x2_le_top j)
  refine h2.trans ?_
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right A hfd u (by exact_mod_cast sa12x2_le_top j)]
  have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j (fderiv ℝ q) (A u)) (fun _ : Fin j => A)
  have h4 : ‖iteratedFDeriv ℝ j (fderiv ℝ q) (A u)‖ ≤ Qj j := by
    rw [norm_iteratedFDeriv_fderiv]
    refine hQj j (A u) ?_
    rw [hAx, norm_smul, norm_inv, Real.norm_of_nonneg hL0.le]
    have : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
    nlinarith [norm_nonneg u]
  have h5 : ∏ _i : Fin j, ‖A‖ ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) hAn
  have h6 : Qj j ≤ ∑ j ∈ Finset.range (m + 1), Qj j :=
    Finset.single_le_sum (f := Qj) (fun j _ => hQ0 j) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  calc ‖e‖ * ‖(iteratedFDeriv ℝ j (fderiv ℝ q) (A u)).compContinuousLinearMap fun _ => A‖
      ≤ 1 * (‖iteratedFDeriv ℝ j (fderiv ℝ q) (A u)‖ * ∏ _i : Fin j, ‖A‖) := by
        gcongr
    _ ≤ 1 * (Qj j * 1) := by
        gcongr
        · exact (norm_nonneg _).trans h4
    _ ≤ _ := by linarith

end HRS.MH.AdjointRd.Phase2SA12Near
