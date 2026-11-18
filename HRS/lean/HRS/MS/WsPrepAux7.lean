import HRS.MS.WsPrepAux3

/-!
# S21R packet 7: monotonicity of the regularity indices (`C_b^k` and `Σ^m` norms)

* `s21p_cbNorm_mono_k`: `cbNorm k f ≤ cbNorm k' f` for `k ≤ k'` (a sum of nonnegative terms).
* `s21p_memOsc_mono`, `s21p_oscNorm_mono`: `MemOsc m f → MemOsc m' f` and `oscNorm m' f ≤ oscNorm m f` for `m' ≤ m` (`λ_α ≥ 1`).
* `s21p_ofFun_dist_le`: the inclusion `Σ^m → Σ^{m'}`, in the sequence model `OscSpace.ofFun`, is 1-Lipschitz on `Σ^m`.
* `s21p_continuousOn_ofFun_mono`: continuity of a family into `Σ^m` implies continuity into `Σ^{m'}`.
They allow the S6.6 / S6.3 conclusions, stated at low indices `(j, m)`, to be applied to the solutions of `IsResultingSolution`
(indices `j + 1 = 100d + 1001`, `m = 102d + 1020`), see `s21p_resulting_in_class_low`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole

variable {d : ℕ}

theorem s21p_cbNorm_mono_k {k k' : ℕ} (h : k ≤ k') (f : Euc d → ℝ) : cbNorm k f ≤ cbNorm k' f := by
  unfold cbNorm
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ h)) ?_
  intro j _ _
  exact Real.iSup_nonneg fun x => norm_nonneg _

theorem s21p_rpow_le {m m' : ℝ} (h : m' ≤ m) (α : MultiIndex d) :
    oscEigenvalue d α ^ m' ≤ oscEigenvalue d α ^ m :=
  Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue α) h

theorem s21p_memOsc_mono {m m' : ℝ} (h : m' ≤ m) {f : Euc d → ℝ} (hf : MemOsc m f) : MemOsc m' f := by
  refine ⟨hf.1, Summable.of_nonneg_of_le (fun α => ?_) (fun α => ?_) hf.2⟩
  · exact mul_nonneg (Real.rpow_nonneg (oscEigenvalue_pos α).le _) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (s21p_rpow_le h α) (sq_nonneg _)

theorem s21p_oscNorm_mono {m m' : ℝ} (h : m' ≤ m) {f : Euc d → ℝ} (hf : MemOsc m f) :
    oscNorm m' f ≤ oscNorm m f := by
  unfold oscNorm
  refine Real.sqrt_le_sqrt (Summable.tsum_le_tsum (fun α => ?_) (s21p_memOsc_mono h hf).2 hf.2)
  exact mul_le_mul_of_nonneg_right (s21p_rpow_le h α) (sq_nonneg _)

theorem s21p_ofFun_dist_le {m m' : ℝ} (h : m' ≤ m) {f g : Euc d → ℝ} (hf : MemOsc m f) (hg : MemOsc m g) :
    dist (OscSpace.ofFun (d := d) m' f) (OscSpace.ofFun m' g) ≤
      dist (OscSpace.ofFun (d := d) m f) (OscSpace.ofFun m g) := by
  have hf' := s21p_memOsc_mono h hf
  have hg' := s21p_memOsc_mono h hg
  have hc : ∀ {m'' : ℝ} {f' g' : Euc d → ℝ}, MemOsc m'' f' → MemOsc m'' g' → ∀ α,
      OscSpace.coord (OscSpace.ofFun (d := d) m'' f' - OscSpace.ofFun m'' g') α =
        oscEigenvalue d α ^ (m'' / 2) * (Whole.hermiteCoeff f' α - Whole.hermiteCoeff g' α) := by
    intro m'' f' g' h1 h2 α
    have e : OscSpace.coord (OscSpace.ofFun (d := d) m'' f' - OscSpace.ofFun m'' g') α =
        OscSpace.coord (OscSpace.ofFun (d := d) m'' f') α - OscSpace.coord (OscSpace.ofFun m'' g') α := rfl
    rw [e, OscSpace.coord_ofFun_eq h1, OscSpace.coord_ofFun_eq h2]; ring
  rw [dist_eq_norm, dist_eq_norm, OscSpace.norm_eq_coord, OscSpace.norm_eq_coord]
  refine Real.sqrt_le_sqrt (Summable.tsum_le_tsum (fun α => ?_) ?_ ?_)
  · rw [hc hf' hg', hc hf hg, mul_pow, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [rpow_half_sq _ _ (oscEv_pos α), rpow_half_sq _ _ (oscEv_pos α)]
    exact s21p_rpow_le h α
  · exact memℓp_two_iff.1 (lp.memℓp (OscSpace.ofFun (d := d) m' f - OscSpace.ofFun m' g))
  · exact memℓp_two_iff.1 (lp.memℓp (OscSpace.ofFun (d := d) m f - OscSpace.ofFun m g))

theorem s21p_continuousOn_ofFun_mono {m m' : ℝ} (h : m' ≤ m) {S : Set ℝ} {F : ℝ → Euc d → ℝ}
    (hmem : ∀ t ∈ S, MemOsc m (F t))
    (hc : ContinuousOn (fun t => OscSpace.ofFun (d := d) m (F t)) S) :
    ContinuousOn (fun t => OscSpace.ofFun (d := d) m' (F t)) S := by
  rw [Metric.continuousOn_iff] at hc ⊢
  intro b hb ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hc b hb ε hε
  refine ⟨δ, hδ, fun a ha hab => ?_⟩
  exact (s21p_ofFun_dist_le h (hmem a ha) (hmem b hb)).trans_lt (hδ' a ha hab)

end HRS.Whole
