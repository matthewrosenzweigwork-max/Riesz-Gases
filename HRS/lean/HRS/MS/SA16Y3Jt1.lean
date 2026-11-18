import HRS.MS.SA16ZR5
import HRS.MS.SA16RExt3

/-!
# S.A.16 (SA16Y3) Jt1: the quantities `S_N(φ)` versus the `L^p` norm of the jet `wJet N φ` (packet P7 iso, step (a))

`sa16y3_S_le_jet`: `S_N(φ) ≤ (∑_{k ≤ N} (d^k + 1)) ‖wJet N φ‖_p` for smooth `φ`; `sa16y3_S_lt_top` for `φ ∈ C_c^∞`.
`sa16y3_jet_le_pd`: `‖wJet m f‖_p ≤ ∑_{j ≤ m} ∑_idx ‖∂^idx f‖_p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Jt1
variable {d : ℕ} {p : ℝ}

lemma sa16y3_vn_le_jet (φ : Euc d → ℝ) {k N : ℕ} (hk : k ≤ N) (x : Euc d) :
    sa16sz_vn φ k x ≤ ((d : ℝ) ^ k + 1) * ‖wJet N φ x‖ := by
  unfold sa16sz_vn vnorm
  have hM := norm_nonneg (wJet N φ x)
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 : ∀ idx : Fin k → Fin d, partialDeriv idx φ x ^ 2 ≤ ‖wJet N φ x‖ ^ 2 := fun idx =>
    sq_le_sq' (by linarith [abs_le.1 (sa16j_pd_le_jet N φ x hk idx)]) (abs_le.1 (sa16j_pd_le_jet N φ x hk idx)).2
  have h2 := Finset.sum_le_sum fun idx (_ : idx ∈ (Finset.univ : Finset (Fin k → Fin d))) => h1 idx
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul] at h2
  push_cast at h2
  have h3 : (d : ℝ) ^ k ≤ ((d : ℝ) ^ k + 1) ^ 2 := by
    have : 0 ≤ (d : ℝ) ^ k := by positivity
    nlinarith
  calc _ ≤ (d : ℝ) ^ k * ‖wJet N φ x‖ ^ 2 := h2
    _ ≤ ((d : ℝ) ^ k + 1) ^ 2 * ‖wJet N φ x‖ ^ 2 := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by ring

lemma sa16y3_eLpNorm_le_vec {E : Type*} [NormedAddCommGroup E] {F : Euc d → ℝ} (hF : AEStronglyMeasurable F volume)
    {g : Euc d → E} (hg : AEStronglyMeasurable g volume) {c : ℝ} (hc : 0 ≤ c) (h : ∀ y, ‖F y‖ ≤ c * ‖g y‖) (q : ℝ≥0∞) :
    eLpNorm F q volume ≤ ENNReal.ofReal c * eLpNorm g q volume := by
  calc eLpNorm F q volume ≤ eLpNorm (c • fun y => ‖g y‖) q volume := by
        refine eLpNorm_mono hF fun y => ?_
        calc ‖F y‖ ≤ c * ‖g y‖ := h y
          _ = ‖(c • fun y => ‖g y‖) y‖ := by simp [abs_of_nonneg hc]
    _ = ENNReal.ofReal c * eLpNorm g q volume := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc, eLpNorm_norm _ hg]

lemma sa16y3_S_le_jet {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (N : ℕ) :
    sa16z_S p φ N ≤ ENNReal.ofReal (∑ k ∈ Finset.range (N + 1), ((d : ℝ) ^ k + 1)) *
      eLpNorm (wJet N φ) (ENNReal.ofReal p) volume := by
  unfold sa16z_S
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  unfold sa16z_JJ
  refine sa16y3_eLpNorm_le_vec (sa16sz_vn_cont φ hφ k).aestronglyMeasurable (sa16j_jet_cont hφ N).aestronglyMeasurable
    (by positivity) (fun y => ?_) _
  rw [Real.norm_eq_abs, abs_of_nonneg (sa16sz_vn_nonneg _ _ _)]
  exact sa16y3_vn_le_jet φ (by have := Finset.mem_range.1 hk; omega) y

lemma sa16y3_S_lt_top {φ : Euc d → ℝ} (hφ : IsCcInfty φ) [Fact (2 ≤ p)] (N : ℕ) : sa16z_S p φ N < ⊤ := by
  refine lt_of_le_of_lt (sa16y3_S_le_jet hφ.1 N) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact (sa16r_jet_memLp_cc (p := p) hφ N).eLpNorm_lt_top

lemma sa16y3_jet_le_pd [Fact (2 ≤ p)] {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    eLpNorm (wJet m f) (ENNReal.ofReal p) volume ≤ ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
      eLpNorm (partialDeriv idx f) (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := Fact.out
  have hpt : ∀ x, ‖wJet m f x‖ ≤ ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ‖partialDeriv idx f x‖ := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)).2
      fun τ => ?_
    have h1 : ‖partialDeriv τ.2 f x‖ ≤ ∑ idx : Fin (τ.1 : ℕ) → Fin d, ‖partialDeriv idx f x‖ :=
      Finset.single_le_sum (f := fun idx : Fin (τ.1 : ℕ) → Fin d => ‖partialDeriv idx f x‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ τ.2)
    refine le_trans ?_ (le_trans h1 ?_)
    · exact le_rfl
    · exact Finset.single_le_sum (f := fun j => ∑ idx : Fin j → Fin d, ‖partialDeriv idx f x‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by have := τ.1.2; omega))
  have hfun : (fun x => ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ‖partialDeriv idx f x‖) =
      ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, fun x => ‖partialDeriv idx f x‖ := by
    funext x; simp [Finset.sum_apply]
  calc eLpNorm (wJet m f) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ‖partialDeriv idx f x‖)
          (ENNReal.ofReal p) volume := by
        refine eLpNorm_mono (sa16j_jet_cont hf m).aestronglyMeasurable fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        exact hpt x
    _ ≤ _ := by
        rw [hfun]
        refine (eLpNorm_sum_le hp1).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (eLpNorm_sum_le hp1).trans (Finset.sum_le_sum fun idx _ => ?_)
        rw [eLpNorm_norm _ ((sa16j_pd_smooth hf idx).continuous.aestronglyMeasurable)]

end Jt1

end HRS.Whole.AppendixA.Phase2SA16R
