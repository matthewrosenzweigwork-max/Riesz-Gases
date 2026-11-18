import HRS.MS.SA16JetSchwartz

/-!
# S.A.16: the weak norm of a smooth function from bounds on its coordinate derivatives

`sa16y_wnorm_of_pd`: if `f` is smooth and every coordinate derivative `∂^idx f`, `|idx| ≤ m`, has `L^p` norm
at most `K < ∞`, then `wNormE m p f ≤ card (WIndex d m) * K`.  (The second half of `sa16j_odd_wnorm`,
with the bound on the derivatives as a hypothesis.)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section Wnorm
variable {d : ℕ}

theorem sa16y_wnorm_of_pd (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : ℝ≥0∞} (hK : K < ⊤)
    (hbound : ∀ {j : ℕ}, j ≤ m → ∀ idx : Fin j → Fin d,
      eLpNorm (partialDeriv idx f) (ENNReal.ofReal p) volume ≤ K) :
    wNormE m p f ≤ (Fintype.card (WIndex d m) : ℝ≥0∞) * K := by
  have hp1 : 1 ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hpdmem : ∀ {j : ℕ}, j ≤ m → ∀ idx : Fin j → Fin d,
      MemLp (partialDeriv idx f) (ENNReal.ofReal p) volume := by
    intro j hj idx
    exact lt_of_le_of_lt (hbound hj idx) hK
  have hSc : MemLp (sa16j_S d m f) (ENNReal.ofReal p) volume := by
    have hg : MemLp (fun x => ∑ j ∈ Finset.range (m + 1), ∑ r : Fin j → Fin d,
        |partialDeriv r f x|) (ENNReal.ofReal p) volume := by
      refine memLp_finsetSum _ fun j hj => memLp_finsetSum _ fun r _ => ?_
      exact (hpdmem (by have := Finset.mem_range.1 hj; omega) r).norm
    refine hg.mono' (sa16j_S_cont hf m).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d m _ x)]
    exact sa16j_S_le m _ x
  rw [sa16j_wNormE_eq d m p hf hSc]
  have hpt : ∀ x, ‖wJet m f x‖ ≤ ∑ τ : WIndex d m, |partialDeriv τ.2 f x| := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun τ => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun τ : WIndex d m => |partialDeriv τ.2 f x|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  have hjc : AEStronglyMeasurable (wJet m f) volume := (sa16j_jet_cont hf m).aestronglyMeasurable
  calc eLpNorm (wJet m f) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => ∑ τ : WIndex d m, |partialDeriv τ.2 f x|) (ENNReal.ofReal p) volume :=
        eLpNorm_mono_ae_real hjc (Eventually.of_forall hpt)
    _ = eLpNorm (∑ τ : WIndex d m, fun x => |partialDeriv τ.2 f x|) (ENNReal.ofReal p) volume := by
        congr 1
        funext x
        simp [Finset.sum_apply]
    _ ≤ ∑ τ : WIndex d m, eLpNorm (fun x => |partialDeriv τ.2 f x|) (ENNReal.ofReal p) volume := by
        refine eLpNorm_sum_le (by simpa using hp1 : 1 ≤ ENNReal.ofReal p)
    _ ≤ ∑ τ : WIndex d m, K := by
        refine Finset.sum_le_sum fun τ _ => ?_
        have := hbound (by have := τ.1.2; omega : (τ.1 : ℕ) ≤ m) τ.2
        refine le_trans (le_of_eq ?_) this
        exact eLpNorm_norm _ (sa16j_pd_smooth hf τ.2).continuous.aestronglyMeasurable
    _ = (Fintype.card (WIndex d m) : ℝ≥0∞) * K := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Wnorm

end HRS.Whole.AppendixA.Phase2SA16
