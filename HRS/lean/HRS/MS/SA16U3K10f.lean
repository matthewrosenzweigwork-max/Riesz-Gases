import HRS.MS.SA16U3K10e

/-!
# S.A.16 K10, part (f): `C_b^1` norm of a partial derivative, the weak norm, and the real forms of K5, K8
(worker SA16U3)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA HRS.CZ.Hls Phase2SA16

section K10f
variable {d : ℕ}

lemma sa16u3_cb_nonneg (k : ℕ) (a : Euc d → ℝ) : 0 ≤ cbNorm k a :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

lemma sa16u3_cb_partial {a : Euc d → ℝ} (ha : MemCb 2 a) (v : Euc d) (hv : ‖v‖ = 1) :
    MemCb 1 (fun x => fderiv ℝ a x v) ∧ cbNorm 1 (fun x => fderiv ℝ a x v) ≤ cbNorm 2 a := by
  have hc : ContDiff ℝ 2 a := by simpa using ha.1
  set b : Euc d → ℝ := fun x => fderiv ℝ a x v with hb
  have hb1 : ContDiff ℝ 1 b :=
    (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hb0 : ∀ x, ‖iteratedFDeriv ℝ 0 b x‖ ≤ ‖iteratedFDeriv ℝ 1 a x‖ := by
    intro x
    rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one]
    calc ‖b x‖ ≤ ‖fderiv ℝ a x‖ * ‖v‖ := (fderiv ℝ a x).le_opNorm v
      _ = ‖fderiv ℝ a x‖ := by rw [hv, mul_one]
  have hb1' : ∀ x, ‖iteratedFDeriv ℝ 1 b x‖ ≤ ‖iteratedFDeriv ℝ 2 a x‖ := by
    intro x
    rw [norm_iteratedFDeriv_one]
    have hd1 : DifferentiableAt ℝ (fderiv ℝ a) x :=
      ((hc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
    refine (fderiv ℝ b x).opNorm_le_bound (M := ‖iteratedFDeriv ℝ 2 a x‖) (norm_nonneg _) fun w => ?_
    have e1 : fderiv ℝ b x w = fderiv ℝ (fderiv ℝ a) x w v := by
      have := fderiv_clm_apply (c := fderiv ℝ a) (u := fun _ => v) (x := x) hd1
        (differentiableAt_const _)
      simp only [hb]
      rw [this]
      simp
    rw [e1]
    have e2 := iteratedFDeriv_two_apply (𝕜 := ℝ) a x ![w, v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e2
    rw [← e2]
    have := (iteratedFDeriv ℝ 2 a x).le_opNorm ![w, v]
    rw [Fin.prod_univ_two] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hv, mul_one] at this
    calc ‖iteratedFDeriv ℝ 2 a x ![w, v]‖ ≤ ‖iteratedFDeriv ℝ 2 a x‖ * ‖w‖ := this
      _ = ‖iteratedFDeriv ℝ 2 a x‖ * ‖w‖ := rfl
  obtain ⟨B1, hB1⟩ := ha.2 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := ha.2 2 le_rfl
  refine ⟨⟨hb1, fun j hj => ?_⟩, ?_⟩
  · interval_cases j
    · exact ⟨B1, by rintro _ ⟨x, rfl⟩; exact (hb0 x).trans (hB1 ⟨x, rfl⟩)⟩
    · exact ⟨B2, by rintro _ ⟨x, rfl⟩; exact (hb1' x).trans (hB2 ⟨x, rfl⟩)⟩
  · unfold cbNorm
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have s0 : (⨆ x, ‖iteratedFDeriv ℝ 0 b x‖) ≤ ⨆ x, ‖iteratedFDeriv ℝ 1 a x‖ :=
      ciSup_le fun x => (hb0 x).trans (le_ciSup (ha.2 1 (by norm_num)) x)
    have s1 : (⨆ x, ‖iteratedFDeriv ℝ 1 b x‖) ≤ ⨆ x, ‖iteratedFDeriv ℝ 2 a x‖ :=
      ciSup_le fun x => (hb1' x).trans (le_ciSup (ha.2 2 le_rfl) x)
    have s2 : 0 ≤ ⨆ x, ‖iteratedFDeriv ℝ 0 a x‖ := Real.iSup_nonneg fun _ => norm_nonneg _
    linarith

/-- the weak norm `wNormE 1 2` is controlled by the `L^2` norms of `Z` and `∇Z` -/
lemma sa16u3_wN_le (Z : SchwartzMap (Euc d) ℝ) [Fact (2 ≤ (2 : ℝ))] :
    wNormE 1 2 (⇑Z) ≠ ⊤ ∧
      (wNormE 1 2 (⇑Z)).toReal ≤ sa16u3_N (⇑Z) + sa16u3_N (fun x => ‖fderiv ℝ Z x‖) := by
  have hZ : ContDiff ℝ ∞ (⇑Z) := Z.smooth'
  have heq := sa16j_wNormE_eq d 1 2 hZ (sa16j_S_memLp 1 2 Z)
  have hjc : AEStronglyMeasurable (wJet 1 (⇑Z)) volume := (sa16j_jet_cont hZ 1).aestronglyMeasurable
  have hZm := sa16u3_memLp_schwartz Z
  have hgm := sa16u3_memLp_gradnorm Z
  have hbd : eLpNorm (wJet 1 (⇑Z)) (ENNReal.ofReal 2) volume ≤
      eLpNorm (⇑Z) 2 volume + eLpNorm (fun x => ‖fderiv ℝ Z x‖) 2 volume := by
    rw [ENNReal.ofReal_ofNat]
    have h1 : eLpNorm (wJet 1 (⇑Z)) 2 volume ≤
        eLpNorm (fun x => ‖Z x‖ + ‖fderiv ℝ Z x‖) 2 volume := by
      refine eLpNorm_mono_real hjc fun x => ?_
      have := sa16j_jet_norm_le 1 (⇑Z) x
      simpa [Finset.sum_range_succ, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one] using this
    refine h1.trans ?_
    have h2 := eLpNorm_add_le (f := fun x => ‖Z x‖) (g := fun x => ‖fderiv ℝ Z x‖) (p := 2) (μ := volume)
      (by norm_num)
    refine h2.trans ?_
    rw [eLpNorm_norm _ hZm.aestronglyMeasurable]
  have hfin : eLpNorm (⇑Z) 2 volume + eLpNorm (fun x => ‖fderiv ℝ Z x‖) 2 volume ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hZm.eLpNorm_ne_top, hgm.eLpNorm_ne_top⟩
  have hne : wNormE 1 2 (⇑Z) ≠ ⊤ := by
    rw [heq]; exact ne_top_of_le_ne_top hfin hbd
  refine ⟨hne, ?_⟩
  rw [heq]
  calc (eLpNorm (wJet 1 (⇑Z)) (ENNReal.ofReal 2) volume).toReal
      ≤ (eLpNorm (⇑Z) 2 volume + eLpNorm (fun x => ‖fderiv ℝ Z x‖) 2 volume).toReal :=
        ENNReal.toReal_mono hfin hbd
    _ = sa16u3_N (⇑Z) + sa16u3_N (fun x => ‖fderiv ℝ Z x‖) := by
        unfold sa16u3_N; rw [ENNReal.toReal_add hZm.eLpNorm_ne_top hgm.eLpNorm_ne_top]

lemma sa16u3_oddBlend_one (θ δ : ℝ) (i : Fin d) (u : Euc d → ℝ) (x : Euc d) :
    oddBlend d θ δ 1 i u x = spliceOdd d θ δ i u x := by
  unfold oddBlend; ring

end K10f
end HRS.Whole.AppendixA.Phase2SA16Cutoff
