import HRS.MC.E718B6

/-!
# Row 7.18 (packet e718b), file 7: basis independence of the quadratic chaos of an isonormal process

The statement is the verbatim `HRS.chaos_isonormal_basis_independent` (`HRS/Prob/GaussianIso.lean`), with
`IsIsonormal` and `isoSection` restated in this namespace (files 1 and 5).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.MC.E718B

section Isonormal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Ω : Type*} [MeasurableSpace Ω]

theorem chaos_isonormal_basis_independent_proof [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H → Ω → ℝ) (hW : IsIsonormal P W)
    (A : H →L[ℝ] H) (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (e e' : HilbertBasis ℕ ℝ H) (hHS : Summable fun i => ‖A (e i)‖ ^ 2) :
    ∃ Q : Ω → ℝ, HRS.TendstoL2 P (isoSection A W e) Q ∧ HRS.TendstoL2 P (isoSection A W e') Q := by
  have hHS' := summable_other_basis A hA e e' hHS
  set G : ℕ → Ω → ℝ := fun i => W (e i) with hGdef
  have hG : HRS.IsStdGaussianSeq P G := hW.stdSeq (fun i => e i) e.orthonormal
  set a : ℕ → ℕ → ℝ := fun i j => inner ℝ (e i) (A (e j)) with ha
  have hsymm : ∀ i j, a i j = a j i := by
    intro i j
    simp only [ha]
    rw [← hA, real_inner_comm]
  have hrow : ∀ i, HasSum (fun j => a i j ^ 2) (‖A (e i)‖ ^ 2) := by
    intro i
    convert hasSum_sq e (A (e i)) using 1
    ext j
    simp only [ha]
    rw [← hA, real_inner_comm]
  have hsum : Summable fun p : ℕ × ℕ => a p.1 p.2 ^ 2 := by
    rw [summable_prod_of_nonneg (fun p => sq_nonneg _)]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    simpa [fun i => (hrow i).tsum_eq] using hHS
  have hAHS : HRS.IsSymmetricHS a := ⟨hsymm, hsum⟩
  have hT : HRS.TendstoL2 P (HRS.chaosSection a G) (HRS.chaos P a G) :=
    HRS.chaos_tendsto P a hAHS G hG
  have hsec : isoSection A W e = HRS.chaosSection a G := rfl
  have hne : ∀ i, e i ≠ 0 := fun i => e.orthonormal.ne_zero i
  have hne' : ∀ i, e' i ≠ 0 := fun i => e'.orthonormal.ne_zero i
  refine ⟨HRS.chaos P a G, by rw [hsec]; exact hT, ?_⟩
  refine tendstoL2_of_comp (Tn := isoSection A W e) (fun L => aesm_isoSection hW A _ hne' L)
    (fun L => aesm_isoSection hW A _ hne L) (by rw [hsec]; exact hT) ?_
  have h0 : Tendsto (fun L => ENNReal.ofReal
      (∑' j, ‖Tb e L A (e j)‖ ^ 2 + ∑' j, ‖Tb e' L A (e' j)‖ ^ 2)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal ((Tb_tail e A hHS).add (Tb_tail e' A hHS'))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun L => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  exact sections_close hW A hA e e' hHS hHS' L hL

end Isonormal

end HRS.MC.E718B
