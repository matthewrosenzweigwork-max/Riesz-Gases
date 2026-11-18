import HRS.MS.QsfAsm9

/-!
# S4.5 packet B5 (assembly), part 10: tails and the final assembly of `quadratic_static_field`
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem S45Feat.mono {s a β : ℝ} {φ χ : Euc d → ℝ} {B B' : ℝ} (h : S45Feat d s a β φ χ B)
    (hB : B ≤ B') : S45Feat d s a β φ χ B' :=
  ⟨h.smooth, fun x => (h.B1 x).trans hB, fun x => (h.B2 x).trans hB, h.corr, h.r2⟩

theorem s45_norm_le_tsum {z : SeqL2} {b : ℕ → ℝ} (hb : Summable b)
    (h : ∀ j, |SeqL2.coord z j| ≤ b j) : ‖z‖ ≤ ∑' j, b j := by
  have hs := lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by simp)
    (show lp (fun _ : ℕ => ℝ) 2 from z)
  have hsum : Summable fun j => |SeqL2.coord z j| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) h hb
  have hn : Summable fun j : ℕ => ‖lp.single (E := fun _ : ℕ => ℝ) 2 j
      ((show lp (fun _ : ℕ => ℝ) 2 from z) j)‖ := by
    simpa [lp.norm_single, SeqL2.coord] using hsum
  have h1 : ‖(show lp (fun _ : ℕ => ℝ) 2 from z)‖ ≤ ∑' j : ℕ, ‖lp.single (E := fun _ : ℕ => ℝ) 2 j
      ((show lp (fun _ : ℕ => ℝ) 2 from z) j)‖ := by
    have e : ‖(show lp (fun _ : ℕ => ℝ) 2 from z)‖ = ‖∑' j : ℕ, lp.single (E := fun _ : ℕ => ℝ) 2 j
        ((show lp (fun _ : ℕ => ℝ) 2 from z) j)‖ := by rw [hs.tsum_eq]
    rw [e]
    exact norm_tsum_le_tsum_norm hn
  refine h1.trans ?_
  refine hn.tsum_le_tsum (fun j => ?_) hb
  simpa [lp.norm_single, SeqL2.coord] using h j

theorem s45_featureVec_norm_le (hN : 1 ≤ N) {J : ℕ} {φ : ℕ → Euc d → ℝ}
    (hφ : HRS.Whole.IsSummableFeatureFamily J φ) {ν : Measure (Euc d)} [IsProbabilityMeasure ν]
    (X : EucConfig d N) : ‖featureVec φ ν X‖ ≤ 2 * Real.sqrt N * featureSum J φ := by
  have hb : Summable fun j => 2 * Real.sqrt N * cbNorm J (φ j) := hφ.2.mul_left _
  have h := s45_norm_le_tsum (z := featureVec φ ν X) hb (fun j => by
    unfold featureVec
    rw [s45_coord_ofSeq (s45_feature_memℓp hN hφ X)]
    exact s45_feature_bound hN hφ.1 X j)
  rw [tsum_mul_left] at h
  exact h

theorem s45_hproj_tendsto (z : SeqL2) :
    Tendsto (fun n => hilbertProj s45_seqBasis n z) atTop (𝓝 z) := by
  have h := (s45_seqBasis.hasSum_repr z).tendsto_sum_nat
  simpa [hilbertProj, HilbertBasis.repr_apply_apply] using h

theorem s45_tail_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : α → SeqL2}
    (hXm : Measurable X) (hXi : Integrable (fun w => ‖X w‖) μ) :
    Tendsto (fun n => ∫ w, ‖X w - hilbertProj s45_seqBasis n (X w)‖ ∂μ) atTop (𝓝 0) := by
  have hpe : ∀ n, hilbertProj s45_seqBasis n = HRS.Whole.Stein.hproj s45_seqBasis n := fun n => rfl
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n w => ‖X w - hilbertProj s45_seqBasis n (X w)‖) (f := fun _ => (0 : ℝ))
    (bound := fun w => 2 * ‖X w‖) ?_ (hXi.const_mul 2) ?_ ?_
  · simpa using h
  · intro n
    simp_rw [hpe]
    exact (hXm.sub ((HRS.Whole.Stein.hproj_continuous s45_seqBasis n).measurable.comp hXm)).norm.aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (norm_sub_le _ _).trans ?_
    have := HRS.Whole.Stein.norm_hproj_le s45_seqBasis n (X w)
    rw [hpe]
    linarith
  · refine Filter.Eventually.of_forall fun w => ?_
    have := (tendsto_iff_norm_sub_tendsto_zero.1 (s45_hproj_tendsto (X w)))
    simpa [norm_sub_rev] using this

end S45

end
