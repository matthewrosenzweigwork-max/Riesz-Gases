import HRS.Prob.HilbertMartingale

/-!
# Trace-class covariance forms under bounded operators (packet KOTELENEZ)

`formComp L C` is the form `(u,v) ↦ C(Lu, Lv)`.  Via the rank-one decompositions of trace-class forms we show that it is
again trace class, and `‖formComp L C‖₁ ≤ ‖L‖² ‖C‖₁`; moreover `‖formComp L C‖₁ ≤ ∑ ‖L^* ℓ_j‖²` for every decomposition.
-/

noncomputable section

open scoped ENNReal NNReal BigOperators
open Filter Topology

namespace HRS
namespace Uniform
namespace Kot

section Forms

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] [SecondCountableTopology K]

/-- The form `(u,v) ↦ C(Lu, Lv)`. -/
def formComp (L : K →L[ℝ] H) (C : H →L[ℝ] H →L[ℝ] ℝ) : K →L[ℝ] K →L[ℝ] ℝ :=
  ((C.comp L).flip.comp L).flip

@[simp] theorem formComp_apply (L : K →L[ℝ] H) (C : H →L[ℝ] H →L[ℝ] ℝ) (u v : K) :
    formComp L C u v = C (L u) (L v) := rfl

theorem formComp_zero (L : K →L[ℝ] H) : formComp L (0 : H →L[ℝ] H →L[ℝ] ℝ) = 0 := by
  ext u v; simp

/-- A form with a rank-one decomposition with `∑ ‖ℓ_j‖² < ∞` is trace class. -/
theorem isTraceClassCov_of_decomp {ℓ : ℕ → K} (hs : Summable fun j => ‖ℓ j‖ ^ 2)
    {F : K →L[ℝ] K →L[ℝ] ℝ}
    (hF : ∀ x y, HasSum (fun j => inner ℝ (ℓ j) x * inner ℝ (ℓ j) y) (F x y)) : IsTraceClassCov F := by
  refine ⟨fun x y => ?_, fun x => ?_, ?_⟩
  · rw [← (hF x y).tsum_eq, ← (hF y x).tsum_eq]
    exact tsum_congr fun j => mul_comm _ _
  · have := (hF x x).nonneg (fun j => by nlinarith [mul_self_nonneg (inner ℝ (ℓ j) x)])
    exact this
  · obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ K
    refine ⟨w, b, ?_⟩
    have hsq : ∀ i, F (b i) (b i) = ∑' j, (inner ℝ (ℓ j) (b i)) ^ 2 := fun i => by
      rw [← (hF (b i) (b i)).tsum_eq]; exact tsum_congr fun j => by ring
    have hsm : ∀ i, Summable fun j => (inner ℝ (ℓ j) (b i)) ^ 2 := fun i => by
      have := (hF (b i) (b i)).summable
      exact this.congr fun j => by ring
    refine summable_of_sum_le (c := ∑' j, ‖ℓ j‖ ^ 2) (fun i => ?_) (fun s => ?_)
    · rw [hsq]; exact tsum_nonneg fun j => sq_nonneg _
    · calc ∑ i ∈ s, F (b i) (b i) = ∑ i ∈ s, ∑' j, (inner ℝ (ℓ j) (b i)) ^ 2 :=
            Finset.sum_congr rfl fun i _ => hsq i
        _ = ∑' j, ∑ i ∈ s, (inner ℝ (ℓ j) (b i)) ^ 2 := (Summable.tsum_finsetSum fun i _ => hsm i).symm
        _ ≤ ∑' j, ‖ℓ j‖ ^ 2 := by
            refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun i _ => hsm i) hs
            have := b.orthonormal.sum_inner_products_le (ℓ j) (s := s)
            have ha : ∀ i, ‖inner ℝ (b i) (ℓ j)‖ ^ 2 = (inner ℝ (ℓ j) (b i)) ^ 2 := by
              intro i; rw [real_inner_comm, Real.norm_eq_abs, sq_abs]
            simpa only [ha] using this

omit [CompleteSpace K] in
/-- The variational trace norm is at most the sum of squares of a decomposition. -/
theorem traceNormForm_le_tsum [CompleteSpace K] {ℓ : ℕ → K} (hs : Summable fun j => ‖ℓ j‖ ^ 2)
    {F : K →L[ℝ] K →L[ℝ] ℝ}
    (hF : ∀ x y, HasSum (fun j => inner ℝ (ℓ j) x * inner ℝ (ℓ j) y) (F x y)) :
    traceNormForm F ≤ ∑' j, ‖ℓ j‖ ^ 2 := by
  refine Real.iSup_le (fun p => ?_) (tsum_nonneg fun j => sq_nonneg _)
  exact sum_abs_le_of_decomp hs hF _ _ p.2.1 p.2.2

/-- Finite diagonal sums along an orthonormal family are bounded by the trace norm. -/
theorem sum_diag_finset_le {ι : Type*} {b : ι → K} (hb : Orthonormal ℝ b) {F : K →L[ℝ] K →L[ℝ] ℝ}
    (hbdd : BddAbove (Set.range fun p : OrthonormalPairs K => ∑ i, |F (p.1.2.1 i) (p.1.2.2 i)|))
    (s : Finset ι) : ∑ i ∈ s, F (b i) (b i) ≤ traceNormForm F := by
  classical
  set e : Fin s.card → K := fun t => b ((s.equivFin.symm t).val) with he
  have hinj : Function.Injective fun t : Fin s.card => ((s.equivFin.symm t).val : ι) :=
    Subtype.val_injective.comp s.equivFin.symm.injective
  have hon : Orthonormal ℝ e := hb.comp _ hinj
  have h1 := pairSum_le_traceNormForm hbdd ⟨⟨s.card, e, e⟩, hon, hon⟩
  have h2 : ∑ i ∈ s, F (b i) (b i) = ∑ t : Fin s.card, F (e t) (e t) := by
    calc ∑ i ∈ s, F (b i) (b i) = ∑ i : ↥s, F (b i.val) (b i.val) :=
          (Finset.sum_coe_sort s (fun i => F (b i) (b i))).symm
      _ = ∑ t : Fin s.card, F (b ((s.equivFin.symm t).val)) (b ((s.equivFin.symm t).val)) :=
          (Equiv.sum_comp (s.equivFin.symm) (fun i : ↥s => F (b i.val) (b i.val))).symm
  rw [h2]
  refine le_trans (Finset.sum_le_sum fun t _ => le_abs_self _) h1

/-- Conversely, the sum of squares of a decomposition of a trace-class form is at most its trace norm. -/
theorem tsum_sq_le_traceNormForm {ℓ : ℕ → K} (hs : Summable fun j => ‖ℓ j‖ ^ 2)
    {F : K →L[ℝ] K →L[ℝ] ℝ}
    (hF : ∀ x y, HasSum (fun j => inner ℝ (ℓ j) x * inner ℝ (ℓ j) y) (F x y)) :
    ∑' j, ‖ℓ j‖ ^ 2 ≤ traceNormForm F := by
  have hbdd : BddAbove (Set.range fun p : OrthonormalPairs K => ∑ i, |F (p.1.2.1 i) (p.1.2.2 i)|) :=
    ⟨∑' j, ‖ℓ j‖ ^ 2, by
      rintro _ ⟨p, rfl⟩
      exact sum_abs_le_of_decomp hs hF _ _ p.2.1 p.2.2⟩
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ K
  refine (Real.tsum_le_of_sum_le (fun j => sq_nonneg _) (fun J => ?_))
  have hP : ∀ j, HasSum (fun i : w => (inner ℝ (ℓ j) (b i)) ^ 2) (‖ℓ j‖ ^ 2) := by
    intro j
    have := b.hasSum_inner_mul_inner (ℓ j) (ℓ j)
    have e : (fun i : w => (inner ℝ (ℓ j) (b i)) ^ 2) =
        fun i => inner ℝ (ℓ j) (b i) * inner ℝ (b i) (ℓ j) := by
      funext i; rw [real_inner_comm (ℓ j) (b i), sq]
    rw [e]; simpa [real_inner_self_eq_norm_sq] using this
  have hFd : ∀ i, ∑ j ∈ J, (inner ℝ (ℓ j) (b i)) ^ 2 ≤ F (b i) (b i) := by
    intro i
    have h1 : HasSum (fun j => inner ℝ (ℓ j) (b i) * inner ℝ (ℓ j) (b i)) (F (b i) (b i)) := hF _ _
    have := sum_le_hasSum J (fun j _ => mul_self_nonneg (inner ℝ (ℓ j) (b i))) h1
    simpa only [sq] using this
  have hlim : Tendsto (fun s : Finset w => ∑ j ∈ J, ∑ i ∈ s, (inner ℝ (ℓ j) (b i)) ^ 2) atTop
      (𝓝 (∑ j ∈ J, ‖ℓ j‖ ^ 2)) := tendsto_finset_sum _ fun j _ => hP j
  refine le_of_tendsto' hlim fun s => ?_
  calc ∑ j ∈ J, ∑ i ∈ s, (inner ℝ (ℓ j) (b i)) ^ 2 = ∑ i ∈ s, ∑ j ∈ J, (inner ℝ (ℓ j) (b i)) ^ 2 :=
        Finset.sum_comm
    _ ≤ ∑ i ∈ s, F (b i) (b i) := Finset.sum_le_sum fun i _ => hFd i
    _ ≤ traceNormForm F := sum_diag_finset_le b.orthonormal hbdd s

theorem norm_adjoint_apply_sq_le (L : K →L[ℝ] H) (x : H) :
    ‖ContinuousLinearMap.adjoint L x‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖x‖ ^ 2 := by
  have h1 : ‖ContinuousLinearMap.adjoint L x‖ ≤ ‖L‖ * ‖x‖ := by
    have := (ContinuousLinearMap.adjoint L).le_opNorm x
    rwa [LinearIsometryEquiv.norm_map] at this
  calc ‖ContinuousLinearMap.adjoint L x‖ ^ 2 ≤ (‖L‖ * ‖x‖) ^ 2 := by gcongr
    _ = ‖L‖ ^ 2 * ‖x‖ ^ 2 := by ring

/-- A decomposition of `C` transports to one of `formComp L C`, with `ℓ̂_j = L^* ℓ_j`. -/
theorem decomp_formComp (L : K →L[ℝ] H) {C : H →L[ℝ] H →L[ℝ] ℝ} {ℓ : ℕ → H}
    (hs : Summable fun j => ‖ℓ j‖ ^ 2)
    (hC : ∀ x y, HasSum (fun j => inner ℝ (ℓ j) x * inner ℝ (ℓ j) y) (C x y)) :
    (Summable fun j => ‖ContinuousLinearMap.adjoint L (ℓ j)‖ ^ 2) ∧
      ∀ u v, HasSum (fun j => inner ℝ (ContinuousLinearMap.adjoint L (ℓ j)) u *
        inner ℝ (ContinuousLinearMap.adjoint L (ℓ j)) v) (formComp L C u v) := by
  refine ⟨?_, fun u v => ?_⟩
  · exact Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => norm_adjoint_apply_sq_le L (ℓ j)) (hs.mul_left (‖L‖ ^ 2))
  · have := hC (L u) (L v)
    simp only [formComp_apply]
    convert this using 2 with j
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

theorem isTraceClassCov_formComp {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) (L : K →L[ℝ] H) :
    IsTraceClassCov (formComp L C) := by
  obtain ⟨ℓ, hs, hℓ⟩ := hC.exists_decomp'
  obtain ⟨hs', hℓ'⟩ := decomp_formComp L hs hℓ
  exact isTraceClassCov_of_decomp hs' hℓ'

theorem traceNormForm_formComp_le_decomp (L : K →L[ℝ] H) {C : H →L[ℝ] H →L[ℝ] ℝ} {ℓ : ℕ → H}
    (hs : Summable fun j => ‖ℓ j‖ ^ 2)
    (hC : ∀ x y, HasSum (fun j => inner ℝ (ℓ j) x * inner ℝ (ℓ j) y) (C x y)) :
    traceNormForm (formComp L C) ≤ ∑' j, ‖ContinuousLinearMap.adjoint L (ℓ j)‖ ^ 2 := by
  obtain ⟨hs', hℓ'⟩ := decomp_formComp L hs hC
  exact traceNormForm_le_tsum hs' hℓ'

theorem tsum_adjoint_sq_le (L : K →L[ℝ] H) {ℓ : ℕ → H} (hs : Summable fun j => ‖ℓ j‖ ^ 2) :
    ∑' j, ‖ContinuousLinearMap.adjoint L (ℓ j)‖ ^ 2 ≤ ‖L‖ ^ 2 * ∑' j, ‖ℓ j‖ ^ 2 := by
  have hsum : Summable fun j => ‖L‖ ^ 2 * ‖ℓ j‖ ^ 2 := hs.mul_left _
  have hs' : Summable fun j => ‖ContinuousLinearMap.adjoint L (ℓ j)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => norm_adjoint_apply_sq_le L (ℓ j)) hsum
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun j => norm_adjoint_apply_sq_le L (ℓ j)) hs' hsum

theorem traceNormForm_formComp_le {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) (L : K →L[ℝ] H) :
    traceNormForm (formComp L C) ≤ ‖L‖ ^ 2 * traceNormForm C := by
  obtain ⟨ℓ, hs, hℓ⟩ := hC.exists_decomp'
  refine (traceNormForm_formComp_le_decomp L hs hℓ).trans ?_
  refine (tsum_adjoint_sq_le L hs).trans ?_
  exact mul_le_mul_of_nonneg_left (tsum_sq_le_traceNormForm hs hℓ) (sq_nonneg _)

end Forms

end Kot
end Uniform
end HRS
