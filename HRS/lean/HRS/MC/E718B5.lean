import HRS.MC.E718B4

/-!
# Row 7.18 (packet e718b), file 5: comparison of the sections computed in two Hilbert bases
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.MC.E718B

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : H → Ω → ℝ}

/-- Verbatim copy of `HRS.isoSection`. -/
def isoSection (A : H →L[ℝ] H) (W : H → Ω → ℝ) (e : ℕ → H) (L : ℕ) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    inner ℝ (e i) (A (e j)) * (W (e i) ω * W (e j) ω - if i = j then 1 else 0)

lemma exists_common_basis (g g' : ℕ → H) (hg : ∀ i, g i ≠ 0) (L : ℕ) (hL : 0 < L) :
    ∃ (m : ℕ) (f : Fin m → H), 0 < m ∧ Orthonormal ℝ f ∧
      (∀ i < L, g i = ∑ k, inner ℝ (f k) (g i) • f k) ∧
      (∀ i < L, g' i = ∑ k, inner ℝ (f k) (g' i) • f k) := by
  set s : Set H := (Set.range fun i : Fin L => g i) ∪ Set.range fun i : Fin L => g' i with hs
  have hfin : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  set F : Submodule ℝ H := Submodule.span ℝ s with hF
  have : FiniteDimensional ℝ F := FiniteDimensional.span_of_finite ℝ hfin
  set b := stdOrthonormalBasis ℝ F with hb
  have hexp : ∀ x ∈ F, x = ∑ k, inner ℝ ((b k : F) : H) x • ((b k : F) : H) := by
    intro x hx
    have := b.sum_repr' ⟨x, hx⟩
    have h2 := congrArg (fun y : F => (y : H)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm.trans (Finset.sum_congr rfl fun k _ => rfl)
  have hon : Orthonormal ℝ (fun k => ((b k : F) : H)) := by
    have := b.orthonormal.comp_linearIsometry F.subtypeₗᵢ
    exact this
  have hmem : ∀ i < L, g i ∈ F ∧ g' i ∈ F := by
    intro i hi
    exact ⟨Submodule.subset_span (Or.inl ⟨⟨i, hi⟩, rfl⟩), Submodule.subset_span (Or.inr ⟨⟨i, hi⟩, rfl⟩)⟩
  refine ⟨Module.finrank ℝ F, fun k => ((b k : F) : H), ?_, hon, fun i hi => hexp _ (hmem i hi).1,
    fun i hi => hexp _ (hmem i hi).2⟩
  by_contra hm
  have h0 : Module.finrank ℝ F = 0 := Nat.eq_zero_of_not_pos hm
  have := hexp (g 0) (hmem 0 hL).1
  have hemp : IsEmpty (Fin (Module.finrank ℝ F)) := ⟨fun k => by have := k.2; omega⟩
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact hg 0 this

lemma Phi_sub {m : ℕ} (f : Fin m → H) (c c' : Fin m → Fin m → ℝ) (ω : Ω) :
    Phi W f c ω - Phi W f c' ω = Phi W f (fun k l => c k l - c' k l) ω := by
  unfold Phi
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

lemma lintegral_enorm_sq_of_memLp {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, X ω ^ 2 ∂P) := by
  have hi : Integrable (fun ω => X ω ^ 2) P := hX.integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  refine lintegral_congr fun ω => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

lemma aesm_isoSection (hW : IsIsonormal P W) (A : H →L[ℝ] H) (g : ℕ → H) (hg : ∀ i, g i ≠ 0) (L : ℕ) :
    AEStronglyMeasurable (isoSection A W g L) P := by
  unfold isoSection
  refine AEMeasurable.aestronglyMeasurable ?_
  have hm : ∀ i, AEMeasurable (W (g i)) P := fun i => hW.aemeasurable_W _ (hg i)
  refine AEMeasurable.const_mul (Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => ?_) _
  exact AEMeasurable.const_mul (((hm i).mul (hm j)).sub aemeasurable_const) _

/-- Comparison principle in `L²`. -/
lemma tendstoL2_of_comp {Sn Tn : ℕ → Ω → ℝ} {Q : Ω → ℝ}
    (hS : ∀ n, AEStronglyMeasurable (Sn n) P) (hT : ∀ n, AEStronglyMeasurable (Tn n) P)
    (hQ : HRS.TendstoL2 P Tn Q)
    (hd : Tendsto (fun n => ∫⁻ ω, ‖Sn n ω - Tn n ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    HRS.TendstoL2 P Sn Q := by
  refine ⟨hQ.1, ?_⟩
  have hsq : ∀ (x : ℕ → ℝ≥0∞), Tendsto (fun n => x n ^ 2) atTop (𝓝 0) → Tendsto x atTop (𝓝 0) := by
    intro x hx
    have hc : Continuous fun y : ℝ≥0∞ => y ^ (1 / 2 : ℝ) := ENNReal.continuous_rpow_const
    have := (hc.tendsto 0).comp hx
    simp only [Function.comp_def] at this
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    refine this.congr fun n => ?_
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have e1 : ∀ n, ∫⁻ ω, ‖Sn n ω - Tn n ω‖ₑ ^ 2 ∂P = eLpNorm (Sn n - Tn n) 2 P ^ 2 :=
    fun n => HRS.lintegral_enorm_sq_eq ((hS n).sub (hT n))
  have d1 : Tendsto (fun n => eLpNorm (Sn n - Tn n) 2 P) atTop (𝓝 0) := by
    refine hsq _ ?_
    simpa [e1] using hd
  have d2 := hQ.tendsto_eLpNorm hT
  have hle : ∀ n, eLpNorm (Sn n - Q) 2 P ≤ eLpNorm (Sn n - Tn n) 2 P + eLpNorm (Tn n - Q) 2 P := by
    intro n
    have e : Sn n - Q = (Sn n - Tn n) + (Tn n - Q) := by abel
    rw [e]
    exact eLpNorm_add_le (by norm_num)
  have d3 : Tendsto (fun n => eLpNorm (Sn n - Q) 2 P) atTop (𝓝 0) := by
    have := d1.add d2
    rw [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun n => bot_le) hle
  have hc : Continuous fun y : ℝ≥0∞ => y ^ 2 := by fun_prop
  have := (hc.tendsto 0).comp d3
  simp only [Function.comp_def] at this
  rw [zero_pow (by norm_num)] at this
  refine this.congr fun n => ?_
  exact (HRS.lintegral_enorm_sq_eq ((hS n).sub hQ.1)).symm

end

end HRS.MC.E718B
