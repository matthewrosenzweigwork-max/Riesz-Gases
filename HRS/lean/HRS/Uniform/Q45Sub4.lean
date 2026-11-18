import HRS.Uniform.Q45Sub3

/-!
# Q45 (Lemma 3.20): the restricted evolution satisfies the hypotheses of Lemma 3.17 (two-level alternative)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

section Sub

variable {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : ℝ} {S : EvolData H E}

theorem subData_isEvolution (hT : 0 < T) (hev : S.IsEvolution T) : (subData S).IsEvolution T where
  inj := fun x y h => hev.inj (congrArg Subtype.val h)
  dense := hev.dense
  self_H := hev.self_H
  self_E := fun t ht => by
    ext y
    show ((VE0 S t t y : E0 S) : E) = (y : E)
    rw [VE0_coe hev ht.1 le_rfl ht.2, hev.self_E t ht]
    rfl
  comp_H := hev.comp_H
  comp_E := fun s r t hs hsr hrt htT => by
    ext y
    show ((VE0 S t r (VE0 S r s y) : E0 S) : E) = ((VE0 S t s y : E0 S) : E)
    rw [VE0_coe hev (hs.trans hsr) hrt htT, VE0_coe hev hs hsr (hrt.trans htT),
      VE0_coe hev hs (hsr.trans hrt) htT]
    have := congrArg (fun F : E →L[ℝ] E => F (y : E)) (hev.comp_E s r t hs hsr hrt htT)
    simpa using this
  intertwine := fun r t hr hrt htT => by
    ext x
    show ((VE0 S t r (j0 S x) : E0 S) : E) = ((j0 S (S.VH t r x) : E0 S) : E)
    rw [VE0_coe hev hr hrt htT]
    have := congrArg (fun F : H →L[ℝ] E => F x) (hev.intertwine r t hr hrt htT)
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this
  cont_E := fun y => by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (hev.cont_E (y : E)).congr fun p hp => ?_
    show ((VE0 S p.1 p.2 y : E0 S) : E) = S.VE p.1 p.2 (y : E)
    exact VE0_coe hev hp.1 hp.2.1 hp.2.2 y
  deriv := fun t ht x r hr => by
    have hd := hev.deriv t ht x r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    refine hasDerivWithinAt_of_coe ?_
    have e1 : (((-(VE0 S t r (A0 S r x)) : E0 S)) : E) = -S.VE t r (S.A r x) := by
      show -((VE0 S t r (A0 S r x) : E0 S) : E) = _
      rw [VE0_coe hev hr.1 hr.2 ht.2, A0_coe hT hev hrT]
    rw [e1]
    refine hd.congr (fun y hy => ?_) ?_
    · show ((VE0 S t y (j0 S x) : E0 S) : E) = S.VE t y (S.j x)
      exact VE0_coe hev hy.1 hy.2 ht.2 _
    · show ((VE0 S t r (j0 S x) : E0 S) : E) = S.VE t r (S.j x)
      exact VE0_coe hev hr.1 hr.2 ht.2 _

theorem subData_twoLevel (hT : 0 < T) (hev : S.IsEvolution T) {K : ℝ} (h : S.TwoLevel T K) :
    (subData S).TwoLevel T K := by
  obtain ⟨hD, hj, hV, hA⟩ := h
  have hK : 0 ≤ K := (norm_nonneg _).trans hj
  refine ⟨hD, ?_, fun r t hr hrt htT => ⟨(hV r t hr hrt htT).1, ?_⟩, fun r hr x => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
    show ‖S.j x‖ ≤ K * ‖x‖
    exact (S.j.le_opNorm x).trans (mul_le_mul_of_nonneg_right hj (norm_nonneg _))
  · refine ContinuousLinearMap.opNorm_le_bound _ hK fun y => ?_
    show ‖((VE0 S t r y : E0 S) : E)‖ ≤ K * ‖y‖
    rw [VE0_coe hev hr hrt htT]
    exact ((S.VE t r).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hV r t hr hrt htT).2 (norm_nonneg _))
  · show ‖((A0 S r x : E0 S) : E)‖ ≤ K * ‖(x : H)‖
    rw [A0_coe hT hev hr x]
    exact hA r hr x

theorem subData_maxHyp_twoLevel {K : ℝ} (hT : 0 < T) (hev : S.IsEvolution T) (h : S.TwoLevel T K) :
    (subData S).MaxHyp T K :=
  ⟨subData_isEvolution hT hev, Or.inl (subData_twoLevel hT hev h)⟩

end Sub

end HRS.Uniform.Q45
