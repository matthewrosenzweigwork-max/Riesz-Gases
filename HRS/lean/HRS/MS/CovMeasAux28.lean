import HRS.MS.CovMeasAux27

/-!
# S10.1 (worker S101B), part 28: interval functions of the push-forward measure (additivity, continuity, total variation)
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9

variable {d : ℕ} {m T : ℝ}

section Interval

variable (hT : 0 ≤ T)
  (J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T))))
  (D : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)

include hT in
lemma s101Jx_empty : s101Jx hT J D ∅ = 0 := by
  unfold s101Jx
  rw [VectorMeasure.empty]
  exact s101Psi_zero hT

include hT in
lemma s101Jx_union {A B : Set ℝ} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    s101Jx hT J D (A ∪ B) = s101Jx hT J D A + s101Jx hT J D B := by
  unfold s101Jx
  rw [VectorMeasure.of_union h hA hB]
  exact s101Psi_add hT _ _

include hT in
lemma s101Jx_Ioc_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    s101Jx hT J D (Ioc a c) = s101Jx hT J D (Ioc a b) + s101Jx hT J D (Ioc b c) := by
  rw [← Set.Ioc_union_Ioc_eq_Ioc hab hbc]
  refine s101Jx_union hT J D ?_ measurableSet_Ioc measurableSet_Ioc
  rw [Set.disjoint_left]
  intro x hx hx'
  exact absurd hx.2 (not_le.2 hx'.1)

include hT in
lemma s101Jx_Ioc_self (a : ℝ) : s101Jx hT J D (Ioc a a) = 0 := by
  rw [Set.Ioc_self]; exact s101Jx_empty hT J D

include hT in
lemma s101Jx_Icc_split {u : ℝ} (hu : 0 ≤ u) :
    s101Jx hT J D (Icc 0 u) = s101Jx hT J D {0} + s101Jx hT J D (Ioc 0 u) := by
  have : Icc (0 : ℝ) u = {0} ∪ Ioc 0 u := by
    ext x
    simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨h, h2⟩
    · rintro (h | h)
      · exact ⟨h.symm.le, h ▸ hu⟩
      · exact ⟨h.1.le, h.2⟩
  rw [this]
  refine s101Jx_union hT J D ?_ (measurableSet_singleton 0) measurableSet_Ioc
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_singleton_iff] at hx
  exact absurd hx (ne_of_gt hx'.1)

end Interval

lemma lipschitz_s101Psi (hT : 0 ≤ T) :
    LipschitzWith (⟨‖(s56_reconCLM hT : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2, by positivity⟩ : ℝ≥0)
      (s101Psi (d := d) (m := m) hT) := by
  refine LipschitzWith.of_dist_le_mul fun τ τ' => ?_
  rw [dist_eq_norm, dist_eq_norm, ← s101Psi_sub]
  exact norm_s101Psi_le hT _

theorem s101_Jx_Ioc0_cont (hT : 0 ≤ T) {C0 : ℝ}
    {J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T)))}
    (hJ : S101Jprops T C0 J) {D : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ}
    (hD : HRS.Uniform.IsTraceDensityL1 T D) :
    ContinuousOn (fun u => s101Jx hT J D (Ioc 0 u)) (Icc 0 T) := by
  have h1 : ContinuousOn (fun u => s101Psi hT (J D (Icc 0 u))) (Icc 0 T) :=
    (lipschitz_s101Psi hT).continuous.comp_continuousOn (hJ.cont D hD)
  have h2 : ContinuousOn (fun u => s101Psi hT (J D (Icc 0 u)) - s101Jx hT J D {0}) (Icc 0 T) :=
    h1.sub continuousOn_const
  refine h2.congr fun u hu => ?_
  have := s101Jx_Icc_split hT J D hu.1
  show s101Jx hT J D (Ioc 0 u) = s101Psi hT (J D (Icc 0 u)) - s101Jx hT J D {0}
  have e : s101Psi hT (J D (Icc 0 u)) = s101Jx hT J D (Icc 0 u) := rfl
  rw [e, this]; abel

theorem s101_Jx_tv (hT : 0 ≤ T) {C0 : ℝ}
    {J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T)))}
    (D : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) (n : ℕ) (u : ℕ → ℝ) (hu : Monotone u)
    (hmem : ∀ i, u i ∈ Icc (0 : ℝ) T) :
    ∑ i ∈ Finset.range n, ‖s101Jx hT J D (Ioc (u i) (u (i + 1)))‖ₑ ≤
      ENNReal.ofReal (‖(s56_reconCLM hT : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2) *
        (J D).variation (Icc 0 T) := by
  calc ∑ i ∈ Finset.range n, ‖s101Jx hT J D (Ioc (u i) (u (i + 1)))‖ₑ
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (‖(s56_reconCLM hT : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2) *
          (J D).variation (Ioc (u i) (u (i + 1))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : ‖s101Jx hT J D (Ioc (u i) (u (i + 1)))‖ₑ ≤
            ENNReal.ofReal (‖(s56_reconCLM hT : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2) *
              ‖J D (Ioc (u i) (u (i + 1)))‖ₑ := by
          have := norm_s101Psi_le hT (J D (Ioc (u i) (u (i + 1))))
          have h2 : ‖s101Jx hT J D (Ioc (u i) (u (i + 1)))‖ₑ ≤
              ENNReal.ofReal (‖(s56_reconCLM hT : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2 *
                ‖J D (Ioc (u i) (u (i + 1)))‖) := by
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal this
          rwa [ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm] at h2
        exact h1.trans (mul_le_mul' le_rfl (VectorMeasure.enorm_measure_le_variation _ _))
    _ = ENNReal.ofReal (‖(s56_reconCLM hT : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2) *
          ∑ i ∈ Finset.range n, (J D).variation (Ioc (u i) (u (i + 1))) := by rw [Finset.mul_sum]
    _ = ENNReal.ofReal (‖(s56_reconCLM hT : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2) *
          (J D).variation (⋃ i ∈ Finset.range n, Ioc (u i) (u (i + 1))) := by
        rw [measure_biUnion_finset ?_ (fun i _ => measurableSet_Ioc)]
        intro i _ j _ hij
        simp only [Function.onFun]
        rw [Set.disjoint_left]
        intro x hx hx'
        rcases lt_or_gt_of_ne hij with h | h
        · exact absurd hx.2 (not_le.2 (lt_of_le_of_lt (hu (Nat.succ_le_of_lt h)) hx'.1))
        · exact absurd hx'.2 (not_le.2 (lt_of_le_of_lt (hu (Nat.succ_le_of_lt h)) hx.1))
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (measure_mono ?_)
        intro x hx
        simp only [mem_iUnion] at hx
        obtain ⟨i, _, hxi⟩ := hx
        exact ⟨(hmem i).1.trans hxi.1.le, hxi.2.trans (hmem (i + 1)).2⟩

end HRS.MS.CovMeas
