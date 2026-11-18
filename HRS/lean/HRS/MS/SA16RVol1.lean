import Mathlib

/-!
# S.A.16 (SA16R) Vol1: weakly singular Volterra operators in a Banach space

For `P τ s : X →L X` (`s = τ - r` the elapsed time) with `‖P τ s‖ ≤ C s^{-1/2}` and strong joint continuity on
`{0 < s ≤ τ ≤ T}`, the operator `(V w)(τ) = ∫_0^τ P τ s (w (τ - s)) ds` maps `C([0,T];X)` into itself
(`sa16r_volt_contOn`).  Used for the heat Duhamel formula at fixed viscosity.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

/-- strong continuity at a point plus a local bound gives continuity of `q ↦ F q (y q)` -/
lemma sa16r_clm_apply_strong {α Y Z : Type*} [TopologicalSpace α] [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Y] [NormedSpace ℝ Z] {F : α → Y →L[ℝ] Z} {y : α → Y}
    {S : Set α} {a : α} {B : ℝ} (hF : ∀ v : Y, ContinuousWithinAt (fun q => F q v) S a)
    (hB : ∀ᶠ q in 𝓝[S] a, ‖F q‖ ≤ B) (hy : ContinuousWithinAt y S a) :
    ContinuousWithinAt (fun q => F q (y q)) S a := by
  have hy' : Tendsto (fun q => ‖y q - y a‖) (𝓝[S] a) (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hy)
    exact this
  have hF' : Tendsto (fun q => ‖F q (y a) - F a (y a)‖) (𝓝[S] a) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hF (y a))
  have hsum : Tendsto (fun q => B * ‖y q - y a‖ + ‖F q (y a) - F a (y a)‖) (𝓝[S] a) (𝓝 0) := by
    have := (hy'.const_mul B).add hF'
    simpa using this
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [hB] with q hq
  rw [norm_norm]
  have e : F q (y q) - F a (y a) = F q (y q - y a) + (F q (y a) - F a (y a)) := by
    simp [map_sub]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact (F q).le_of_opNorm_le hq _ |>.trans (by rfl)

/-- The kernel hypotheses in the variables `(τ, s)`, `s = τ - r ∈ (0, τ]`. -/
structure VoltKer {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (T C : ℝ)
    (P : ℝ → ℝ → X →L[ℝ] X) : Prop where
  bound : ∀ τ s : ℝ, 0 < s → s ≤ τ → τ ≤ T → ‖P τ s‖ ≤ C * s ^ (-(1 / 2 : ℝ))
  cont : ∀ x : X, ContinuousOn (fun q : ℝ × ℝ => P q.1 q.2 x) {q | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}

section Volt
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- the Volterra operator -/
def voltOp (P : ℝ → ℝ → X →L[ℝ] X) (w : ℝ → X) (τ : ℝ) : X :=
  ∫ s in (0 : ℝ)..τ, P τ s (w (τ - s))

lemma VoltKer.contApply {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKer T C P) {w : ℝ → X}
    (hw : ContinuousOn w (Icc 0 T)) :
    ContinuousOn (fun q : ℝ × ℝ => P q.1 q.2 (w (q.1 - q.2)))
      {q | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} := by
  intro q0 hq0
  obtain ⟨h0, h1, h2⟩ := hq0
  have hmem : ∀ q ∈ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}, q.1 - q.2 ∈ Icc (0 : ℝ) T := by
    rintro q ⟨a, b, c⟩
    exact ⟨by linarith, by linarith⟩
  refine sa16r_clm_apply_strong (B := C * (q0.2 / 2) ^ (-(1 / 2 : ℝ))) (fun v => hP.cont v q0 ⟨h0, h1, h2⟩) ?_ ?_
  · have hs : ∀ᶠ q in 𝓝[{q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}] q0, q0.2 / 2 < q.2 := by
      have hc : Continuous (fun q : ℝ × ℝ => q.2) := continuous_snd
      have : ∀ᶠ q in 𝓝 q0, q0.2 / 2 < q.2 := hc.continuousAt.eventually (lt_mem_nhds (by linarith))
      exact nhdsWithin_le_nhds this
    filter_upwards [hs, self_mem_nhdsWithin] with q hq hqS
    refine (hP.bound q.1 q.2 hqS.1 hqS.2.1 hqS.2.2).trans ?_
    have h3 : 0 < q0.2 / 2 := by linarith
    have := Real.rpow_le_rpow_of_nonpos h3 hq.le (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have hC : 0 ≤ C := by
      have := hP.bound q0.1 q0.2 h0 h1 h2
      have h5 : 0 ≤ ‖P q0.1 q0.2‖ := norm_nonneg _
      have h6 : 0 < q0.2 ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos h0 _
      by_contra hneg
      have hneg' : C < 0 := lt_of_not_ge hneg
      nlinarith
    exact mul_le_mul_of_nonneg_left this hC
  · have hl : ContinuousWithinAt (fun q : ℝ × ℝ => q.1 - q.2)
        {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} q0 :=
      (continuous_fst.sub continuous_snd).continuousWithinAt
    exact ContinuousWithinAt.comp (g := w) (f := fun q : ℝ × ℝ => q.1 - q.2) (t := Icc (0 : ℝ) T)
      (hw (q0.1 - q0.2) ⟨by linarith, by linarith⟩) hl (fun q hq => hmem q hq)

end Volt

end HRS.Whole.AppendixA.Phase2SA16R
