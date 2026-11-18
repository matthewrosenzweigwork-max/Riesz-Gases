import HRS.MS.SA16E1Red

/-!
# S.A.16 E1: the translated drift satisfies `IsDriftBounds`; `charFlow - a` is its flow
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.Whole.AppendixALemmas

theorem e1_hdb {d m : ℕ} {B : ℝ} {b : ℝ → Euc d → Euc d} (hb : DriftBounds d (m+1) B b)
    (ν : ℝ) (w : ℝ≥0 → Fin d → ℝ) {T : ℝ} :
    ∀ s ∈ Icc (0 : ℝ) T, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (e1bt d ν w b s) x‖ ≤ B := by
  intro s hs j hj1 hj2 x
  have h := (hb.2 s hs.1).2.2 j hj1 hj2 (x + e1a d ν w s)
  have e : e1bt d ν w b s = fun y => b s (y + e1a d ν w s) := rfl
  rw [e, iteratedFDeriv_comp_add_right]
  exact h

theorem e1_driftBounds {d m : ℕ} {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d (m+1) B b) (ν : ℝ) {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) {T : ℝ} :
    ∃ Λg : ℝ, B ≤ Λg ∧ IsDriftBounds T m Λg (e1bt d ν w b) := by
  have hk : 1 ≤ m + 1 := by omega
  have hB := e1_B_nonneg hb
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (e1_a_cont d ν hw).continuousOn (s := Icc (0 : ℝ) T)
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hAτ : ∀ τ ∈ Icc (0 : ℝ) T, ‖e1a d ν w τ‖ ≤ A' := fun τ hτ => (hA τ hτ).trans (le_max_left _ _)
  have hΛ : B ≤ B * (1 + A') := by nlinarith
  refine ⟨B * (1 + A'), hΛ, ?_, ?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun p : ℝ × Euc d => (p.1, p.2 + e1a d ν w p.1))
        (Icc (0 : ℝ) T ×ˢ univ) :=
      (continuous_fst.prodMk (continuous_snd.add ((e1_a_cont d ν hw).comp continuous_fst))).continuousOn
    exact hb.1.comp h1 (fun p hp => ⟨hp.1.1, trivial⟩)
  · intro τ hτ
    have := (hb.2 τ hτ.1).1
    exact this.comp (contDiff_id.add contDiff_const)
  · intro τ hτ j hj1 hj2 x
    exact (e1_hdb hb ν w τ hτ j hj1 hj2 x).trans hΛ
  · intro τ hτ y
    have h1 : ‖b τ (y + e1a d ν w τ)‖ ≤ B + B * ‖y + e1a d ν w τ‖ := by
      have := e1_lipB hk hb hτ.1 (y + e1a d ν w τ) 0
      have h0 := (hb.2 τ hτ.1).2.1
      calc ‖b τ (y + e1a d ν w τ)‖ = ‖(b τ (y + e1a d ν w τ) - b τ 0) + b τ 0‖ := by simp
        _ ≤ ‖b τ (y + e1a d ν w τ) - b τ 0‖ + ‖b τ 0‖ := norm_add_le _ _
        _ ≤ B * ‖y + e1a d ν w τ - 0‖ + B := add_le_add this h0
        _ = B + B * ‖y + e1a d ν w τ‖ := by rw [sub_zero]; ring
    have h2 : ‖y + e1a d ν w τ‖ ≤ ‖y‖ + A' := (norm_add_le _ _).trans (by linarith [hAτ τ hτ])
    show ‖b τ (y + e1a d ν w τ)‖ ≤ B * (1 + A') * (1 + ‖y‖)
    nlinarith [norm_nonneg y, mul_nonneg hB hA'0, mul_nonneg (mul_nonneg hB hA'0) (norm_nonneg y),
      mul_nonneg hB (norm_nonneg y)]

theorem e1_negFlow {d k : ℕ} (hk : 1 ≤ k) {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d k B b) (ν : ℝ) {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) (T : ℝ) :
    HRS.Whole.AppendixALemmas.IsNegDriftFlow T (e1bt d ν w b) (fun τ x => charFlow d b ν w τ x - e1a d ν w τ) := by
  refine ⟨fun x => ?_, fun x τ hτ => ?_⟩
  · have := e1_flow_eq hk hb ν hw x (le_refl (0:ℝ))
    simp only [intervalIntegral.integral_same, sub_zero] at this
    simp only [this, e1_a_zero d ν w hw0]
    abel
  · set g : ℝ → Euc d := fun s => b (max s 0) (charFlow d b ν w (max s 0) x) with hg
    have hgc : Continuous g := e1_integrand_cont hk hb ν hw x
    have hd : HasDerivAt (fun τ' => ∫ s in (0:ℝ)..τ', g s) (g τ) τ :=
      (hgc.integral_hasStrictDerivAt 0 τ).hasDerivAt
    have h2 := (hd.const_sub x).hasDerivWithinAt (s := Icc (0 : ℝ) T)
    have hgτ : g τ = b τ (charFlow d b ν w τ x) := by simp [hg, max_eq_left hτ.1]
    rw [hgτ] at h2
    have h3 : HasDerivWithinAt (fun τ' => x - ∫ s in (0:ℝ)..τ', g s)
        (-(e1bt d ν w b τ (charFlow d b ν w τ x - e1a d ν w τ))) (Icc (0 : ℝ) T) τ := by
      have e : e1bt d ν w b τ (charFlow d b ν w τ x - e1a d ν w τ) = b τ (charFlow d b ν w τ x) := by
        simp [e1bt]
      rw [e]; exact h2
    refine h3.congr (fun y hy => ?_) ?_
    · rw [e1_flow_eq hk hb ν hw x hy.1]
      have : ∫ s in (0:ℝ)..y, g s = ∫ s in (0:ℝ)..y, b s (charFlow d b ν w s x) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le hy.1] at hs
        simp [hg, max_eq_left hs.1]
      rw [this]; abel
    · rw [e1_flow_eq hk hb ν hw x hτ.1]
      have : ∫ s in (0:ℝ)..τ, g s = ∫ s in (0:ℝ)..τ, b s (charFlow d b ν w s x) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le hτ.1] at hs
        simp [hg, max_eq_left hs.1]
      rw [this]; abel

end HRS.Whole.AppendixA.Phase2SA16Evolution
