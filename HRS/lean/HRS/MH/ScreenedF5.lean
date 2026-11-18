import HRS.MH.ScreenedDefs

/-! Packet F5 of `B:lem:screened` (S.B.4): proof of the statement of `advCutoff_facts` in `ScreenedSpec.lean`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem f5_zero_of_far (f : Euc d → ℝ) (R : ℝ) (hsupp : tsupport f ⊆ Metric.ball 0 R) (w : Euc d)
    (hw : R ≤ ‖w‖) : f w = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => by
    have h' := hsupp h
    rw [Metric.mem_ball, dist_zero_right] at h'
    linarith)

theorem f5_cont_of_lip (Φ : Euc d → Euc d) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ x y, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) : Continuous Φ := by
  have hL' : LipschitzWith (Real.toNNReal L) Φ :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL]; exact h x y
  exact hL'.continuous

theorem f5_lip_comp (f : Euc d → ℝ) (Lc L : ℝ) (hL : 0 ≤ L) (hf : ∀ x y, |f x - f y| ≤ Lc * ‖x - y‖)
    (Φ : Euc d → Euc d) (z : Euc d) (hΦ : ∀ x y, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) :
    ∀ x y, |f (Φ x - z) - f (Φ y - z)| ≤ Lc * L * ‖x - y‖ := by
  intro x y
  have hP : ‖(Φ x - z) - (Φ y - z)‖ = ‖Φ x - Φ y‖ := by rw [sub_sub_sub_cancel_right]
  rcases lt_or_ge Lc 0 with hLc | hLc
  · have h1 := hf x y
    have h0 := abs_nonneg (f x - f y)
    have hD' : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
    have hD : ‖x - y‖ = 0 := le_antisymm hD' (norm_nonneg _)
    have h2 := hf (Φ x - z) (Φ y - z)
    have h3 : Lc * ‖(Φ x - z) - (Φ y - z)‖ ≤ 0 := by nlinarith [norm_nonneg ((Φ x - z) - (Φ y - z))]
    rw [hD, mul_zero]
    linarith
  · calc |f (Φ x - z) - f (Φ y - z)| ≤ Lc * ‖(Φ x - z) - (Φ y - z)‖ := hf _ _
      _ = Lc * ‖Φ x - Φ y‖ := by rw [hP]
      _ ≤ Lc * (L * ‖x - y‖) := mul_le_mul_of_nonneg_left (hΦ x y) hLc
      _ = Lc * L * ‖x - y‖ := by ring

/-- **F5** (size S).  Advected cutoffs: values in `[0,1]`; `χ_z(x) ≠ 0 → ‖Φ x - z‖ < 2`;
`χ̂_z(x) ≠ 0 → ‖Φ x - z‖ < 8`; `‖Φ x - z‖ ≤ 1 → χ_z x = 1`; `‖Φ x - z‖ ≤ 6 → χ̂_z x = 1`;
`tsupport` inclusions via `tsupport_comp_subset_preimage` (`Φ` continuous); `χ_z, χ̂_z` are
`(Lχ L)`-Lipschitz with `Lχ` from `cutoff_lipschitz`. -/
theorem advCutoff_facts_proof (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ)
    (L Lχ : ℝ) (hL : 0 ≤ L)
    (hlipi : ∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ L * ‖x - y‖)
    (hLχ : (∀ x y, |χ x - χ y| ≤ Lχ * ‖x - y‖) ∧ (∀ x y, |χh x - χh y| ≤ Lχ * ‖x - y‖)) (z : Euc d) :
    (∀ x, advCutoff χ Ψ τ z x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, advCutoff χh Ψ τ z x ∈ Icc (0 : ℝ) 1) ∧
    (∀ x, x ∈ tsupport (advCutoff χ Ψ τ z) → ‖Function.invFun (Ψ τ) x - z‖ < 2) ∧
    (∀ x, ‖Function.invFun (Ψ τ) x - z‖ ≥ 8 → advCutoff χh Ψ τ z x = 0) ∧
    (∀ x, ‖Function.invFun (Ψ τ) x - z‖ ≥ 2 → advCutoff χ Ψ τ z x = 0) ∧
    (∀ x, ‖Function.invFun (Ψ τ) x - z‖ ≤ 6 → advCutoff χh Ψ τ z x = 1) ∧
    (∀ x y, |advCutoff χ Ψ τ z x - advCutoff χ Ψ τ z y| ≤ Lχ * L * ‖x - y‖) ∧
    (∀ x y, |advCutoff χh Ψ τ z x - advCutoff χh Ψ τ z y| ≤ Lχ * L * ‖x - y‖) := by
  unfold IsCutoffPair at hχ
  obtain ⟨⟨hc1, hs1, hsup1, hr1, -⟩, ⟨hc2, hs2, hsup2, hr2, hone2⟩⟩ := hχ
  have hΦc : Continuous (Function.invFun (Ψ τ)) := f5_cont_of_lip _ L hL hlipi
  have hfc : Continuous (fun y => Function.invFun (Ψ τ) y - z) := hΦc.sub continuous_const
  refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_,
    f5_lip_comp χ Lχ L hL hLχ.1 (Function.invFun (Ψ τ)) z hlipi,
    f5_lip_comp χh Lχ L hL hLχ.2 (Function.invFun (Ψ τ)) z hlipi⟩
  · unfold advCutoff
    exact hr1 _
  · unfold advCutoff
    exact hr2 _
  · have hx' : x ∈ tsupport (χ ∘ (fun y => Function.invFun (Ψ τ) y - z)) := by
      have e : advCutoff χ Ψ τ z = χ ∘ (fun y => Function.invFun (Ψ τ) y - z) := rfl
      rw [← e]; exact hx
    have h2 : Function.invFun (Ψ τ) x - z ∈ Metric.ball (0 : Euc d) 2 :=
      hsup1 (tsupport_comp_subset_preimage χ hfc hx')
    rwa [Metric.mem_ball, dist_zero_right] at h2
  · exact f5_zero_of_far χh 8 hsup2 _ hx
  · exact f5_zero_of_far χ 2 hsup1 _ hx
  · unfold advCutoff
    exact hone2 _ (by rw [mem_closedBall_zero_iff]; exact hx)

end HRS.MH.Screened
