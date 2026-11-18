import HRS.MS.SA12X3C7C2

/-!
# S.A.12 C7 (SA12X3), part C3 (7C): geometry of a moving cell

Uniform constants `R'`, `h`: if `χ_{c0}^τ(x) ≠ 0` then `x ∈ B(Ψ_τ c0, R')` and `χ̂_{c0}^τ = 1` on `B(x, h)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_geom (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ R' h : ℝ, 0 < R' ∧ 0 < h ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → HRS.Whole.IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ c0 : Euc d,
      tsupport (advCutoff χh Ψ τ c0) ⊆ ball (Ψ τ c0) R' ∧
      ∀ x : Euc d, advCutoff χ Ψ τ c0 x ≠ 0 → x ∈ ball (Ψ τ c0) R' ∧
        ∀ y ∈ ball x h, advCutoff χh Ψ τ c0 y = 1 := by
  obtain ⟨B, R, hB, hR1, hfacts⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  obtain ⟨CF, hCF0, hCF⟩ := HRS.MH.Screened.flow_lip_sep_proof hd m Cb T χ χh hχ
  refine ⟨R + 1, 4 * Real.exp (-(CF * T)), by linarith, by positivity, ?_⟩
  intro b Ψ hb hΨ τ hτ c0
  have hcut := hfacts b Ψ hb hΨ τ hτ c0
  have hsupp : Function.support (advCutoff χh Ψ τ c0) ⊆ closedBall (Ψ τ c0) R := hcut.2.2
  refine ⟨(closure_minimal hsupp isClosed_closedBall).trans (closedBall_subset_ball (by linarith)), ?_⟩
  intro x hx
  refine ⟨closedBall_subset_ball (by linarith) (hsupp (sa12z3_adv_support_le hχ Ψ τ c0 hx)), ?_⟩
  intro y hy
  by_contra hne
  have hy1 : y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ c0 y) :=
    subset_tsupport _ (Function.mem_support.2 (fun h0 => hne (by linarith)))
  have hx1 : x ∈ tsupport (advCutoff χ Ψ τ c0) := subset_tsupport _ hx
  have hsep := (hCF b Ψ hb hΨ τ hτ).2.2 c0 x y hx1 hy1
  have hle : Real.exp (-(CF * T)) ≤ Real.exp (-(CF * τ)) :=
    Real.exp_le_exp.2 (by nlinarith [hτ.2, hCF0])
  have hd' : ‖x - y‖ < 4 * Real.exp (-(CF * T)) := by
    have hy' := mem_ball.1 hy
    rw [dist_eq_norm] at hy'
    rwa [norm_sub_rev]
  linarith

end HRS.MH.AdjointRd.Phase2SA12Near
