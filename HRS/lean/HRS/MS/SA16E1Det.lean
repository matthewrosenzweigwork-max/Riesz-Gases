import HRS.MS.SA16E1Bnd

/-!
# S.A.16 E1: deterministic flow geometry with a separated growth constant

For a drift `bt` with `IsDriftBounds T m Λg bt` (growth constant `Λg` arbitrary) and derivative bounds `Λ`
(`hdb`), the flow of `-bt` and its inverses are `C^{m+1}` with all derivatives of order `1..m+1` bounded by a
constant depending only on `d, m, T, Λ`.
-/

open Set
open HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.SA16E1

open HRS.MS.FlowB

variable {d : ℕ}

theorem e1_hdb_rev {τ : ℝ} {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hdb : ∀ s ∈ Icc (0 : ℝ) τ, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (b s) x‖ ≤ Λ) :
    ∀ s ∈ Icc (0 : ℝ) τ, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (FlowA.rev τ b s) x‖ ≤ Λ := by
  intro s hs j hj1 hj2 x
  have hs' : τ - s ∈ Icc (0 : ℝ) τ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have e : FlowA.rev τ b s = -(b (τ - s)) := by funext y; simp [FlowA.rev]
  rw [e, iteratedFDeriv_neg_apply, norm_neg]
  exact hdb (τ - s) hs' j hj1 hj2 x

theorem e1_det (d m : ℕ) (T Λ : ℝ) (hT : 0 ≤ T) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λg : ℝ) (bt : ℝ → Euc d → Euc d), IsDriftBounds T m Λg bt →
      (∀ s ∈ Icc (0 : ℝ) T, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (bt s) x‖ ≤ Λ) →
      ∀ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T bt Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
        (∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d, ‖iteratedFDeriv ℝ j (Ψ τ) x‖ ≤ C) ∧
        ∀ Φ : Euc d → Euc d, (∀ x, Φ (Ψ τ x) = x) → (∀ y, Ψ τ (Φ y) = y) →
          ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Φ ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ y : Euc d, ‖iteratedFDeriv ℝ j Φ y‖ ≤ C := by
  obtain ⟨K, hK1, hK⟩ := fc_flow_bound (E := Euc d) m T Λ hΛ
  refine ⟨K, by linarith, fun Λg bt hb hdb Ψ hΨ τ hτ => ?_⟩
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  refine ⟨fun j hj1 hjm x => hK T hT le_rfl Λg bt (db_of_drift hb) hdb Ψ hΨ.init
    (fun y => hΨ.eqn y) τ hτ j hj1 hjm x, fun Φ _ hΦ2 => ?_⟩
  have H := FlowA.hyp_of_drift hT hb
  have hrev : DB τ m Λg (FlowA.rev τ bt) := db_rev hT (db_of_drift hb) hτT
  have Hr : FlowA.Hyp τ Λg (FlowA.rev τ bt) := H.rev hτT
  choose f hf0 hfs using fun y => FlowA.exists_sol Hr hτ0 y
  have hΦeq : ∀ y, Φ y = f y τ := by
    intro y
    have hv : FlowA.Sol τ (FlowA.rev τ bt) (fun s => Ψ (τ - s) (Φ y)) :=
      FlowA.Sol.rev ((FlowA.sol_of_flow hΨ (Φ y)).mono hτT)
    have := FlowA.sol_unique Hr le_rfl hv (hfs y) (by simp [hΦ2, hf0]) τ ⟨hτ0, le_rfl⟩
    simpa [hΨ.init] using this
  have hΦfun : Φ = fun y => f y τ := funext hΦeq
  have hdbr : ∀ s ∈ Icc (0 : ℝ) τ, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (FlowA.rev τ bt s) x‖ ≤ Λ :=
    e1_hdb_rev (fun s hs => hdb s ⟨hs.1, hs.2.trans hτT⟩)
  refine ⟨?_, fun j hj1 hjm y => ?_⟩
  · rw [hΦfun]
    exact contDiff_iff_contDiffAt.2 fun y =>
      contDiffAt_flow (Ψ := fun s y => f y s) hτ0 hrev hf0 hfs ⟨hτ0, le_rfl⟩ y
  · rw [hΦfun]
    exact hK τ hτ0 hτT Λg (FlowA.rev τ bt) hrev hdbr (fun s y => f y s) hf0 hfs τ
      ⟨hτ0, le_rfl⟩ j hj1 hjm y

end HRS.MS.SA16E1
