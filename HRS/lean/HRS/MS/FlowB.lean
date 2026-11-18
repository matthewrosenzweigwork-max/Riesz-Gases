import HRS.MS.FlowA
import HRS.MS.FlowBAux6

/-!
# MS-FLOW-B: regularity of the flow of `-b` (Lemma S.A.32)

For `b` with `IsDriftBounds T m Λ b` and the flow `Ψ` of `-b`: every `Ψ τ` is `C^{m+1}`, `‖∇Ψ τ‖ ≤ e^{Λτ}`,
every inverse `Φ` of `Ψ τ` is `C^{m+1}` with `‖∇Φ‖ ≤ e^{Λτ}`, and `∇Ψ τ` solves the variational equation in
integral form.  (The pointwise `τ`-derivative of `∇Ψ τ` is not claimed: `∇_x b` is only measurable in `τ`.)

Route: `FlowBPlan.md`; the `C^{m+1}` statement is proved in `FlowBAux6` for a generic finite-dimensional space.
-/

open Set
open HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.FlowB

variable {d : ℕ}

/-- `IsDriftBounds` gives the generic drift hypotheses. -/
theorem db_of_drift {T : ℝ} {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) : DB T m Λ b :=
  ⟨hb.cont, hb.smooth, hb.deriv_bound, hb.growth⟩

/-- The time-reversed field satisfies the same bounds on `[0,τ]`. -/
theorem db_rev {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d} (hb : DB T m Λ b)
    {τ : ℝ} (hτ : τ ≤ T) : DB τ m Λ (FlowA.rev τ b) where
  cont := ((hb.hyp hT).rev hτ).cont
  smooth s hs := by
    have := hb.smooth (τ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact this.neg
  deriv_bound s hs j hj1 hj2 x := by
    have hs' : τ - s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have e : FlowA.rev τ b s = -(b (τ - s)) := by funext y; simp [FlowA.rev]
    rw [e, iteratedFDeriv_neg_apply, norm_neg]
    exact hb.deriv_bound (τ - s) hs' j hj1 hj2 x
  growth := ((hb.hyp hT).rev hτ).growth

theorem fderiv_le_of_lip {f : Euc d → Euc d} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖) (x : Euc d) : ‖fderiv ℝ f x‖ ≤ C := by
  have hl : LipschitzWith C.toNNReal f := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal C hC]; exact hf x y
  have := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := x)
  rwa [Real.coe_toNNReal C hC] at this

/-- (a) The flow map `Ψ τ` is `C^{m+1}`. -/
theorem flow_contDiff {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ) :
    ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψ τ) := fun τ hτ =>
  contDiff_iff_contDiffAt.2 fun x =>
    contDiffAt_flow hT (db_of_drift hb) hΨ.init (fun y => hΨ.eqn y) hτ x

/-- (b) The derivative bound `‖∇Ψ τ‖ ≤ e^{Λτ}`. -/
theorem flow_fderiv_bound {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ x, ‖fderiv ℝ (Ψ τ) x‖ ≤ Real.exp (Λ * τ) := fun τ hτ x =>
  fderiv_le_of_lip (Real.exp_pos _).le (fun y z => by
    have := FlowA.flow_lipschitz hT hb hΨ τ hτ y z
    exact this) x

/-- (c) Any inverse `Φ` of `Ψ τ` is `C^{m+1}` with `‖∇Φ‖ ≤ e^{Λτ}`. -/
theorem flow_inv_contDiff {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ Φ : Euc d → Euc d, (∀ x, Φ (Ψ τ x) = x) → (∀ y, Ψ τ (Φ y) = y) →
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Φ ∧ ∀ y, ‖fderiv ℝ Φ y‖ ≤ Real.exp (Λ * τ) := by
  intro τ hτ Φ _ hΦ2
  have H := FlowA.hyp_of_drift hT hb
  have hrev : DB τ m Λ (FlowA.rev τ b) := db_rev hT (db_of_drift hb) hτ.2
  have Hr : FlowA.Hyp τ Λ (FlowA.rev τ b) := H.rev hτ.2
  choose f hf0 hfs using fun y => FlowA.exists_sol Hr hτ.1 y
  have hΦeq : ∀ y, Φ y = f y τ := by
    intro y
    have hv : FlowA.Sol τ (FlowA.rev τ b) (fun s => Ψ (τ - s) (Φ y)) :=
      FlowA.Sol.rev ((FlowA.sol_of_flow hΨ (Φ y)).mono hτ.2)
    have := FlowA.sol_unique Hr le_rfl hv (hfs y) (by simp [hΦ2, hf0]) τ ⟨hτ.1, le_rfl⟩
    simpa [hΨ.init] using this
  have hΦfun : Φ = fun y => f y τ := funext hΦeq
  refine ⟨?_, ?_⟩
  · rw [hΦfun]
    exact contDiff_iff_contDiffAt.2 fun y =>
      contDiffAt_flow (Ψ := fun s y => f y s) hτ.1 hrev hf0 hfs ⟨hτ.1, le_rfl⟩ y
  · refine fderiv_le_of_lip (Real.exp_pos _).le (fun y y' => ?_)
    rw [hΦeq, hΦeq]
    have := FlowA.gron Hr le_rfl (hfs y) (hfs y') τ ⟨hτ.1, le_rfl⟩
    rw [hf0, hf0, mul_comm] at this
    exact this

/-- Integral form of the variational equation: `∇Ψ_τ(x) v = v - ∫_0^τ ∇b^s(Ψ_s x) ∇Ψ_s(x) v ds`. -/
theorem flow_fderiv_integral {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ x v : Euc d, fderiv ℝ (Ψ τ) x v =
      v - ∫ s in (0 : ℝ)..τ, fderiv ℝ (b s) (Ψ s x) (fderiv ℝ (Ψ s) x v) := fun τ hτ x v =>
  fderiv_flow_integral hT (db_of_drift hb) hΨ.init (fun y => hΨ.eqn y) hτ x v

end HRS.MS.FlowB
