import HRS.Whole.AppendixALemmas
import HRS.MS.FlowAAux2

/-!
# MS-FLOW-A: the flow of `-b` (Lemma S.A.32, ODE part)

Existence, uniqueness, Gronwall Lipschitz bound, continuity and invertibility (with the backward
Lipschitz bound) of the flow `Ψ` of `-b` on `[0,T]`, for `b` satisfying `IsDriftBounds`.
-/

open Set
open HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.FlowA

variable {d : ℕ}

/-- The drift bounds give the generic hypotheses. -/
theorem hyp_of_drift {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) : Hyp T Λ b where
  Λ_nonneg := (norm_nonneg _).trans (hb.deriv_bound 0 ⟨le_rfl, hT⟩ 1 le_rfl (by omega) 0)
  cont := hb.cont
  lip τ hτ x y := by
    have hd : Differentiable ℝ (b τ) :=
      (hb.smooth τ hτ).differentiable (by exact_mod_cast Nat.succ_ne_zero m)
    have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := b τ) (C := Λ) (fun x _ => hd x)
      (fun x _ => by
        rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
        exact hb.deriv_bound τ hτ 1 le_rfl (by omega) x) (mem_univ y) (mem_univ x)
    exact this
  growth := hb.growth

theorem sol_of_flow {T : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d}
    (hΨ : IsNegDriftFlow T b Ψ) (x : Euc d) : Sol T b (fun τ => Ψ τ x) := hΨ.eqn x

/-- 1. Global existence of the flow. -/
theorem flow_exists {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) : ∃ Ψ, IsNegDriftFlow T b Ψ := by
  choose f hf0 hfs using fun x => exists_sol (hyp_of_drift hT hb) hT x
  exact ⟨fun τ x => f x τ, ⟨hf0, hfs⟩⟩

/-- 2. Uniqueness of the flow. -/
theorem flow_unique {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) {Ψ Ψ' : ℝ → Euc d → Euc d}
    (hΨ : IsNegDriftFlow T b Ψ) (hΨ' : IsNegDriftFlow T b Ψ') :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ x, Ψ τ x = Ψ' τ x := fun τ hτ x =>
  sol_unique (hyp_of_drift hT hb) le_rfl (sol_of_flow hΨ x) (sol_of_flow hΨ' x)
    (by rw [hΨ.init, hΨ'.init]) τ hτ

/-- 3. Gronwall Lipschitz bound. -/
theorem flow_lipschitz {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ Real.exp (Λ * τ) * ‖x - y‖ := by
  intro τ hτ x y
  have := gron (hyp_of_drift hT hb) le_rfl (sol_of_flow hΨ x) (sol_of_flow hΨ y) τ hτ
  rw [hΨ.init, hΨ.init, mul_comm] at this
  exact this

/-- 4. Joint continuity of the flow. -/
theorem flow_continuous {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ) :
    ContinuousOn (fun p : ℝ × Euc d => Ψ p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have hΛ := (hyp_of_drift hT hb).Λ_nonneg
  refine continuousOn_prod_of_continuousOn_lipschitzOnWith'
    (f := fun p : ℝ × Euc d => Ψ p.1 p.2) (s := Icc (0 : ℝ) T) (t := univ)
    (Real.exp (Λ * T)).toNNReal ?_ ?_
  · intro a ha
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le]
    refine (flow_lipschitz hT hb hΨ a ha x y).trans ?_
    gcongr
    exact ha.2
  · intro x _
    exact (sol_of_flow hΨ x).continuousOn

/-- 5. Invertibility with the backward Lipschitz bound. -/
theorem flow_invertible {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsDriftBounds T m Λ b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∃ Φ : Euc d → Euc d, (∀ x, Φ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Φ y) = y) ∧
      ∀ y y', ‖Φ y - Φ y'‖ ≤ Real.exp (Λ * τ) * ‖y - y'‖ := by
  intro τ hτ
  have H := hyp_of_drift hT hb
  have Hr : Hyp τ Λ (rev τ b) := H.rev hτ.2
  choose f hf0 hfs using fun y => exists_sol Hr hτ.1 y
  refine ⟨fun y => f y τ, ?_, ?_, ?_⟩
  · intro x
    have hv : Sol τ (rev τ b) (fun s => Ψ (τ - s) x) :=
      Sol.rev ((sol_of_flow hΨ x).mono hτ.2)
    have := sol_unique Hr le_rfl (hfs (Ψ τ x)) hv (by simp [hf0]) τ ⟨hτ.1, le_rfl⟩
    simpa [hΨ.init] using this
  · intro y
    have hw : Sol τ b (fun s => f y (τ - s)) := by
      have := (hfs y).rev
      rwa [rev_rev] at this
    have := sol_unique H hτ.2 ((sol_of_flow hΨ (f y τ)).mono hτ.2) hw
      (by simp [hΨ.init]) τ ⟨hτ.1, le_rfl⟩
    simpa [hf0] using this
  · intro y y'
    have := gron Hr le_rfl (hfs y) (hfs y') τ ⟨hτ.1, le_rfl⟩
    rw [hf0, hf0, mul_comm] at this
    exact this

end HRS.MS.FlowA
