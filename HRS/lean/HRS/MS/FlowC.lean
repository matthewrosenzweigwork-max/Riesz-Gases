import HRS.MS.FlowB
import HRS.MS.FlowCAux2

/-!
# MS-FLOW-C: higher-order derivative bounds of the flow (Lemma S.A.32 (i))

For `IsDriftBounds T m Λ b` and the flow `Ψ` of `-b`, `‖D^jΨ_τ‖ ≤ C e^{C m τ}` for `2 ≤ j ≤ m+1`, and the same for any
inverse of `Ψ_τ`; `C` depends only on `d, m, T, Λ`.  Route: `FlowCPlan.md` (a uniform bound `K(m,T,Λ)` suffices since
`C e^{C m τ} ≥ C`).
-/

open Set
open HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped BoundedContinuousFunction

namespace HRS.MS.FlowC

open HRS.MS.FlowB

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- The induction on the order. -/
theorem fc_induction (m : ℕ) (T Λ : ℝ) :
    ∀ n : ℕ, n ≤ m + 1 → ∃ K : ℝ, 1 ≤ K ∧ ∀ S : ℝ, 0 ≤ S → S ≤ T → ∀ b : ℝ → E → E,
      DB S m Λ b → ∀ Ξ : E → (ℝ →ᵇ E), ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ →
      (∀ x, Gmap S b (Ξ x) = constCLM E x) →
      ∀ x : E, ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i Ξ x‖ ≤ K := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨1, le_rfl, fun _ _ _ _ _ _ _ _ i h1 h2 => by omega⟩
  | succ n ih =>
    intro hn
    obtain ⟨K, hK1, hK⟩ := ih (by omega)
    set K' : ℝ := max K (Real.exp (Λ * T) * (Fintype.card (OrderedFinpartition (n + 1)) *
      (Λ * T) * K ^ (n + 1))) with hK'
    set K'' : ℝ := max K' (Real.exp (Λ * T)) with hK''
    refine ⟨K'', hK1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
    intro S hS0 hST b hb Ξ hΞ hG x i hi1 hi2
    have hΛ := hb.Λ_nonneg hS0
    have hexp : Real.exp (Λ * S) ≤ Real.exp (Λ * T) := Real.exp_le_exp.2 (by gcongr)
    by_cases hin : i ≤ n
    · exact (hK S hS0 hST b hb Ξ hΞ hG x i hi1 hin).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · have hi : i = n + 1 := by omega
      subst hi
      by_cases hn0 : n = 0
      · subst hn0
        rw [norm_iteratedFDeriv_one (𝕜 := ℝ)]
        exact ((fc_base hS0 hb hΞ hG x).trans hexp).trans (le_max_right _ _)
      · have hlow : ∀ i, 1 ≤ i → i < n + 1 → ‖iteratedFDeriv ℝ i Ξ x‖ ≤ K := fun i h1 h2 =>
          hK S hS0 hST b hb Ξ hΞ hG x i h1 (by omega)
        refine (fc_step hS0 hb hΞ hG (j := n + 1) (by omega) hn x hK1 hlow).trans ?_
        refine le_trans ?_ ((le_max_right K _).trans (le_max_left _ _))
        have hK0 : 0 ≤ K := by linarith
        have hcard : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition (n + 1)) := by positivity
        have hΛS : Λ * S ≤ Λ * T := by gcongr
        calc Real.exp (Λ * S) * (Fintype.card (OrderedFinpartition (n + 1)) * (Λ * S) * K ^ (n + 1))
            ≤ Real.exp (Λ * T) * (Fintype.card (OrderedFinpartition (n + 1)) * (Λ * T) *
              K ^ (n + 1)) := by
              gcongr

/-- Uniform bound on all derivatives of the flow map, generic space. -/
theorem fc_flow_bound (m : ℕ) (T Λ : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ S : ℝ, 0 ≤ S → S ≤ T → ∀ b : ℝ → E → E, DB S m Λ b →
      ∀ Ψ : ℝ → E → E, (∀ x, Ψ 0 x = x) → (∀ x, FlowA.Sol S b (fun τ => Ψ τ x)) →
      ∀ τ ∈ Icc (0 : ℝ) S, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : E,
        ‖iteratedFDeriv ℝ j (Ψ τ) x‖ ≤ K := by
  obtain ⟨K, hK1, hK⟩ := fc_induction (E := E) m T Λ (m + 1) le_rfl
  refine ⟨K, hK1, fun S hS0 hST b hb Ψ h0 hs τ hτ j hj1 hjm x => ?_⟩
  obtain ⟨Ξ, hΞ, hG, hΞΨ⟩ := fc_exists_param hS0 hb h0 hs
  have hfun : Ψ τ = (BoundedContinuousFunction.evalCLM (β := E) ℝ τ) ∘ Ξ :=
    funext fun y => (hΞΨ y τ hτ).symm
  have hjn : (j : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hjm
  have hL : ‖BoundedContinuousFunction.evalCLM (β := E) ℝ τ‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun γ => by
      simpa using γ.norm_coe_le_norm τ
  rw [hfun]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hΞ.contDiffAt) hjn).trans ?_
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ j Ξ x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ ≤ K := by rw [one_mul]; exact hK S hS0 hST b hb Ξ hΞ hG x j hj1 hjm

end Generic

variable {d : ℕ}

/-- S.A.32 (i): higher-order derivative bounds for the flow and its inverses. -/
theorem flow_iter_bound (d m : ℕ) (T Λ : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ → Euc d → Euc d, IsDriftBounds T m Λ b →
      ∀ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
        (∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (Ψ τ) x‖ ≤ C * Real.exp (C * m * τ)) ∧
        (∀ Φ : Euc d → Euc d, (∀ x, Φ (Ψ τ x) = x) → (∀ y, Ψ τ (Φ y) = y) →
          ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ y : Euc d,
          ‖iteratedFDeriv ℝ j Φ y‖ ≤ C * Real.exp (C * m * τ)) := by
  obtain ⟨K, hK1, hK⟩ := fc_flow_bound (E := Euc d) m T Λ
  have hK0 : 0 ≤ K := by linarith
  refine ⟨K, by linarith, fun b hb Ψ hΨ τ hτ => ?_⟩
  have hτ0 : 0 ≤ τ := hτ.1
  have hexp : K ≤ K * Real.exp (K * m * τ) :=
    le_mul_of_one_le_right hK0 (Real.one_le_exp (by positivity))
  refine ⟨fun j hj2 hjm x => ?_, fun Φ _ hΦ2 j hj2 hjm y => ?_⟩
  · exact (hK T hT le_rfl b (db_of_drift hb) Ψ hΨ.init (fun y => hΨ.eqn y) τ hτ j (by omega) hjm
      x).trans hexp
  · have H := FlowA.hyp_of_drift hT hb
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
    rw [hΦfun]
    exact (hK τ hτ.1 hτ.2 (FlowA.rev τ b) hrev (fun s y => f y s) hf0 hfs τ ⟨hτ.1, le_rfl⟩ j
      (by omega) hjm y).trans hexp

end HRS.MS.FlowC
