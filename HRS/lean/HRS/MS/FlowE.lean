import HRS.MS.FlowC
import HRS.MS.FlowD
import HRS.MS.FlowEAux1

/-!
# MS-FLOW-E: conjuncts (i) and (ii) of Lemma S.A.32 (`uloc_bilip`)

`uloc_bilip_i_ii` has the hypotheses of `uloc_bilip` and, as conclusion, the existence of the flow together with
conjuncts (i), (ii) copied verbatim (so that the final assembly is an `And` combination).  Route and constants:
`FlowEPlan.md`.
-/

open Set MeasureTheory
open scoped ENNReal ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.FlowE

variable {d : ℕ}

theorem uloc_bilip_i_ii (m : ℕ) (T Λ : ℝ) (hT : 0 < T) (χ χh : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (hχh : IsCutoffRad 6 8 χh) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ → Euc d → Euc d, IsDriftBounds T m Λ b →
      (∃ Ψ, IsNegDriftFlow T b Ψ) ∧
      ∀ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T b Ψ →
        ∃ Ψinv : ℝ → Euc d → Euc d, ∀ τ ∈ Set.Icc (0 : ℝ) T,
          -- (i)
          ((∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y) ∧
            ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψ τ) ∧
            ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψinv τ) ∧
            (∀ x, ‖fderiv ℝ (Ψ τ) x‖ ≤ Real.exp (C * τ)) ∧
            (∀ y, ‖fderiv ℝ (Ψinv τ) y‖ ≤ Real.exp (C * τ)) ∧
            ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
              ‖iteratedFDeriv ℝ j (Ψ τ) x‖ ≤ C * Real.exp (C * m * τ) ∧
              ‖iteratedFDeriv ℝ j (Ψinv τ) x‖ ≤ C * Real.exp (C * m * τ)) ∧
          -- (ii)
          (∀ z : Euc d, (∀ x, HasDerivWithinAt (fun τ' => χ (Ψinv τ' x - z))
              (inner ℝ (b τ x) (gradient (fun y => χ (Ψinv τ y - z)) x)) (Set.Icc (0 : ℝ) T) τ) ∧
            MemCb (m + 1) (fun x => χ (Ψinv τ x - z)) ∧
            cbNorm (m + 1) (fun x => χ (Ψinv τ x - z)) ≤ C * Real.exp (C * m * τ)) := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := FlowC.flow_iter_bound d m T Λ hT.le
  obtain ⟨K, hK0, hK⟩ := cb_comp_bound m χ hχ.1 hχ.2.1
  obtain ⟨D, hD1, hD2, hD3⟩ : ∃ D : ℝ, 1 ≤ D ∧ Real.exp (Λ * T) ≤ D ∧
      C₀ * Real.exp (C₀ * m * T) ≤ D :=
    ⟨max 1 (max (Real.exp (Λ * T)) (C₀ * Real.exp (C₀ * m * T))), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨C, hC1, hC2, hC3⟩ : ∃ C : ℝ, C₀ ≤ C ∧ Λ ≤ C ∧ K * D ^ (m + 1) ≤ C :=
    ⟨max (max C₀ Λ) (K * D ^ (m + 1)), (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  have hC0 : 0 < C := lt_of_lt_of_le hC₀ hC1
  refine ⟨C, hC0, fun b hb => ⟨FlowA.flow_exists hT.le hb, fun Ψ hΨ => ?_⟩⟩
  classical
  have hinvex := FlowA.flow_invertible hT.le hb hΨ
  let Ψinv : ℝ → Euc d → Euc d :=
    fun τ => if h : τ ∈ Icc (0 : ℝ) T then Classical.choose (hinvex τ h) else id
  have hinv : ∀ τ ∈ Icc (0 : ℝ) T,
      (∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y) := by
    intro τ hτ
    have := Classical.choose_spec (hinvex τ hτ)
    simp only [Ψinv, dif_pos hτ]
    exact ⟨this.1, this.2.1⟩
  refine ⟨Ψinv, fun τ hτ => ?_⟩
  have hΛ := FlowD.Λ_nonneg' hT.le hb
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  obtain ⟨hiter1, hiter2⟩ := hC₀b b hb Ψ hΨ τ hτ
  have hinvC := FlowB.flow_inv_contDiff hT.le hb hΨ τ hτ (Ψinv τ) (hinv τ hτ).1 (hinv τ hτ).2
  have hiterinv := hiter2 (Ψinv τ) (hinv τ hτ).1 (hinv τ hτ).2
  have hmτ : (0 : ℝ) ≤ m * τ := by positivity
  have hexpC : C₀ * Real.exp (C₀ * m * τ) ≤ C * Real.exp (C * m * τ) :=
    mul_le_mul hC1 (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le hC0.le
  have hexpL : Real.exp (Λ * τ) ≤ Real.exp (C * τ) := Real.exp_le_exp.2 (by nlinarith)
  refine ⟨⟨(hinv τ hτ).1, (hinv τ hτ).2, FlowB.flow_contDiff hT.le hb hΨ τ hτ, hinvC.1,
    fun x => (FlowB.flow_fderiv_bound hT.le hb hΨ τ hτ x).trans hexpL,
    fun y => (hinvC.2 y).trans hexpL,
    fun j hj2 hjm x => ⟨(hiter1 j hj2 hjm x).trans hexpC, (hiterinv j hj2 hjm x).trans hexpC⟩⟩, ?_⟩
  intro z
  refine ⟨fun x => FlowD.flow_cutoff_hasDerivWithinAt hT.le hb hΨ Ψinv hinv χ hχ.1 z x τ hτ, ?_⟩
  have hDder : ∀ x : Euc d, ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 → ‖iteratedFDeriv ℝ i (Ψinv τ) x‖ ≤ D := by
    intro x i h1 h2
    by_cases hi : i = 1
    · subst hi
      rw [norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact (hinvC.2 x).trans ((Real.exp_le_exp.2 (by nlinarith)).trans hD2)
    · refine (hiterinv i (by omega) h2 x).trans ?_
      refine le_trans ?_ hD3
      have : C₀ * m * τ ≤ C₀ * m * T := by
        have : (0 : ℝ) ≤ C₀ * m := by positivity
        exact mul_le_mul_of_nonneg_left hτT this
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) hC₀.le
  obtain ⟨hmem, hcb⟩ := hK D hD1 (Ψinv τ) hinvC.1 hDder z
  refine ⟨hmem, hcb.trans ?_⟩
  exact hC3.trans (le_mul_of_one_le_right hC0.le (Real.one_le_exp (by positivity)))

end HRS.MS.FlowE
