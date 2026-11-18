import HRS.MS.LcFlowAux2
import HRS.Whole.Adjoint

/-!
# LC-2, part 1: comparability of `⟨X_v^x⟩` and `⟨x⟩` (statement (i) of `lc_weights`)

With `Λ = lcLam Q Λc ΛB`, `D = lcDrift Q c B g r` (so `lcFlow r v x = Y_{v-r}(x) + lcU r v` with
`Y' = -D(τ,Y)`), the drift `-D` has linear growth `‖D τ z‖ ≤ Λ (1 + ‖z‖)`, so that along a
solution `1 + ‖Y_t‖ ≤ (1 + ‖Y_0‖) e^{Λt}` and, by time reversal, `1 + ‖Y_0‖ ≤ (1 + ‖Y_t‖) e^{Λt}`.
Adding the shift `lcU` (of norm `≤ κ`) gives
`⟨X_v^x⟩ ≤ A (1+κ) ⟨x⟩` and `⟨x⟩ ≤ A (1+κ) ⟨X_v^x⟩`, `A = 2 e^{ΛT}`, for `r ≤ v ≤ T`.

Helper lemmas carry the prefix `lc2_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ}

/-! ### The bracket `⟨x⟩` -/

theorem lc2_jb_ge_one (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 by nlinarith [sq_nonneg ‖x‖])
  simpa using this

theorem lc2_jb_pos (x : Euc d) : 0 < jbracket x := lt_of_lt_of_le one_pos (lc2_jb_ge_one x)

theorem lc2_jb_le (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  unfold jbracket
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg x]

theorem lc2_le_jb (x : Euc d) : 1 + ‖x‖ ≤ 2 * jbracket x := by
  have h0 : 0 ≤ jbracket x := (lc2_jb_pos x).le
  have h2 : jbracket x ^ 2 = 1 + ‖x‖ ^ 2 := by
    unfold jbracket; rw [Real.sq_sqrt (by positivity)]
  have h1 := lc2_jb_ge_one x
  nlinarith [sq_nonneg (1 - ‖x‖), norm_nonneg x]

/-! ### Growth of solutions of `f' = -b(τ, f)` forwards and backwards -/

section Growth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A solution of `f' = -b(τ, f)` with linear growth satisfies `1 + ‖f t‖ ≤ (1 + ‖f 0‖) e^{Λt}`. -/
theorem lc2_sol_growth {T Λ : ℝ} {b : ℝ → E → E} (hΛ : 0 ≤ Λ)
    (hg : ∀ τ ∈ Icc (0 : ℝ) T, ∀ z, ‖b τ z‖ ≤ Λ * (1 + ‖z‖)) {f : ℝ → E}
    (hf : FlowA.Sol T b f) :
    ∀ t ∈ Icc (0 : ℝ) T, 1 + ‖f t‖ ≤ (1 + ‖f 0‖) * Real.exp (Λ * t) := by
  intro t ht
  have hmem : ∀ t ∈ Ico (0 : ℝ) T, Icc (0 : ℝ) T ∈ 𝓝[≥] t := fun t ht =>
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le (f := f)
    (f' := fun t => -(b t (f t))) (δ := ‖f 0‖) (K := Λ) (ε := Λ) (a := 0) (b := T)
    hf.continuousOn
    (fun t ht => (hf t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (hmem t ht)) le_rfl
    (fun t ht => by
      rw [norm_neg]
      refine (hg t ⟨ht.1, ht.2.le⟩ _).trans (le_of_eq ?_)
      ring) t ht
  rw [sub_zero] at hmain
  by_cases hΛ0 : Λ = 0
  · subst hΛ0
    rw [gronwallBound_K0] at hmain
    simp only [zero_mul, add_zero] at hmain
    simp only [zero_mul, Real.exp_zero, mul_one]
    linarith
  · rw [gronwallBound_of_K_ne_0 hΛ0] at hmain
    simp only at hmain
    rw [div_self hΛ0] at hmain
    nlinarith [Real.exp_pos (Λ * t)]

end Growth

/-! ### Comparability along the flow -/

section Comp

variable {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
  {B : ℝ → Euc d → Euc d} {g : ℝ → Euc d}

/-- Forward and backward growth of the random-ODE solution `Y_S = lcZ D x S`. -/
theorem lc2_Y_comp (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    {S : ℝ} (hS : 0 ≤ S) (x : Euc d) :
    1 + ‖lcZ (lcDrift Q c B g r) x S‖ ≤
        (1 + ‖x‖) * Real.exp (lcLam Q Λc ΛB * S) ∧
      1 + ‖x‖ ≤ (1 + ‖lcZ (lcDrift Q c B g r) x S‖) * Real.exp (lcLam Q Λc ΛB * S) := by
  have hdb := lcDrift_isDriftBounds H hg hr S
  have hΛ : 0 ≤ lcLam Q Λc ΛB := H.lam_nonneg
  have hHyp := FlowA.hyp_of_drift hS hdb
  have hsol : FlowA.Sol S (fun τ z => -lcDrift Q c B g r τ z)
      (fun τ => lcZ (lcDrift Q c B g r) x τ) :=
    FlowA.sol_of_flow (lc2_isNegDriftFlow H hg hr hS) x
  have hS' : S ∈ Icc (0 : ℝ) S := ⟨hS, le_rfl⟩
  have h0 : lcZ (lcDrift Q c B g r) x 0 = x := lcZ_zero (lcDrift_isLipschitz H hg hr) x
  refine ⟨?_, ?_⟩
  · have := lc2_sol_growth hΛ hdb.growth hsol S hS'
    rwa [h0] at this
  · have hrev := (hHyp.rev (le_refl S))
    have hsr : FlowA.Sol S (FlowA.rev S (fun τ z => -lcDrift Q c B g r τ z))
        (fun s => lcZ (lcDrift Q c B g r) x (S - s)) := FlowA.Sol.rev hsol
    have := lc2_sol_growth hΛ hrev.growth hsr S hS'
    simp only [sub_self, sub_zero, h0] at this
    rw [mul_comm]
    simpa only [mul_comm] using this

/-- The flow in terms of the random-ODE solution. -/
theorem lc2_flow_eq (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d)
    (g : ℝ → Euc d) (r v : ℝ) (x : Euc d) :
    lcFlow Q c B g r v x = lcZ (lcDrift Q c B g r) x (v - r) + lcU Q g r v := rfl

/-- Comparability of `1 + ‖·‖` along the flow. -/
theorem lc2_flow_comp (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r v κ : ℝ} (hr : 0 ≤ r)
    (hrv : r ≤ v) (hκ : ∀ u ∈ Icc r v, ‖lcU Q g r u‖ ≤ κ) (x : Euc d) :
    1 + ‖lcFlow Q c B g r v x‖ ≤
        (1 + κ) * Real.exp (lcLam Q Λc ΛB * (v - r)) * (1 + ‖x‖) ∧
      1 + ‖x‖ ≤ (1 + κ) * Real.exp (lcLam Q Λc ΛB * (v - r)) * (1 + ‖lcFlow Q c B g r v x‖) := by
  have hS : 0 ≤ v - r := sub_nonneg.2 hrv
  obtain ⟨h1, h2⟩ := lc2_Y_comp H hg hr hS x
  have hU := hκ v ⟨hrv, le_rfl⟩
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans hU
  have hE := Real.exp_pos (lcLam Q Λc ΛB * (v - r))
  set Y := lcZ (lcDrift Q c B g r) x (v - r) with hY
  set E := Real.exp (lcLam Q Λc ΛB * (v - r)) with hEdef
  rw [lc2_flow_eq, ← hY]
  have hn : ‖Y + lcU Q g r v‖ ≤ ‖Y‖ + κ := (norm_add_le _ _).trans (by linarith)
  have hY0 := norm_nonneg Y
  have hx0 := norm_nonneg x
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg H.lam_nonneg hS)
  constructor
  · calc 1 + ‖Y + lcU Q g r v‖ ≤ (1 + κ) * (1 + ‖Y‖) := by nlinarith
      _ ≤ (1 + κ) * ((1 + ‖x‖) * E) := by gcongr
      _ = (1 + κ) * E * (1 + ‖x‖) := by ring
  · calc 1 + ‖x‖ ≤ (1 + ‖Y‖) * E := h2
      _ ≤ (1 + (‖Y + lcU Q g r v‖ + κ)) * E := by
          gcongr
          have : ‖Y‖ ≤ ‖Y + lcU Q g r v‖ + ‖lcU Q g r v‖ := by
            calc ‖Y‖ = ‖(Y + lcU Q g r v) - lcU Q g r v‖ := by rw [add_sub_cancel_right]
              _ ≤ _ := norm_sub_le _ _
          linarith
      _ ≤ (1 + κ) * E * (1 + ‖Y + lcU Q g r v‖) := by
          have hz := norm_nonneg (Y + lcU Q g r v)
          nlinarith [mul_nonneg hκ0 hz, mul_nonneg hκ0 hE.le]

/-- Comparability of the brackets: `⟨X_v^x⟩ ≤ A (1+κ) ⟨x⟩` and `⟨x⟩ ≤ A (1+κ) ⟨X_v^x⟩`,
`A = 2 e^{ΛT}` (any `T ≥ v - r`). -/
theorem lc2_jb_comp (H : LcHyp Q k Λc ΛB c B) (hg : Continuous g) {r v T κ : ℝ} (hr : 0 ≤ r)
    (hrv : r ≤ v) (hvT : v - r ≤ T) (hκ : ∀ u ∈ Icc r v, ‖lcU Q g r u‖ ≤ κ) (x : Euc d) :
    jbracket (lcFlow Q c B g r v x) ≤
        (2 * Real.exp (lcLam Q Λc ΛB * T)) * (1 + κ) * jbracket x ∧
      jbracket x ≤
        (2 * Real.exp (lcLam Q Λc ΛB * T)) * (1 + κ) * jbracket (lcFlow Q c B g r v x) := by
  obtain ⟨h1, h2⟩ := lc2_flow_comp H hg hr hrv hκ x
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ v ⟨hrv, le_rfl⟩)
  have hE : Real.exp (lcLam Q Λc ΛB * (v - r)) ≤ Real.exp (lcLam Q Λc ΛB * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hvT H.lam_nonneg)
  have hE0 := Real.exp_pos (lcLam Q Λc ΛB * (v - r))
  set X := lcFlow Q c B g r v x
  have hk : 0 ≤ (1 + κ) := by linarith
  have hEk : (1 + κ) * Real.exp (lcLam Q Λc ΛB * (v - r)) ≤
      (1 + κ) * Real.exp (lcLam Q Λc ΛB * T) := mul_le_mul_of_nonneg_left hE hk
  have hP : 0 ≤ (1 + κ) * Real.exp (lcLam Q Λc ΛB * (v - r)) := by positivity
  constructor
  · calc jbracket X ≤ 1 + ‖X‖ := lc2_jb_le X
      _ ≤ (1 + κ) * Real.exp (lcLam Q Λc ΛB * (v - r)) * (1 + ‖x‖) := h1
      _ ≤ (1 + κ) * Real.exp (lcLam Q Λc ΛB * (v - r)) * (2 * jbracket x) := by
          gcongr; exact lc2_le_jb x
      _ ≤ (1 + κ) * Real.exp (lcLam Q Λc ΛB * T) * (2 * jbracket x) := by
          gcongr; linarith [lc2_jb_pos x]
      _ = (2 * Real.exp (lcLam Q Λc ΛB * T)) * (1 + κ) * jbracket x := by ring
  · calc jbracket x ≤ 1 + ‖x‖ := lc2_jb_le x
      _ ≤ (1 + κ) * Real.exp (lcLam Q Λc ΛB * (v - r)) * (1 + ‖X‖) := h2
      _ ≤ (1 + κ) * Real.exp (lcLam Q Λc ΛB * (v - r)) * (2 * jbracket X) := by
          gcongr; exact lc2_le_jb X
      _ ≤ (1 + κ) * Real.exp (lcLam Q Λc ΛB * T) * (2 * jbracket X) := by
          gcongr; linarith [lc2_jb_pos X]
      _ = (2 * Real.exp (lcLam Q Λc ΛB * T)) * (1 + κ) * jbracket X := by ring

end Comp

end HRS.MS.Lc
