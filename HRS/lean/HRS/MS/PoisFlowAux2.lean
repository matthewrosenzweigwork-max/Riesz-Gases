import HRS.MS.PoisFlowAux1

/-!
# POIS-FLOW, part 2: regularity of the pathwise flow in `x`, uniform in the noise path

Main theorem `HRS.MS.PoisFlow.pois_flow` (supplement foundation packet POIS-FLOW).  For `q > 0`,
`2 ≤ m`, `T ≥ 0` there is `C > 0`, depending only on `(d, q, Mb, m, T)`, such that for every
`B` with `HasCbBound m Mb B` and every continuous noise path `w` with `w 0 = 0`:

* for every `x`, `t ↦ flowMap q B w t x` is a pathwise solution of
  `X_t = x + ∫_0^t (-q X_s + B X_s) ds + ∑_k w^k_t σ_k` on `[0, ∞)` (`σ k = √2 e_k`), and
* for `t ∈ [0, T]`, `flowMap q B w t` is `C^m` with `‖D^j flowMap q B w t‖ ≤ C` for `1 ≤ j ≤ m`.

Route.  `Z_t(x) = pfZ q B w x t` is the flow of the field `b^τ(z) = -pfDrift τ z = q z - B(z + √2 U_τ)`,
which satisfies `IsDriftBounds T (m-1) Λ b` with `Λ = q + |Mb|` independently of `w`
(`‖b^τ z‖ ≤ q‖z‖ + Mb`, `‖D b^τ‖ ≤ q + Mb`, `‖D^j b^τ‖ ≤ Mb`, `j ≥ 2`), so `FlowB.flow_contDiff`,
`FlowB.flow_fderiv_bound` and `FlowC.flow_iter_bound` (constant depending only on `d, m-1, T, Λ`)
apply; `flowMap t = Z_t + (const in x)` has the same derivatives of order `≥ 1`.

Statement adjustments relative to the packet sketch: the hypothesis `1 ≤ d` is not needed and is
omitted (for `d = 0` everything is trivially true); `q`, `Mb` are explicit real arguments; the
noise directions are `pfSigma d`, and `ouShift`, `flowMap` read the noise path `w : ℝ≥0 → Fin d → ℝ`
as the vector `toLp 2 (w t)`.  Helper lemmas carry the prefix `pf_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

namespace HRS.MS.PoisFlow

variable {d : ℕ}

theorem pf_iter_add_const {f : Euc d → Euc d} (c : Euc d) {k : ℕ} (hf : ContDiff ℝ (k : WithTop ℕ∞) f)
    {j : ℕ} (hj0 : j ≠ 0) (hjk : j ≤ k) (x : Euc d) :
    iteratedFDeriv ℝ j (fun y => f y + c) x = iteratedFDeriv ℝ j f x := by
  have hf' : ContDiffAt ℝ (j : WithTop ℕ∞) f x :=
    (hf.of_le (by exact_mod_cast hjk)).contDiffAt
  have e : (fun y => f y + c) = f + fun _ => c := rfl
  rw [e, iteratedFDeriv_add_apply hf' contDiffAt_const, iteratedFDeriv_const_of_ne hj0]
  simp

theorem pf_iter_clm_zero (L : Euc d →L[ℝ] Euc d) {j : ℕ} (hj : 2 ≤ j) (x : Euc d) :
    iteratedFDeriv ℝ j (fun z => L z) x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp
  rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
  rfl

/-- Derivative bounds of the field `z ↦ q z - B(z + v)`. -/
theorem pf_deriv_bound {q Mb : ℝ} (hq : 0 ≤ q) {n : ℕ} {B : Euc d → Euc d}
    (hB : HasCbBound (n + 1) Mb B) (v : Euc d) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ n + 1)
    (x : Euc d) : ‖iteratedFDeriv ℝ j (fun z => q • z - B (z + v)) x‖ ≤ q + |Mb| := by
  have hshift : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun z : Euc d => B (z + v)) :=
    hB.1.comp (contDiff_id.add contDiff_const)
  have hBj : ContDiffAt ℝ (j : WithTop ℕ∞) (fun z : Euc d => B (z + v)) x :=
    (hshift.of_le (by exact_mod_cast hj2)).contDiffAt
  have hLj : ContDiffAt ℝ (j : WithTop ℕ∞) (fun z : Euc d => q • z) x :=
    (contDiff_id.const_smul q).contDiffAt
  have e0 : (fun z : Euc d => q • z - B (z + v)) = (fun z : Euc d => q • z) - fun z => B (z + v) :=
    rfl
  rw [e0, iteratedFDeriv_sub_apply hLj hBj, iteratedFDeriv_comp_add_right]
  refine (norm_sub_le _ _).trans ?_
  have h2 : ‖iteratedFDeriv ℝ j B (x + v)‖ ≤ |Mb| :=
    (hB.2 j hj2 _).trans (le_abs_self _)
  by_cases hj : j = 1
  · subst hj
    have h1 : ‖iteratedFDeriv ℝ 1 (fun z : Euc d => q • z) x‖ ≤ q := by
      rw [norm_iteratedFDeriv_one]
      have e : fderiv ℝ (fun z : Euc d => q • z) x = q • ContinuousLinearMap.id ℝ (Euc d) :=
        ((hasFDerivAt_id x).const_smul q).fderiv
      rw [e]
      refine (norm_smul _ _).le.trans ?_
      rw [Real.norm_of_nonneg hq]
      calc q * ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ q * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hq
        _ = q := mul_one q
    linarith
  · have e : iteratedFDeriv ℝ j (fun z : Euc d => q • z) x = 0 :=
      pf_iter_clm_zero (q • ContinuousLinearMap.id ℝ (Euc d)) (by omega) x
    rw [e, norm_zero]
    linarith [abs_nonneg Mb]

/-- The negated drift satisfies the drift bounds `IsDriftBounds` of order `n` with `Λ = q + |Mb|`,
for every continuous noise path. -/
theorem pf_isDriftBounds {q Mb : ℝ} {n : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb (n + 1) B w) (T : ℝ) :
    IsDriftBounds T n (q + |Mb|) (fun τ z => -pfDrift q B w τ z) where
  cont := (pf_continuous_drift H.hB.1.continuous H.hw).neg.continuousOn
  smooth τ _ := by
    have h : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞)
        (fun z : Euc d => q • z - B (z + Real.sqrt 2 • ouShift q w τ)) :=
      (contDiff_id.const_smul q).sub (H.hB.1.comp (contDiff_id.add contDiff_const))
    convert h using 2 with z
    simp only [pfDrift, neg_add, neg_smul, neg_neg, sub_eq_add_neg]
  deriv_bound τ _ j hj1 hj2 x := by
    have e : (fun z : Euc d => -pfDrift q B w τ z) =
        fun z => q • z - B (z + Real.sqrt 2 • ouShift q w τ) := by
      funext z; simp only [pfDrift, neg_add, neg_smul, neg_neg, sub_eq_add_neg]
    rw [e]
    exact pf_deriv_bound H.hq H.hB _ hj1 hj2 x
  growth τ _ z := by
    have hB0 : ‖B (z + Real.sqrt 2 • ouShift q w τ)‖ ≤ |Mb| := by
      have := H.hB.2 0 (Nat.zero_le _) (z + Real.sqrt 2 • ouShift q w τ)
      rw [norm_iteratedFDeriv_zero] at this
      exact this.trans (le_abs_self _)
    have hq := H.hq
    calc ‖-pfDrift q B w τ z‖ = ‖-q • z + B (z + Real.sqrt 2 • ouShift q w τ)‖ := by
          rw [norm_neg]; rfl
      _ ≤ ‖-q • z‖ + ‖B (z + Real.sqrt 2 • ouShift q w τ)‖ := norm_add_le _ _
      _ ≤ q * ‖z‖ + |Mb| := by
          rw [norm_smul, norm_neg, Real.norm_of_nonneg hq]; linarith
      _ ≤ (q + |Mb|) * (1 + ‖z‖) := by
          nlinarith [abs_nonneg Mb, norm_nonneg z, mul_nonneg (abs_nonneg Mb) (norm_nonneg z)]

/-- **POIS-FLOW.**  The pathwise flow `flowMap` solves `X_t = x + ∫_0^t (-q X + B X) + ∑_k w^k_t σ_k`
(`σ k = √2 e_k`) on `[0, ∞)`, is `C^m` in `x`, and has derivatives of order `1 ≤ j ≤ m` bounded by a
constant `C` depending only on `(d, q, Mb, m, T)`, uniformly in the continuous noise path `w`,
`w 0 = 0`, and in `B` with `HasCbBound m Mb B`. -/
theorem pois_flow (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ w : ℝ≥0 → Fin d → ℝ, Continuous w → w 0 = 0 →
        (∀ x : Euc d, IsPathSolution (fun _ y => -q • y + B y) (pfSigma d) w x ⊤
          (fun t => flowMap q B w t x)) ∧
        ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ (m : WithTop ℕ∞) (flowMap q B w t) ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x : Euc d, ‖iteratedFDeriv ℝ j (flowMap q B w t) x‖ ≤ C := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨C0, hC0, hC0b⟩ := FlowC.flow_iter_bound d n T (q + |Mb|) hT
  have hΛ : 0 ≤ q + |Mb| := by positivity
  refine ⟨max (Real.exp ((q + |Mb|) * T)) (C0 * Real.exp (C0 * n * T)),
    lt_max_of_lt_left (Real.exp_pos _), fun B hB w hw hw0 => ?_⟩
  have H : PfHyp q Mb (n + 1) B w := ⟨hq.le, by omega, hB, hw, hw0⟩
  refine ⟨pf_flowMap_isPathSolution H, fun t ht => ?_⟩
  have hb := pf_isDriftBounds H T
  have hΨ := pf_isNegDriftFlow H hT
  have hcd : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun x => pfZ q B w x t) :=
    FlowB.flow_contDiff hT hb hΨ t ht
  have hfm : flowMap q B w t = fun x => pfZ q B w x t + Real.sqrt 2 • ouShift q w t := rfl
  refine ⟨?_, fun j hj1 hjm x => ?_⟩
  · rw [hfm]; exact hcd.add contDiff_const
  · rw [hfm, pf_iter_add_const _ hcd (by omega) hjm x]
    by_cases hj : j = 1
    · subst hj
      rw [norm_iteratedFDeriv_one]
      have := FlowB.flow_fderiv_bound hT hb hΨ t ht x
      refine this.trans ((Real.exp_le_exp.2 ?_).trans (le_max_left _ _))
      exact mul_le_mul_of_nonneg_left ht.2 hΛ
    · have := (hC0b _ hb _ hΨ t ht).1 j (by omega) hjm x
      refine this.trans ((?_ : _ ≤ C0 * Real.exp (C0 * n * T)).trans (le_max_right _ _))
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0.le
      exact mul_le_mul_of_nonneg_left ht.2 (by positivity)

end HRS.MS.PoisFlow
