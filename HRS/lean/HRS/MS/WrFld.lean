import HRS.MS.WrFldAux1

/-!
# HRS.MS.WrFld -- smallness `KappaSmall` and Wu's inequality for the calibrated reference (WR-12b)

Packet WR-12b of `docs/SUPP_FOUND_PACKETS.md` (track D, T3 NEW part).  Euclidean port of
`HRS/Equilibrium/CalibratedReference.lean:1016 KappaSmall` and `:1019 RefHyp.var_sum_le`, on top of
`weakPotE` and `RN_eq_fieldLaw` of `WrFldAux1`.

Exports (namespace `HRS.MS.Wr`):
* `KappaSmall β γ : Prop` (`4 e^{2βγ+1} βγ ≤ 1/2`), `KappaSmall.mono` (monotone in `β` and in `γ`),
  `exists_kappaSmall` (`∃ δ > 0, ∀ β γ ≥ 0, β γ ≤ δ → KappaSmall β γ`);
* `weakKappa_weakPotE_le`: `KappaSmall β a → weakKappa (weakPotE ..) β ≤ 1/2`;
* `RN_evariance_sum_le`, `RN_var_sum_le` (`A:eq:weak-linear` for `R_N`):
  `Var_{R_N}(∑ f(x_i)) ≤ 2 N Var_π(f)`, `π` the one-point marginal, for bounded measurable `f`
  (the extended-variance form needs only measurability of `f`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External

variable {d : ℕ}

/-- Smallness hypothesis of Wu's inequality for `R_N`: `κ = 4 e^{M+M'+βγ} βγ ≤ 1/2` with `M = βγ + 1`,
`M' = 0` (`CalibratedReference.lean:1016`). -/
def KappaSmall (β γ : ℝ) : Prop := 4 * Real.exp (2 * (β * γ) + 1) * (β * γ) ≤ 1 / 2

/-- `KappaSmall` is monotone in the product `βγ ≥ 0`. -/
lemma KappaSmall.mono {β γ β' γ' : ℝ} (h : KappaSmall β' γ') (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hle : β * γ ≤ β' * γ') : KappaSmall β γ := by
  unfold KappaSmall at *
  have h0 : 0 ≤ β * γ := mul_nonneg hβ hγ
  calc 4 * Real.exp (2 * (β * γ) + 1) * (β * γ)
      ≤ 4 * Real.exp (2 * (β' * γ') + 1) * (β' * γ') := by
        refine mul_le_mul (by gcongr) hle h0 (by positivity)
    _ ≤ 1 / 2 := h

/-- Smallness is available: `βγ ≤ δ` implies `KappaSmall β γ` for a universal `δ > 0`. -/
lemma exists_kappaSmall : ∃ δ : ℝ, 0 < δ ∧ ∀ β γ : ℝ, 0 ≤ β → 0 ≤ γ → β * γ ≤ δ → KappaSmall β γ := by
  refine ⟨min 1 (1 / (16 * Real.exp 3)), lt_min one_pos (by positivity), fun β γ hβ hγ h => ?_⟩
  unfold KappaSmall
  set x := β * γ with hx
  have hx0 : 0 ≤ x := mul_nonneg hβ hγ
  have hx1 : x ≤ 1 := h.trans (min_le_left _ _)
  have hx2 : x ≤ 1 / (16 * Real.exp 3) := h.trans (min_le_right _ _)
  have he : Real.exp (2 * x + 1) ≤ Real.exp 3 := Real.exp_le_exp.2 (by linarith)
  have hpos : 0 < Real.exp 3 := Real.exp_pos _
  calc 4 * Real.exp (2 * x + 1) * x ≤ 4 * Real.exp 3 * (1 / (16 * Real.exp 3)) :=
        mul_le_mul (by linarith) hx2 hx0 (by positivity)
    _ = 1 / 4 := by field_simp; ring
    _ ≤ 1 / 2 := by norm_num

section Wu

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Euc d → Euc d → ℝ}
  {Ψ : Euc d → H} {B β : ℝ} {N : ℕ}

/-- The Dobrushin coefficient of `weakPotE` is at most `1/2` when `KappaSmall β a`. -/
theorem weakKappa_weakPotE_le (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B)
    (t : H) (ht : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β a) :
    weakKappa (weakPotE hK ha hβ h t ht) β ≤ 1 / 2 := by
  have e : weakKappa (weakPotE hK ha hβ h t ht) β = 4 * Real.exp (2 * (β * a) + 1) * (β * a) := by
    unfold weakKappa
    rw [weakPotE_M, weakPotE_M', weakPotE_γ]
    congr 2
    ring
  rw [e]
  exact hκ

/-- **`A:eq:weak-linear` for `R_N` (extended variance)**: `Var_{R_N}(∑_i f(x_i)) ≤ 2N Var_π(f)`, where
`π` is the one-point marginal of `R_N`, for every measurable `f`. -/
theorem RN_evariance_sum_le (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B)
    [NeZero N] (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β a)
    (f : Euc d → ℝ) (hf : Measurable f) :
    evariance (fun X : Fin N → Euc d => ∑ i, f (X i)) (RN q μ Ψ β N)
      ≤ 2 * N * evariance f ((RN q μ Ψ β N).map (fun X => X 0)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hpin := RN_eq_pinnedLaw hK ha hβ h hN ht
  have key := weak_linear_variance_symm (B := Empty) (n := N)
    (weakPotE hK ha hβ h (tN q μ Ψ β N) ht) hβ hN (by simp) (fun e => e.elim)
    (weakKappa_weakPotE_le hK ha hβ h _ ht hκ) f hf
  rw [← hpin] at key
  exact key

/-- **`A:eq:weak-linear` for `R_N`** (real variance, bounded `f`):
`Var_{R_N}(∑_i f(x_i)) ≤ 2 N Var_π(f)` (`CalibratedReference.lean:1019 RefHyp.var_sum_le`). -/
theorem RN_var_sum_le (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B)
    [NeZero N] (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β a)
    (f : Euc d → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    variance (fun X : Fin N → Euc d => ∑ i, f (X i)) (RN q μ Ψ β N) ≤
      2 * N * variance f ((RN q μ Ψ β N).map (fun X => X 0)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : IsProbabilityMeasure (RN q μ Ψ β N) := isProb_RN hK h hβ hN
  have key := RN_evariance_sum_le hK ha hβ h ht hκ f hf
  have hF : Measurable fun X : Fin N → Euc d => ∑ i, f (X i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have hm0 : Measurable (fun X : Fin N → Euc d => X 0) := measurable_pi_apply 0
  have hf2 : MemLp f 2 ((RN q μ Ψ β N).map (fun X => X 0)) :=
    MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hF2 : MemLp (fun X : Fin N → Euc d => ∑ i, f (X i)) 2 (RN q μ Ψ β N) :=
    MemLp.of_bound hF.aestronglyMeasurable (N * C)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        calc |∑ i, f (X i)| ≤ ∑ i, |f (X i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum fun i _ => hC _
          _ = N * C := by simp)
  rw [← ofReal_variance hf2, ← ofReal_variance hF2] at key
  have h0 : 0 ≤ 2 * (N : ℝ) * variance f ((RN q μ Ψ β N).map (fun X => X 0)) :=
    mul_nonneg (by positivity) (variance_nonneg _ _)
  have e : (2 : ℝ≥0∞) * N * ENNReal.ofReal (variance f ((RN q μ Ψ β N).map (fun X => X 0))) =
      ENNReal.ofReal (2 * N * variance f ((RN q μ Ψ β N).map (fun X => X 0))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [e, ENNReal.ofReal_le_ofReal_iff h0] at key
  exact key

end Wu

end HRS.MS.Wr
