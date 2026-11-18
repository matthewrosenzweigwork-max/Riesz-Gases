import HRS.MS.WrPoleAux1

/-!
# HRS.MS.WrPoleAux2 -- pole variance, part 2: marginals, second moment, `P ≤ C R^{x,t}` (WR-13b)

Packet WR-13b (T8 of `docs/WR_B_PLAN.md`), namespace `HRS.MS.Wr`, helper prefix `wr13b_`.
Euclidean port of `HRS/Equilibrium/PoleVariance.lean:748-1175` (`marginal_tv_le`, `mean_norm_le`,
`Esq_le`, `pole_le_Rpole`, `pole_evariance_le`) for a separable real Hilbert feature space `H`.

Standing hypotheses: `h : TransferHyp μ a q k g Ψ` (weak kernel `q(x-y)`, Gram kernel `k`, `g = q + k` off the
origin, `μ` atomless), `0 < β`, the smallness `|⟪t_{n+1}, Ξ⟫| ≤ 1` (`ht`) and `wr11b_KappaSmall β a` (`hκ`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External

section Marg

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q k g : Euc d → ℝ} {Ψ : Euc d → H}
  (h : TransferHyp μ a q k g Ψ) {β : ℝ} (hβ : 0 < β)

include h hβ in
theorem wr13b_weakKappa_Vp_le (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : wr11b_KappaSmall β a) : weakKappa (wr13b_Vp h hβ n ht) β ≤ 1 / 2 :=
  weakKappa_weakPotE_le h.weak h.a_nonneg hβ.le h.calFeat _ ht hκ

include h hβ in
theorem wr13b_RN_eq_pinned (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) :
    RN (wr11b_dk q) μ Ψ β (n + 1) =
      pinnedLaw (wr13b_Vp h hβ n ht) (wr13b_lamN β n) (n + 1) (fun e : Empty => e.elim) :=
  RN_eq_pinnedLaw h.weak h.a_nonneg hβ.le h.calFeat (Nat.succ_pos n) ht

include h hβ in
/-- The marginals of the weak reference with the pole are within `3κ/(n+1)` (total variation) of
the marginals of the calibrated reference `R_{n+1}`. -/
theorem wr13b_marginal_tv_le (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : wr11b_KappaSmall β a) (x : Euc d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin n) :
    HRS.External.Entropy.tvDist ((wr13b_Rpole h hβ n ht x t).map (fun y => y i))
      ((RN (wr11b_dk q) μ Ψ β (n + 1)).map (fun X => X ((0 : Fin (n + 1)).succAbove i)))
      ≤ 3 * weakKappa (wr13b_Vp h hβ n ht) β / ((n : ℝ) + 1) := by
  have hκ' := wr13b_weakKappa_Vp_le h hβ n ht hκ
  have : Nonempty {A : Set (Euc d) // MeasurableSet A} := ⟨⟨∅, MeasurableSet.empty⟩⟩
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hlam : wr13b_lamN β n = β / ((n + 1 : ℕ) : ℝ) := rfl
  unfold HRS.External.Entropy.tvDist
  refine ciSup_le fun A => ?_
  have h1 := HRS.External.PoleVar.pin_pole_event (wr13b_Vp h hβ n ht) hβ.le (N := n + 1) (n := n)
    (Nat.succ_pos n) le_rfl hκ' x ht0 ht1 i A.2
  have h2 := rvh_pin_comparison (wr13b_Vp h hβ n ht) hβ.le (N := n + 1) (n := n) (Nat.succ_pos n)
    (by simp) (fun e : Empty => e.elim) hκ' 0 i x A.2
  rw [wr13b_RN_eq_pinned h hβ n ht]
  unfold wr13b_Rpole
  rw [hlam]
  have h3 := abs_sub_le (((fieldLaw (wr13b_Vp h hβ n ht)
      (HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) t x)
      (β / ((n + 1 : ℕ) : ℝ)) n).map (fun y => y i)).real A.1)
    (((pinnedLaw (wr13b_Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun y => y i)).real A.1)
    (((pinnedLaw (wr13b_Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) (n + 1)
      (fun e : Empty => e.elim)).map (fun y => y ((0 : Fin (n + 1)).succAbove i))).real A.1)
  rw [abs_sub_comm (((fieldLaw (wr13b_Vp h hβ n ht)
      (HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) t x)
      (β / ((n + 1 : ℕ) : ℝ)) n).map (fun y => y i)).real A.1)
    (((pinnedLaw (wr13b_Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun y => y i)).real A.1)] at h3
  have hk : 3 * weakKappa (wr13b_Vp h hβ n ht) β / ((n : ℝ) + 1)
      = weakKappa (wr13b_Vp h hβ n ht) β / ((n + 1 : ℕ) : ℝ)
        + 2 * weakKappa (wr13b_Vp h hβ n ht) β / ((n + 1 : ℕ) : ℝ) := by
    rw [hcast]; ring
  rw [hk]
  linarith

include h hβ in
theorem wr13b_Xibar_mul (n : ℕ) :
    ((n : ℝ) + 1) • Xibar (wr11b_dk q) μ Ψ β (n + 1)
      = ∑ j : Fin (n + 1), ∫ X, Xi μ Ψ (X j) ∂(RN (wr11b_dk q) μ Ψ β (n + 1)) := by
  have := isProb_RN h.weak h.calFeat hβ.le (Nat.succ_pos n)
  unfold Xibar empXi
  rw [integral_smul, smul_smul]
  have hint : ∀ j : Fin (n + 1), Integrable (fun X : Fin (n + 1) → Euc d => Xi μ Ψ (X j))
      (RN (wr11b_dk q) μ Ψ β (n + 1)) := fun j =>
    Integrable.of_bound ((h.calFeat.continuous_Xi.comp (continuous_apply j)).aestronglyMeasurable)
      (2 * Real.sqrt (k 0)) (Filter.Eventually.of_forall fun X => h.calFeat.norm_Xi_le _)
  rw [integral_finsetSum _ fun j _ => hint j]
  have : ((n : ℝ) + 1) * (1 / (((n + 1 : ℕ) : ℝ))) = 1 := by
    push_cast
    field_simp
  rw [this, one_smul]

include h hβ in
/-- **Mean comparison** (the pole and the pin only move the mean statistic by `O(1)`). -/
theorem wr13b_mean_norm_le (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : wr11b_KappaSmall β a) (x : Euc d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖∫ y, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar (wr11b_dk q) μ Ψ β (n + 1)))
        ∂(wr13b_Rpole h hβ n ht x t)‖ ≤ 10 * Real.sqrt (k 0) := by
  have := wr13b_isProb_Rpole h hβ n ht x ht0 ht1
  have := isProb_RN h.weak h.calFeat hβ.le (Nat.succ_pos n)
  set ν := wr13b_Rpole h hβ n ht x t with hν
  set ρN := RN (wr11b_dk q) μ Ψ β (n + 1) with hρN
  set r := Real.sqrt (k 0) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hκ' := wr13b_weakKappa_Vp_le h hβ n ht hκ
  have hκ0 := weakKappa_nonneg (wr13b_Vp h hβ n ht) hβ.le
  set κ := weakKappa (wr13b_Vp h hβ n ht) β with hκdef
  have hXm := h.calFeat.continuous_Xi (μ := μ)
  have hXb : ∀ z, ‖Xi μ Ψ z‖ ≤ 2 * r := fun z => h.calFeat.norm_Xi_le z
  have hint : ∀ i : Fin n, Integrable (fun y : Fin n → Euc d => Xi μ Ψ (y i)) ν := fun i =>
    Integrable.of_bound (hXm.comp (continuous_apply i)).aestronglyMeasurable (2 * r)
      (Filter.Eventually.of_forall fun y => hXb _)
  have hintN : ∀ j : Fin (n + 1), Integrable (fun X : Fin (n + 1) → Euc d => Xi μ Ψ (X j)) ρN :=
    fun j => Integrable.of_bound (hXm.comp (continuous_apply j)).aestronglyMeasurable (2 * r)
      (Filter.Eventually.of_forall fun y => hXb _)
  have hmean : ∫ y, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar (wr11b_dk q) μ Ψ β (n + 1))) ∂ν
      = ∑ i : Fin n, (∫ y, Xi μ Ψ (y i) ∂ν
          - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN)
        + (Xi μ Ψ x - ∫ X, Xi μ Ψ (X 0) ∂ρN) := by
    have e1 : ∫ y, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar (wr11b_dk q) μ Ψ β (n + 1))) ∂ν
        = ∑ i, ∫ y, Xi μ Ψ (y i) ∂ν
          + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar (wr11b_dk q) μ Ψ β (n + 1)) := by
      rw [integral_add (integrable_finsetSum _ fun i _ => hint i) (integrable_const _),
        integral_finsetSum _ fun i _ => hint i]
      simp
    rw [e1, wr13b_Xibar_mul h hβ n, Fin.sum_univ_succAbove _ (0 : Fin (n + 1)), Finset.sum_sub_distrib]
    abel
  rw [hmean]
  have hcalXi : CalFeat (Xi μ Ψ) (2 * r) := ⟨hXm, hXb⟩
  have hcoord : ∀ i : Fin n, ‖∫ y, Xi μ Ψ (y i) ∂ν
      - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN‖ ≤ 2 * (2 * r) * (3 * κ / ((n : ℝ) + 1)) := by
    intro i
    have htv := wr13b_marginal_tv_le h hβ n ht hκ x ht0 ht1 i
    have hnorm := wr12_norm_integral_sub_le (ν.map (fun y : Fin n → Euc d => y i))
      (ρN.map (fun X : Fin (n + 1) → Euc d => X ((0 : Fin (n + 1)).succAbove i))) hcalXi
    rw [integral_map (measurable_pi_apply i).aemeasurable hXm.aestronglyMeasurable,
      integral_map (measurable_pi_apply ((0 : Fin (n + 1)).succAbove i)).aemeasurable
        hXm.aestronglyMeasurable] at hnorm
    refine hnorm.trans ?_
    exact mul_le_mul_of_nonneg_left htv (by positivity)
  have hsum : ‖∑ i : Fin n, (∫ y, Xi μ Ψ (y i) ∂ν
      - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN)‖ ≤ 6 * r := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin n, ‖∫ y, Xi μ Ψ (y i) ∂ν
          - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN‖
        ≤ ∑ _i : Fin n, 2 * (2 * r) * (3 * κ / ((n : ℝ) + 1)) := Finset.sum_le_sum fun i _ => hcoord i
      _ = n * (2 * (2 * r) * (3 * κ / ((n : ℝ) + 1))) := by simp
      _ ≤ 6 * r := by
          have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have : (n : ℝ) * (2 * (2 * r) * (3 * κ / ((n : ℝ) + 1)))
              = (12 * r * κ) * ((n : ℝ) / ((n : ℝ) + 1)) := by
            field_simp
            ring
          rw [this]
          have h1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
            rw [div_le_one hn1]; linarith
          have h2 : 0 ≤ 12 * r * κ := by positivity
          nlinarith
  have hrest : ‖Xi μ Ψ x - ∫ X, Xi μ Ψ (X 0) ∂ρN‖ ≤ 4 * r := by
    refine (norm_sub_le _ _).trans ?_
    have : ‖∫ X, Xi μ Ψ (X 0) ∂ρN‖ ≤ 2 * r := by
      have := norm_integral_le_of_norm_le_const (μ := ρN) (f := fun X : Fin (n + 1) → Euc d => Xi μ Ψ (X 0))
        (C := 2 * r) (Filter.Eventually.of_forall fun X => hXb _)
      simpa using this
    linarith [hXb x]
  calc _ ≤ ‖∑ i : Fin n, (∫ y, Xi μ Ψ (y i) ∂ν
      - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN)‖
      + ‖Xi μ Ψ x - ∫ X, Xi μ Ψ (X 0) ∂ρN‖ := norm_add_le _ _
    _ ≤ 10 * r := by linarith

theorem wr13b_Wv_eq {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure (Euc d)) (Ψ : Euc d → H) (n : ℕ) (x : Euc d) (Xb : H) (y : Fin n → Euc d) :
    ∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)
      = ∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xb) := by
  simp only [Xi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  module

include h hβ in
/-- The Wu data of the weak reference with the pole: `Λ`-bound and row sums. -/
theorem wr13b_wu_data (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : wr11b_KappaSmall β a) :
    (wr13b_Vp h hβ n ht).M' + wr13b_lamN β n * (wr13b_Vp h hβ n ht).γ
        + wr13b_lamN β n * n * (wr13b_Vp h hβ n ht).γ
      ≤ (wr13b_Vp h hβ n ht).M' + β * (wr13b_Vp h hβ n ht).γ ∧
    ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i,
      4 * Real.exp ((wr13b_Vp h hβ n ht).M + ((wr13b_Vp h hβ n ht).M' + β * (wr13b_Vp h hβ n ht).γ))
        * wr13b_lamN β n * (wr13b_Vp h hβ n ht).γ ≤ 1 / 2 := by
  have hκ' := wr13b_weakKappa_Vp_le h hβ n ht hκ
  have hmul : wr13b_lamN β n * ((n : ℝ) + 1) = β := (wr13b_lamN_mul (β := β) n).symm
  have hlam : wr13b_lamN β n = β / ((n + 1 : ℕ) : ℝ) := rfl
  refine ⟨le_of_eq ?_, fun i => ?_⟩
  · calc (wr13b_Vp h hβ n ht).M' + wr13b_lamN β n * (wr13b_Vp h hβ n ht).γ
          + wr13b_lamN β n * n * (wr13b_Vp h hβ n ht).γ
        = (wr13b_Vp h hβ n ht).M' + (wr13b_lamN β n * ((n : ℝ) + 1)) * (wr13b_Vp h hβ n ht).γ := by ring
      _ = _ := by rw [hmul]
  · rw [hlam, four_exp_eq]
    exact (row_sum_le_of_uniform (Nat.succ_pos n) (Nat.le_succ n)
      (weakKappa_nonneg (wr13b_Vp h hβ n ht) hβ.le) i).trans hκ'

include h hβ in
/-- **Second moment** `E_R |S + Ψ x - (n+1)(m + Ξ̄)|² ≤ 100 (n+1) k(0)`. -/
theorem wr13b_Esq_le (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : wr11b_KappaSmall β a) (x : Euc d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ y, ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) •
        (∫ w, Ψ w ∂μ + Xibar (wr11b_dk q) μ Ψ β (n + 1))‖ ^ 2 ∂(wr13b_Rpole h hβ n ht x t)
      ≤ 100 * ((n : ℝ) + 1) * k 0 := by
  have : NeZero n := ⟨by omega⟩
  have := wr13b_isProb_Rpole h hβ n ht x ht0 ht1
  have hlam0 := wr13b_lamN_nonneg hβ n
  have hψ := HRS.External.PoleVar.isField_psiPole (wr13b_Vp h hβ n ht) hlam0 ht0 ht1 x
  obtain ⟨hΛ, hrow⟩ := wr13b_wu_data h hβ n ht hκ
  have hmain := wr13b_field_second_moment_H (V := wr13b_Vp h hβ n ht) hψ hlam0
    (Λ := (wr13b_Vp h hβ n ht).M' + β * (wr13b_Vp h hβ n ht).γ)
    (by simpa using hΛ) hrow h.feat.continuous (r := Real.sqrt (k 0)) (fun z => (h.feat.norm_eq z).le)
    (Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar (wr11b_dk q) μ Ψ β (n + 1)))
  have hg0 := h.feat.k_zero_nonneg
  have hr2 : Real.sqrt (k 0) ^ 2 = k 0 := Real.sq_sqrt hg0
  have e1 : ∀ y : Fin n → Euc d, ∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar (wr11b_dk q) μ Ψ β (n + 1))
      = ∑ i, Ψ (y i) + (Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar (wr11b_dk q) μ Ψ β (n + 1))) :=
    fun y => by abel
  have e2 : ∀ y : Fin n → Euc d, ∑ i, Ψ (y i) + (Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar (wr11b_dk q) μ Ψ β (n + 1)))
      = ∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar (wr11b_dk q) μ Ψ β (n + 1)) :=
    fun y => by rw [← e1, wr13b_Wv_eq]
  simp_rw [e2] at hmain
  have hmain' : ∫ y : Fin n → Euc d, ‖∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar (wr11b_dk q) μ Ψ β (n + 1))‖ ^ 2
        ∂(wr13b_Rpole h hβ n ht x t)
      ≤ 2 * n * ∫ y : Fin n → Euc d, ‖Ψ (y 0)‖ ^ 2 ∂(wr13b_Rpole h hβ n ht x t)
        + ‖∫ y : Fin n → Euc d, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar (wr11b_dk q) μ Ψ β (n + 1)))
            ∂(wr13b_Rpole h hβ n ht x t)‖ ^ 2 := hmain
  have e3 : ∫ y : Fin n → Euc d, ‖Ψ (y 0)‖ ^ 2 ∂(wr13b_Rpole h hβ n ht x t) = k 0 := by
    have : ∀ y : Fin n → Euc d, ‖Ψ (y 0)‖ ^ 2 = k 0 := fun y => h.feat.norm_sq (y 0)
    simp_rw [this]
    simp
  rw [e3] at hmain'
  have hmean := wr13b_mean_norm_le h hβ n ht hκ x ht0 ht1
  have hsq : ‖∫ y : Fin n → Euc d, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar (wr11b_dk q) μ Ψ β (n + 1)))
        ∂(wr13b_Rpole h hβ n ht x t)‖ ^ 2 ≤ 100 * k 0 := by
    calc _ ≤ (10 * Real.sqrt (k 0)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmean 2
      _ = 100 * k 0 := by rw [mul_pow, hr2]; ring
  simp_rw [e1, e2]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn0 hg0]

include h hβ in
/-- **Density bound for the pole law** (`A:eq:bounded-transfer` with the pole present):
`P ≤ e^{52 β k(0)} R^{x,t}`. -/
theorem wr13b_pole_le_Rpole (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : wr11b_KappaSmall β a) (x : Euc d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Measure.pi fun _ : Fin n => μ).tilted
        (wr13b_EP (fun w => q w + k w) μ n (wr13b_lamN β n) β t x) ≤
      ENNReal.ofReal (Real.exp (52 * β * k 0)) • wr13b_Rpole h hβ n ht x t := by
  rw [wr13b_pole_tilted_eq h hβ n ht x ht0 ht1]
  have h1 := wr13b_tilted_aPole_le h hβ n ht x ht0 ht1
    (Esq := 100 * ((n : ℝ) + 1) * k 0) (wr13b_Esq_le h hβ n hn ht hκ x ht0 ht1)
  refine h1.trans ?_
  have hmul : wr13b_lamN β n * ((n : ℝ) + 1) = β := (wr13b_lamN_mul (β := β) n).symm
  have : 2 * β * k 0 + wr13b_lamN β n / 2 * (100 * ((n : ℝ) + 1) * k 0) = 52 * β * k 0 := by
    calc 2 * β * k 0 + wr13b_lamN β n / 2 * (100 * ((n : ℝ) + 1) * k 0)
        = 2 * β * k 0 + 50 * (wr13b_lamN β n * ((n : ℝ) + 1)) * k 0 := by ring
      _ = _ := by rw [hmul]; ring
  rw [this]

include h hβ in
/-- **The variance bound for the weak reference with a pole, transferred to the pole law.** -/
theorem wr13b_pole_evariance_le (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : wr11b_KappaSmall β a) (x : Euc d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P : Measure (Fin n → Euc d)) [IsProbabilityMeasure P]
    (hP : P = (Measure.pi fun _ : Fin n => μ).tilted
        (wr13b_EP (fun w => q w + k w) μ n (wr13b_lamN β n) β t x))
    {f : Euc d → ℝ} (hf : Measurable f) :
    evariance (fun y : Fin n → Euc d => ∑ i, f (y i)) P ≤
      ENNReal.ofReal (Real.exp (52 * β * k 0)) * (2 * n *
        ∫⁻ z, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (β * a +
          HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z)) ∂μ) := by
  have : NeZero n := ⟨by omega⟩
  have := wr13b_isProb_Rpole h hβ n ht x ht0 ht1
  have hle := wr13b_pole_le_Rpole h hβ n hn ht hκ x ht0 ht1
  rw [← hP] at hle
  have hF : Measurable fun y : Fin n → Euc d => ∑ i, f (y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  refine (HRS.External.PoleVar.evariance_le_of_le_smul hle hF).trans ?_
  gcongr
  have hlam0 := wr13b_lamN_nonneg hβ n
  have hψ := HRS.External.PoleVar.isField_psiPole (wr13b_Vp h hβ n ht) hlam0 ht0 ht1 x
  obtain ⟨hΛ, hrow⟩ := wr13b_wu_data h hβ n ht hκ
  have hvar := HRS.External.PoleVar.field_linear_variance_symm (V := wr13b_Vp h hβ n ht) hψ hlam0
    (Λ := (wr13b_Vp h hβ n ht).M' + β * (wr13b_Vp h hβ n ht).γ) (by simpa using hΛ) hrow f hf
  refine hvar.trans ?_
  gcongr
  set π0 := (wr13b_Rpole h hβ n ht x t).map (fun y => y 0) with hπ0
  have : IsProbabilityMeasure π0 := inferInstance
  refine (evariance_le_lintegral_sub π0 hf.aestronglyMeasurable 0).trans ?_
  have hdom : π0 ≤ μ.withDensity (fun z => ENNReal.ofReal (Real.exp
      ((wr13b_Vp h hβ n ht).M' + β * (wr13b_Vp h hβ n ht).γ +
        HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z))) := by
    rw [Measure.le_iff]
    intro A hA
    rw [withDensity_apply _ hA]
    exact HRS.External.PoleVar.field_marginal_le (V := wr13b_Vp h hβ n ht) hψ hlam0
      (by simpa using hΛ) ⟨0, by omega⟩ hA
  have hM' : (wr13b_Vp h hβ n ht).M' = 0 := rfl
  have hγ : (wr13b_Vp h hβ n ht).γ = a := rfl
  rw [hM', hγ, zero_add] at hdom
  calc ∫⁻ z, ‖f z - 0‖ₑ ^ 2 ∂π0
      ≤ ∫⁻ z, ‖f z - 0‖ₑ ^ 2 ∂(μ.withDensity (fun z => ENNReal.ofReal (Real.exp
          (β * a + HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z)))) :=
        lintegral_mono' hdom le_rfl
    _ = ∫⁻ z, ENNReal.ofReal (Real.exp (β * a +
          HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x z))
          * ‖f z - 0‖ₑ ^ 2 ∂μ := by
        rw [lintegral_withDensity_eq_lintegral_mul₀]
        · rfl
        · exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (measurable_const.add hψ.measurable))).aemeasurable
        · exact ((hf.sub_const 0).enorm.pow_const 2).aemeasurable
    _ = _ := by
        refine lintegral_congr fun z => ?_
        rw [sub_zero, mul_comm]

end Marg

end HRS.MS.Wr
