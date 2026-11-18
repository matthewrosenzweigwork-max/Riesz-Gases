import HRS.MC.QRPChaosAux4

/-!
# Packet CHAOS-LP (aux 5): finite sections of a Wick quadratic form

The difference of two finite Wick sections `F ⊆ S` is a Gaussian chaos with matrix `½ a 1_{(S×S)∖(F×F)}`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.QRPChaos

open Classical in
/-- The squared entries of `a` outside `F × F` (the summand of `tailHS`). -/
def qpcTail {τ : Type} (a : τ → τ → ℝ) (F : Finset τ) (q : τ × τ) : ℝ :=
  if q.1 ∈ F ∧ q.2 ∈ F then 0 else a q.1 q.2 ^ 2

open Classical in
/-- Sum over `S × S` minus the sum over `F × F`, as a sum with the entries inside `F × F` removed. -/
lemma qpc_sum_sub {τ : Type} (S F : Finset τ) (hFS : F ⊆ S) (g : τ → τ → ℝ) :
    ∑ k ∈ S, ∑ l ∈ S, (if k ∈ F ∧ l ∈ F then 0 else g k l) =
      ∑ k ∈ S, ∑ l ∈ S, g k l - ∑ k ∈ F, ∑ l ∈ F, g k l := by
  have h1 : ∑ k ∈ S, ∑ l ∈ S, (if k ∈ F ∧ l ∈ F then g k l else 0) = ∑ k ∈ F, ∑ l ∈ F, g k l := by
    have : ∀ k, ∑ l ∈ S, (if k ∈ F ∧ l ∈ F then g k l else 0) =
        if k ∈ F then ∑ l ∈ F, g k l else 0 := by
      intro k
      by_cases hk : k ∈ F
      · simp only [hk, true_and, ite_true]
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hFS]
      · simp [hk]
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hFS]
  have h2 : ∀ k l, (if k ∈ F ∧ l ∈ F then (0 : ℝ) else g k l) =
      g k l - (if k ∈ F ∧ l ∈ F then g k l else 0) := by
    intro k l; split_ifs <;> simp
  simp_rw [h2, Finset.sum_sub_distrib, h1]

open Classical in
/-- The difference of two finite Wick sections is a Gaussian chaos over `↥S`; apply the finite bound. -/
lemma qpc_section {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Type} (c : τ → Ω → ℝ)
    (hG : ∀ S : Finset τ, HasGaussianLaw (fun ω (k : S) => c k.1 ω) P)
    (h0 : ∀ k, ∫ ω, c k ω ∂P = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (S : Finset τ) (b : τ → ℝ), ∫ ω, (∑ k ∈ S, b k * c k ω) ^ 2 ∂P ≤ K * ∑ k ∈ S, b k ^ 2)
    (a : τ → τ → ℝ) (F S : Finset τ) (hFS : F ⊆ S) {p C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ {ι : Type} [Fintype ι] (ξ : ι → Ω → ℝ), HasGaussianLaw (fun ω i => ξ i ω) P →
      (∀ i, ∫ ω, ξ i ω ∂P = 0) → ∀ K : ℝ, 0 ≤ K →
      (∀ a : ι → ℝ, ∫ ω, (∑ i, a i * ξ i ω) ^ 2 ∂P ≤ K * ∑ i, a i ^ 2) →
      ∀ A : ι → ι → ℝ,
        eLpNorm (fun ω => ∑ i, ∑ j, A i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P))
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C * K * Real.sqrt (∑ i, ∑ j, A i j ^ 2))) :
    eLpNorm (fun ω => (1 / 2) * ∑ k ∈ S, ∑ l ∈ S, a k l * (c k ω * c l ω - ∫ ω', c k ω' * c l ω' ∂P)
        - (1 / 2) * ∑ k ∈ F, ∑ l ∈ F, a k l * (c k ω * c l ω - ∫ ω', c k ω' * c l ω' ∂P))
      (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (C * K * Real.sqrt (∑ q ∈ S ×ˢ S, qpcTail a F q)) := by
  set ξ : ↥S → Ω → ℝ := fun i ω => c i.1 ω with hξ
  set A' : ↥S → ↥S → ℝ := fun i j => (1 / 2) * (if i.1 ∈ F ∧ j.1 ∈ F then 0 else a i.1 j.1) with hA'
  have hKop : ∀ b' : ↥S → ℝ, ∫ ω, (∑ i, b' i * ξ i ω) ^ 2 ∂P ≤ K * ∑ i, b' i ^ 2 := by
    intro b'
    set b : τ → ℝ := fun k => if h : k ∈ S then b' ⟨k, h⟩ else 0 with hb
    have hbi : ∀ i : ↥S, b i.1 = b' i := fun i => by simp [hb]
    have e1 : ∀ ω, ∑ i, b' i * ξ i ω = ∑ k ∈ S, b k * c k ω := fun ω => by
      rw [← Finset.sum_coe_sort S (fun k => b k * c k ω)]
      exact Finset.sum_congr rfl fun i _ => by simp [hξ, hbi]
    have e2 : ∑ i, b' i ^ 2 = ∑ k ∈ S, b k ^ 2 := by
      rw [← Finset.sum_coe_sort S (fun k => b k ^ 2)]
      exact Finset.sum_congr rfl fun i _ => by simp [hbi]
    simp_rw [e1, e2]
    exact hK S b
  have hmain := hC ξ (hG S) (fun i => h0 i.1) K hK0 hKop A'
  have e3 : ∀ g : τ → τ → ℝ, ∑ i : ↥S, ∑ j : ↥S, g i.1 j.1 = ∑ k ∈ S, ∑ l ∈ S, g k l := fun g => by
    rw [← Finset.sum_coe_sort S (fun k => ∑ l ∈ S, g k l)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_coe_sort S (g i.1)
  have hfun : (fun ω => ∑ i : ↥S, ∑ j : ↥S, A' i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P)) =
      fun ω => (1 / 2) * ∑ k ∈ S, ∑ l ∈ S, a k l * (c k ω * c l ω - ∫ ω', c k ω' * c l ω' ∂P)
        - (1 / 2) * ∑ k ∈ F, ∑ l ∈ F, a k l * (c k ω * c l ω - ∫ ω', c k ω' * c l ω' ∂P) := by
    funext ω
    have := e3 (fun k l => (1 / 2) * (if k ∈ F ∧ l ∈ F then 0 else a k l) *
      (c k ω * c l ω - ∫ ω', c k ω' * c l ω' ∂P))
    simp only [hA', hξ]
    rw [this]
    have h2 := qpc_sum_sub S F hFS (fun k l => a k l * (c k ω * c l ω - ∫ ω', c k ω' * c l ω' ∂P))
    have h3 : ∀ k l, (1 / 2 : ℝ) * (if k ∈ F ∧ l ∈ F then 0 else a k l) *
        (c k ω * c l ω - ∫ ω', c k ω' * c l ω' ∂P) =
        (1 / 2) * (if k ∈ F ∧ l ∈ F then 0 else
          a k l * (c k ω * c l ω - ∫ ω', c k ω' * c l ω' ∂P)) := by
      intro k l; split_ifs <;> simp [mul_assoc]
    simp_rw [h3, ← Finset.mul_sum]
    rw [h2]; ring
  rw [hfun] at hmain
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsum : ∑ i : ↥S, ∑ j : ↥S, A' i j ^ 2 ≤ ∑ q ∈ S ×ˢ S, qpcTail a F q := by
    have := e3 (fun k l => ((1 / 2) * (if k ∈ F ∧ l ∈ F then 0 else a k l)) ^ 2)
    simp only [hA']
    rw [this, Finset.sum_product]
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
    simp only [qpcTail]
    split_ifs
    · simp
    · nlinarith [sq_nonneg (a k l)]
  have := Real.sqrt_le_sqrt hsum
  exact mul_le_mul_of_nonneg_left this (mul_nonneg hC0 hK0)

end HRS.MC.QRPChaos

end
