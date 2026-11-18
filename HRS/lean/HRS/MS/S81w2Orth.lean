import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# S8.1 (worker S81W2): orthogonal series in a Hilbert space with exact tails

`s81w2_orth_sum`: if `g_l` are pairwise orthogonal with `‖g_l‖² = ω_l > 0` and `Σ ω_l c_l² < ∞`, the series `Σ c_l g_l`
converges (`HasSum`) and its `L`-th remainder has squared norm exactly `Σ_{l ≥ L} ω_l c_l²`.
-/

set_option autoImplicit false

noncomputable section
open Filter Topology
open scoped BigOperators InnerProductSpace

namespace HRS.Whole.S81W2

theorem s81w2_orth_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : ℕ → H) (om : ℕ → ℝ) (hom : ∀ l, 0 < om l)
    (hg : ∀ l k, inner ℝ (g l) (g k) = if l = k then om l else 0) (c : ℕ → ℝ)
    (hc : Summable fun l => om l * c l ^ 2) :
    ∃ G : H, HasSum (fun l => c l • g l) G ∧
      ∀ L : ℕ, ‖G - ∑ l ∈ Finset.range L, c l • g l‖ ^ 2 = ∑' l, om (l + L) * c (l + L) ^ 2 := by
  classical
  set w : ℕ → H := fun l => (Real.sqrt (om l))⁻¹ • g l with hw
  have hwo : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [hw, inner_smul_left, inner_smul_right, hg]
    by_cases h : i = j
    · subst h
      have h1 := Real.mul_self_sqrt (hom i).le
      have h2 := (Real.sqrt_pos.2 (hom i)).ne'
      simp only [if_true, conj_trivial]
      field_simp
      linarith
    · simp [h]
  have hV := hwo.orthogonalFamily
  set F : ℕ → ℝ := fun l => Real.sqrt (om l) * c l with hF
  have hVF : ∀ l, LinearIsometry.toSpanSingleton ℝ H (hwo.1 l) (F l) = c l • g l := by
    intro l
    have h2 := (Real.sqrt_pos.2 (hom l)).ne'
    simp only [LinearIsometry.toSpanSingleton_apply, hw, hF, smul_smul]
    congr 1
    field_simp
  have hFn : ∀ l, ‖F l‖ ^ 2 = om l * c l ^ 2 := by
    intro l
    rw [Real.norm_eq_abs, sq_abs, hF]
    simp only [mul_pow]
    rw [Real.sq_sqrt (hom l).le]
  have hsum : Summable fun l => LinearIsometry.toSpanSingleton ℝ H (hwo.1 l) (F l) :=
    (hV.summable_iff_norm_sq_summable F).2 (by simpa only [hFn] using hc)
  have hsum' : HasSum (fun l => c l • g l) (∑' l, c l • g l) := by
    have := hsum.hasSum
    simpa only [hVF] using this
  refine ⟨∑' l, c l • g l, hsum', fun L => ?_⟩
  -- the tail
  set G : H := ∑' l, c l • g l with hG
  have hnorm : ∀ n : ℕ, ‖∑ l ∈ Finset.range (n + L), c l • g l - ∑ l ∈ Finset.range L, c l • g l‖ ^ 2 =
      ∑ l ∈ Finset.range (n + L), om l * c l ^ 2 - ∑ l ∈ Finset.range L, om l * c l ^ 2 := by
    intro n
    have h1 := hV.norm_sum F (Finset.Ico L (n + L))
    have e1 : ∑ l ∈ Finset.Ico L (n + L), LinearIsometry.toSpanSingleton ℝ H (hwo.1 l) (F l) =
        ∑ l ∈ Finset.range (n + L), c l • g l - ∑ l ∈ Finset.range L, c l • g l := by
      rw [← Finset.sum_Ico_eq_sub _ (by omega)]
      exact Finset.sum_congr rfl fun l _ => hVF l
    rw [e1] at h1
    rw [h1, ← Finset.sum_Ico_eq_sub _ (by omega)]
    exact Finset.sum_congr rfl fun l _ => hFn l
  have hlim1 : Tendsto (fun n : ℕ => ‖∑ l ∈ Finset.range (n + L), c l • g l -
      ∑ l ∈ Finset.range L, c l • g l‖ ^ 2) atTop (𝓝 (‖G - ∑ l ∈ Finset.range L, c l • g l‖ ^ 2)) :=
    (((hsum'.tendsto_sum_nat.comp (tendsto_add_atTop_nat L)).sub_const _).norm).pow 2
  have hlim2 : Tendsto (fun n : ℕ => ∑ l ∈ Finset.range (n + L), om l * c l ^ 2 -
      ∑ l ∈ Finset.range L, om l * c l ^ 2) atTop
      (𝓝 ((∑' l, om l * c l ^ 2) - ∑ l ∈ Finset.range L, om l * c l ^ 2)) :=
    ((hc.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat L)).sub_const _)
  have hlim1' : Tendsto (fun n : ℕ => ‖∑ l ∈ Finset.range (n + L), c l • g l -
      ∑ l ∈ Finset.range L, c l • g l‖ ^ 2) atTop
      (𝓝 ((∑' l, om l * c l ^ 2) - ∑ l ∈ Finset.range L, om l * c l ^ 2)) := by
    simpa only [hnorm] using hlim2
  have := tendsto_nhds_unique hlim1 hlim1'
  rw [this]
  have h3 := hc.sum_add_tsum_nat_add L
  linarith

end HRS.Whole.S81W2
