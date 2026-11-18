import Mathlib

/-!
# U6 aux 4: uniform derivative bounds for `ψ · G(∑_k ψ(L_k · + b_k)²)`
-/

noncomputable section

open scoped ContDiff
open Finset

namespace HRS.U6

section Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma u6_comp_affine_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ M) (L : E →L[ℝ] E) (b u : E) :
    ‖iteratedFDeriv ℝ n (fun v => ψ (L v + b)) u‖ ≤ M * ‖L‖ ^ n := by
  have h1 : (fun v => ψ (L v + b)) = (fun w => ψ (w + b)) ∘ L := rfl
  have hc : ContDiff ℝ ∞ (fun w => ψ (w + b)) := hψ.comp (contDiff_id.add contDiff_const)
  rw [h1, L.iteratedFDeriv_comp_right hc u (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [iteratedFDeriv_comp_add_right, prod_const, card_univ, Fintype.card_fin]
  have := hM (L u + b)
  have h0 : 0 ≤ ‖L‖ ^ n := by positivity
  nlinarith

lemma u6_sumsq_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (M : ℕ → ℝ)
    (hM : ∀ n x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ M n) (Λ : ℝ) {ι : Type*} (N : Finset ι)
    (L : ι → E →L[ℝ] E) (b : ι → E) (hL : ∀ k ∈ N, ‖L k‖ ≤ Λ) (n : ℕ) (u : E) :
    ‖iteratedFDeriv ℝ n (fun v => ∑ k ∈ N, ψ (L k v + b k) ^ 2) u‖ ≤
      N.card * ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (M i * Λ ^ i) * (M (n - i) * Λ ^ (n - i)) := by
  have hcd : ∀ k ∈ N, ContDiff ℝ ∞ (fun v => ψ (L k v + b k)) := fun k _ =>
    hψ.comp ((L k).contDiff.add contDiff_const)
  have hcd2 : ∀ k ∈ N, ContDiff ℝ n (fun v => ψ (L k v + b k) ^ 2) := fun k hk =>
    ((hcd k hk).pow 2).of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_fun_sum_apply (fun k hk => (hcd2 k hk).contDiffAt)]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine (Finset.sum_le_card_nsmul _ _ _ (fun k hk => ?_))
  have hMnn : ∀ i, 0 ≤ M i := fun i => (norm_nonneg _).trans (hM i 0)
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hL k hk)
  have e : (fun v => ψ (L k v + b k) ^ 2) = fun v => ψ (L k v + b k) * ψ (L k v + b k) := by
    funext v; ring
  rw [e]
  refine (norm_iteratedFDeriv_mul_le (hcd k hk) (hcd k hk) u (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  have b1 : ∀ m, ‖iteratedFDeriv ℝ m (fun v => ψ (L k v + b k)) u‖ ≤ M m * Λ ^ m := by
    intro m
    refine (u6_comp_affine_bound hψ m (hM m) (L k) (b k) u).trans ?_
    have := hL k hk
    gcongr
    exact hMnn m
  have c1 := b1 i
  have c2 := b1 (n - i)
  have : (0 : ℝ) ≤ n.choose i := by positivity
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun v => ψ (L k v + b k)) u‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun v => ψ (L k v + b k)) u‖
      ≤ (n.choose i : ℝ) * (M i * Λ ^ i) * (M (n - i) * Λ ^ (n - i)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left c1 this) c2 (norm_nonneg _)
          (mul_nonneg this (mul_nonneg (hMnn i) (pow_nonneg hΛ i)))

lemma u6_G_comp_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (M : ℕ → ℝ)
    (hM : ∀ n x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ M n) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (K : ℕ)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (m : ℕ) :
    ∃ C : ℝ, ∀ {ι : Type} (N : Finset ι) (L : ι → E →L[ℝ] E) (b : ι → E), N.card ≤ K →
      (∀ k ∈ N, ‖L k‖ ≤ Λ) → ∀ u : E,
        ‖iteratedFDeriv ℝ m (fun v => G (∑ k ∈ N, ψ (L k v + b k) ^ 2)) u‖ ≤ C := by
  have hMnn : ∀ i, 0 ≤ M i := fun i => (norm_nonneg _).trans (hM i 0)
  set Mx : ℝ := (K : ℝ) * M 0 ^ 2 with hMx
  have hcG : ∀ i : ℕ, ∃ c : ℝ, ∀ t ∈ Set.Icc 0 Mx, ‖iteratedFDeriv ℝ i G t‖ ≤ c := fun i =>
    isCompact_Icc.exists_bound_of_continuousOn
      ((hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn)
  choose cG hcG using hcG
  set CG : ℝ := ∑ i ∈ range (m + 1), |cG i| with hCG
  set Q : ℕ → ℝ := fun i => ∑ l ∈ range (i + 1),
    (i.choose l : ℝ) * (M l * Λ ^ l) * (M (i - l) * Λ ^ (i - l)) with hQ
  have hQnn : ∀ i, 0 ≤ Q i := fun i => by
    refine Finset.sum_nonneg (fun l _ => ?_)
    have := hMnn l; have := hMnn (i - l)
    positivity
  set D : ℝ := 1 + ∑ i ∈ range (m + 1), |(K : ℝ) * Q i| with hD
  have hD1 : 1 ≤ D := by
    rw [hD]; have : 0 ≤ ∑ i ∈ range (m + 1), |(K : ℝ) * Q i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  refine ⟨(m.factorial : ℝ) * CG * D ^ m, fun {ι} N L b hN hL u => ?_⟩
  have hcd : ∀ k ∈ N, ContDiff ℝ ∞ (fun v => ψ (L k v + b k)) := fun k _ =>
    hψ.comp ((L k).contDiff.add contDiff_const)
  have hf : ContDiff ℝ ∞ (fun v => ∑ k ∈ N, ψ (L k v + b k) ^ 2) :=
    ContDiff.sum (fun k hk => (hcd k hk).pow 2)
  have hrange : (∑ k ∈ N, ψ (L k u + b k) ^ 2) ∈ Set.Icc 0 Mx := by
    refine ⟨Finset.sum_nonneg (fun k _ => sq_nonneg _), ?_⟩
    have h1 : ∀ k ∈ N, ψ (L k u + b k) ^ 2 ≤ M 0 ^ 2 := by
      intro k _
      have := hM 0 (L k u + b k)
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      have h2 : |ψ (L k u + b k)| ≤ M 0 := this
      calc ψ (L k u + b k) ^ 2 = |ψ (L k u + b k)| ^ 2 := (sq_abs _).symm
        _ ≤ M 0 ^ 2 := by gcongr
    calc ∑ k ∈ N, ψ (L k u + b k) ^ 2 ≤ ∑ k ∈ N, M 0 ^ 2 := Finset.sum_le_sum h1
      _ = N.card * M 0 ^ 2 := by simp
      _ ≤ Mx := by rw [hMx]; gcongr
  have key := norm_iteratedFDeriv_comp_le (g := G) (f := fun v => ∑ k ∈ N, ψ (L k v + b k) ^ 2)
    (n := m) (N := ∞) hG hf (by exact_mod_cast le_top) u (C := CG) (D := D) ?_ ?_
  · exact key
  · intro i hi
    refine (hcG i _ hrange).trans ?_
    rw [hCG]
    refine (le_abs_self _).trans ?_
    exact Finset.single_le_sum (f := fun i => |cG i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  · intro i hi1 him
    refine (u6_sumsq_bound hψ M hM Λ N L b hL i u).trans ?_
    have h1 : (N.card : ℝ) * Q i ≤ (K : ℝ) * Q i := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (hQnn i)
    have h2 : (K : ℝ) * Q i ≤ |(K : ℝ) * Q i| := le_abs_self _
    have h3 : |(K : ℝ) * Q i| ≤ ∑ j ∈ range (m + 1), |(K : ℝ) * Q j| :=
      Finset.single_le_sum (f := fun j => |(K : ℝ) * Q j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le him))
    have h4 : D ≤ D ^ i := le_self_pow₀ hD1 (by omega)
    have h5 : D = 1 + ∑ i ∈ range (m + 1), |(K : ℝ) * Q i| := hD
    show (N.card : ℝ) * Q i ≤ D ^ i
    linarith

theorem u6_chi_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (M : ℕ → ℝ)
    (hM : ∀ n x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ M n) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (K : ℕ)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (n : ℕ) :
    ∃ C : ℝ, ∀ {ι : Type} (N : Finset ι) (L : ι → E →L[ℝ] E) (b : ι → E), N.card ≤ K →
      (∀ k ∈ N, ‖L k‖ ≤ Λ) → ∀ u : E,
        ‖iteratedFDeriv ℝ n (fun v => ψ v * G (∑ k ∈ N, ψ (L k v + b k) ^ 2)) u‖ ≤ C := by
  have hMnn : ∀ i, 0 ≤ M i := fun i => (norm_nonneg _).trans (hM i 0)
  choose C' hC' using fun m => u6_G_comp_bound hψ M hM hG K Λ hΛ m
  refine ⟨∑ i ∈ range (n + 1), (n.choose i : ℝ) * M i * |C' (n - i)|, fun {ι} N L b hN hL u => ?_⟩
  have hcd : ∀ k ∈ N, ContDiff ℝ ∞ (fun v => ψ (L k v + b k)) := fun k _ =>
    hψ.comp ((L k).contDiff.add contDiff_const)
  have hf : ContDiff ℝ ∞ (fun v => ∑ k ∈ N, ψ (L k v + b k) ^ 2) :=
    ContDiff.sum (fun k hk => (hcd k hk).pow 2)
  have hGf : ContDiff ℝ ∞ (fun v => G (∑ k ∈ N, ψ (L k v + b k) ^ 2)) := hG.comp hf
  refine (norm_iteratedFDeriv_mul_le hψ hGf u (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h1 := hM i u
  have h2 := hC' (n - i) N L b hN hL u
  have h3 : (0 : ℝ) ≤ n.choose i := by positivity
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ u‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun v => G (∑ k ∈ N, ψ (L k v + b k) ^ 2)) u‖
      ≤ (n.choose i : ℝ) * M i * |C' (n - i)| :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) (h2.trans (le_abs_self _)) (norm_nonneg _)
          (mul_nonneg h3 (hMnn i))

end Analysis

end HRS.U6
