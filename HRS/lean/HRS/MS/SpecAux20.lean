import HRS.MS.SpecAux5
import HRS.Whole.Hermite

/-!
# S8P: Weyl-type growth `ω_ℓ ≥ c (ℓ+1)^{1/d}` from a Rayleigh bound in the Hermite basis (S8.7, packet E6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.

* `s8p_hermite_count`: `#{α : MultiIndex d | 2|α|+d+1 ≤ Λ} ≤ (Λ+1)^d`;
* `s8p_growth_count`: if `u_0,…,u_ℓ` orthonormal and the oscillator form `∑ λ_α ⟨b_α, v⟩²` is bounded by `Cr (ω_ℓ+1) ‖v‖²` on their
  span, then `ℓ+1 ≤ (Cr(ω_ℓ+1)+2)^d`;
* `s8p_growth_lin`: with `ω_ℓ ≥ ω_0 > 0` this gives `c (ℓ+1)^{1/d} ≤ ω_ℓ`.
-/

noncomputable section

open Filter Topology Module
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

theorem s8p_hermite_count (d : ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (({α : MultiIndex d | oscEigenvalue d α ≤ Λ}).ncard : ℝ) ≤ (Λ + 1) ^ d := by
  classical
  have hfin : {α : MultiIndex d | oscEigenvalue d α ≤ Λ}.Finite := by
    refine (multiIndex_sublevel_finite d ⌊Λ⌋₊).subset fun α hα => ?_
    simp only [Set.mem_setOf_eq] at hα ⊢
    have h1 : (α.degree : ℝ) ≤ Λ := by
      unfold oscEigenvalue at hα
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    exact Nat.le_floor h1
  -- inject into functions `Fin d → Fin (⌊Λ⌋₊+1)`
  let F : MultiIndex d → (Fin d → Fin (⌊Λ⌋₊ + 1)) := fun α i =>
    ⟨min (α i) ⌊Λ⌋₊, by omega⟩
  have hF : Set.InjOn F {α : MultiIndex d | oscEigenvalue d α ≤ Λ} := by
    intro α hα β hβ hαβ
    funext i
    have hαi : α i ≤ ⌊Λ⌋₊ := by
      have h1 : (α.degree : ℝ) ≤ Λ := by
        have := hα; simp only [Set.mem_setOf_eq] at this; unfold oscEigenvalue at this
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith
      have h2 : α i ≤ α.degree := by
        unfold MultiIndex.degree
        exact Finset.single_le_sum (f := fun j => α j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact le_trans h2 (Nat.le_floor h1)
    have hβi : β i ≤ ⌊Λ⌋₊ := by
      have h1 : (β.degree : ℝ) ≤ Λ := by
        have := hβ; simp only [Set.mem_setOf_eq] at this; unfold oscEigenvalue at this
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith
      have h2 : β i ≤ β.degree := by
        unfold MultiIndex.degree
        exact Finset.single_le_sum (f := fun j => β j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact le_trans h2 (Nat.le_floor h1)
    have := congrFun hαβ i
    simp only [F, Fin.mk.injEq] at this
    rwa [min_eq_left hαi, min_eq_left hβi] at this
  have hcard : ({α : MultiIndex d | oscEigenvalue d α ≤ Λ}).ncard ≤ (⌊Λ⌋₊ + 1) ^ d := by
    have := Set.ncard_le_ncard_of_injOn F (fun _ _ => Set.mem_univ _) hF Set.finite_univ
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun] using this
  calc (({α : MultiIndex d | oscEigenvalue d α ≤ Λ}).ncard : ℝ) ≤ ((⌊Λ⌋₊ + 1) ^ d : ℕ) := by
        exact_mod_cast hcard
    _ ≤ (Λ + 1) ^ d := by
        push_cast
        gcongr
        exact (Nat.floor_le hΛ).trans (le_refl _) |>.trans (by linarith) |> fun h => by linarith [Nat.floor_le hΛ]

end HRS.MS.Spec
