import HRS.Sections.QuenchAux29

/-!
# Packet QUENCH (Q27), part 30: upper/lower bounds and the nonvanishing of `D_*`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ} {m T : ℝ} {s β β₀ : ℝ}

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
variable (Δ : ℝ → (PathSpace d m T [×2]→L[ℝ] ℝ) → ℝ)

include hd hs0 hsd hβ in
theorem upper_bound (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) (hT : 0 < T)
    (hser : ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ a M =
      ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)]))
    {a : ℝ} (ha : 0 ≤ a) (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    |Δ a M| ≤ ‖M‖ * (Real.exp (-2 * lamStar d s β * a) * ∑' k, wk d s β β₀ m T k) := by
  have hl : ∀ k : PosHalf d, 0 ≤ lamMode d s β k.1 := fun k => (lamMode_pos' hd hs0 hsd hβ k).le
  have hwsum := summable_wk (β₀ := β₀) (m := m) (T := T) hd hs0 hsd hβ hβ₀ hm hT
  rw [ser_ck Δ hser ha M]
  have hb : ∀ k : PosHalf d, ‖Real.exp (-2 * lamMode d s β k.1 * a) * ckM d s β β₀ m T M k‖ ≤
      Real.exp (-2 * lamStar d s β * a) * (‖M‖ * wk d s β β₀ m T k) := by
    intro k
    have h1 := lamStar_le hd hs0 hsd hβ k
    have h2 : Real.exp (-2 * lamMode d s β k.1 * a) ≤ Real.exp (-2 * lamStar d s β * a) :=
      Real.exp_le_exp.2 (by nlinarith)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    exact mul_le_mul h2 (abs_ckM_le M hl k) (abs_nonneg _) (Real.exp_pos _).le
  have := tsum_of_norm_bounded ((hwsum.hasSum.mul_left ‖M‖).mul_left (Real.exp (-2 * lamStar d s β * a))) hb
  rw [Real.norm_eq_abs] at this
  calc _ ≤ _ := this
    _ = _ := by ring

lemma M0of_diag (ℓ : PathSpace d m T →L[ℝ] ℝ) (x : PathSpace d m T) : M0of ℓ ![x, x] = ℓ x * ℓ x :=
  M0of_apply ℓ x x

include hd hs0 hsd hβ in
theorem test_form (hβ₀ : 0 < β₀) (hne : β₀ ≠ β) (hT : 0 < T)
    (hser : ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ a M =
      ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)])) :
    ∃ (M0 : PathSpace d m T [×2]→L[ℝ] ℝ) (c0 : ℝ), ‖M0‖ ≤ 1 ∧ c0 ≠ 0 ∧
      slowTensor d s β β₀ m T M0 = c0 ∧
      ∀ a : ℝ, 0 ≤ a → Δ a M0 = Real.exp (-2 * lamStar d s β * a) * c0 := by
  classical
  obtain ⟨k0, hk0⟩ := exists_min_lam hd hs0 hsd hβ
  have he := lamStar_eq hd hs0 hsd hβ k0 hk0
  set j0 : NonzeroLattice d := idx k0 true with hj0
  set M0 : PathSpace d m T [×2]→L[ℝ] ℝ := M0of (ell hT j0) with hM0
  set c0 : ℝ := deltaVar d s β β₀ k0.1 * Lattice.jp k0.1 ^ (-(2 * m)) with hc0
  have hjp2 : ∀ k : PosHalf d, (sgn true * Lattice.jp k.1 ^ (-m)) ^ 2 = Lattice.jp k.1 ^ (-(2 * m)) := by
    intro k
    rw [mul_pow, sgn_sq, one_mul, Torus.jp_rpow_sq]; congr 1; ring
  have hdiag : ∀ (k : PosHalf d) (b : Bool), M0 ![mpk d s β m T k b, mpk d s β m T k b] =
      Lattice.jp k.1 ^ (-(2 * m)) * (if j0 = idx k b then 1 else 0) := by
    intro k b
    rw [hM0, M0of_diag, ell_mp]
    have h1 : (sgn b * Lattice.jp k.1 ^ (-m)) ^ 2 = Lattice.jp k.1 ^ (-(2 * m)) := by
      rw [mul_pow, sgn_sq, one_mul, Torus.jp_rpow_sq]; congr 1; ring
    by_cases h : j0 = idx k b
    · simp only [h, if_true, mul_one]
      rw [← sq, h1]
    · simp [h]
  have hck : ∀ k : PosHalf d, ckM d s β β₀ m T M0 k = if k = k0 then c0 else 0 := by
    intro k
    unfold ckM
    rw [hdiag, hdiag]
    by_cases hk : k = k0
    · subst hk
      have hf : ¬ (j0 = idx k false) := fun h => by
        have := idx_injective (p := (k, true)) (q := (k, false)) h
        simp at this
      have hf' : ¬ (idx k true = idx k false) := hf
      simp [hf', hc0, hj0]
    · have h1 : ¬ (j0 = idx k true) := fun h => hk (by
        have := idx_injective (p := (k0, true)) (q := (k, true)) h
        exact (congrArg Prod.fst this).symm)
      have h2 : ¬ (j0 = idx k false) := fun h => by
        have := idx_injective (p := (k0, true)) (q := (k, false)) h
        simp at this
      simp [hk, h1, h2]
  refine ⟨M0, c0, norm_M0of _ (norm_ell_le hT j0), ?_, ?_, ?_⟩
  · have h1 := deltaVar_ne_zero hd hs0 hsd hβ hβ₀ hne ⟨k0.1, ne_zero_of_posHalf k0.2⟩
    have h2 : 0 < Lattice.jp k0.1 ^ (-(2 * m)) := Real.rpow_pos_of_pos (Torus.jp_pos _) _
    exact mul_ne_zero h1 h2.ne'
  · unfold slowTensor
    show ∑' x : {k : PosHalf d // lamMode d s β k.1 = lamStar d s β}, ckM d s β β₀ m T M0 x.1 = c0
    rw [tsum_eq_single ⟨k0, he.symm⟩]
    · rw [hck]; simp
    · intro x hx
      rw [hck]
      have : x.1 ≠ k0 := fun h => hx (Subtype.ext h)
      simp [this]
  · intro a ha
    rw [ser_ck Δ hser ha M0, tsum_eq_single k0]
    · rw [hck, ← he]; simp
    · intro k hk
      rw [hck]; simp [hk]

end Qch

end HRS
