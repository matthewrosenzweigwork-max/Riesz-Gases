import HRS.Sections.QuenchFinal

/-!
# Packet 7.14 CT (form): the rank-one test form `ℓ_{j₀} ⊗ ℓ_{j₀}` at a slowest mode

Same computation as `Qch.test_form`, but with the form `M0of (ell hT (idx k₀ true))` exposed.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.CT

open HRS HRS.Sec7 HRS.Qch

variable {d : ℕ} {m T : ℝ} {s β β₀ : ℝ}

theorem ct_test_form (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (Δ : ℝ → (PathSpace d m T [×2]→L[ℝ] ℝ) → ℝ)
    (hβ₀ : 0 < β₀) (hne : β₀ ≠ β) (hT : 0 < T)
    (hser : ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ a M =
      ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)])) :
    ∃ (k0 : PosHalf d) (c0 : ℝ), c0 ≠ 0 ∧
      ∀ a : ℝ, 0 ≤ a → Δ a (M0of (ell hT (idx k0 true))) = Real.exp (-2 * lamStar d s β * a) * c0 := by
  classical
  obtain ⟨k0, hk0⟩ := exists_min_lam hd hs0 hsd hβ
  have he := lamStar_eq hd hs0 hsd hβ k0 hk0
  set j0 : NonzeroLattice d := idx k0 true with hj0
  set M0 : PathSpace d m T [×2]→L[ℝ] ℝ := M0of (ell hT j0) with hM0
  set c0 : ℝ := deltaVar d s β β₀ k0.1 * Lattice.jp k0.1 ^ (-(2 * m)) with hc0
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
  refine ⟨k0, c0, ?_, ?_⟩
  · have h1 := deltaVar_ne_zero hd hs0 hsd hβ hβ₀ hne ⟨k0.1, ne_zero_of_posHalf k0.2⟩
    have h2 : 0 < Lattice.jp k0.1 ^ (-(2 * m)) := Real.rpow_pos_of_pos (Torus.jp_pos _) _
    exact mul_ne_zero h1 h2.ne'
  · intro a ha
    rw [ser_ck Δ hser ha M0, tsum_eq_single k0]
    · rw [hck, ← he]; simp
    · intro k hk
      rw [hck]; simp [hk]

end HRS.MC.Q714.CT
