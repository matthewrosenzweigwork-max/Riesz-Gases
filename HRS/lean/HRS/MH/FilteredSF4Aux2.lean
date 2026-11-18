import HRS.MH.FilteredSF4Aux1

/-!
# Packet SF4, helper 2: the derivative bound for one dyadic shell block
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.Uniform HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

lemma sf4_block_bound (n : ℕ) {γ : ℝ} (hγ : (d : ℝ) / 2 + n + 1 < γ) {C : ℝ}
    (hC : ∀ R : ℝ, 0 < R → {k : NonzeroLattice d | Lattice.jp k.1 ≤ R}.Finite ∧
      (({k : NonzeroLattice d | Lattice.jp k.1 ≤ R}).ncard : ℝ) ≤
        C * R ^ ((d : ℝ) / 2 + (γ - 1 - n)))
    (j : Fin d) (s : ℕ) (i : ℕ) (hi : i ≤ n) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (fun z => ∑ k ∈ (sf4_shell_finite hC s).1.toFinset, gfb3_term γ j k z) y‖ ≤
      Real.sqrt (2 * C * (2 : ℝ) ^ ((d : ℝ) / 2 + (γ - 1 - n))) *
        (Real.sqrt ((2 : ℝ) ^ ((d : ℝ) / 2 - (γ - 1 - n)))) ^ s := by
  classical
  obtain ⟨hf, hcard⟩ := sf4_shell_finite hC s
  set a : ℝ := γ - 1 - n with ha
  set t : ℝ := (d : ℝ) / 2 + a with ht
  set I := (sf4_shell_finite hC s).1.toFinset with hI
  have hg : ∀ k, ContDiff ℝ n (sf4_g γ j k) := fun k =>
    contDiff_const.mul (gfb3_contDiff_Dmode k j n)
  set q : ℝ := (2 : ℝ) ^ (-a) with hq
  set B : NonzeroLattice d → ℝ := fun k =>
    Real.sqrt 2 * Lattice.jp k.1 ^ (-γ) * Lattice.jp k.1 ^ (i + 1) with hBdef
  have h3 := sf3_block_iter_norm (sf4_e γ) (sf4_e_orthonormal γ) I (sf4_g γ j) n hg B i hi
    (fun k y => sf4_norm_iter_g γ j k i y) y
  have h3' : ‖iteratedFDeriv ℝ i (fun z => ∑ k ∈ I, gfb3_term γ j k z) y‖ ≤
      Real.sqrt (∑ k ∈ I, B k ^ 2) := h3
  refine h3'.trans ?_
  have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hB : ∀ k ∈ I, B k ≤ Real.sqrt 2 * q ^ s := by
    intro k hk
    have hks : sf4_shell k = s := by
      rw [hI, Set.Finite.mem_toFinset] at hk; exact hk
    have hb := sf4_shell_bounds k
    rw [hks] at hb
    have hj1 : 1 ≤ Lattice.jp k.1 := Torus.jp_ge_one k.1
    have hj0 : 0 < Lattice.jp k.1 := lt_of_lt_of_le one_pos hj1
    have e1 : B k = Real.sqrt 2 * Lattice.jp k.1 ^ (-γ + ((i + 1 : ℕ) : ℝ)) := by
      simp only [hBdef]
      rw [mul_assoc, ← Real.rpow_natCast (Lattice.jp k.1) (i + 1), ← Real.rpow_add hj0]
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have h1 : Lattice.jp k.1 ^ (-γ + ((i + 1 : ℕ) : ℝ)) ≤ Lattice.jp k.1 ^ (-a) := by
      refine Real.rpow_le_rpow_of_exponent_le hj1 ?_
      push_cast
      rw [ha]; linarith
    have h2 : Lattice.jp k.1 ^ (-a) ≤ ((2 : ℝ) ^ s) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb.1 (by rw [ha]; linarith)
    have h4 : ((2 : ℝ) ^ s) ^ (-a) = q ^ s := by
      rw [hq, Real.rpow_pow_comm (by norm_num) (-a) s]
    exact h1.trans (h2.trans h4.le)
  have hsum : ∑ k ∈ I, B k ^ 2 ≤ (I.card : ℝ) * (2 * (q ^ s) ^ 2) := by
    have hle : ∑ k ∈ I, B k ^ 2 ≤ ∑ _k ∈ I, (Real.sqrt 2 * q ^ s) ^ 2 := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hB0 : 0 ≤ B k := by
        simp only [hBdef]
        have := Torus.jp_pos k.1
        positivity
      exact pow_le_pow_left₀ hB0 (hB k hk) 2
    refine hle.trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_pow, Real.sq_sqrt (by norm_num)]
  have hcardI : (I.card : ℝ) = (({k : NonzeroLattice d | sf4_shell k = s}).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hf]
  set T : ℝ := (2 : ℝ) ^ t with hT
  have hT0 : 0 < T := by positivity
  have hq0 : 0 < q := by positivity
  have hcard2 : (I.card : ℝ) ≤ C * T ^ (s + 1) := by
    rw [hcardI]
    refine hcard.trans (le_of_eq ?_)
    rw [hT, ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) t (s + 1)]
  have hC0 : 0 ≤ C := by
    have := (hC 1 one_pos).2
    have h0 : (0 : ℝ) ≤ (({k : NonzeroLattice d | Lattice.jp k.1 ≤ 1}).ncard : ℝ) := Nat.cast_nonneg _
    simp only [Real.one_rpow, mul_one] at this
    linarith
  set P : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2 - a) with hP
  have hPeq : T * q ^ 2 = P := by
    rw [hP, hT, hq, ← Real.rpow_natCast ((2 : ℝ) ^ (-a)) 2, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    rw [ht]; push_cast; ring
  have hPs : P ^ s = T ^ s * (q ^ s) ^ 2 := by
    rw [← hPeq, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 s]
  have hP0 : 0 ≤ P ^ s := by positivity
  have hmain : ∑ k ∈ I, B k ^ 2 ≤ 2 * C * T * P ^ s := by
    refine hsum.trans ?_
    calc (I.card : ℝ) * (2 * (q ^ s) ^ 2) ≤ (C * T ^ (s + 1)) * (2 * (q ^ s) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard2 (by positivity)
      _ = 2 * C * T * P ^ s := by rw [hPs]; ring
  have hρ : Real.sqrt (P ^ s) = Real.sqrt P ^ s := by
    have hP1 : 0 ≤ P := by positivity
    have h5 : P ^ s = (Real.sqrt P ^ s) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hP1]
    rw [h5, Real.sqrt_sq (by positivity)]
  calc Real.sqrt (∑ k ∈ I, B k ^ 2) ≤ Real.sqrt (2 * C * T * P ^ s) := Real.sqrt_le_sqrt hmain
    _ = Real.sqrt (2 * C * T) * Real.sqrt (P ^ s) := Real.sqrt_mul (by positivity) _
    _ = _ := by rw [hρ]

end HRS.MH.FilteredP
