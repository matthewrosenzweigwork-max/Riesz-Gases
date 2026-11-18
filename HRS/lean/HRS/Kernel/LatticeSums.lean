import HRS.PDE.Toolbox.Kernel

/-!
# Lattice sums over boxes (packet Q39, Lemma C.2 infrastructure)

Shell counting in `ℤ^d` with the sup norm: the shell `boxF (n+1) ∖ boxF n` has at most
`2 d (2n+3)^{d-1}` points, all with Euclidean norm in `[n+1, d(n+1)]`.  From this we get the
partial-sum bounds `∑_{0<|k|≲J} |k|^{σ-d} ≲ J^σ` (`σ > 0`), `≲ 1 + log J` (`σ = 0`) and the tail bound
`∑_{|k|≥T} (1+|k|)^{-d-p} ≲ (1+T)^{-p}` (`p > 0`).
-/

noncomputable section

open Finset
open scoped BigOperators

namespace HRS
namespace LatSum

open HRS.PDE.Kern

variable {d : ℕ}

theorem mem_boxF' {n : ℕ} {k : Lattice d} : k ∈ boxF d n ↔ ∀ i, |k i| ≤ (n : ℤ) := by
  simp [boxF, Fintype.mem_piFinset, abs_le]

theorem boxF_mono {m n : ℕ} (h : m ≤ n) : boxF d m ⊆ boxF d n := by
  intro k hk
  rw [mem_boxF'] at hk ⊢
  intro i
  exact (hk i).trans (by exact_mod_cast h)

theorem pow_sub_pow_le (e : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    a ^ (e + 1) - b ^ (e + 1) ≤ ((e : ℝ) + 1) * (a - b) * a ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have ha : 0 ≤ a := hb.trans hab
    have h1 : b ^ (e + 1) ≤ a ^ (e + 1) := pow_le_pow_left₀ hb hab _
    calc a ^ (e + 1 + 1) - b ^ (e + 1 + 1)
        = a * (a ^ (e + 1) - b ^ (e + 1)) + b ^ (e + 1) * (a - b) := by ring
      _ ≤ a * (((e : ℝ) + 1) * (a - b) * a ^ e) + a ^ (e + 1) * (a - b) := by
        gcongr
      _ = (((e + 1 : ℕ) : ℝ) + 1) * (a - b) * a ^ (e + 1) := by push_cast; ring

/-- number of points of the shell -/
theorem card_shell (n : ℕ) :
    (boxF d (n + 1) \ boxF d n).card = (2 * (n + 1) + 1) ^ d - (2 * n + 1) ^ d := by
  rw [Finset.card_sdiff_of_subset (boxF_mono (Nat.le_succ n)), card_boxF, card_boxF]

theorem card_shell_le (e n : ℕ) :
    (((boxF (e + 1) (n + 1) \ boxF (e + 1) n).card : ℕ) : ℝ) ≤
      2 * ((e : ℝ) + 1) * (3 * ((n : ℝ) + 1)) ^ e := by
  rw [card_shell]
  have hle : (2 * n + 1) ^ (e + 1) ≤ (2 * (n + 1) + 1) ^ (e + 1) :=
    Nat.pow_le_pow_left (by omega) _
  rw [Nat.cast_sub hle]
  push_cast
  have := pow_sub_pow_le e (a := 2 * ((n : ℝ) + 1) + 1) (b := 2 * (n : ℝ) + 1) (by positivity)
    (by linarith)
  have h2 : (2 * ((n : ℝ) + 1) + 1) - (2 * (n : ℝ) + 1) = 2 := by ring
  rw [h2] at this
  refine this.trans ?_
  have h3 : 2 * ((n : ℝ) + 1) + 1 ≤ 3 * ((n : ℝ) + 1) := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h4 : (2 * ((n : ℝ) + 1) + 1) ^ e ≤ (3 * ((n : ℝ) + 1)) ^ e :=
    pow_le_pow_left₀ (by positivity) h3 _
  nlinarith [h4, show (0 : ℝ) ≤ (e : ℝ) + 1 by positivity]

/-- points of the shell have Euclidean norm at least `n+1` -/
theorem enorm_ge_of_shell {n : ℕ} {k : Lattice d} (hk : k ∈ boxF d (n + 1) \ boxF d n) :
    (n : ℝ) + 1 ≤ Lattice.enorm k := by
  rw [Finset.mem_sdiff, mem_boxF', mem_boxF'] at hk
  obtain ⟨_, h2⟩ := hk
  push Not at h2
  obtain ⟨i, hi⟩ := h2
  have h3 : ((n : ℤ) + 1) ≤ |k i| := by omega
  have h4 : (((n : ℤ) + 1 : ℤ) : ℝ) ≤ ((|k i| : ℤ) : ℝ) := by exact_mod_cast h3
  have h5 : |(k i : ℝ)| = ((|k i| : ℤ) : ℝ) := by push_cast; rfl
  have h6 : ‖(Lattice.toEuc k) i‖ ≤ ‖Lattice.toEuc k‖ := PiLp.norm_apply_le _ i
  have h7 : ‖(Lattice.toEuc k) i‖ = |(k i : ℝ)| := by simp [Lattice.toEuc]
  push_cast at h4
  unfold Lattice.enorm
  linarith

theorem enorm_le_of_box {n : ℕ} {k : Lattice d} (hk : k ∈ boxF d n) :
    Lattice.enorm k ≤ (d : ℝ) * n := by
  rw [mem_boxF'] at hk
  have h1 : ‖(WithLp.toLp 2 (fun i => (k i : ℝ)) : Euc d)‖ ≤ ∑ j, |(k j : ℝ)| := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sqrt_le_left (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun j => |(k j : ℝ)|)
      (fun j _ => abs_nonneg _)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have h2 : ∀ j, |(k j : ℝ)| ≤ n := fun j => by
    have := hk j
    have h3 : ((|k j| : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h3
  calc Lattice.enorm k = ‖(WithLp.toLp 2 (fun i => (k i : ℝ)) : Euc d)‖ := rfl
    _ ≤ ∑ j, |(k j : ℝ)| := h1
    _ ≤ ∑ _j : Fin d, (n : ℝ) := Finset.sum_le_sum fun j _ => h2 j
    _ = d * n := by simp


theorem boxF_zero : boxF d 0 = {0} := by
  ext k
  rw [mem_boxF', Finset.mem_singleton]
  constructor
  · intro h; funext i; have := h i; simpa using this
  · rintro rfl i; simp

theorem sum_boxF_le {e : ℕ} (g : Lattice (e + 1) → ℝ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hg : ∀ n k, k ∈ boxF (e + 1) (n + 1) \ boxF (e + 1) n → g k ≤ a n) (J : ℕ) :
    ∑ k ∈ boxF (e + 1) J, g k ≤
      g 0 + ∑ n ∈ Finset.range J, 2 * ((e : ℝ) + 1) * (3 * ((n : ℝ) + 1)) ^ e * a n := by
  induction J with
  | zero => simp [boxF_zero]
  | succ J ih =>
    rw [← Finset.sum_sdiff (boxF_mono (Nat.le_succ J)), Finset.sum_range_succ]
    have h1 : ∑ k ∈ boxF (e + 1) (J + 1) \ boxF (e + 1) J, g k ≤
        (((boxF (e + 1) (J + 1) \ boxF (e + 1) J).card : ℕ) : ℝ) * a J := by
      rw [← nsmul_eq_mul]
      exact Finset.sum_le_card_nsmul _ _ _ (fun k hk => hg J k hk)
    have h2 : (((boxF (e + 1) (J + 1) \ boxF (e + 1) J).card : ℕ) : ℝ) * a J ≤
        2 * ((e : ℝ) + 1) * (3 * ((J : ℝ) + 1)) ^ e * a J :=
      mul_le_mul_of_nonneg_right (card_shell_le e J) (ha J)
    linarith


/-- one-dimensional power sums, exponent `σ - 1`, `σ > 0` -/
theorem sum_rpow_le {σ : ℝ} (hσ : 0 < σ) (J : ℕ) :
    ∑ n ∈ Finset.range J, ((n : ℝ) + 1) ^ (σ - 1) ≤ (1 + 1 / σ) * (J : ℝ) ^ σ := by
  rcases le_or_gt 1 σ with h1 | h1
  · rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ; simp [Real.zero_rpow hσ.ne']
    · have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      have : ∀ n ∈ Finset.range J, ((n : ℝ) + 1) ^ (σ - 1) ≤ (J : ℝ) ^ (σ - 1) := by
        intro n hn
        have : (n : ℝ) + 1 ≤ J := by
          have := Finset.mem_range.mp hn
          exact_mod_cast this
        exact Real.rpow_le_rpow (by positivity) this (by linarith)
      calc ∑ n ∈ Finset.range J, ((n : ℝ) + 1) ^ (σ - 1) ≤ ∑ _n ∈ Finset.range J, (J : ℝ) ^ (σ - 1) :=
            Finset.sum_le_sum this
        _ = (J : ℝ) ^ σ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Real.rpow_one_add' (by positivity) (by linarith)]
            ring_nf
        _ ≤ (1 + 1 / σ) * (J : ℝ) ^ σ := by
            have : 0 ≤ (J : ℝ) ^ σ := by positivity
            have : 0 ≤ 1 / σ := by positivity
            nlinarith
  · have key : ∀ J : ℕ, ∑ n ∈ Finset.range J, ((n : ℝ) + 1) ^ (σ - 1) ≤ (J : ℝ) ^ σ / σ := by
      intro J
      induction J with
      | zero => simp [Real.zero_rpow hσ.ne']
      | succ J ih =>
        rw [Finset.sum_range_succ]
        have hx : (-1 : ℝ) ≤ -1 / ((J : ℝ) + 1) := by
          rw [le_div_iff₀ (by positivity)]
          have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
          nlinarith
        have hb := rpow_one_add_le_one_add_mul_self hx hσ.le h1.le
        have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
        have h2 : (J : ℝ) = ((J : ℝ) + 1) * (1 + -1 / ((J : ℝ) + 1)) := by field_simp; ring
        have h3 : (J : ℝ) ^ σ = ((J : ℝ) + 1) ^ σ * (1 + -1 / ((J : ℝ) + 1)) ^ σ := by
          conv_lhs => rw [h2]
          rw [Real.mul_rpow hJ1.le (by linarith)]
        have h4 : (J : ℝ) ^ σ ≤ ((J : ℝ) + 1) ^ σ * (1 + σ * (-1 / ((J : ℝ) + 1))) := by
          rw [h3]; exact mul_le_mul_of_nonneg_left hb (by positivity)
        have h5 : ((J : ℝ) + 1) ^ (σ - 1) = ((J : ℝ) + 1) ^ σ / ((J : ℝ) + 1) := by
          rw [Real.rpow_sub hJ1, Real.rpow_one]
        have h6 : ((J : ℝ) + 1) ^ σ * (1 + σ * (-1 / ((J : ℝ) + 1))) =
            ((J : ℝ) + 1) ^ σ - σ * (((J : ℝ) + 1) ^ σ / ((J : ℝ) + 1)) := by field_simp; ring
        push_cast
        rw [h5]
        have h7 : ((J : ℝ) ^ σ / σ + ((J : ℝ) + 1) ^ σ / ((J : ℝ) + 1)) ≤ ((J : ℝ) + 1) ^ σ / σ := by
          rw [div_add' _ _ _ hσ.ne', div_le_div_iff_of_pos_right hσ]
          rw [h6] at h4
          have : 0 ≤ ((J : ℝ) + 1) ^ σ / ((J : ℝ) + 1) := by positivity
          nlinarith
        calc _ ≤ (J : ℝ) ^ σ / σ + ((J : ℝ) + 1) ^ σ / ((J : ℝ) + 1) := by linarith
          _ ≤ _ := h7
    calc _ ≤ (J : ℝ) ^ σ / σ := key J
      _ = (1 / σ) * (J : ℝ) ^ σ := by ring
      _ ≤ (1 + 1 / σ) * (J : ℝ) ^ σ := by
          have : 0 ≤ (J : ℝ) ^ σ := by positivity
          nlinarith


theorem pow_mul_rpow_shift (e : ℕ) (σ : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) ^ e * ((n : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)) = ((n : ℝ) + 1) ^ (σ - 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_add hn]
  congr 1; ring

/-- shell estimate for the weights `|k|^{σ-d}` -/
theorem shell_weight_le {e : ℕ} (σ : ℝ) {n : ℕ} {k : Lattice (e + 1)}
    (hk : k ∈ boxF (e + 1) (n + 1) \ boxF (e + 1) n) :
    (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (σ - ((e + 1 : ℕ) : ℝ))) ≤
      max 1 (((e : ℝ) + 1) ^ (σ - ((e : ℝ) + 1))) * ((n : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)) := by
  have hge := enorm_ge_of_shell hk
  have hle : Lattice.enorm k ≤ ((e + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) :=
    enorm_le_of_box (Finset.mem_sdiff.mp hk).1
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h0 : Lattice.toEuc (0 : Lattice (e + 1)) = 0 := by ext i; simp [Lattice.toEuc]
    have : Lattice.enorm (0 : Lattice (e + 1)) = 0 := by simp [Lattice.enorm, h0]
    rw [this] at hge
    linarith
  rw [if_neg hk0]
  push_cast at hle ⊢
  rcases le_or_gt 0 (σ - ((e : ℝ) + 1)) with hs | hs
  · calc Lattice.enorm k ^ (σ - ((e : ℝ) + 1)) ≤ (((e : ℝ) + 1) * ((n : ℝ) + 1)) ^ (σ - ((e : ℝ) + 1)) :=
          Real.rpow_le_rpow (norm_nonneg _) hle hs
      _ = ((e : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)) * ((n : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)) :=
          Real.mul_rpow (by positivity) hn.le
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _
  · calc Lattice.enorm k ^ (σ - ((e : ℝ) + 1)) ≤ ((n : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)) :=
          Real.rpow_le_rpow_of_nonpos hn hge hs.le
      _ = 1 * ((n : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)) := (one_mul _).symm
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _

theorem low_sum_aux {e : ℕ} (σ : ℝ) (J : ℕ) :
    ∑ k ∈ boxF (e + 1) J, (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (σ - ((e + 1 : ℕ) : ℝ))) ≤
      (2 * ((e : ℝ) + 1) * 3 ^ e * max 1 (((e : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)))) *
        ∑ n ∈ Finset.range J, ((n : ℝ) + 1) ^ (σ - 1) := by
  set D := max 1 (((e : ℝ) + 1) ^ (σ - ((e : ℝ) + 1))) with hD
  have hD0 : 0 ≤ D := le_trans zero_le_one (le_max_left _ _)
  have := sum_boxF_le (e := e) (fun k => if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (σ - ((e + 1 : ℕ) : ℝ)))
    (fun n => D * ((n : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)))
    (fun n => mul_nonneg hD0 (Real.rpow_nonneg (by positivity) _))
    (fun n k hk => shell_weight_le σ hk) J
  refine this.trans ?_
  simp only [if_true, zero_add]
  rw [Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun n _ => ?_)
  rw [mul_pow]
  calc 2 * ((e : ℝ) + 1) * (3 ^ e * ((n : ℝ) + 1) ^ e) * (D * ((n : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)))
      = (2 * ((e : ℝ) + 1) * 3 ^ e * D) * (((n : ℝ) + 1) ^ e * ((n : ℝ) + 1) ^ (σ - ((e : ℝ) + 1))) := by ring
    _ = _ := by rw [pow_mul_rpow_shift]

/-- partial sums of `|k|^{σ-d}`, `σ > 0` -/
theorem low_sum (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ J : ℕ,
      ∑ k ∈ boxF d J, (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (σ - (d : ℝ))) ≤ A * (J : ℝ) ^ σ := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  refine ⟨(2 * ((e : ℝ) + 1) * 3 ^ e * max 1 (((e : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)))) * (1 + 1 / σ),
    by positivity, fun J => ?_⟩
  refine (low_sum_aux σ J).trans ?_
  calc _ ≤ (2 * ((e : ℝ) + 1) * 3 ^ e * max 1 (((e : ℝ) + 1) ^ (σ - ((e : ℝ) + 1)))) *
        ((1 + 1 / σ) * (J : ℝ) ^ σ) :=
        mul_le_mul_of_nonneg_left (sum_rpow_le hσ J) (by positivity)
    _ = _ := by ring

/-- the logarithmic case `σ = 0` -/
theorem low_sum_log (hd : 1 ≤ d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ J : ℕ, 1 ≤ J →
      ∑ k ∈ boxF d J, (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ ((0 : ℝ) - (d : ℝ))) ≤
        A * (1 + Real.log J) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  refine ⟨2 * ((e : ℝ) + 1) * 3 ^ e * max 1 (((e : ℝ) + 1) ^ (0 - ((e : ℝ) + 1))), by positivity, fun J hJ => ?_⟩
  refine (low_sum_aux 0 J).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ∑ n ∈ Finset.range J, ((n : ℝ) + 1) ^ ((0 : ℝ) - 1) = ((harmonic J : ℚ) : ℝ) := by
    rw [harmonic]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [zero_sub, Real.rpow_neg_one]
  rw [h1]
  exact_mod_cast harmonic_le_one_add_log J


/-- telescoping step for the tail of `∑ j^{-1-p}`, `p ≥ 1` -/
theorem tail_step {p : ℝ} (hp : 1 ≤ p) {x : ℝ} (hx : 1 ≤ x) :
    p * (x + 1) ^ (-1 - p) ≤ x ^ (-p) - (x + 1) ^ (-p) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hb := one_add_mul_self_le_rpow_one_add (s := 1 / x) (by
    have : 0 ≤ 1 / x := by positivity
    linarith) hp
  have h1 : (x + 1) ^ p = x ^ p * (1 + 1 / x) ^ p := by
    rw [← Real.mul_rpow hx0.le (by positivity)]
    congr 1; field_simp
  have h2 : x ^ p * (1 + p * (1 / x)) ≤ (x + 1) ^ p := by
    rw [h1]; exact mul_le_mul_of_nonneg_left hb (by positivity)
  set A := x ^ p with hA
  set Bv := (x + 1) ^ p with hBv
  have hA0 : 0 < A := Real.rpow_pos_of_pos hx0 _
  have hB0 : 0 < Bv := Real.rpow_pos_of_pos hx1 _
  have e1 : x ^ (-p) = 1 / A := by rw [Real.rpow_neg hx0.le, one_div]
  have e2 : (x + 1) ^ (-p) = 1 / Bv := by rw [Real.rpow_neg hx1.le, one_div]
  have e3 : (x + 1) ^ (-1 - p) = 1 / ((x + 1) * Bv) := by
    rw [show (-1 - p) = -(1 + p) by ring, Real.rpow_neg hx1.le, Real.rpow_add hx1, Real.rpow_one,
      one_div, mul_inv]
  rw [e1, e2, e3]
  have h3 : Bv - A ≥ p * A / x := by
    have : A * (1 + p * (1 / x)) = A + p * A / x := by field_simp
    rw [this] at h2; linarith
  rw [div_sub_div _ _ hA0.ne' hB0.ne', mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : p * (A * Bv) ≤ (1 * Bv - A * 1) * ((x + 1) * Bv) := by
    have h5 : 1 * Bv - A * 1 ≥ p * A / x := by linarith
    have h6 : p * A / x * ((x + 1) * Bv) ≥ p * (A * Bv) := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hx0]
      have : 0 ≤ p * (A * Bv) := by positivity
      nlinarith
    calc p * (A * Bv) ≤ p * A / x * ((x + 1) * Bv) := h6
      _ ≤ (1 * Bv - A * 1) * ((x + 1) * Bv) := mul_le_mul_of_nonneg_right h5 (by positivity)
  nlinarith [h4]


theorem tail_1d_aux {p : ℝ} (hp : 1 ≤ p) {j0 : ℕ} (hj0 : 1 ≤ j0) (M : ℕ) :
    ∑ n ∈ Finset.range M, (if j0 ≤ n + 1 then ((n : ℝ) + 1) ^ (-1 - p) else 0) ≤
      if M < j0 then 0 else ((j0 : ℝ) ^ (-1 - p) + (((j0 : ℝ) ^ (-p) - (M : ℝ) ^ (-p)) / p)) := by
  have hp0 : 0 < p := by linarith
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    split_ifs with h
    · exact le_rfl
    · exact absurd (by omega) h
  | succ M ih =>
    rw [Finset.sum_range_succ]
    by_cases h1 : M + 1 < j0
    · have h2 : M < j0 := by omega
      have h3 : ¬ (j0 ≤ M + 1) := by omega
      rw [if_pos h2] at ih
      simp only [h3, if_false, add_zero, if_pos h1]
      exact ih
    · by_cases h2 : M + 1 = j0
      · have h3 : M < j0 := by omega
        rw [if_pos h3] at ih
        have h4 : j0 ≤ M + 1 := by omega
        simp only [if_pos h4, if_neg h1]
        have h5 : (((M + 1 : ℕ) : ℝ)) = (j0 : ℝ) := by rw [h2]
        have e : ((M : ℝ) + 1) = (j0 : ℝ) := by rw [← h5]; push_cast; ring
        rw [e]
        have : (((j0 : ℝ) ^ (-p) - ((M + 1 : ℕ) : ℝ) ^ (-p)) / p) = 0 := by rw [h5]; simp
        rw [this]
        linarith
      · have h3 : j0 ≤ M := by omega
        have h4 : ¬ (M < j0) := by omega
        rw [if_neg h4] at ih
        have h5 : j0 ≤ M + 1 := by omega
        simp only [if_pos h5, if_neg h1]
        have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (le_trans hj0 h3)
        have := tail_step hp hM1
        push_cast
        have h6 : p * ((M : ℝ) + 1) ^ (-1 - p) / p = ((M : ℝ) + 1) ^ (-1 - p) := by field_simp
        have h7 : ((M : ℝ) + 1) ^ (-1 - p) ≤ ((M : ℝ) ^ (-p) - ((M : ℝ) + 1) ^ (-p)) / p := by
          rw [le_div_iff₀ hp0]; linarith
        have : ((j0 : ℝ) ^ (-1 - p) + (((j0 : ℝ) ^ (-p) - (M : ℝ) ^ (-p)) / p)) + ((M : ℝ) + 1) ^ (-1 - p)
            ≤ (j0 : ℝ) ^ (-1 - p) + (((j0 : ℝ) ^ (-p) - ((M : ℝ) + 1) ^ (-p)) / p) := by
          have : ((j0 : ℝ) ^ (-p) - ((M : ℝ) + 1) ^ (-p)) / p =
              ((j0 : ℝ) ^ (-p) - (M : ℝ) ^ (-p)) / p + ((M : ℝ) ^ (-p) - ((M : ℝ) + 1) ^ (-p)) / p := by
            ring
          rw [this]; linarith
        linarith

theorem tail_1d {p : ℝ} (hp : 1 ≤ p) {j0 : ℕ} (hj0 : 1 ≤ j0) (M : ℕ) :
    ∑ n ∈ Finset.range M, (if j0 ≤ n + 1 then ((n : ℝ) + 1) ^ (-1 - p) else 0) ≤
      2 * (j0 : ℝ) ^ (-p) := by
  refine (tail_1d_aux hp hj0 M).trans ?_
  have hj : (1 : ℝ) ≤ j0 := by exact_mod_cast hj0
  have hj1 : (0 : ℝ) < j0 := by linarith
  have h0 : 0 ≤ (j0 : ℝ) ^ (-p) := by positivity
  split_ifs with h
  · exact mul_nonneg (by norm_num) h0
  · have h1 : (j0 : ℝ) ^ (-1 - p) ≤ (j0 : ℝ) ^ (-p) :=
      Real.rpow_le_rpow_of_exponent_le hj (by linarith)
    have h2 : 0 ≤ (M : ℝ) ^ (-p) := by positivity
    have h3 : ((j0 : ℝ) ^ (-p) - (M : ℝ) ^ (-p)) / p ≤ (j0 : ℝ) ^ (-p) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith


theorem enorm_zero' : Lattice.enorm (0 : Lattice d) = 0 := by
  have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
  simp [Lattice.enorm, h0]

theorem tail_sum_aux {e : ℕ} {p : ℝ} (hp : 0 ≤ p) (T : ℝ) (M : ℕ) :
    ∑ k ∈ boxF (e + 1) M, (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-((e + 1 : ℕ) : ℝ) - p) else 0) ≤
      (if T ≤ 0 then 1 else 0) +
      (2 * ((e : ℝ) + 1) * 3 ^ e) * ∑ n ∈ Finset.range M,
        (if T ≤ ((e : ℝ) + 1) * ((n : ℝ) + 1) then ((n : ℝ) + 1) ^ (-p - 1) else 0) := by
  have := sum_boxF_le (e := e)
    (fun k => if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-((e + 1 : ℕ) : ℝ) - p) else 0)
    (fun n => if T ≤ ((e : ℝ) + 1) * ((n : ℝ) + 1) then ((n : ℝ) + 1) ^ (-((e : ℝ) + 1) - p) else 0)
    (fun n => by split_ifs <;> positivity)
    (fun n k hk => by
      have hge := enorm_ge_of_shell hk
      have hle : Lattice.enorm k ≤ ((e + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) :=
        enorm_le_of_box (Finset.mem_sdiff.mp hk).1
      push_cast at hle
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      by_cases hTk : T ≤ Lattice.enorm k
      · have hTn : T ≤ ((e : ℝ) + 1) * ((n : ℝ) + 1) := hTk.trans hle
        simp only [hTk, hTn, if_true]
        push_cast
        apply Real.rpow_le_rpow_of_nonpos hn (by linarith)
        have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
        linarith
      · rw [if_neg hTk]
        split_ifs <;> positivity) M
  refine this.trans ?_
  rw [enorm_zero']
  have h1 : ∀ n ∈ Finset.range M, 2 * ((e : ℝ) + 1) * (3 * ((n : ℝ) + 1)) ^ e *
      (if T ≤ ((e : ℝ) + 1) * ((n : ℝ) + 1) then ((n : ℝ) + 1) ^ (-((e : ℝ) + 1) - p) else 0) =
      (2 * ((e : ℝ) + 1) * 3 ^ e) *
      (if T ≤ ((e : ℝ) + 1) * ((n : ℝ) + 1) then ((n : ℝ) + 1) ^ (-p - 1) else 0) := by
    intro n _
    split_ifs
    · rw [mul_pow]
      calc 2 * ((e : ℝ) + 1) * (3 ^ e * ((n : ℝ) + 1) ^ e) * ((n : ℝ) + 1) ^ (-((e : ℝ) + 1) - p)
          = (2 * ((e : ℝ) + 1) * 3 ^ e) * (((n : ℝ) + 1) ^ e * ((n : ℝ) + 1) ^ (-p - ((e : ℝ) + 1))) := by
            rw [show -((e : ℝ) + 1) - p = -p - ((e : ℝ) + 1) by ring]; ring
        _ = _ := by rw [pow_mul_rpow_shift]
    · simp
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have h0 : (if T ≤ (0 : ℝ) then (1 + (0 : ℝ)) ^ (-((e + 1 : ℕ) : ℝ) - p) else 0) ≤ (if T ≤ 0 then (1 : ℝ) else 0) := by
    split_ifs <;> simp
  linarith


/-- tail sums `∑_{|k| ≥ T} (1+|k|)^{-d-p} ≲ (1+T)^{-p}`, `p ≥ 1` -/
theorem tail_sum (hd : 1 ≤ d) {p : ℝ} (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (M : ℕ) (T : ℝ), 0 ≤ T →
      ∑ k ∈ boxF d M, (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - p) else 0) ≤
        A * (1 + T) ^ (-p) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hp0 : 0 < p := by linarith
  set c : ℝ := 2 * ((e : ℝ) + 1) * 3 ^ e with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨1 + c * (2 * (2 ^ p * ((e : ℝ) + 1) ^ p)), by positivity, fun M T hT => ?_⟩
  refine (tail_sum_aux (e := e) hp0.le T M).trans ?_
  set x : ℝ := T / ((e : ℝ) + 1) with hx
  have he1 : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  have hx0 : 0 ≤ x := by positivity
  set j0 : ℕ := max 1 ⌈x⌉₊ with hj0
  have hj01 : 1 ≤ j0 := le_max_left _ _
  have hjx : x ≤ (j0 : ℝ) := by
    have := Nat.le_ceil x
    exact this.trans (by exact_mod_cast le_max_right 1 ⌈x⌉₊)
  have hj1 : (1 : ℝ) ≤ j0 := by exact_mod_cast hj01
  -- the indicator is dominated
  have hind : ∑ n ∈ Finset.range M,
      (if T ≤ ((e : ℝ) + 1) * ((n : ℝ) + 1) then ((n : ℝ) + 1) ^ (-p - 1) else 0) ≤
      ∑ n ∈ Finset.range M, (if j0 ≤ n + 1 then ((n : ℝ) + 1) ^ (-1 - p) else 0) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have e1 : (-p - 1) = (-1 - p) := by ring
    rw [e1]
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      apply h2
      have h3 : x ≤ (n : ℝ) + 1 := by
        rw [hx, div_le_iff₀ he1]; linarith
      have h4 : ⌈x⌉₊ ≤ n + 1 := Nat.ceil_le.mpr (by exact_mod_cast h3)
      exact max_le (by omega) h4
    · positivity
    · exact le_rfl
  have h5 := tail_1d hp hj01 M
  have h6 : (j0 : ℝ) ^ (-p) ≤ 2 ^ p * (1 + x) ^ (-p) := by
    have h7 : (1 + x) / 2 ≤ (j0 : ℝ) := by linarith
    calc (j0 : ℝ) ^ (-p) ≤ ((1 + x) / 2) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) h7 (by linarith)
      _ = 2 ^ p * (1 + x) ^ (-p) := by
          rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) p,
            div_inv_eq_mul, mul_comm]
  have h8 : (1 + x) ^ (-p) ≤ ((e : ℝ) + 1) ^ p * (1 + T) ^ (-p) := by
    have h9 : (1 + T) / ((e : ℝ) + 1) ≤ 1 + x := by
      rw [div_le_iff₀ he1]
      have : (1 + x) * ((e : ℝ) + 1) = (e : ℝ) + 1 + T := by rw [hx]; field_simp
      rw [this]
      have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      linarith
    calc (1 + x) ^ (-p) ≤ ((1 + T) / ((e : ℝ) + 1)) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h9 (by linarith)
      _ = ((e : ℝ) + 1) ^ p * (1 + T) ^ (-p) := by
          rw [Real.div_rpow (by positivity) he1.le, Real.rpow_neg he1.le, Real.rpow_neg (by positivity)]
          field_simp
  have hW : 0 ≤ (1 + T) ^ (-p) := by positivity
  have hg0 : (if T ≤ 0 then (1 : ℝ) else 0) ≤ (1 + T) ^ (-p) := by
    split_ifs with h
    · have : T = 0 := le_antisymm h hT
      subst this; simp
    · exact hW
  have hsum : ∑ n ∈ Finset.range M,
      (if T ≤ ((e : ℝ) + 1) * ((n : ℝ) + 1) then ((n : ℝ) + 1) ^ (-p - 1) else 0) ≤
      2 * (2 ^ p * (((e : ℝ) + 1) ^ p * (1 + T) ^ (-p))) := by
    refine hind.trans (h5.trans ?_)
    have : (2 : ℝ) * (j0 : ℝ) ^ (-p) ≤ 2 * (2 ^ p * (1 + x) ^ (-p)) := by linarith
    refine this.trans ?_
    have h2p : (0 : ℝ) ≤ 2 ^ p := by positivity
    nlinarith
  calc _ ≤ (1 + T) ^ (-p) + c * (2 * (2 ^ p * (((e : ℝ) + 1) ^ p * (1 + T) ^ (-p)))) := by
        have := mul_le_mul_of_nonneg_left hsum hc0
        linarith
    _ = _ := by ring

end LatSum
end HRS
