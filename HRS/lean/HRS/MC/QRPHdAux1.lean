import HRS.Kernel.LatticeSums
import HRS.MC.QRVocab

/-!
# Packet HD, part 1: lattice sums (tails for every exponent `p > 0`, low-frequency sums)

`HRS.LatSum.tail_sum` needs the decay exponent `p ≥ 1`; the HD estimate needs `p = d - 2s ∈ (0, d]`.  Here the
telescoping argument is redone for every `p > 0` (the constant becomes `1 + 1/p`), and the sums over `boxF d M` are
turned into `tsum`s over the whole lattice.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace HRS.MC.QRSpec.Hd

open HRS HRS.LatSum HRS.PDE.Kern

variable {d : ℕ}

theorem hd_tail_step {p : ℝ} (hp : 0 < p) {x : ℝ} (hx : 1 ≤ x) :
    p * (x + 1) ^ (-1 - p) ≤ x ^ (-p) - (x + 1) ^ (-p) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hlog : 1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div hx1.ne' hx0.ne'] at h
    have : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
    rw [this] at h
    exact h
  have e1 : x ^ (-p) = (x + 1) ^ (-p) * Real.exp (p * (Real.log (x + 1) - Real.log x)) := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx1, ← Real.exp_add]
    congr 1; ring
  have e2 : (x + 1) ^ (-1 - p) = (x + 1) ^ (-p) * (1 / (x + 1)) := by
    rw [show (-1 - p) = -p + (-1) by ring, Real.rpow_add hx1, Real.rpow_neg_one]
    ring
  have hB : 0 < (x + 1) ^ (-p) := Real.rpow_pos_of_pos hx1 _
  have h3 : 1 + p * (1 / (x + 1)) ≤ Real.exp (p * (Real.log (x + 1) - Real.log x)) := by
    have := Real.add_one_le_exp (p * (Real.log (x + 1) - Real.log x))
    have h4 : p * (1 / (x + 1)) ≤ p * (Real.log (x + 1) - Real.log x) :=
      mul_le_mul_of_nonneg_left hlog hp.le
    linarith
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left h3 hB.le]

theorem hd_tail_1d_aux {p : ℝ} (hp : 0 < p) {j0 : ℕ} (hj0 : 1 ≤ j0) (M : ℕ) :
    ∑ n ∈ Finset.range M, (if j0 ≤ n + 1 then ((n : ℝ) + 1) ^ (-1 - p) else 0) ≤
      if M < j0 then 0 else ((j0 : ℝ) ^ (-1 - p) + (((j0 : ℝ) ^ (-p) - (M : ℝ) ^ (-p)) / p)) := by
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
        have := hd_tail_step hp hM1
        push_cast
        have h6 : p * ((M : ℝ) + 1) ^ (-1 - p) / p = ((M : ℝ) + 1) ^ (-1 - p) := by field_simp
        have h7 : ((M : ℝ) + 1) ^ (-1 - p) ≤ ((M : ℝ) ^ (-p) - ((M : ℝ) + 1) ^ (-p)) / p := by
          rw [le_div_iff₀ hp]; linarith
        have : ((j0 : ℝ) ^ (-1 - p) + (((j0 : ℝ) ^ (-p) - (M : ℝ) ^ (-p)) / p)) + ((M : ℝ) + 1) ^ (-1 - p)
            ≤ (j0 : ℝ) ^ (-1 - p) + (((j0 : ℝ) ^ (-p) - ((M : ℝ) + 1) ^ (-p)) / p) := by
          have : ((j0 : ℝ) ^ (-p) - ((M : ℝ) + 1) ^ (-p)) / p =
              ((j0 : ℝ) ^ (-p) - (M : ℝ) ^ (-p)) / p + ((M : ℝ) ^ (-p) - ((M : ℝ) + 1) ^ (-p)) / p := by
            ring
          rw [this]; linarith
        linarith

theorem hd_tail_1d {p : ℝ} (hp : 0 < p) {j0 : ℕ} (hj0 : 1 ≤ j0) (M : ℕ) :
    ∑ n ∈ Finset.range M, (if j0 ≤ n + 1 then ((n : ℝ) + 1) ^ (-1 - p) else 0) ≤
      (1 + 1 / p) * (j0 : ℝ) ^ (-p) := by
  refine (hd_tail_1d_aux hp hj0 M).trans ?_
  have hj : (1 : ℝ) ≤ j0 := by exact_mod_cast hj0
  have hj1 : (0 : ℝ) < j0 := by linarith
  have h0 : 0 ≤ (j0 : ℝ) ^ (-p) := by positivity
  have hp1 : 0 ≤ 1 / p := by positivity
  split_ifs with h
  · exact mul_nonneg (by linarith) h0
  · have h1 : (j0 : ℝ) ^ (-1 - p) ≤ (j0 : ℝ) ^ (-p) :=
      Real.rpow_le_rpow_of_exponent_le hj (by linarith)
    have h2 : 0 ≤ (M : ℝ) ^ (-p) := by positivity
    have h3 : ((j0 : ℝ) ^ (-p) - (M : ℝ) ^ (-p)) / p ≤ (1 / p) * (j0 : ℝ) ^ (-p) := by
      rw [div_eq_mul_inv, one_div]
      nlinarith [inv_nonneg.mpr hp.le]
    nlinarith

/-- tail sums `∑_{|k| ≥ T} (1+|k|)^{-d-p} ≲ (1+T)^{-p}` for every `p > 0`. -/
theorem hd_tail_sum (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (M : ℕ) (T : ℝ), 0 ≤ T →
      ∑ k ∈ boxF d M, (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - p) else 0) ≤
        A * (1 + T) ^ (-p) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  set c : ℝ := 2 * ((e : ℝ) + 1) * 3 ^ e with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨1 + c * ((1 + 1 / p) * (2 ^ p * ((e : ℝ) + 1) ^ p)), by positivity, fun M T hT => ?_⟩
  refine (tail_sum_aux (e := e) hp.le T M).trans ?_
  set x : ℝ := T / ((e : ℝ) + 1) with hx
  have he1 : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  have hx0 : 0 ≤ x := by positivity
  set j0 : ℕ := max 1 ⌈x⌉₊ with hj0
  have hj01 : 1 ≤ j0 := le_max_left _ _
  have hjx : x ≤ (j0 : ℝ) := by
    have := Nat.le_ceil x
    exact this.trans (by exact_mod_cast le_max_right 1 ⌈x⌉₊)
  have hj1 : (1 : ℝ) ≤ j0 := by exact_mod_cast hj01
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
  have h5 := hd_tail_1d hp hj01 M
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
      (1 + 1 / p) * (2 ^ p * (((e : ℝ) + 1) ^ p * (1 + T) ^ (-p))) := by
    refine hind.trans (h5.trans ?_)
    have hq : 0 ≤ 1 + 1 / p := by positivity
    have : (1 + 1 / p) * (j0 : ℝ) ^ (-p) ≤ (1 + 1 / p) * (2 ^ p * (1 + x) ^ (-p)) :=
      mul_le_mul_of_nonneg_left h6 hq
    refine this.trans ?_
    have h2p : (0 : ℝ) ≤ 2 ^ p := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h8 h2p) hq
  calc _ ≤ (1 + T) ^ (-p) + c * ((1 + 1 / p) * (2 ^ p * (((e : ℝ) + 1) ^ p * (1 + T) ^ (-p)))) := by
        have := mul_le_mul_of_nonneg_left hsum hc0
        linarith
    _ = _ := by ring

/-- Every finite subset of the lattice lies in a box. -/
theorem hd_exists_box (u : Finset (Lattice d)) : ∃ M : ℕ, u ⊆ boxF d M := by
  classical
  refine ⟨u.sup fun k => Finset.univ.sup fun i => (k i).natAbs, fun k hk => ?_⟩
  rw [LatSum.mem_boxF']
  intro i
  have h1 : (k i).natAbs ≤ Finset.univ.sup fun i => (k i).natAbs :=
    Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)
  have h2 : (Finset.univ.sup fun i => (k i).natAbs) ≤ u.sup fun k => Finset.univ.sup fun i => (k i).natAbs :=
    Finset.le_sup (f := fun k => Finset.univ.sup fun i => (k i).natAbs) hk
  have := h1.trans h2
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this

/-- A nonnegative function on the lattice with uniformly bounded box sums is summable, with `tsum ≤` the bound. -/
theorem hd_summable_of_box {f : Lattice d → ℝ} (hf : ∀ k, 0 ≤ f k) {B : ℝ}
    (h : ∀ M : ℕ, ∑ k ∈ boxF d M, f k ≤ B) : Summable f ∧ ∑' k, f k ≤ B := by
  have h' : ∀ u : Finset (Lattice d), ∑ k ∈ u, f k ≤ B := by
    intro u
    obtain ⟨M, hM⟩ := hd_exists_box u
    exact (Finset.sum_le_sum_of_subset_of_nonneg hM fun k _ _ => hf k).trans (h M)
  exact ⟨summable_of_sum_le hf h', Real.tsum_le_of_sum_le hf h'⟩

theorem hd_enorm_nonneg (k : Lattice d) : 0 ≤ Lattice.enorm k := norm_nonneg _

theorem hd_enorm_ge_one {k : Lattice d} (hk : k ≠ 0) : 1 ≤ Lattice.enorm k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(k i : ℝ)| := h1
    _ = ‖(Lattice.toEuc k) i‖ := by simp [Lattice.toEuc]
    _ ≤ ‖Lattice.toEuc k‖ := PiLp.norm_apply_le _ i

/-- Euclidean tail: `∑_{|k| ≥ T} |k|^{-(d+p)} ≲ T^{-p}` for `T ≥ 1`, `p > 0`. -/
theorem hd_tail_tsum (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, 1 ≤ T →
      Summable (fun k : Lattice d => if T ≤ Lattice.enorm k then Lattice.enorm k ^ (-(d : ℝ) - p) else 0) ∧
      ∑' k : Lattice d, (if T ≤ Lattice.enorm k then Lattice.enorm k ^ (-(d : ℝ) - p) else 0) ≤
        A * T ^ (-p) := by
  obtain ⟨A0, hA0, hA⟩ := hd_tail_sum (d := d) hd hp
  set q : ℝ := (d : ℝ) + p with hq
  have hq0 : 0 ≤ q := by positivity
  refine ⟨2 ^ q * A0, by positivity, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hpt : ∀ k : Lattice d, (if T ≤ Lattice.enorm k then Lattice.enorm k ^ (-(d : ℝ) - p) else 0) ≤
      2 ^ q * (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - p) else 0) := by
    intro k
    by_cases hk : T ≤ Lattice.enorm k
    · simp only [hk, if_true]
      have hk1 : 1 ≤ Lattice.enorm k := hT.trans hk
      have hk0 : 0 < Lattice.enorm k := by linarith
      have h2 : 1 + Lattice.enorm k ≤ 2 * Lattice.enorm k := by linarith
      have e : -(d : ℝ) - p = -q := by rw [hq]; ring
      rw [e]
      calc Lattice.enorm k ^ (-q) = 2 ^ q * (2 * Lattice.enorm k) ^ (-q) := by
            rw [Real.mul_rpow (by norm_num) hk0.le, Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num) q]
            field_simp
        _ ≤ 2 ^ q * (1 + Lattice.enorm k) ^ (-q) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos (by linarith) h2 (by linarith)) (by positivity)
    · simp [hk]
  have hnn : ∀ k : Lattice d, 0 ≤ (if T ≤ Lattice.enorm k then Lattice.enorm k ^ (-(d : ℝ) - p) else 0) := by
    intro k; split_ifs
    · exact Real.rpow_nonneg (hd_enorm_nonneg k) _
    · exact le_rfl
  have := hd_summable_of_box (d := d) (f := fun k : Lattice d =>
    if T ≤ Lattice.enorm k then Lattice.enorm k ^ (-(d : ℝ) - p) else 0) hnn
    (B := 2 ^ q * (A0 * (1 + T) ^ (-p))) (fun M => by
      calc _ ≤ ∑ k ∈ boxF d M, 2 ^ q * (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - p) else 0) :=
            Finset.sum_le_sum fun k _ => hpt k
        _ = 2 ^ q * ∑ k ∈ boxF d M, (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - p) else 0) := by
            rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hA M T hT0) (by positivity))
  refine ⟨this.1, this.2.trans ?_⟩
  have h3 : (1 + T) ^ (-p) ≤ T ^ (-p) := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  calc 2 ^ q * (A0 * (1 + T) ^ (-p)) ≤ 2 ^ q * (A0 * T ^ (-p)) := by gcongr
    _ = _ := by ring

/-- Low-frequency sums: `∑_{0<|k|<R} |k|^{σ-d} ≲ (R+1)^σ`, `σ > 0`. -/
theorem hd_low_tsum (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 0 ≤ R →
      Summable (fun k : Lattice d => if Lattice.enorm k < R then
        (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (σ - (d : ℝ))) else 0) ∧
      ∑' k : Lattice d, (if Lattice.enorm k < R then
        (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (σ - (d : ℝ))) else 0) ≤ A * (R + 1) ^ σ := by
  obtain ⟨A0, hA0, hA⟩ := LatSum.low_sum (d := d) hd hσ
  refine ⟨A0, hA0, fun R hR => ?_⟩
  set J : ℕ := ⌈R⌉₊ with hJ
  have hRJ : R ≤ (J : ℝ) := Nat.le_ceil R
  have hJR : (J : ℝ) ≤ R + 1 := (Nat.ceil_lt_add_one hR).le
  have hnn : ∀ k : Lattice d, 0 ≤ (if Lattice.enorm k < R then
        (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (σ - (d : ℝ))) else 0) := by
    intro k; split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (hd_enorm_nonneg k) _
    · exact le_rfl
  have hbox : ∀ k : Lattice d, Lattice.enorm k < R → k ∈ boxF d J := by
    intro k hk
    rw [LatSum.mem_boxF']
    intro i
    have h1 : |(k i : ℝ)| ≤ Lattice.enorm k := by
      have h6 : ‖(Lattice.toEuc k) i‖ ≤ ‖Lattice.toEuc k‖ := PiLp.norm_apply_le _ i
      have h7 : ‖(Lattice.toEuc k) i‖ = |(k i : ℝ)| := by simp [Lattice.toEuc]
      unfold Lattice.enorm
      linarith
    have h2 : ((|k i| : ℤ) : ℝ) ≤ J := by
      have : ((|k i| : ℤ) : ℝ) = |(k i : ℝ)| := by push_cast; rfl
      rw [this]; linarith
    exact_mod_cast h2
  have key : ∀ M : ℕ, ∑ k ∈ boxF d M, (if Lattice.enorm k < R then
        (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (σ - (d : ℝ))) else 0) ≤ A0 * (R + 1) ^ σ := by
    intro M
    set g : Lattice d → ℝ := fun k => if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (σ - (d : ℝ)) with hg
    have hg0 : ∀ k, 0 ≤ g k := by
      intro k; simp only [hg]; split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (hd_enorm_nonneg k) _
    calc ∑ k ∈ boxF d M, (if Lattice.enorm k < R then g k else 0)
        = ∑ k ∈ (boxF d M).filter (fun k => Lattice.enorm k < R), g k := by
          rw [Finset.sum_filter]
      _ ≤ ∑ k ∈ boxF d J, g k := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hg0 k
          intro k hk
          exact hbox k (Finset.mem_filter.mp hk).2
      _ ≤ A0 * (J : ℝ) ^ σ := hA J
      _ ≤ A0 * (R + 1) ^ σ := by
          gcongr
  exact hd_summable_of_box hnn key

end HRS.MC.QRSpec.Hd

end
