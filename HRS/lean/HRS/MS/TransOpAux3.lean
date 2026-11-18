import HRS.MS.TransOpAux2

/-!
# S611 packet P1c: combinatorial pieces of the energy estimate

* the finite sets `s611_D d N = {α : |α| ≤ N}`, degrees of `α ± e_i`, `dec`/`inc` inverses;
* the scalar inequality `|a A₁ A₂ (λ^m - (λ-2)^m)| ≤ (m 3^m / 2)(λ^m A₁² + (λ-2)^m A₂²)` (`s611_term_le`);
* two-sided Gronwall (`s611_gronwall`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- `{α : |α| ≤ N}` as a finset. -/
def s611_D (d N : ℕ) : Finset (MultiIndex d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.range (N + 1)).filter fun α => α.degree ≤ N

theorem s611_mem_D {N : ℕ} {α : MultiIndex d} : α ∈ s611_D d N ↔ α.degree ≤ N := by
  unfold s611_D
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  rw [Finset.mem_range]
  have : α i ≤ α.degree :=
    Finset.single_le_sum (f := fun j => α j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem s611_degree_update (α : MultiIndex d) (i : Fin d) (k : ℕ) :
    MultiIndex.degree (Function.update α i k) + α i = α.degree + k := by
  unfold MultiIndex.degree
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h1 := Finset.add_sum_erase Finset.univ (fun j => α j) (Finset.mem_univ i)
  have h2 : (Finset.univ \ {i}) = Finset.univ.erase i := by
    ext j; simp
  rw [h2]
  omega

theorem s611_degree_inc (α : MultiIndex d) (i : Fin d) : (s611_inc α i).degree = α.degree + 1 := by
  have := s611_degree_update α i (α i + 1)
  unfold s611_inc
  omega

theorem s611_degree_dec (α : MultiIndex d) (i : Fin d) (h : 1 ≤ α i) :
    (s611_dec α i).degree + 1 = α.degree := by
  have := s611_degree_update α i (α i - 1)
  unfold s611_dec
  omega

theorem s611_inc_apply (α : MultiIndex d) (i : Fin d) : s611_inc α i i = α i + 1 := by
  simp [s611_inc]

theorem s611_dec_apply (α : MultiIndex d) (i : Fin d) : s611_dec α i i = α i - 1 := by
  simp [s611_dec]

theorem s611_dec_inc (α : MultiIndex d) (i : Fin d) : s611_dec (s611_inc α i) i = α := by
  unfold s611_dec s611_inc
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem s611_inc_dec (α : MultiIndex d) (i : Fin d) (h : 1 ≤ α i) : s611_inc (s611_dec α i) i = α := by
  unfold s611_dec s611_inc
  ext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [hj]

/-- Scalar inequality for the energy derivative. -/
theorem s611_term_le (m : ℕ) (hm : 1 ≤ m) (lam a A1 A2 : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ lam / 2)
    (hl : 3 ≤ lam) :
    |a * A1 * A2 * (lam ^ m - (lam - 2) ^ m)| ≤
      ((m : ℝ) * 3 ^ m / 2) * (lam ^ m * A1 ^ 2 + (lam - 2) ^ m * A2 ^ 2) := by
  have hlam : 0 < lam := by linarith
  have hl2 : 0 ≤ lam - 2 := by linarith
  have hδ0 : 0 ≤ lam ^ m - (lam - 2) ^ m :=
    sub_nonneg.2 (pow_le_pow_left₀ hl2 (by linarith) m)
  -- Bernoulli
  have hber : lam ^ m - 2 * m * (lam ^ m / lam) ≤ (lam - 2) ^ m := by
    have h1 := one_add_mul_le_pow (a := -2 / lam) (by
      rw [le_div_iff₀ hlam]; linarith) m
    have e : lam - 2 = lam * (1 + -2 / lam) := by field_simp; ring
    rw [e, mul_pow]
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hlam.le m)
    calc lam ^ m - 2 * m * (lam ^ m / lam) = lam ^ m * (1 + m * (-2 / lam)) := by
          field_simp
          ring
      _ ≤ lam ^ m * (1 + -2 / lam) ^ m := h2
  have hδ : lam ^ m - (lam - 2) ^ m ≤ 2 * m * (lam ^ m / lam) := by linarith
  have hpm : 0 ≤ lam ^ m := pow_nonneg hlam.le m
  have h3 : lam ^ m ≤ 3 ^ m * (lam - 2) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlam.le (by linarith) m
  have hmpos : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h31 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
  have hA : |a * A1 * A2 * (lam ^ m - (lam - 2) ^ m)| ≤ m * lam ^ m * (|A1| * |A2|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hδ0]
    have : a * (|A1| * |A2|) * (lam ^ m - (lam - 2) ^ m) ≤ (lam / 2) * (|A1| * |A2|) * (2 * m * (lam ^ m / lam)) := by
      have hp : 0 ≤ |A1| * |A2| := by positivity
      calc a * (|A1| * |A2|) * (lam ^ m - (lam - 2) ^ m)
          ≤ (lam / 2) * (|A1| * |A2|) * (lam ^ m - (lam - 2) ^ m) := by gcongr
        _ ≤ (lam / 2) * (|A1| * |A2|) * (2 * m * (lam ^ m / lam)) := by gcongr
    calc a * |A1| * |A2| * (lam ^ m - (lam - 2) ^ m)
        = a * (|A1| * |A2|) * (lam ^ m - (lam - 2) ^ m) := by ring
      _ ≤ (lam / 2) * (|A1| * |A2|) * (2 * m * (lam ^ m / lam)) := this
      _ = m * lam ^ m * (|A1| * |A2|) := by field_simp
  calc |a * A1 * A2 * (lam ^ m - (lam - 2) ^ m)| ≤ m * lam ^ m * (|A1| * |A2|) := hA
    _ ≤ m * lam ^ m * ((A1 ^ 2 + A2 ^ 2) / 2) := by
        gcongr
        nlinarith [sq_abs A1, sq_abs A2, sq_nonneg (|A1| - |A2|)]
    _ = (m / 2) * (lam ^ m * A1 ^ 2 + lam ^ m * A2 ^ 2) := by ring
    _ ≤ (m / 2) * (lam ^ m * A1 ^ 2 + (3 ^ m * (lam - 2) ^ m) * A2 ^ 2) := by gcongr
    _ ≤ ((m : ℝ) * 3 ^ m / 2) * (lam ^ m * A1 ^ 2 + (lam - 2) ^ m * A2 ^ 2) := by
        have hq : 0 ≤ (lam - 2) ^ m * A2 ^ 2 := by positivity
        have hr : 0 ≤ lam ^ m * A1 ^ 2 := by positivity
        nlinarith [mul_nonneg hmpos (mul_nonneg (sub_nonneg.2 h31) hr), mul_nonneg hmpos hq]

/-- Two-sided Gronwall for a nonnegative `E` with `|E'| ≤ K E`. -/
theorem s611_gronwall (E E' : ℝ → ℝ) (K : ℝ) (_hK : 0 ≤ K) (hd : ∀ t, HasDerivAt E (E' t) t)
    (hb : ∀ t, |E' t| ≤ K * E t) (t : ℝ) : E t ≤ Real.exp (K * |t|) * E 0 := by
  rcases le_total 0 t with ht | ht
  · have hφ : ∀ s, HasDerivAt (fun s => Real.exp (-K * s) * E s)
        (Real.exp (-K * s) * (E' s - K * E s)) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => Real.exp (-K * s)) (Real.exp (-K * s) * (-K)) s := by
        have := (hasDerivAt_id s).const_mul (-K)
        simpa using this.exp
      have := h1.mul (hd s)
      convert this using 1
      ring
    have hanti : Antitone (fun s => Real.exp (-K * s) * E s) := by
      refine antitone_of_deriv_nonpos (fun s => (hφ s).differentiableAt) fun s => ?_
      rw [(hφ s).deriv]
      refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
      have := hb s
      have := (abs_le.1 this).2
      linarith
    have h0 := hanti ht
    simp only [mul_zero, Real.exp_zero, one_mul] at h0
    rw [abs_of_nonneg ht]
    have : E t ≤ Real.exp (K * t) * E 0 := by
      have h2 : Real.exp (K * t) * (Real.exp (-K * t) * E t) ≤ Real.exp (K * t) * E 0 :=
        mul_le_mul_of_nonneg_left h0 (Real.exp_pos _).le
      rwa [← mul_assoc, ← Real.exp_add, show K * t + -K * t = 0 by ring, Real.exp_zero, one_mul] at h2
    exact this
  · have hψ : ∀ s, HasDerivAt (fun s => Real.exp (K * s) * E s)
        (Real.exp (K * s) * (E' s + K * E s)) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => Real.exp (K * s)) (Real.exp (K * s) * K) s := by
        have := (hasDerivAt_id s).const_mul K
        simpa using this.exp
      have := h1.mul (hd s)
      convert this using 1
      ring
    have hmono : Monotone (fun s => Real.exp (K * s) * E s) := by
      refine monotone_of_deriv_nonneg (fun s => (hψ s).differentiableAt) fun s => ?_
      rw [(hψ s).deriv]
      refine mul_nonneg (Real.exp_pos _).le ?_
      have := hb s
      have := (abs_le.1 this).1
      linarith
    have h0 := hmono ht
    simp only [mul_zero, Real.exp_zero, one_mul] at h0
    rw [abs_of_nonpos ht]
    have h2 : Real.exp (-K * t) * (Real.exp (K * t) * E t) ≤ Real.exp (-K * t) * E 0 :=
      mul_le_mul_of_nonneg_left h0 (Real.exp_pos _).le
    rw [← mul_assoc, ← Real.exp_add, show -K * t + K * t = 0 by ring, Real.exp_zero, one_mul] at h2
    calc E t ≤ Real.exp (-K * t) * E 0 := h2
      _ = Real.exp (K * -t) * E 0 := by congr 2; ring

end HRS.MS.TransOp

end
