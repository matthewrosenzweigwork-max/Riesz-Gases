import HRS.MC.QRPHdAux1

/-!
# Packet HD, part 2: the vector symbol `q(c) = ĝ(c) c` and its differences

`q c = rieszCoeff d s c • toEuc c`, so `‖q c‖ = |κ₀| ‖c‖^{s-d+1}` for `c ≠ 0`.  The commutator kernel has the Fourier
multiplier `(2πi)² λ·(q(β) - q(λ+β))` (part 3); here are the two bounds used for the lattice sums:
`‖q α - q (α+λ)‖ ≤ ‖q α‖ + ‖q (α+λ)‖` and the mean-value bound for `‖α‖ ≥ 2‖λ‖`.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace HRS.MC.QRSpec.Hd

open HRS

variable {d : ℕ}

/-- The vector symbol `q(c) = ĝ(c) c`. -/
def hdq (d : ℕ) (s : ℝ) (c : Lattice d) : Euc d := rieszCoeff d s c • Lattice.toEuc c

/-- The constant `κ₀ = c_{d,s} (2π)^{s-d}`. -/
def hdκ (d : ℕ) (s : ℝ) : ℝ := rieszConst d s * (2 * Real.pi) ^ (s - (d : ℝ))

theorem hd_enorm_def (k : Lattice d) : Lattice.enorm k = ‖Lattice.toEuc k‖ := rfl

theorem hd_toEuc_neg (k : Lattice d) : Lattice.toEuc (-k) = -Lattice.toEuc k := by
  ext i; simp [Lattice.toEuc]

theorem hd_toEuc_add (k l : Lattice d) : Lattice.toEuc (k + l) = Lattice.toEuc k + Lattice.toEuc l := by
  ext i; simp [Lattice.toEuc]

theorem hd_toEuc_zero : Lattice.toEuc (0 : Lattice d) = 0 := by
  ext i; simp [Lattice.toEuc]

theorem hd_enorm_neg (k : Lattice d) : Lattice.enorm (-k) = Lattice.enorm k := by
  rw [hd_enorm_def, hd_enorm_def, hd_toEuc_neg, norm_neg]

theorem hd_enorm_pos {k : Lattice d} (hk : k ≠ 0) : 0 < Lattice.enorm k :=
  lt_of_lt_of_le one_pos (hd_enorm_ge_one hk)

theorem hd_rieszCoeff_zero (s : ℝ) : rieszCoeff d s (0 : Lattice d) = 0 := by
  simp [rieszCoeff]

theorem hd_rieszCoeff_eq (s : ℝ) {k : Lattice d} (hk : k ≠ 0) :
    rieszCoeff d s k = hdκ d s * Lattice.enorm k ^ (s - (d : ℝ)) := by
  unfold rieszCoeff hdκ
  rw [if_neg hk, Real.mul_rpow (by positivity) (hd_enorm_nonneg k)]
  ring

theorem hd_rieszCoeff_neg (s : ℝ) (k : Lattice d) : rieszCoeff d s (-k) = rieszCoeff d s k := by
  unfold rieszCoeff
  by_cases hk : k = 0
  · subst hk; simp
  · have : -k ≠ 0 := neg_ne_zero.mpr hk
    rw [if_neg hk, if_neg this, hd_enorm_neg]

theorem hdq_zero (s : ℝ) : hdq d s 0 = 0 := by
  simp [hdq, hd_rieszCoeff_zero]

theorem hdq_neg (s : ℝ) (c : Lattice d) : hdq d s (-c) = -hdq d s c := by
  simp [hdq, hd_rieszCoeff_neg, hd_toEuc_neg]

theorem hdq_norm (s : ℝ) {c : Lattice d} (hc : c ≠ 0) :
    ‖hdq d s c‖ = |hdκ d s| * Lattice.enorm c ^ (s - (d : ℝ) + 1) := by
  have hpos := hd_enorm_pos hc
  unfold hdq
  rw [norm_smul, hd_rieszCoeff_eq s hc, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hpos.le _), ← hd_enorm_def, mul_assoc, ← Real.rpow_add_one hpos.ne']

theorem hdq_norm_le (s : ℝ) (c : Lattice d) :
    ‖hdq d s c‖ ≤ |hdκ d s| * Lattice.enorm c ^ (s - (d : ℝ) + 1) ∨ c = 0 := by
  by_cases hc : c = 0
  · exact Or.inr hc
  · exact Or.inl (hdq_norm s hc).le

/-- Lipschitz bound of `t ↦ t^τ` (`τ < 0`) on `[r, ∞)`. -/
theorem hd_rpow_lip {τ : ℝ} (hτ : τ < 0) {r : ℝ} (hr : 0 < r) {t u : ℝ} (ht : r ≤ t) (hu : r ≤ u) :
    |t ^ τ - u ^ τ| ≤ |τ| * r ^ (τ - 1) * |t - u| := by
  have hconv : Convex ℝ (Set.Ici r) := convex_Ici r
  have hd : ∀ x ∈ Set.Ici r, DifferentiableAt ℝ (fun x : ℝ => x ^ τ) x := by
    intro x hx
    exact Real.differentiableAt_rpow_const_of_ne τ (ne_of_gt (lt_of_lt_of_le hr hx))
  have hb : ∀ x ∈ Set.Ici r, ‖deriv (fun x : ℝ => x ^ τ) x‖ ≤ |τ| * r ^ (τ - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr hx
    rw [Real.deriv_rpow_const, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr hx (by linarith)) (abs_nonneg _)
  have := hconv.norm_image_sub_le_of_norm_deriv_le hd hb hu ht
  simpa [Real.norm_eq_abs] using this

/-- Mean value bound for the vector map `x ↦ ‖x‖^τ x`. -/
theorem hd_vec_lip {τ : ℝ} (hτ : τ < 0) {r : ℝ} (hr : 0 < r) {x y : Euc d}
    (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) (hy3 : ‖y‖ ≤ 3 * r) :
    ‖‖x‖ ^ τ • x - ‖y‖ ^ τ • y‖ ≤ (1 + 3 * |τ|) * r ^ τ * ‖x - y‖ := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le hr hx
  have e : ‖x‖ ^ τ • x - ‖y‖ ^ τ • y = ‖x‖ ^ τ • (x - y) + (‖x‖ ^ τ - ‖y‖ ^ τ) • y := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have h1 : ‖x‖ ^ τ ≤ r ^ τ := Real.rpow_le_rpow_of_nonpos hr hx hτ.le
  have h2 := hd_rpow_lip hτ hr hx hy
  have h3 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have h4 : |τ| * r ^ (τ - 1) * |‖x‖ - ‖y‖| ≤ |τ| * r ^ (τ - 1) * ‖x - y‖ :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : r ^ (τ - 1) * r = r ^ τ := by
    rw [← Real.rpow_add_one hr.ne']; ring_nf
  have hrp : 0 ≤ r ^ (τ - 1) := Real.rpow_nonneg hr.le _
  calc ‖x‖ ^ τ * ‖x - y‖ + |‖x‖ ^ τ - ‖y‖ ^ τ| * ‖y‖
      ≤ r ^ τ * ‖x - y‖ + (|τ| * r ^ (τ - 1) * ‖x - y‖) * (3 * r) := by
        gcongr
        exact h2.trans h4
    _ = (1 + 3 * |τ|) * r ^ τ * ‖x - y‖ := by
        have : (|τ| * r ^ (τ - 1) * ‖x - y‖) * (3 * r) = 3 * |τ| * (r ^ (τ - 1) * r) * ‖x - y‖ := by ring
        rw [this, h5]; ring

/-- The mean value bound for the symbol: for `‖α‖ ≥ 2‖λ‖`, `α ≠ 0`. -/
theorem hdq_diff_le {s : ℝ} (hs : s < d) {α lam : Lattice d} (hα : α ≠ 0)
    (h2 : 2 * Lattice.enorm lam ≤ Lattice.enorm α) :
    ‖hdq d s α - hdq d s (α + lam)‖ ≤
      |hdκ d s| * (1 + 3 * |s - (d : ℝ)|) * 2 ^ ((d : ℝ) - s) * Lattice.enorm lam *
        Lattice.enorm α ^ (s - (d : ℝ)) := by
  set τ : ℝ := s - (d : ℝ) with hτdef
  have hτ : τ < 0 := by rw [hτdef]; linarith
  have hapos := hd_enorm_pos hα
  set x : Euc d := Lattice.toEuc α with hx
  set y : Euc d := Lattice.toEuc (α + lam) with hy
  set r : ℝ := Lattice.enorm α / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hxn : ‖x‖ = Lattice.enorm α := rfl
  have hl : ‖x - y‖ = Lattice.enorm lam := by
    rw [hx, hy, hd_toEuc_add]
    simp [hd_enorm_def]
  have hy1 : r ≤ ‖y‖ := by
    have : ‖x‖ - ‖x - y‖ ≤ ‖y‖ := by
      have := norm_sub_norm_le x (x - y)
      simpa using this
    rw [hxn, hl] at this
    rw [hr]; linarith
  have hy3 : ‖y‖ ≤ 3 * r := by
    have : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      have := norm_le_norm_add_norm_sub' y x
      rw [norm_sub_rev] at this
      linarith
    rw [hxn, hl] at this
    rw [hr]; linarith
  have hy0 : α + lam ≠ 0 := by
    intro h
    have : ‖y‖ = 0 := by rw [hy, h, hd_toEuc_zero, norm_zero]
    linarith
  have hqα : hdq d s α = hdκ d s • (‖x‖ ^ τ • x) := by
    unfold hdq
    rw [hd_rieszCoeff_eq s hα, smul_smul]
    rfl
  have hqy : hdq d s (α + lam) = hdκ d s • (‖y‖ ^ τ • y) := by
    unfold hdq
    rw [hd_rieszCoeff_eq s hy0, smul_smul]
    rfl
  rw [hqα, hqy, ← smul_sub, norm_smul, Real.norm_eq_abs]
  have hx1 : r ≤ ‖x‖ := by rw [hxn, hr]; linarith
  have hv := hd_vec_lip hτ hr0 hx1 hy1 hy3
  rw [hl] at hv
  have hrt : r ^ τ = 2 ^ (-τ) * Lattice.enorm α ^ τ := by
    rw [hr, Real.div_rpow hapos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have : 2 ^ (-τ) = (2 : ℝ) ^ ((d : ℝ) - s) := by rw [hτdef]; ring_nf
  rw [hrt, this] at hv
  calc |hdκ d s| * ‖‖x‖ ^ τ • x - ‖y‖ ^ τ • y‖
      ≤ |hdκ d s| * ((1 + 3 * |τ|) * (2 ^ ((d : ℝ) - s) * Lattice.enorm α ^ τ) * Lattice.enorm lam) :=
        mul_le_mul_of_nonneg_left hv (abs_nonneg _)
    _ = _ := by rw [hτdef]; ring

end HRS.MC.QRSpec.Hd

end
