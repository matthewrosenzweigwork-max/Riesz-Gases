import Mathlib

/-!
# MOVA3 (spike): abstract Stein interpolation for infinite matrices with positive weights

Infrastructure for `mo_interp_osc` (MOV-A3a, `docs/MOV_PLAN.md`, Brief MOV-A3a).  This file is
generic: an index type `ι`, positive weights `w : ι → ℝ` (later `w = oscEigenvalue d`) and a real
matrix `K : ι → ι → ℝ` (later `K α β = ⟨T h_α, h_β⟩`).

`mova3_Hop w K r s M` is the finite-section form of the bound `‖T f‖_{s} ≤ M ‖f‖_{r}`:
for all finite sets `S, S'` and all real coefficient vectors `c`,
`∑_{β ∈ S'} w_β^s (∑_{α ∈ S} c_α K_{αβ})² ≤ M² ∑_{α ∈ S} w_α^r c_α²`.

Main theorem `mova3_matrix_interp`: `Hop` at `(r0, s0, M0)` and at `(r1, s1, M1)` implies `Hop`
at `((1-θ) r0 + θ r1, (1-θ) s0 + θ s1, M0^(1-θ) M1^θ)`, for `θ ∈ [0,1]` and `M0, M1 ≥ 0`.

Proof: with `ℓ_α = log w_α`, `F(z) = ∑_{β ∈ S'} d_β w_β^{(z-θ)(s1-s0)/2} ∑_{α ∈ S} c_α w_α^{(θ-z)(r1-r0)/2} K_{αβ}`
is entire, bounded on `0 ≤ Re z ≤ 1`; on both boundary lines the bound follows from the
complexification of `Hop` and Cauchy-Schwarz (the rotated vectors have the same weighted
`ℓ²` norms as `c`, `d`); Mathlib's three-lines theorem
(`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`) gives `|F(θ)|`;
finally the choice `d_β = w_β^{s_θ} y_β` turns the bilinear bound into `Hop`.
-/

noncomputable section

open Complex Finset

namespace HRS.MS.MovInterp

variable {ι : Type*}

lemma mova3_rpow_eq {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = Real.exp (y * Real.log x) := by
  rw [Real.rpow_def_of_pos hx, mul_comm]

lemma mova3_rpow_half_sq {x : ℝ} (hx : 0 < x) (a : ℝ) : (x ^ (a / 2)) ^ 2 = x ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1; push_cast; ring

/-- Finite-section form of `‖T f‖_s ≤ M ‖f‖_r`. -/
def mova3_Hop (w : ι → ℝ) (K : ι → ι → ℝ) (r s M : ℝ) : Prop :=
  ∀ (S S' : Finset ι) (c : ι → ℝ),
    ∑ β ∈ S', w β ^ s * (∑ α ∈ S, c α * K α β) ^ 2 ≤ M ^ 2 * ∑ α ∈ S, w α ^ r * c α ^ 2

/-- Complexification of `mova3_Hop` (exact: real and imaginary parts are treated separately). -/
lemma mova3_Hop_complex {w : ι → ℝ} {K : ι → ι → ℝ} {r s M : ℝ} (h : mova3_Hop w K r s M)
    (S S' : Finset ι) (u : ι → ℂ) :
    ∑ β ∈ S', w β ^ s * ‖∑ α ∈ S, u α * (K α β : ℂ)‖ ^ 2 ≤
      M ^ 2 * ∑ α ∈ S, w α ^ r * ‖u α‖ ^ 2 := by
  have h1 := h S S' (fun α => (u α).re)
  have h2 := h S S' (fun α => (u α).im)
  have e1 : ∀ β, (∑ α ∈ S, u α * (K α β : ℂ)).re = ∑ α ∈ S, (u α).re * K α β := by
    intro β; simp [Complex.re_sum, Complex.mul_re]
  have e2 : ∀ β, (∑ α ∈ S, u α * (K α β : ℂ)).im = ∑ α ∈ S, (u α).im * K α β := by
    intro β; simp [Complex.im_sum, Complex.mul_im]
  have e3 : ∀ β, ‖∑ α ∈ S, u α * (K α β : ℂ)‖ ^ 2 =
      (∑ α ∈ S, (u α).re * K α β) ^ 2 + (∑ α ∈ S, (u α).im * K α β) ^ 2 := by
    intro β
    rw [Complex.sq_norm, Complex.normSq_apply, e1, e2]; ring
  have e4 : ∀ α, ‖u α‖ ^ 2 = (u α).re ^ 2 + (u α).im ^ 2 := by
    intro α; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp_rw [e3, e4, mul_add, Finset.sum_add_distrib]
  linarith

/-! ### The rotated vectors -/

/-- Rotated input vector `c_α w_α^{(θ-z)(r1-r0)/2}`. -/
def mova3_ua (w : ι → ℝ) (c : ι → ℝ) (θ r0 r1 : ℝ) (z : ℂ) (α : ι) : ℂ :=
  (c α : ℂ) * Complex.exp (((θ : ℂ) - z) * ((r1 : ℂ) - r0) / 2 * (Real.log (w α) : ℂ))

/-- Rotated output vector `d_β w_β^{(z-θ)(s1-s0)/2}`. -/
def mova3_vb (w : ι → ℝ) (d : ι → ℝ) (θ s0 s1 : ℝ) (z : ℂ) (β : ι) : ℂ :=
  (d β : ℂ) * Complex.exp ((z - (θ : ℂ)) * ((s1 : ℂ) - s0) / 2 * (Real.log (w β) : ℂ))

/-- The analytic family. -/
def mova3_F (w : ι → ℝ) (K : ι → ι → ℝ) (c d : ι → ℝ) (θ r0 r1 s0 s1 : ℝ)
    (S S' : Finset ι) (z : ℂ) : ℂ :=
  ∑ β ∈ S', mova3_vb w d θ s0 s1 z β * ∑ α ∈ S, mova3_ua w c θ r0 r1 z α * (K α β : ℂ)

lemma mova3_norm_ua_sq (w : ι → ℝ) (c : ι → ℝ) (θ r0 r1 : ℝ) (z : ℂ) (α : ι) :
    ‖mova3_ua w c θ r0 r1 z α‖ ^ 2 =
      c α ^ 2 * Real.exp ((θ - z.re) * (r1 - r0) * Real.log (w α)) := by
  unfold mova3_ua
  rw [norm_mul, Complex.norm_exp, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Real.exp_nat_mul]
  congr 2
  have : (((θ : ℂ) - z) * ((r1 : ℂ) - r0) / 2 * (Real.log (w α) : ℂ)).re =
      (θ - z.re) * (r1 - r0) / 2 * Real.log (w α) := by
    simp [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.sub_im]
  rw [this]; push_cast; ring

lemma mova3_norm_vb_sq (w : ι → ℝ) (d : ι → ℝ) (θ s0 s1 : ℝ) (z : ℂ) (β : ι) :
    ‖mova3_vb w d θ s0 s1 z β‖ ^ 2 =
      d β ^ 2 * Real.exp ((z.re - θ) * (s1 - s0) * Real.log (w β)) := by
  unfold mova3_vb
  rw [norm_mul, Complex.norm_exp, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Real.exp_nat_mul]
  congr 2
  have : ((z - (θ : ℂ)) * ((s1 : ℂ) - s0) / 2 * (Real.log (w β) : ℂ)).re =
      (z.re - θ) * (s1 - s0) / 2 * Real.log (w β) := by
    simp [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.sub_im]
  rw [this]; push_cast; ring


/-! ### Boundary bound -/

lemma mova3_endpoint {w : ι → ℝ} (hw : ∀ i, 0 < w i) {K : ι → ι → ℝ} {r s M ρ σ : ℝ}
    (hHop : mova3_Hop w K r s M) (hM : 0 ≤ M) (S S' : Finset ι) (c d : ι → ℝ)
    (θ r0 r1 s0 s1 : ℝ) (z : ℂ)
    (hu : ∀ α, w α ^ r * ‖mova3_ua w c θ r0 r1 z α‖ ^ 2 = w α ^ ρ * c α ^ 2)
    (hv : ∀ β, w β ^ (-s) * ‖mova3_vb w d θ s0 s1 z β‖ ^ 2 = w β ^ σ * d β ^ 2) :
    ‖mova3_F w K c d θ r0 r1 s0 s1 S S' z‖ ≤
      M * Real.sqrt (∑ α ∈ S, w α ^ ρ * c α ^ 2) * Real.sqrt (∑ β ∈ S', w β ^ σ * d β ^ 2) := by
  set Y : ι → ℂ := fun β => ∑ α ∈ S, mova3_ua w c θ r0 r1 z α * (K α β : ℂ) with hY
  have hone : ∀ β, w β ^ (-s / 2) * w β ^ (s / 2) = 1 := fun β => by
    rw [← Real.rpow_add (hw β), show -s / 2 + s / 2 = 0 by ring, Real.rpow_zero]
  have h1 : ‖mova3_F w K c d θ r0 r1 s0 s1 S S' z‖ ≤
      ∑ β ∈ S', (‖mova3_vb w d θ s0 s1 z β‖ * w β ^ (-s / 2)) * (‖Y β‖ * w β ^ (s / 2)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
    rw [norm_mul]
    have : (‖mova3_vb w d θ s0 s1 z β‖ * w β ^ (-s / 2)) * (‖Y β‖ * w β ^ (s / 2)) =
        ‖mova3_vb w d θ s0 s1 z β‖ * ‖Y β‖ * (w β ^ (-s / 2) * w β ^ (s / 2)) := by ring
    rw [this, hone]; simp [hY]
  refine h1.trans ((Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_)
  have e1 : ∑ β ∈ S', (‖mova3_vb w d θ s0 s1 z β‖ * w β ^ (-s / 2)) ^ 2 =
      ∑ β ∈ S', w β ^ σ * d β ^ 2 := by
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [mul_pow, mova3_rpow_half_sq (hw β), mul_comm]; exact hv β
  have e2 : ∑ β ∈ S', (‖Y β‖ * w β ^ (s / 2)) ^ 2 ≤ M ^ 2 * ∑ α ∈ S, w α ^ ρ * c α ^ 2 := by
    have := mova3_Hop_complex hHop S S' (mova3_ua w c θ r0 r1 z)
    calc ∑ β ∈ S', (‖Y β‖ * w β ^ (s / 2)) ^ 2
        = ∑ β ∈ S', w β ^ s * ‖Y β‖ ^ 2 := by
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [mul_pow, mova3_rpow_half_sq (hw β), mul_comm]
      _ ≤ M ^ 2 * ∑ α ∈ S, w α ^ r * ‖mova3_ua w c θ r0 r1 z α‖ ^ 2 := this
      _ = M ^ 2 * ∑ α ∈ S, w α ^ ρ * c α ^ 2 := by
          congr 1; exact Finset.sum_congr rfl fun α _ => hu α
  rw [e1]
  have e3 : Real.sqrt (∑ β ∈ S', (‖Y β‖ * w β ^ (s / 2)) ^ 2) ≤
      M * Real.sqrt (∑ α ∈ S, w α ^ ρ * c α ^ 2) := by
    refine (Real.sqrt_le_sqrt e2).trans ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM]
  calc Real.sqrt (∑ β ∈ S', w β ^ σ * d β ^ 2) *
        Real.sqrt (∑ β ∈ S', (‖Y β‖ * w β ^ (s / 2)) ^ 2)
      ≤ Real.sqrt (∑ β ∈ S', w β ^ σ * d β ^ 2) *
          (M * Real.sqrt (∑ α ∈ S, w α ^ ρ * c α ^ 2)) :=
        mul_le_mul_of_nonneg_left e3 (Real.sqrt_nonneg _)
    _ = M * Real.sqrt (∑ α ∈ S, w α ^ ρ * c α ^ 2) *
          Real.sqrt (∑ β ∈ S', w β ^ σ * d β ^ 2) := by ring


lemma mova3_norm_ua (w : ι → ℝ) (c : ι → ℝ) (θ r0 r1 : ℝ) (z : ℂ) (α : ι) :
    ‖mova3_ua w c θ r0 r1 z α‖ =
      |c α| * Real.exp ((θ - z.re) * (r1 - r0) / 2 * Real.log (w α)) := by
  unfold mova3_ua
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 2
  simp [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.sub_im]

lemma mova3_norm_vb (w : ι → ℝ) (d : ι → ℝ) (θ s0 s1 : ℝ) (z : ℂ) (β : ι) :
    ‖mova3_vb w d θ s0 s1 z β‖ =
      |d β| * Real.exp ((z.re - θ) * (s1 - s0) / 2 * Real.log (w β)) := by
  unfold mova3_vb
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 2
  simp [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.sub_im]

lemma mova3_hu {w : ι → ℝ} (hw : ∀ i, 0 < w i) (c : ι → ℝ) (θ r0 r1 : ℝ) (z : ℂ) (α : ι) :
    w α ^ (r0 + z.re * (r1 - r0)) * ‖mova3_ua w c θ r0 r1 z α‖ ^ 2 =
      w α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2 := by
  have : (r0 + z.re * (r1 - r0)) * Real.log (w α) + (θ - z.re) * (r1 - r0) * Real.log (w α) =
      ((1 - θ) * r0 + θ * r1) * Real.log (w α) := by ring
  rw [mova3_norm_ua_sq, mova3_rpow_eq (hw α), mova3_rpow_eq (hw α), mul_left_comm,
    ← Real.exp_add, this]
  ring

lemma mova3_hv {w : ι → ℝ} (hw : ∀ i, 0 < w i) (d : ι → ℝ) (θ s0 s1 : ℝ) (z : ℂ) (β : ι) :
    w β ^ (-(s0 + z.re * (s1 - s0))) * ‖mova3_vb w d θ s0 s1 z β‖ ^ 2 =
      w β ^ (-((1 - θ) * s0 + θ * s1)) * d β ^ 2 := by
  have : (-(s0 + z.re * (s1 - s0))) * Real.log (w β) + (z.re - θ) * (s1 - s0) * Real.log (w β) =
      (-((1 - θ) * s0 + θ * s1)) * Real.log (w β) := by ring
  rw [mova3_norm_vb_sq, mova3_rpow_eq (hw β), mova3_rpow_eq (hw β), mul_left_comm,
    ← Real.exp_add, this]
  ring

/-! ### Analyticity and boundedness on the strip -/

lemma mova3_F_differentiable (w : ι → ℝ) (K : ι → ι → ℝ) (c d : ι → ℝ) (θ r0 r1 s0 s1 : ℝ)
    (S S' : Finset ι) : Differentiable ℂ (mova3_F w K c d θ r0 r1 s0 s1 S S') := by
  unfold mova3_F mova3_vb mova3_ua
  fun_prop

lemma mova3_exp_arg_le {θ x a l : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (θ - x) * a / 2 * l ≤ |a| * |l| / 2 ∧ (x - θ) * a / 2 * l ≤ |a| * |l| / 2 := by
  have h1 : |θ - x| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |x - θ| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have h3 : 0 ≤ |a| * |l| / 2 := by positivity
  have e : ∀ t : ℝ, |t| ≤ 1 → t * a / 2 * l ≤ |a| * |l| / 2 := by
    intro t ht
    calc t * a / 2 * l ≤ |t * a / 2 * l| := le_abs_self _
      _ = |t| * (|a| * |l| / 2) := by
          rw [abs_mul, abs_div, abs_mul, abs_two]; ring
      _ ≤ 1 * (|a| * |l| / 2) := mul_le_mul_of_nonneg_right ht h3
      _ = _ := one_mul _
  exact ⟨e _ h1, e _ h2⟩

lemma mova3_F_bdd (w : ι → ℝ) (K : ι → ι → ℝ) (c d : ι → ℝ) {θ : ℝ} (r0 r1 s0 s1 : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (S S' : Finset ι) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ‖mova3_F w K c d θ r0 r1 s0 s1 S S' z‖ ≤ C := by
  refine ⟨∑ β ∈ S', ∑ α ∈ S, (|d β| * Real.exp (|s1 - s0| * |Real.log (w β)| / 2)) *
      ((|c α| * Real.exp (|r1 - r0| * |Real.log (w α)| / 2)) * |K α β|), fun z hz0 hz1 => ?_⟩
  unfold mova3_F
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun α _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb : ‖mova3_vb w d θ s0 s1 z β‖ ≤ |d β| * Real.exp (|s1 - s0| * |Real.log (w β)| / 2) := by
    rw [mova3_norm_vb]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mova3_exp_arg_le hθ0 hθ1 hz0 hz1).2) (abs_nonneg _)
  have ha : ‖mova3_ua w c θ r0 r1 z α‖ ≤ |c α| * Real.exp (|r1 - r0| * |Real.log (w α)| / 2) := by
    rw [mova3_norm_ua]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mova3_exp_arg_le hθ0 hθ1 hz0 hz1).1) (abs_nonneg _)
  exact mul_le_mul hb (mul_le_mul_of_nonneg_right ha (abs_nonneg _)) (by positivity)
    (by positivity)


/-! ### Three-lines step: the bilinear bound -/

lemma mova3_bilinear {w : ι → ℝ} (hw : ∀ i, 0 < w i) {K : ι → ι → ℝ}
    {r0 r1 s0 s1 M0 M1 θ : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (H0 : mova3_Hop w K r0 s0 M0) (H1 : mova3_Hop w K r1 s1 M1)
    (S S' : Finset ι) (c d : ι → ℝ) :
    |∑ β ∈ S', d β * ∑ α ∈ S, c α * K α β| ≤
      M0 ^ (1 - θ) * M1 ^ θ *
        (Real.sqrt (∑ α ∈ S, w α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2) *
          Real.sqrt (∑ β ∈ S', w β ^ (-((1 - θ) * s0 + θ * s1)) * d β ^ 2)) := by
  set X := Real.sqrt (∑ α ∈ S, w α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2) with hX
  set Y := Real.sqrt (∑ β ∈ S', w β ^ (-((1 - θ) * s0 + θ * s1)) * d β ^ 2) with hY
  have hXn : 0 ≤ X := Real.sqrt_nonneg _
  have hYn : 0 ≤ Y := Real.sqrt_nonneg _
  set F := mova3_F w K c d θ r0 r1 s0 s1 S S' with hF
  have hdiff : Differentiable ℂ F := mova3_F_differentiable w K c d θ r0 r1 s0 s1 S S'
  obtain ⟨C, hC⟩ := mova3_F_bdd w K c d r0 r1 s0 s1 hθ0 hθ1 S S'
  have hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC z hz.1 hz.2
  have ha : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖F z‖ ≤ M0 * (X * Y) := by
    intro z hz
    have hz0 : z.re = 0 := hz
    have := mova3_endpoint hw H0 hM0 S S' c d θ r0 r1 s0 s1 z
      (ρ := (1 - θ) * r0 + θ * r1) (σ := -((1 - θ) * s0 + θ * s1))
      (fun α => by have h := mova3_hu hw c θ r0 r1 z α; rwa [hz0, zero_mul, add_zero] at h)
      (fun β => by have h := mova3_hv hw d θ s0 s1 z β; rwa [hz0, zero_mul, add_zero] at h)
    exact this.trans (le_of_eq (mul_assoc _ _ _))
  have hb : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖F z‖ ≤ M1 * (X * Y) := by
    intro z hz
    have hz1 : z.re = 1 := hz
    have := mova3_endpoint hw H1 hM1 S S' c d θ r0 r1 s0 s1 z
      (ρ := (1 - θ) * r0 + θ * r1) (σ := -((1 - θ) * s0 + θ * s1))
      (fun α => by have h := mova3_hu hw c θ r0 r1 z α; rwa [hz1, one_mul, add_sub_cancel] at h)
      (fun β => by have h := mova3_hv hw d θ s0 s1 z β; rwa [hz1, one_mul, add_sub_cancel] at h)
    exact this.trans (le_of_eq (mul_assoc _ _ _))
  have hzmem : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage,
      Complex.ofReal_re, Set.mem_Icc]
    exact ⟨hθ0, hθ1⟩
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := F) (z := (θ : ℂ)) (a := M0 * (X * Y)) (b := M1 * (X * Y)) (l := 0) (u := 1)
    zero_lt_one hzmem hdiff.diffContOnCl hB ha hb
  have hFθ : F (θ : ℂ) = ((∑ β ∈ S', d β * ∑ α ∈ S, c α * K α β : ℝ) : ℂ) := by
    simp [hF, mova3_F, mova3_vb, mova3_ua]
  rw [hFθ, Complex.norm_real, Real.norm_eq_abs] at key
  simp only [Complex.ofReal_re, sub_zero, div_one] at key
  refine key.trans (le_of_eq ?_)
  have hXY : 0 ≤ X * Y := mul_nonneg hXn hYn
  rw [Real.mul_rpow hM0 hXY, Real.mul_rpow hM1 hXY]
  have : (X * Y) ^ (1 - θ) * (X * Y) ^ θ = X * Y := by
    rw [← Real.rpow_add' hXY (by linarith : (1 - θ) + θ ≠ 0)]
    simp
  calc M0 ^ (1 - θ) * (X * Y) ^ (1 - θ) * (M1 ^ θ * (X * Y) ^ θ)
      = M0 ^ (1 - θ) * M1 ^ θ * ((X * Y) ^ (1 - θ) * (X * Y) ^ θ) := by ring
    _ = _ := by rw [this]

/-- **Stein interpolation for weighted infinite matrices.** -/
theorem mova3_matrix_interp {w : ι → ℝ} (hw : ∀ i, 0 < w i) {K : ι → ι → ℝ}
    {r0 r1 s0 s1 M0 M1 θ : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (H0 : mova3_Hop w K r0 s0 M0) (H1 : mova3_Hop w K r1 s1 M1) :
    mova3_Hop w K ((1 - θ) * r0 + θ * r1) ((1 - θ) * s0 + θ * s1) (M0 ^ (1 - θ) * M1 ^ θ) := by
  intro S S' c
  set B := M0 ^ (1 - θ) * M1 ^ θ with hBdef
  have hB : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hM1 _)
  set A := Real.sqrt (∑ α ∈ S, w α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2) with hA
  have hAn : 0 ≤ A := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = ∑ α ∈ S, w α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun α _ => mul_nonneg (Real.rpow_nonneg (hw α).le _)
      (sq_nonneg _))
  set σ := (1 - θ) * s0 + θ * s1 with hσ
  set y : ι → ℝ := fun β => ∑ α ∈ S, c α * K α β with hy
  set P := ∑ β ∈ S', w β ^ σ * y β ^ 2 with hP
  have hPn : 0 ≤ P := Finset.sum_nonneg fun β _ => mul_nonneg (Real.rpow_nonneg (hw β).le _)
    (sq_nonneg _)
  -- choose d β = w β ^ σ * y β
  have hbil := mova3_bilinear hw hM0 hM1 hθ0 hθ1 H0 H1 S S' c (fun β => w β ^ σ * y β)
  have hlhs : ∑ β ∈ S', (w β ^ σ * y β) * ∑ α ∈ S, c α * K α β = P := by
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [hy]; ring
  have hrhs : ∑ β ∈ S', w β ^ (-σ) * (w β ^ σ * y β) ^ 2 = P := by
    refine Finset.sum_congr rfl fun β _ => ?_
    have : w β ^ (-σ) * w β ^ σ = 1 := by
      rw [← Real.rpow_add (hw β)]; simp
    calc w β ^ (-σ) * (w β ^ σ * y β) ^ 2
        = (w β ^ (-σ) * w β ^ σ) * (w β ^ σ * y β ^ 2) := by ring
      _ = _ := by rw [this, one_mul]
  rw [hlhs, hrhs, abs_of_nonneg hPn, ← hA] at hbil
  -- P ≤ B * A * sqrt P
  have h1 : P ≤ B * A * Real.sqrt P := by
    refine hbil.trans (le_of_eq ?_)
    rw [hBdef]; ring
  have h2 : Real.sqrt P ≤ B * A := by
    rcases (Real.sqrt_nonneg P).eq_or_lt with h0 | hpos
    · rw [← h0]; exact mul_nonneg hB hAn
    · have : Real.sqrt P * Real.sqrt P ≤ (B * A) * Real.sqrt P := by
        rw [Real.mul_self_sqrt hPn]; exact h1
      exact le_of_mul_le_mul_right this hpos
  calc P = Real.sqrt P ^ 2 := (Real.sq_sqrt hPn).symm
    _ ≤ (B * A) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    _ = B ^ 2 * A ^ 2 := by ring
    _ = _ := by rw [hAsq]

end HRS.MS.MovInterp
