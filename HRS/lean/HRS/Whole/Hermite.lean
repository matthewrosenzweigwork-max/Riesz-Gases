import HRS.Torus.Basic
import HRS.Whole.GaussianDensity

/-!
# Whole-space foundations I: Hermite functions on `ℝ` and `ℝ^d`

Source: HRS whole-space supplement, `W:eq:euc-oscillator-space` (source lines 287-293) and
`H:eq:oscillator-space` (lines 353-360): "Let `𝓗 = 1 - Δ + |x|²`, with real orthonormal
Hermite functions `h_j` and `𝓗 h_j = λ_j h_j`", enumerated in nondecreasing eigenvalue order.

Mathlib (pin v4.34.1) only has the probabilists' Hermite *polynomials* `Polynomial.hermite n`
(`He_{n+1} = x He_n - He_n'`, `Polynomial.hermite_succ`) and their relation to Gaussian
derivatives (`Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`).  Everything about the
Hermite *functions* is built here.

## Representation decisions

* The one-dimensional `L²(ℝ)`-normalised Hermite functions are
  `h_n(x) = (n! √π)^{-1/2} He_n(√2 x) e^{-x²/2}` (`hermiteFun`).  With the physicists'
  polynomials `H_n(x) = 2^{n/2} He_n(√2 x)` this is the classical
  `(2^n n! √π)^{-1/2} H_n(x) e^{-x²/2}`, the eigenfunction of `-d²/dx² + x²` with eigenvalue
  `2n+1`.
* The `d`-dimensional Hermite functions are indexed by multi-indices `α : Fin d → ℕ`
  (`hermiteFunD α x = ∏ᵢ h_{αᵢ}(xᵢ)`) with eigenvalue `λ_α = 2|α| + d + 1` of
  `𝓗 = 1 - Δ + |x|²` (`oscEigenvalue`).  The source enumerates `(h_j)_{j ≥ 1}` in
  nondecreasing eigenvalue order; every formula of the supplement that involves the basis is
  an order-independent sum (norms, Parseval, `ℓ²` norms of coefficient sequences as in
  `H:eq:whole-initial-orbit`), so indexing by multi-indices is faithful.  The existence of a
  nondecreasing enumeration is recorded as `exists_monotone_enumeration`.
* The elements `hermiteLp n`, `hermiteLpD α` of `L²` are defined by cases on `MemLp`
  (never the bad branch, `memLp_hermiteFun`), so that the definitions contain no `sorry`.
  Orthonormality and completeness are theorems; the `HilbertBasis` itself is
  `exists_hermiteHilbertBasis` (its construction needs the sorried lemmas and is left to the
  proof workers of SFOUND-01).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

/-! ### One-dimensional Hermite functions -/

/-- The probabilists' Hermite polynomial `He_n` evaluated at `x ∈ ℝ`
(Mathlib's `Polynomial.hermite`, `He_{n+1} = x He_n - He_n'`). -/
def hermitePoly (n : ℕ) (x : ℝ) : ℝ := Polynomial.aeval x (Polynomial.hermite n)

/-- The `L²(ℝ)`-normalised Hermite function
`h_n(x) = (n! √π)^{-1/2} He_n(√2 x) e^{-x²/2}`, eigenfunction of `-d²/dx² + x²` with eigenvalue
`2n + 1`. -/
def hermiteFun (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹ *
    hermitePoly n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2 / 2))

open Classical in
/-- The element `h_n ∈ L²(ℝ)`; defined by cases on `MemLp` (the bad branch is never taken,
`memLp_hermiteFun`). -/
def hermiteLp (n : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  if h : MemLp (hermiteFun n) 2 (volume : Measure ℝ) then h.toLp (hermiteFun n) else 0

/-! ### `d`-dimensional Hermite functions -/

/-- Multi-indices `α ∈ ℕ^d`. -/
abbrev MultiIndex (d : ℕ) := Fin d → ℕ

/-- `|α| = ∑ᵢ αᵢ`. -/
def MultiIndex.degree {d : ℕ} (α : MultiIndex d) : ℕ := ∑ i, α i

/-- The tensorised Hermite function `h_α(x) = ∏ᵢ h_{αᵢ}(xᵢ)` on `ℝ^d`. -/
def hermiteFunD {d : ℕ} (α : MultiIndex d) (x : Euc d) : ℝ := ∏ i, hermiteFun (α i) (x i)

/-- The eigenvalue `λ_α = 2|α| + d + 1` of `𝓗 = 1 - Δ + |x|²` on `h_α`
(source lines 288-289, 355-356). -/
def oscEigenvalue (d : ℕ) (α : MultiIndex d) : ℝ := 2 * (α.degree : ℝ) + d + 1

/-- The harmonic-oscillator operator `𝓗 f = f - Δf + |x|² f` (source line 287, 353), with
Mathlib's Laplacian on the inner product space `ℝ^d`. -/
def oscillatorOp {d : ℕ} (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  f x - Laplacian.laplacian f x + ‖x‖ ^ 2 * f x

/-- The normalised test functions `φ_j = λ_j^{-m/2} h_j` of `W:eq:euc-oscillator-space`
(line 290): the orthonormal basis of `Σ^m`. -/
def oscTestFun {d : ℕ} (m : ℝ) (α : MultiIndex d) (x : Euc d) : ℝ :=
  oscEigenvalue d α ^ (-(m / 2)) * hermiteFunD α x

open Classical in
/-- The element `h_α ∈ L²(ℝ^d)` (cases on `MemLp`; the bad branch is never taken). -/
def hermiteLpD {d : ℕ} (α : MultiIndex d) : Lp ℝ 2 (volume : Measure (Euc d)) :=
  if h : MemLp (hermiteFunD α) 2 (volume : Measure (Euc d)) then h.toLp (hermiteFunD α) else 0

/-! ### Facts about the one-dimensional Hermite functions (work package SFOUND-01) -/

section OneDim

/-- Appell property of `Polynomial.hermite` at the level of `ℤ[X]`. -/
theorem derivative_hermite_succ (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite (n + 1)) =
      ((n : Polynomial ℤ) + 1) * Polynomial.hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := Polynomial.hermite_succ n
    have h2 : Polynomial.hermite (n + 1 + 1) = Polynomial.X * Polynomial.hermite (n + 1) -
        Polynomial.derivative (Polynomial.hermite (n + 1)) :=
      Polynomial.hermite_succ (n + 1)
    have h3 : Polynomial.derivative (Polynomial.hermite (n + 1 + 1)) =
        Polynomial.hermite (n + 1) + Polynomial.X * Polynomial.derivative (Polynomial.hermite (n + 1))
        - Polynomial.derivative (Polynomial.derivative (Polynomial.hermite (n + 1))) := by
      rw [h2, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X]; ring
    rw [h3, ih, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_add, Polynomial.derivative_natCast,
      Polynomial.derivative_one, add_zero, zero_mul]
    push_cast
    linear_combination (-((n : Polynomial ℤ) + 1) : Polynomial ℤ) * h1

/-- The Hermite differential equation `He'' - x He' + n He = 0` in `ℤ[X]`. -/
theorem hermite_ode_poly (n : ℕ) :
    Polynomial.derivative (Polynomial.derivative (Polynomial.hermite n)) -
      Polynomial.X * Polynomial.derivative (Polynomial.hermite n) +
        (n : Polynomial ℤ) * Polynomial.hermite n = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have h1 := Polynomial.hermite_succ n
    rw [derivative_hermite_succ, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_add, Polynomial.derivative_natCast,
      Polynomial.derivative_one, add_zero, zero_mul]
    push_cast
    linear_combination (((n : Polynomial ℤ) + 1) : Polynomial ℤ) * h1

theorem deriv_hermitePoly (n : ℕ) (x : ℝ) :
    deriv (hermitePoly n) x = Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n)) :=
  Polynomial.deriv_aeval _

theorem hasDerivAt_hermitePoly (n : ℕ) (x : ℝ) :
    HasDerivAt (hermitePoly n)
      (Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n))) x :=
  (Polynomial.hermite n).hasDerivAt_aeval x

theorem contDiff_hermitePoly (n : ℕ) {k : WithTop ℕ∞} : ContDiff ℝ k (hermitePoly n) :=
  Polynomial.contDiff_aeval _ _

/-- Three-term structure inherited from `Polynomial.hermite_succ`:
`He_{n+1}(x) = x He_n(x) - He_n'(x)`. -/
theorem hermitePoly_succ (n : ℕ) (x : ℝ) :
    hermitePoly (n + 1) x = x * hermitePoly n x - deriv (hermitePoly n) x := by
  rw [deriv_hermitePoly, hermitePoly, Polynomial.hermite_succ]
  simp [map_sub, map_mul, hermitePoly]

/-- `He_{n+1}' = (n+1) He_n` (Appell property; from the coefficient recursion
`Polynomial.coeff_hermite_succ_succ`). -/
theorem deriv_hermitePoly_succ (n : ℕ) (x : ℝ) :
    deriv (hermitePoly (n + 1)) x = (n + 1) * hermitePoly n x := by
  rw [deriv_hermitePoly, derivative_hermite_succ]
  simp [map_mul, hermitePoly]

/-- The normalising constant of `h_n`. -/
def hermiteConst (n : ℕ) : ℝ := (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹

/-- The Gaussian `e^{-x²/2}`. -/
def gauss (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

theorem hermiteFun_eq (n : ℕ) (x : ℝ) :
    hermiteFun n x = hermiteConst n * hermitePoly n (Real.sqrt 2 * x) * gauss x := rfl

theorem hasDerivAt_gauss (x : ℝ) : HasDerivAt gauss (-x * gauss x) x := by
  have h : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x :=
    (((hasDerivAt_pow 2 x).div_const 2).neg).congr_deriv (by simp)
  exact h.exp.congr_deriv (by simp [gauss]; ring)

theorem contDiff_gauss {k : WithTop ℕ∞} : ContDiff ℝ k gauss := by
  unfold gauss; fun_prop

theorem hasDerivAt_hermitePoly_sqrt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => hermitePoly n (Real.sqrt 2 * y))
      (Real.sqrt 2 * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.derivative (Polynomial.hermite n))) x := by
  have h := (hasDerivAt_hermitePoly n (Real.sqrt 2 * x)).comp x ((hasDerivAt_id x).const_mul (Real.sqrt 2))
  exact h.congr_deriv (by simp [mul_comm])

/-- `h_n` is smooth. -/
theorem contDiff_hermiteFun (n : ℕ) : ContDiff ℝ ∞ (hermiteFun n) := by
  have h1 : ContDiff ℝ ∞ (fun y => hermitePoly n (Real.sqrt 2 * y)) :=
    (contDiff_hermitePoly n).comp (contDiff_const.mul contDiff_id)
  have := (contDiff_const (c := hermiteConst n)).mul h1 |>.mul (contDiff_gauss (k := ∞))
  exact this

/-- The Hermite ODE `-h_n'' + x² h_n = (2n+1) h_n` (the one-dimensional case of
`𝓗 h_j = λ_j h_j`, source line 289, up to the additive `1`). -/
theorem hermiteFun_ode (n : ℕ) (x : ℝ) :
    -(iteratedDeriv 2 (hermiteFun n) x) + x ^ 2 * hermiteFun n x =
      (2 * (n : ℝ) + 1) * hermiteFun n x := by
  set c := hermiteConst n with hc
  set s := Real.sqrt 2 with hs
  have hs2 : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  let A1 : ℝ → ℝ := fun y => Polynomial.aeval y (Polynomial.derivative (Polynomial.hermite n))
  let A2 : ℝ → ℝ := fun y =>
    Polynomial.aeval y (Polynomial.derivative (Polynomial.derivative (Polynomial.hermite n)))
  have hA1 : ∀ y, HasDerivAt A1 (A2 y) y := fun y =>
    (Polynomial.derivative (Polynomial.hermite n)).hasDerivAt_aeval y
  have hP : ∀ y, HasDerivAt (fun y => hermitePoly n (s * y)) (s * A1 (s * y)) y :=
    hasDerivAt_hermitePoly_sqrt n
  have hA1' : ∀ y, HasDerivAt (fun y => A1 (s * y)) (s * A2 (s * y)) y := by
    intro y
    have h := (hA1 (s * y)).comp y ((hasDerivAt_id y).const_mul s)
    exact h.congr_deriv (by simp [mul_comm])
  -- first derivative
  have hd1 : ∀ y, HasDerivAt (hermiteFun n)
      (c * (s * A1 (s * y) - y * hermitePoly n (s * y)) * gauss y) y := by
    intro y
    have h := (((hP y).const_mul c).mul (hasDerivAt_gauss y))
    exact h.congr_deriv (by ring)
  have hderiv1 : deriv (hermiteFun n) =
      fun y => c * (s * A1 (s * y) - y * hermitePoly n (s * y)) * gauss y :=
    funext fun y => (hd1 y).deriv
  have hd2 : ∀ y, HasDerivAt (fun y => c * (s * A1 (s * y) - y * hermitePoly n (s * y)) * gauss y)
      (c * ((s * (s * A2 (s * y))) - (hermitePoly n (s * y) + y * (s * A1 (s * y)))) * gauss y +
        c * (s * A1 (s * y) - y * hermitePoly n (s * y)) * (-y * gauss y)) y := by
    intro y
    have h1 := ((hA1' y).const_mul s)
    have h2 := (hasDerivAt_id y).mul (hP y)
    have h := (((h1.sub h2).const_mul c).mul (hasDerivAt_gauss y))
    exact h.congr_deriv (by simp)
  have hII : iteratedDeriv 2 (hermiteFun n) x =
      c * ((s * (s * A2 (s * x))) - (hermitePoly n (s * x) + x * (s * A1 (s * x)))) * gauss x +
        c * (s * A1 (s * x) - x * hermitePoly n (s * x)) * (-x * gauss x) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv1]
    exact (hd2 x).deriv
  have hode := congrArg (fun p => Polynomial.aeval (s * x) p) (hermite_ode_poly n)
  simp only [map_add, map_sub, map_mul, Polynomial.aeval_X, map_zero, map_natCast] at hode
  have hode' : A2 (s * x) - (s * x) * A1 (s * x) + n * hermitePoly n (s * x) = 0 := hode
  rw [hII, hermiteFun_eq]
  have : A2 (s * x) = (s * x) * A1 (s * x) - n * hermitePoly n (s * x) := by linarith
  rw [this]
  have e : s * (s * ((s * x) * A1 (s * x) - n * hermitePoly n (s * x))) =
      2 * (s * x * A1 (s * x) - n * hermitePoly n (s * x)) := by
    rw [← mul_assoc, hs2]
  rw [e]
  have e2 : s * x * A1 (s * x) * 2 = 2 * (s * x * A1 (s * x)) := by ring
  have e3 : 2 * x * (s * A1 (s * x)) = 2 * (s * x * A1 (s * x)) := by ring
  nlinarith [e2, e3]

theorem integrable_pow_mul_exp_neg_mul_sq' (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ)) (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith)
  simpa [Real.rpow_natCast] using this

theorem integrable_poly_mul_exp_neg_mul_sq (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have := hp.add hq
    simp only [Polynomial.eval_add, add_mul]
    exact this
  | monomial k a =>
    simpa [mul_assoc] using (integrable_pow_mul_exp_neg_mul_sq' k hb).const_mul a

/-- The real polynomial `He_n`. -/
def hermiteR (n : ℕ) : Polynomial ℝ := (Polynomial.hermite n).map (Int.castRingHom ℝ)

theorem hermitePoly_eq_eval (n : ℕ) (x : ℝ) : hermitePoly n x = (hermiteR n).eval x := by
  simp [hermitePoly, hermiteR, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

theorem hermiteFun_eq_poly (n : ℕ) :
    ∃ p : Polynomial ℝ, ∀ x, hermiteFun n x = p.eval x * Real.exp (-(1 / 2) * x ^ 2) := by
  refine ⟨Polynomial.C (hermiteConst n) * (hermiteR n).comp (Polynomial.C (Real.sqrt 2) * Polynomial.X), fun x => ?_⟩
  simp only [hermiteFun_eq, hermitePoly_eq_eval, gauss, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_X]
  congr 2
  ring

/-- `h_n ∈ L¹(ℝ)`. -/
theorem integrable_hermiteFun (n : ℕ) : Integrable (hermiteFun n) (volume : Measure ℝ) := by
  obtain ⟨p, hp⟩ := hermiteFun_eq_poly n
  have : hermiteFun n = fun x => p.eval x * Real.exp (-(1 / 2) * x ^ 2) := funext hp
  rw [this]
  exact integrable_poly_mul_exp_neg_mul_sq p (by norm_num)

theorem integrable_hermiteFun_mul (n m : ℕ) :
    Integrable (fun x => hermiteFun n x * hermiteFun m x) (volume : Measure ℝ) := by
  obtain ⟨p, hp⟩ := hermiteFun_eq_poly n
  obtain ⟨q, hq⟩ := hermiteFun_eq_poly m
  have : (fun x => hermiteFun n x * hermiteFun m x) =
      fun x => (p * q).eval x * Real.exp (-1 * x ^ 2) := by
    funext x
    rw [hp, hq, Polynomial.eval_mul, mul_mul_mul_comm, ← Real.exp_add]
    congr 2
    ring
  rw [this]
  exact integrable_poly_mul_exp_neg_mul_sq _ (by norm_num)

/-- `h_n ∈ L²(ℝ)`. -/
theorem memLp_hermiteFun (n : ℕ) : MemLp (hermiteFun n) 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq (contDiff_hermiteFun n).continuous.aestronglyMeasurable]
  simpa [sq] using integrable_hermiteFun_mul n n

theorem gauss_eq (x : ℝ) : gauss x = Real.exp (-(1 / 2) * x ^ 2) := by
  unfold gauss; congr 1; ring

theorem integrable_poly_mul_gauss (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x * gauss x) (volume : Measure ℝ) := by
  simp_rw [gauss_eq]
  exact integrable_poly_mul_exp_neg_mul_sq p (by norm_num)

theorem integral_gauss : ∫ x : ℝ, gauss x = Real.sqrt (2 * Real.pi) := by
  have := integral_gaussian (1 / 2)
  simp_rw [gauss_eq]
  rw [this]
  congr 1
  field_simp

/-- Weighted integration by parts for polynomials against the Gaussian weight. -/
theorem integral_poly_ibp (p q : Polynomial ℝ) :
    ∫ x : ℝ, ((Polynomial.X * p - Polynomial.derivative p) * q).eval x * gauss x =
      ∫ x : ℝ, (p * Polynomial.derivative q).eval x * gauss x := by
  have hu : ∀ x ∈ tsupport (fun x => p.eval x * gauss x), HasDerivAt (fun x => q.eval x)
      ((Polynomial.derivative q).eval x) x := fun x _ => q.hasDerivAt x
  have hv : ∀ x ∈ tsupport (fun x => q.eval x), HasDerivAt (fun x => p.eval x * gauss x)
      ((Polynomial.derivative p).eval x * gauss x + p.eval x * (-x * gauss x)) x := fun x _ =>
    (p.hasDerivAt x).mul (hasDerivAt_gauss x)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => q.eval x) (v := fun x => p.eval x * gauss x)
    (u' := fun x => (Polynomial.derivative q).eval x)
    (v' := fun x => (Polynomial.derivative p).eval x * gauss x + p.eval x * (-x * gauss x))
    hu hv ?_ ?_ ?_
  · have e1 : (fun x : ℝ => ((Polynomial.X * p - Polynomial.derivative p) * q).eval x * gauss x) =
        fun x => -(q.eval x * ((Polynomial.derivative p).eval x * gauss x +
          p.eval x * (-x * gauss x))) := by
      funext x; simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X]; ring
    have e2 : (fun x : ℝ => (p * Polynomial.derivative q).eval x * gauss x) =
        fun x => (Polynomial.derivative q).eval x * (p.eval x * gauss x) := by
      funext x; simp only [Polynomial.eval_mul]; ring
    rw [e1, e2, integral_neg, key]
    simp
  · have : (fun x : ℝ => q.eval x * ((Polynomial.derivative p).eval x * gauss x +
        p.eval x * (-x * gauss x))) =
        fun x => (q * (Polynomial.derivative p - Polynomial.X * p)).eval x * gauss x := by
      funext x; simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X]; ring
    show Integrable (fun x => q.eval x * ((Polynomial.derivative p).eval x * gauss x +
        p.eval x * (-x * gauss x))) _
    rw [this]; exact integrable_poly_mul_gauss _
  · have : (fun x : ℝ => (Polynomial.derivative q).eval x * (p.eval x * gauss x)) =
        fun x => (Polynomial.derivative q * p).eval x * gauss x := by
      funext x; simp only [Polynomial.eval_mul]; ring
    show Integrable (fun x => (Polynomial.derivative q).eval x * (p.eval x * gauss x)) _
    rw [this]; exact integrable_poly_mul_gauss _
  · have : (fun x : ℝ => q.eval x * (p.eval x * gauss x)) =
        fun x => (q * p).eval x * gauss x := by
      funext x; simp only [Polynomial.eval_mul]; ring
    show Integrable (fun x => q.eval x * (p.eval x * gauss x)) _
    rw [this]; exact integrable_poly_mul_gauss _

theorem hermiteR_succ (n : ℕ) :
    hermiteR (n + 1) = Polynomial.X * hermiteR n - Polynomial.derivative (hermiteR n) := by
  simp [hermiteR, Polynomial.hermite_succ, Polynomial.derivative_map]

theorem derivative_hermiteR_succ (n : ℕ) :
    Polynomial.derivative (hermiteR (n + 1)) = ((n : Polynomial ℝ) + 1) * hermiteR n := by
  have := congrArg (Polynomial.map (Int.castRingHom ℝ)) (derivative_hermite_succ n)
  simpa [hermiteR, Polynomial.derivative_map] using this

theorem natDegree_hermiteR (n : ℕ) : (hermiteR n).natDegree ≤ n := by
  unfold hermiteR
  exact (Polynomial.natDegree_map_le).trans (by simp)

theorem iterate_derivative_hermiteR_self (n : ℕ) :
    (Polynomial.derivative)^[n] (hermiteR n) = (n.factorial : Polynomial ℝ) := by
  induction n with
  | zero => simp [hermiteR]
  | succ n ih =>
    rw [Function.iterate_succ_apply, derivative_hermiteR_succ]
    have : ((n : Polynomial ℝ) + 1) * hermiteR n = (n + 1 : ℝ) • hermiteR n := by
      rw [Polynomial.smul_eq_C_mul]; simp
    rw [this, Polynomial.iterate_derivative_smul, ih]
    simp [Nat.factorial_succ]
    rw [Polynomial.smul_eq_C_mul]; simp

theorem integral_hermiteR_mul_poly (n : ℕ) :
    ∀ q : Polynomial ℝ, ∫ x : ℝ, (hermiteR n * q).eval x * gauss x =
      ∫ x : ℝ, ((Polynomial.derivative)^[n] q).eval x * gauss x := by
  induction n with
  | zero => intro q; simp [show hermiteR 0 = 1 by simp [hermiteR]]
  | succ n ih =>
    intro q
    rw [hermiteR_succ, integral_poly_ibp, Function.iterate_succ_apply, ← ih]

theorem integral_hermiteR_mul_hermiteR (n m : ℕ) :
    ∫ x : ℝ, (hermiteR n * hermiteR m).eval x * gauss x =
      if n = m then (n.factorial : ℝ) * Real.sqrt (2 * Real.pi) else 0 := by
  rcases lt_trichotomy m n with h | h | h
  · rw [integral_hermiteR_mul_poly, Polynomial.iterate_derivative_eq_zero
      (lt_of_le_of_lt (natDegree_hermiteR m) h)]
    simp [ne_of_gt h]
  · subst h
    rw [integral_hermiteR_mul_poly, iterate_derivative_hermiteR_self]
    simp [integral_const_mul, integral_gauss]
  · rw [mul_comm, integral_hermiteR_mul_poly, Polynomial.iterate_derivative_eq_zero
      (lt_of_le_of_lt (natDegree_hermiteR n) h)]
    simp [ne_of_lt h]

theorem gauss_mul_gauss (x : ℝ) : gauss x * gauss x = gauss (Real.sqrt 2 * x) := by
  unfold gauss
  rw [← Real.exp_add]
  congr 1
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem hermiteConst_sq (n : ℕ) : hermiteConst n ^ 2 = ((n.factorial : ℝ) * Real.sqrt Real.pi)⁻¹ := by
  unfold hermiteConst
  rw [inv_pow, Real.sq_sqrt]
  positivity

/-- Orthonormality `∫ h_n h_m dx = δ_{nm}` ("real orthonormal Hermite functions", line 354). -/
theorem hermiteFun_orthonormal (n m : ℕ) :
    ∫ x, hermiteFun n x * hermiteFun m x = if n = m then 1 else 0 := by
  have e : (fun x => hermiteFun n x * hermiteFun m x) = fun x =>
      hermiteConst n * hermiteConst m *
        ((fun y => (hermiteR n * hermiteR m).eval y * gauss y) (Real.sqrt 2 * x)) := by
    funext x
    simp only [hermiteFun_eq, hermitePoly_eq_eval, Polynomial.eval_mul, ← gauss_mul_gauss]
    ring
  rw [e, integral_const_mul]
  have hsc := Measure.integral_comp_mul_left
    (fun y => (hermiteR n * hermiteR m).eval y * gauss y) (Real.sqrt 2)
  rw [hsc, integral_hermiteR_mul_hermiteR]
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hp : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := Real.sqrt_mul (by norm_num) _
  split_ifs with h
  · subst h
    have := hermiteConst_sq n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [abs_of_pos (by positivity)]
    simp only [smul_eq_mul]
    rw [h2]
    have : hermiteConst n * hermiteConst n = ((n.factorial : ℝ) * Real.sqrt Real.pi)⁻¹ := by
      rw [← sq]; exact this
    rw [← mul_assoc, this]
    field_simp
  · simp

theorem hermiteFun_eq_poly' (n : ℕ) :
    ∃ p : Polynomial ℝ, ∀ x, hermiteFun n x = p.eval x * gauss x := by
  obtain ⟨p, hp⟩ := hermiteFun_eq_poly n
  exact ⟨p, fun x => by rw [hp x, gauss_eq]⟩

theorem hasDerivAt_poly_mul_gauss (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun x => p.eval x * gauss x)
      (((Polynomial.derivative p) - Polynomial.X * p).eval x * gauss x) x :=
  ((p.hasDerivAt x).mul (hasDerivAt_gauss x)).congr_deriv (by simp; ring)

theorem gauss_mul_self (x : ℝ) : gauss x * gauss x = Real.exp (-1 * x ^ 2) := by
  unfold gauss; rw [← Real.exp_add]; congr 1; ring

theorem integrable_polygauss_mul (a b : Polynomial ℝ) :
    Integrable (fun x : ℝ => (a.eval x * gauss x) * (b.eval x * gauss x)) := by
  have : (fun x : ℝ => (a.eval x * gauss x) * (b.eval x * gauss x)) =
      fun x => (a * b).eval x * Real.exp (-1 * x ^ 2) := by
    funext x
    rw [Polynomial.eval_mul, ← gauss_mul_self]; ring
  rw [this]
  exact integrable_poly_mul_exp_neg_mul_sq _ (by norm_num)

/-- `∫ h'² ≤ 2n+1`. -/
theorem integral_deriv_hermiteFun_sq_le (n : ℕ) :
    ∃ q : Polynomial ℝ, (∀ x, HasDerivAt (hermiteFun n) (q.eval x * gauss x) x) ∧
      ∫ x, (q.eval x * gauss x) * (q.eval x * gauss x) ≤ 2 * (n : ℝ) + 1 := by
  obtain ⟨p, hp⟩ := hermiteFun_eq_poly' n
  have hh : hermiteFun n = fun x => p.eval x * gauss x := funext hp
  set q := Polynomial.derivative p - Polynomial.X * p with hq
  set r := Polynomial.derivative q - Polynomial.X * q with hr
  have hd1 : ∀ x, HasDerivAt (hermiteFun n) (q.eval x * gauss x) x := by
    rw [hh]; exact hasDerivAt_poly_mul_gauss p
  have hder1 : deriv (hermiteFun n) = fun x => q.eval x * gauss x :=
    funext fun x => (hd1 x).deriv
  have hd2 : ∀ x, HasDerivAt (deriv (hermiteFun n)) (r.eval x * gauss x) x := by
    rw [hder1]; exact hasDerivAt_poly_mul_gauss q
  have hode : ∀ x, r.eval x * gauss x = (x ^ 2 - (2 * (n : ℝ) + 1)) * hermiteFun n x := by
    intro x
    have h := hermiteFun_ode n x
    rw [iteratedDeriv_succ, iteratedDeriv_one, (hd2 x).deriv] at h
    linarith
  have hint : ∀ a b : Polynomial ℝ, Integrable (fun x : ℝ => (a.eval x * gauss x) * (b.eval x * gauss x)) :=
    integrable_polygauss_mul
  refine ⟨q, hd1, ?_⟩
  -- integration by parts
  have hIBP : ∫ x, hermiteFun n x * (r.eval x * gauss x) =
      - ∫ x, (q.eval x * gauss x) * (q.eval x * gauss x) := by
    have := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := hermiteFun n) (v := fun x => q.eval x * gauss x)
      (u' := fun x => q.eval x * gauss x) (v' := fun x => r.eval x * gauss x)
      (fun x _ => hd1 x) (fun x _ => by
        have := hd2 x
        rwa [hder1] at this)
      ?_ ?_ ?_
    · exact this
    · simp only [Pi.mul_def]
      have : (fun x => hermiteFun n x * (r.eval x * gauss x)) =
          fun x => (p.eval x * gauss x) * (r.eval x * gauss x) := by funext x; rw [hp]
      rw [this]; exact hint p r
    · exact hint q q
    · have : (fun x => hermiteFun n x * (q.eval x * gauss x)) =
          fun x => (p.eval x * gauss x) * (q.eval x * gauss x) := by funext x; rw [hp]
      simp only [Pi.mul_def]
      rw [this]; exact hint p q
  have hhh : Integrable (fun x => hermiteFun n x * hermiteFun n x) := integrable_hermiteFun_mul n n
  have hx2 : Integrable (fun x : ℝ => x ^ 2 * (hermiteFun n x * hermiteFun n x)) := by
    have : (fun x : ℝ => x ^ 2 * (hermiteFun n x * hermiteFun n x)) =
        fun x => ((Polynomial.X ^ 2 * p).eval x * gauss x) * (p.eval x * gauss x) := by
      funext x; rw [hp]; simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]; ring
    rw [this]; exact hint _ _
  have e1 : ∫ x, hermiteFun n x * (r.eval x * gauss x) =
      ∫ x, (x ^ 2 * (hermiteFun n x * hermiteFun n x) -
        (2 * (n : ℝ) + 1) * (hermiteFun n x * hermiteFun n x)) := by
    congr 1; funext x; rw [hode]; ring
  rw [e1, integral_sub hx2 (hhh.const_mul _), integral_const_mul,
    hermiteFun_orthonormal n n] at hIBP
  have hnn : 0 ≤ ∫ x, x ^ 2 * (hermiteFun n x * hermiteFun n x) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg x) (mul_self_nonneg _)
  simp only [ite_true] at hIBP
  linarith

theorem hermiteFun_sq_le (n : ℕ) (x : ℝ) :
    hermiteFun n x * hermiteFun n x ≤ 2 * Real.sqrt (2 * (n : ℝ) + 1) := by
  obtain ⟨q, hd1, hq⟩ := integral_deriv_hermiteFun_sq_le n
  obtain ⟨p, hp⟩ := hermiteFun_eq_poly' n
  have hn : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  set t := Real.sqrt (2 * (n : ℝ) + 1) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr hn
  have ht2 : t * t = 2 * (n : ℝ) + 1 := Real.mul_self_sqrt hn.le
  have hderiv : ∀ y, HasDerivAt (fun y => hermiteFun n y * hermiteFun n y)
      ((q.eval y * gauss y) * hermiteFun n y + hermiteFun n y * (q.eval y * gauss y)) y :=
    fun y => (hd1 y).mul (hd1 y)
  have hf'int : Integrable (fun y => (q.eval y * gauss y) * hermiteFun n y +
      hermiteFun n y * (q.eval y * gauss y)) := by
    have e : (fun y => (q.eval y * gauss y) * hermiteFun n y +
        hermiteFun n y * (q.eval y * gauss y)) =
        fun y => (q.eval y * gauss y) * (p.eval y * gauss y) +
          (p.eval y * gauss y) * (q.eval y * gauss y) := by
      funext y; rw [hp]
    rw [e]
    exact (integrable_polygauss_mul q p).add (integrable_polygauss_mul p q)
  have hfint := integrable_hermiteFun_mul n n
  have hzero := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := x) (fun y _ => hderiv y)
    hf'int.integrableOn hfint.integrableOn
  have hftc := integral_Iic_of_hasDerivAt_of_tendsto' (a := x) (fun y _ => hderiv y)
    hf'int.integrableOn hzero
  rw [sub_zero] at hftc
  have hqq : Integrable (fun y => (q.eval y * gauss y) * (q.eval y * gauss y)) :=
    integrable_polygauss_mul q q
  have hG : Integrable (fun y => t * (hermiteFun n y * hermiteFun n y) +
      (1 / t) * ((q.eval y * gauss y) * (q.eval y * gauss y))) :=
    (hfint.const_mul t).add (hqq.const_mul (1 / t))
  have hpt : ∀ y, (q.eval y * gauss y) * hermiteFun n y + hermiteFun n y * (q.eval y * gauss y) ≤
      t * (hermiteFun n y * hermiteFun n y) +
        (1 / t) * ((q.eval y * gauss y) * (q.eval y * gauss y)) := by
    intro y
    set a := hermiteFun n y
    set b := q.eval y * gauss y
    have : 2 * a * b * t ≤ t * a * a * t + b * b := by nlinarith [sq_nonneg (t * a - b)]
    have h1 : 2 * a * b ≤ t * (a * a) + (1 / t) * (b * b) := by
      rw [← sub_nonneg]
      have : t * (a * a) + (1 / t) * (b * b) - 2 * a * b = (t * a - b) ^ 2 / t := by
        field_simp; ring
      rw [this]; positivity
    linarith
  have hmono : ∫ y in Set.Iic x, ((q.eval y * gauss y) * hermiteFun n y +
      hermiteFun n y * (q.eval y * gauss y)) ≤ ∫ y in Set.Iic x, (t * (hermiteFun n y * hermiteFun n y) +
        (1 / t) * ((q.eval y * gauss y) * (q.eval y * gauss y))) :=
    setIntegral_mono_on hf'int.integrableOn hG.integrableOn measurableSet_Iic fun y _ => hpt y
  have hle : ∫ y in Set.Iic x, (t * (hermiteFun n y * hermiteFun n y) +
        (1 / t) * ((q.eval y * gauss y) * (q.eval y * gauss y))) ≤
      ∫ y, (t * (hermiteFun n y * hermiteFun n y) +
        (1 / t) * ((q.eval y * gauss y) * (q.eval y * gauss y))) :=
    setIntegral_le_integral hG (Eventually.of_forall fun y => by
      have := mul_self_nonneg (hermiteFun n y)
      have := mul_self_nonneg (q.eval y * gauss y)
      positivity)
  have htot : ∫ y, (t * (hermiteFun n y * hermiteFun n y) +
        (1 / t) * ((q.eval y * gauss y) * (q.eval y * gauss y))) ≤ 2 * t := by
    rw [integral_add (hfint.const_mul t) (hqq.const_mul (1 / t)), integral_const_mul,
      integral_const_mul, hermiteFun_orthonormal n n]
    simp only [ite_true]
    have h2 : (1 / t) * ∫ y, (q.eval y * gauss y) * (q.eval y * gauss y) ≤ (1 / t) * (t * t) := by
      rw [ht2]
      exact mul_le_mul_of_nonneg_left hq (by positivity)
    have h3 : (1 / t) * (t * t) = t := by field_simp
    linarith
  linarith


/-! #### Cramér's inequality: route of the proof

Fix `y = √2 x`, `n ≥ 1`, `s = √n`.
1. `G_y(t) = exp(y t - t²/2)` is entire and `(d/dt)^n G_y (t) = G_y(t) He_n(y - t)`
   (`CramerAux.iteratedDeriv_genFun`), so `iteratedDeriv n G_y 0 = He_n(y)`.
2. Cauchy's formula for derivatives on the circle of radius `s`
   (`DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul`) gives
   `|He_n(y)| ≤ n!/(2π) s^{-n} ∫_0^{2π} |G_y(s e^{iθ})| dθ`.
3. `|G_y(s e^{iθ})| = exp(n/2 + y²/4 - (s cos θ - y/2)²)`.
4. `∫_0^{2π} exp(-(s cos θ - b)²) dθ ≤ 14 / √s` for `s ≥ 1`, uniformly in `b`: bound
   `exp(-v²) ≤ 1/(1+v²)`, split `[0, π]` into `[0,a] ∪ [a, π-a] ∪ [π-a, π]` with `a = s^{-1/2}`;
   the outer pieces contribute `≤ a` each, and on the middle piece `sin θ ≥ sin a ≥ 2a/π`, so the
   integrand is `≤ (1/(s sin a)) (d/dθ)(-arctan(s cos θ - b))`, giving `≤ π / (s sin a)`.
   The piece `[π, 2π]` is the case `b ↦ -b` of `[0, π]`.
5. Stirling: `n! ≤ e √n (n/e)^n` (monotonicity of `stirlingSeq`).
6. Combine: `|h_n(x)| ≤ (√(n! √π))^{-1} n!/(2π) s^{-n} e^{n/2} 14/√s ≤ 7 √e`. -/

section CramerAux
open scoped Real
namespace CramerAux

/-- the antiderivative piece -/
lemma hasDerivAt_negArctan (s b θ : ℝ) :
    HasDerivAt (fun θ => -Real.arctan (s * Real.cos θ - b))
      (s * Real.sin θ / (1 + (s * Real.cos θ - b) ^ 2)) θ := by
  have h1 : HasDerivAt (fun θ => s * Real.cos θ - b) (-(s * Real.sin θ)) θ := by
    simpa using ((Real.hasDerivAt_cos θ).const_mul s).sub_const b
  have h2 := (Real.hasDerivAt_arctan (s * Real.cos θ - b)).comp θ h1
  have h3 := h2.neg
  refine h3.congr_deriv ?_
  ring

lemma integral_middle (s b a : ℝ) (hs : 0 < s) (ha : 0 < a) (hapi : a ≤ π / 2) :
    ∫ θ in a..(π - a), 1 / (1 + (s * Real.cos θ - b) ^ 2) ≤ π / (s * Real.sin a) := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])
  have hc : 0 < s * Real.sin a := mul_pos hs hsa
  have hab : a ≤ π - a := by linarith
  have hD : ∀ θ ∈ Set.uIcc a (π - a), HasDerivAt (fun θ => -Real.arctan (s * Real.cos θ - b))
      (s * Real.sin θ / (1 + (s * Real.cos θ - b) ^ 2)) θ := fun θ _ => hasDerivAt_negArctan s b θ
  have hcont : Continuous (fun θ : ℝ => s * Real.sin θ / (1 + (s * Real.cos θ - b) ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ; positivity
  have hDint : IntervalIntegrable (fun θ : ℝ => s * Real.sin θ / (1 + (s * Real.cos θ - b) ^ 2))
      volume a (π - a) := hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hDint
  have hfc : Continuous (fun θ : ℝ => 1 / (1 + (s * Real.cos θ - b) ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ; positivity
  have hmono : ∫ θ in a..(π - a), 1 / (1 + (s * Real.cos θ - b) ^ 2) ≤
      ∫ θ in a..(π - a), (1 / (s * Real.sin a)) *
        (s * Real.sin θ / (1 + (s * Real.cos θ - b) ^ 2)) := by
    apply intervalIntegral.integral_mono_on hab (hfc.intervalIntegrable _ _)
      ((continuous_const.mul hcont).intervalIntegrable _ _)
    intro θ hθ
    have hsin : Real.sin a ≤ Real.sin θ := by
      rcases le_total θ (π / 2) with h | h
      · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h hθ.1
      · rw [← Real.sin_pi_sub θ]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith [hθ.2])
    have hq : 0 < 1 + (s * Real.cos θ - b) ^ 2 := by positivity
    show 1 / (1 + (s * Real.cos θ - b) ^ 2) ≤ (1 / (s * Real.sin a)) *
        (s * Real.sin θ / (1 + (s * Real.cos θ - b) ^ 2))
    rw [one_div_mul_eq_div, div_div, div_le_div_iff₀ hq (mul_pos hq hc)]
    · nlinarith [mul_le_mul_of_nonneg_left hsin hs.le]
  rw [intervalIntegral.integral_const_mul, hFTC] at hmono
  refine hmono.trans ?_
  have : (fun θ => -Real.arctan (s * Real.cos θ - b)) (π - a) -
      (fun θ => -Real.arctan (s * Real.cos θ - b)) a ≤ π := by
    simp only
    have h1 := Real.arctan_lt_pi_div_two (s * Real.cos a - b)
    have h2 := Real.neg_pi_div_two_lt_arctan (s * Real.cos (π - a) - b)
    linarith
  rw [one_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right this hc.le


lemma integral_half (s b : ℝ) (hs : 1 ≤ s) :
    ∫ θ in (0:ℝ)..π, 1 / (1 + (s * Real.cos θ - b) ^ 2) ≤ 7 / Real.sqrt s := by
  have hs0 : 0 < s := by linarith
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsq1 : 1 ≤ Real.sqrt s := by simpa using Real.sqrt_le_sqrt hs
  set a := 1 / Real.sqrt s with ha_def
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha_def]; exact (div_le_one hsq).2 hsq1
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hapi : a ≤ π / 2 := by linarith
  have hfc : Continuous (fun θ : ℝ => 1 / (1 + (s * Real.cos θ - b) ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ; positivity
  have hle1 : ∀ θ : ℝ, 1 / (1 + (s * Real.cos θ - b) ^ 2) ≤ 1 := fun θ => by
    rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (s * Real.cos θ - b)]
  have hout : ∀ u v : ℝ, u ≤ v → ∫ θ in u..v, 1 / (1 + (s * Real.cos θ - b) ^ 2) ≤ v - u := by
    intro u v huv
    have := intervalIntegral.integral_mono_on huv (hfc.intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := (1:ℝ))) (fun θ _ => hle1 θ)
    simpa using this
  have hmid := integral_middle s b a hs0 ha hapi
  have hsina : 2 / π * a ≤ Real.sin a := Real.mul_le_sin ha.le hapi
  have hsa_pos : 0 < 2 / π * a := by positivity
  have h1 : ∫ θ in (0:ℝ)..π, 1 / (1 + (s * Real.cos θ - b) ^ 2) =
      (∫ θ in (0:ℝ)..a, 1 / (1 + (s * Real.cos θ - b) ^ 2)) +
      (∫ θ in a..(π - a), 1 / (1 + (s * Real.cos θ - b) ^ 2)) +
      ∫ θ in (π - a)..π, 1 / (1 + (s * Real.cos θ - b) ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
  have e1 := hout 0 a ha.le
  have e3 := hout (π - a) π (by linarith)
  have hsa : s * a = Real.sqrt s := by
    rw [ha_def]; field_simp; exact (Real.sq_sqrt hs0.le).symm
  have e2 : π / (s * Real.sin a) ≤ π ^ 2 / 2 / Real.sqrt s := by
    have : s * (2 / π * a) ≤ s * Real.sin a := mul_le_mul_of_nonneg_left hsina hs0.le
    calc π / (s * Real.sin a) ≤ π / (s * (2 / π * a)) :=
          div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) this
      _ = π ^ 2 / 2 / Real.sqrt s := by
          rw [← hsa]; field_simp
  have hpi2 : π ^ 2 / 2 ≤ 5 := by nlinarith [Real.pi_lt_d2]
  have ha' : a = 1 / Real.sqrt s := ha_def
  calc _ ≤ (a - 0) + π ^ 2 / 2 / Real.sqrt s + (π - (π - a)) := by
        rw [h1]; linarith
    _ ≤ 7 / Real.sqrt s := by
        have : π ^ 2 / 2 / Real.sqrt s ≤ 5 / Real.sqrt s :=
          div_le_div_of_nonneg_right hpi2 hsq.le
        rw [ha'] at *
        have h7 : (1 / Real.sqrt s - 0) + (π - (π - 1 / Real.sqrt s)) = 2 / Real.sqrt s := by ring
        have : 7 / Real.sqrt s = 2 / Real.sqrt s + 5 / Real.sqrt s := by ring
        linarith


lemma exp_le_inv (v : ℝ) : Real.exp (-v ^ 2) ≤ 1 / (1 + v ^ 2) := by
  have h := Real.add_one_le_exp (v ^ 2)
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma integral_half_exp (s b : ℝ) (hs : 1 ≤ s) :
    ∫ θ in (0:ℝ)..π, Real.exp (-(s * Real.cos θ - b) ^ 2) ≤ 7 / Real.sqrt s := by
  refine le_trans (intervalIntegral.integral_mono_on Real.pi_pos.le ?_ ?_ (fun θ _ => exp_le_inv _))
    (integral_half s b hs)
  · exact (by fun_prop : Continuous fun θ : ℝ => Real.exp (-(s * Real.cos θ - b) ^ 2)).intervalIntegrable _ _
  · exact (Continuous.div (by fun_prop) (by fun_prop) (fun θ => by positivity) :
      Continuous fun θ : ℝ => 1 / (1 + (s * Real.cos θ - b) ^ 2)).intervalIntegrable _ _

lemma integral_full_exp (s b : ℝ) (hs : 1 ≤ s) :
    ∫ θ in (0:ℝ)..(2 * π), Real.exp (-(s * Real.cos θ - b) ^ 2) ≤ 14 / Real.sqrt s := by
  have hc : Continuous fun θ : ℝ => Real.exp (-(s * Real.cos θ - b) ^ 2) := by fun_prop
  have h1 : ∫ θ in (0:ℝ)..(2 * π), Real.exp (-(s * Real.cos θ - b) ^ 2) =
      (∫ θ in (0:ℝ)..π, Real.exp (-(s * Real.cos θ - b) ^ 2)) +
      ∫ θ in π..(2 * π), Real.exp (-(s * Real.cos θ - b) ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have h2 : ∫ θ in π..(2 * π), Real.exp (-(s * Real.cos θ - b) ^ 2) =
      ∫ θ in (0:ℝ)..π, Real.exp (-(s * Real.cos θ - (-b)) ^ 2) := by
    have := intervalIntegral.integral_comp_add_right
      (fun θ : ℝ => Real.exp (-(s * Real.cos θ - b) ^ 2)) (a := 0) (b := π) π
    rw [zero_add, show π + π = 2 * π by ring] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [Real.cos_add_pi]
    ring_nf
  rw [h1, h2]
  have := integral_half_exp s b hs
  have := integral_half_exp s (-b) hs
  have : (14 : ℝ) / Real.sqrt s = 7 / Real.sqrt s + 7 / Real.sqrt s := by ring
  linarith


/-- generating function `G_y(t) = exp(y t - t²/2)` -/
noncomputable def genFun (y : ℝ) (t : ℂ) : ℂ := Complex.exp ((y : ℂ) * t - t ^ 2 / 2)

lemma hasDerivAt_genFun (y : ℝ) (t : ℂ) :
    HasDerivAt (genFun y) (((y : ℂ) - t) * genFun y t) t := by
  have h : HasDerivAt (fun t : ℂ => (y : ℂ) * t - t ^ 2 / 2) ((y : ℂ) - t) t := by
    have := (((hasDerivAt_id t).const_mul (y : ℂ)).sub ((hasDerivAt_pow 2 t).div_const 2))
    refine this.congr_deriv ?_
    simp
  exact (h.cexp).congr_deriv (by simp [genFun]; ring)

lemma differentiable_genFun (y : ℝ) : Differentiable ℂ (genFun y) :=
  fun t => (hasDerivAt_genFun y t).differentiableAt

lemma iteratedDeriv_genFun (y : ℝ) (n : ℕ) :
    iteratedDeriv n (genFun y) =
      fun t => genFun y t * Polynomial.aeval ((y : ℂ) - t) (Polynomial.hermite n) := by
  induction n with
  | zero => funext t; simp [Polynomial.hermite_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h1 := hasDerivAt_genFun y t
    have h2 : HasDerivAt (fun t : ℂ => Polynomial.aeval ((y : ℂ) - t) (Polynomial.hermite n))
        (-(Polynomial.aeval ((y : ℂ) - t) (Polynomial.derivative (Polynomial.hermite n)))) t := by
      have := (Polynomial.hermite n).hasDerivAt_aeval ((y : ℂ) - t)
      have h3 : HasDerivAt (fun t : ℂ => (y : ℂ) - t) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (y : ℂ)
      exact (this.comp t h3).congr_deriv (by ring)
    refine (h1.mul h2).deriv.trans ?_
    rw [Polynomial.hermite_succ]
    simp only [map_sub, map_mul, Polynomial.aeval_X]
    ring


lemma norm_iteratedDeriv_genFun_le (y : ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ‖iteratedDeriv n (genFun y) 0‖ ≤
      (n.factorial : ℝ) / (2 * π) * (r⁻¹ ^ n * ∫ θ in (0:ℝ)..(2 * π), ‖genFun y (circleMap 0 r θ)‖) := by
  have hcau := (differentiable_genFun y).differentiableOn.diffContOnCl (s := Metric.ball 0 r)
  have h := hcau.circleIntegral_one_div_sub_center_pow_smul hr n
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : iteratedDeriv n (genFun y) 0 =
      ((n.factorial : ℂ) / (2 * π * Complex.I)) • ∮ z in C(0, r), (1 / (z - 0) ^ (n + 1)) • genFun y z := by
    rw [h, smul_smul]
    have : (n.factorial : ℂ) / (2 * π * Complex.I) * (2 * π * Complex.I / n.factorial) = 1 := by
      field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rw [this, one_smul]
  rw [h2, norm_smul]
  have hn : ‖((n.factorial : ℂ) / (2 * π * Complex.I))‖ = (n.factorial : ℝ) / (2 * π) := by
    simp [abs_of_pos Real.pi_pos]
  rw [hn]
  gcongr
  unfold circleIntegral
  refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
  have : ∀ θ : ℝ, ‖deriv (circleMap 0 r) θ • (1 / (circleMap 0 r θ - 0) ^ (n + 1)) •
      genFun y (circleMap 0 r θ)‖ = r⁻¹ ^ n * ‖genFun y (circleMap 0 r θ)‖ := by
    intro θ
    have hn0 : ‖circleMap 0 r θ‖ = r := by simp [abs_of_pos hr]
    rw [deriv_circleMap]
    simp only [norm_smul, norm_mul, norm_div, norm_pow, sub_zero, norm_one, hn0,
      Complex.norm_I, mul_one, one_div, norm_inv]
    have hr0 : r ≠ 0 := hr.ne'
    field_simp
    rw [one_div, inv_pow]
    field_simp
    ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]


lemma norm_genFun_circle (y r θ : ℝ) :
    ‖genFun y (circleMap 0 r θ)‖ =
      Real.exp (r ^ 2 / 2 + y ^ 2 / 4 - (r * Real.cos θ - y / 2) ^ 2) := by
  have hre : (circleMap 0 r θ).re = r * Real.cos θ := by simp [circleMap]
  have him : (circleMap 0 r θ).im = r * Real.sin θ := by simp [circleMap]
  unfold genFun
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, pow_two, Complex.div_ofNat_re, hre, him]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination (r ^ 2 / 2) * this


lemma abs_hermite_le (y : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |Polynomial.aeval y (Polynomial.hermite n)| ≤
      (n.factorial : ℝ) / (2 * π) * ((Real.sqrt n)⁻¹ ^ n *
        (Real.exp ((n : ℝ) / 2 + y ^ 2 / 4) * (14 / Real.sqrt (Real.sqrt n)))) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn'
  have hs0 : 0 < Real.sqrt n := by linarith
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
  have h := norm_iteratedDeriv_genFun_le y n hs0
  have hL : ‖iteratedDeriv n (genFun y) 0‖ = |Polynomial.aeval y (Polynomial.hermite n)| := by
    rw [iteratedDeriv_genFun]
    have : Polynomial.aeval ((y : ℂ) - 0) (Polynomial.hermite n) =
        ((Polynomial.aeval y (Polynomial.hermite n) : ℝ) : ℂ) := by
      rw [sub_zero]
      exact (Polynomial.aeval_algebraMap_apply ℂ y (Polynomial.hermite n)).trans (by simp)
    show ‖genFun y 0 * Polynomial.aeval ((y : ℂ) - 0) (Polynomial.hermite n)‖ = _
    rw [this]
    simp [genFun]
  rw [hL] at h
  refine h.trans ?_
  gcongr
  have hI : ∫ θ in (0:ℝ)..(2 * π), ‖genFun y (circleMap 0 (Real.sqrt n) θ)‖ =
      Real.exp ((n : ℝ) / 2 + y ^ 2 / 4) *
        ∫ θ in (0:ℝ)..(2 * π), Real.exp (-(Real.sqrt n * Real.cos θ - y / 2) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [norm_genFun_circle, hsq]
    rw [← Real.exp_add]; congr 1
  rw [hI]
  gcongr
  exact integral_full_exp _ _ hs1


lemma factorial_le_stirling {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le (n - 1))
  simp only [Function.comp, Nat.succ_eq_add_one, Nat.sub_add_cancel hn, zero_add,
    Stirling.stirlingSeq_one] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n := by positivity
  unfold Stirling.stirlingSeq at h
  rw [div_le_div_iff₀ hpos (by positivity)] at h
  have h2 : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt n := Real.sqrt_mul (by norm_num) _
  have hs2 : 0 < Real.sqrt 2 := by positivity
  rw [h2] at h
  have : (n.factorial : ℝ) * Real.sqrt 2 ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n * Real.sqrt 2 := by
    nlinarith [h]
  exact le_of_mul_le_mul_right this hs2

lemma factorial_mul_sq_le {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) * ((Real.sqrt n)⁻¹ ^ n * Real.exp ((n : ℝ) / 2)) ^ 2 ≤
      Real.exp 1 * Real.sqrt n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := factorial_le_stirling hn
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have e1 : ((Real.sqrt n)⁻¹ ^ n * Real.exp ((n : ℝ) / 2)) ^ 2 = ((n : ℝ) ^ n)⁻¹ * Real.exp n := by
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, inv_pow, hsq, ← Real.exp_nat_mul]
    congr 2
    · exact inv_pow (n : ℝ) n
    · push_cast; ring
  rw [e1]
  calc (n.factorial : ℝ) * (((n : ℝ) ^ n)⁻¹ * Real.exp n)
      ≤ (Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n) * (((n : ℝ) ^ n)⁻¹ * Real.exp n) := by
        gcongr
    _ = Real.exp 1 * Real.sqrt n := by
        rw [div_pow, Real.exp_one_pow]
        have : (n : ℝ) ^ n ≠ 0 := by positivity
        have : Real.exp n ≠ 0 := by positivity
        field_simp


lemma final_arith {n : ℕ} (hn : 1 ≤ n) :
    (Real.sqrt ((n.factorial : ℝ) * Real.sqrt π))⁻¹ *
      ((n.factorial : ℝ) / (2 * π) * (((Real.sqrt n)⁻¹ ^ n * Real.exp ((n : ℝ) / 2)) *
        (14 / Real.sqrt (Real.sqrt n)))) ≤ 7 * Real.sqrt (Real.exp 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn'
  have hs0 : 0 < Real.sqrt n := by linarith
  have hss : 0 < Real.sqrt (Real.sqrt n) := Real.sqrt_pos.2 hs0
  set A : ℝ := (n.factorial : ℝ) with hA
  have hApos : 0 < A := by rw [hA]; exact_mod_cast n.factorial_pos
  set W : ℝ := (Real.sqrt n)⁻¹ ^ n * Real.exp ((n : ℝ) / 2) with hW
  have hWpos : 0 < W := by positivity
  have hAW := factorial_mul_sq_le hn
  rw [← hA, ← hW] at hAW
  have hpi1 : 1 ≤ π := by linarith [Real.pi_gt_three]
  have hsp : 1 ≤ Real.sqrt π := by simpa using Real.sqrt_le_sqrt hpi1
  have hv : 1 ≤ Real.sqrt (Real.sqrt π) := by simpa using Real.sqrt_le_sqrt hsp
  set v := Real.sqrt (Real.sqrt π) with hvdef
  set u := Real.sqrt A with hudef
  have hu : 0 < u := Real.sqrt_pos.2 hApos
  have hu2 : u ^ 2 = A := Real.sq_sqrt hApos.le
  have hsplit : Real.sqrt (A * Real.sqrt π) = u * v := Real.sqrt_mul hApos.le _
  have huW : u * W ≤ Real.sqrt (Real.exp 1) * Real.sqrt (Real.sqrt n) := by
    rw [← Real.sqrt_mul (Real.exp_pos 1).le]
    have : u * W = Real.sqrt (A * W ^ 2) := by
      rw [Real.sqrt_mul hApos.le, Real.sqrt_sq hWpos.le]
    rw [this]
    exact Real.sqrt_le_sqrt hAW
  rw [hsplit]
  have e1 : (u * v)⁻¹ * (A / (2 * π) * (W * (14 / Real.sqrt (Real.sqrt n)))) =
      (u * W) * (7 / (π * v * Real.sqrt (Real.sqrt n))) := by
    rw [← hu2]; field_simp; norm_num
  rw [e1]
  have hpv : 1 ≤ π * v := by nlinarith
  calc (u * W) * (7 / (π * v * Real.sqrt (Real.sqrt n)))
      ≤ (Real.sqrt (Real.exp 1) * Real.sqrt (Real.sqrt n)) * (7 / (π * v * Real.sqrt (Real.sqrt n))) := by
        gcongr
    _ = 7 * Real.sqrt (Real.exp 1) / (π * v) := by field_simp
    _ ≤ 7 * Real.sqrt (Real.exp 1) := by
        rw [div_le_iff₀ (by positivity)]
        have : 0 ≤ 7 * Real.sqrt (Real.exp 1) := by positivity
        nlinarith

end CramerAux
end CramerAux

/-- Cramér's inequality: the Hermite functions are uniformly bounded,
`sup_{n,x} |h_n(x)| ≤ C` (classically `C = 1.0865 π^{-1/4} < 1`).  Used to embed finite
measures into `B_m` for `m > d`. -/
theorem hermiteFun_uniform_bound : ∃ C : ℝ, ∀ (n : ℕ) (x : ℝ), |hermiteFun n x| ≤ C := by
  refine ⟨1 + 7 * Real.sqrt (Real.exp 1), fun n x => ?_⟩
  have hC : 0 ≤ 7 * Real.sqrt (Real.exp 1) := by positivity
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hsp : 1 ≤ Real.sqrt Real.pi := by simpa using Real.sqrt_le_sqrt hpi1
  have hex : Real.exp (-(x ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : hermitePoly 0 (Real.sqrt 2 * x) = 1 := by
      simp [hermitePoly, Polynomial.hermite_zero]
    have hq : (Real.sqrt (Real.sqrt Real.pi))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      simpa using Real.sqrt_le_sqrt hsp
    unfold hermiteFun
    rw [h0]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
    rw [abs_of_nonneg (by positivity)]
    have := Real.exp_pos (-(x ^ 2 / 2))
    have hq0 : 0 ≤ (Real.sqrt (Real.sqrt Real.pi))⁻¹ := by positivity
    nlinarith
  · have hn1 : 1 ≤ n := hn
    have hb := CramerAux.abs_hermite_le (Real.sqrt 2 * x) hn1
    have hy : (Real.sqrt 2 * x) ^ 2 / 4 = x ^ 2 / 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring
    rw [hy] at hb
    have hfa := CramerAux.final_arith hn1
    have hcpos : 0 ≤ (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹ := by positivity
    have hEx : Real.exp ((n : ℝ) / 2 + x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)) = Real.exp ((n : ℝ) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmain : |hermiteFun n x| ≤ 7 * Real.sqrt (Real.exp 1) := by
      unfold hermiteFun
      rw [abs_mul, abs_mul, abs_of_nonneg hcpos, abs_of_nonneg (Real.exp_pos _).le]
      have e : hermitePoly n (Real.sqrt 2 * x) = Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n) := rfl
      rw [e]
      calc (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹ *
            |Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n)| * Real.exp (-(x ^ 2 / 2))
          ≤ (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹ *
            ((n.factorial : ℝ) / (2 * Real.pi) * ((Real.sqrt n)⁻¹ ^ n *
              (Real.exp ((n : ℝ) / 2 + x ^ 2 / 2) * (14 / Real.sqrt (Real.sqrt n))))) *
              Real.exp (-(x ^ 2 / 2)) := by gcongr
        _ = (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹ *
            ((n.factorial : ℝ) / (2 * Real.pi) * (((Real.sqrt n)⁻¹ ^ n * Real.exp ((n : ℝ) / 2)) *
              (14 / Real.sqrt (Real.sqrt n)))) := by
            rw [← hEx]; ring
        _ ≤ _ := hfa
    linarith

/-- Elementary (non-sharp) bound `|h_n(x)| ≤ √2 (2n+1)^{1/4}`, from
`h² (x) = ∫_{-∞}^x 2 h h' ≤ 2‖h‖₂‖h'‖₂` and `‖h_n'‖₂² ≤ ∫(h_n'² + x² h_n²) = 2n+1`.  It gives the
embedding of finite measures into `B_m` for `m > 3d/2`, which covers every use in the
supplement (`m = 24d + 240`); the sharp threshold `m > d` needs `hermiteFun_uniform_bound`. -/
theorem hermiteFun_polynomial_bound (n : ℕ) (x : ℝ) :
    |hermiteFun n x| ≤ Real.sqrt 2 * (2 * (n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
  have hn : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hsq := hermiteFun_sq_le n x
  have hB : (Real.sqrt 2 * (2 * (n : ℝ) + 1) ^ ((1 : ℝ) / 4)) ^ 2 = 2 * Real.sqrt (2 * (n : ℝ) + 1) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul hn.le,
      Real.sqrt_eq_rpow]
    norm_num
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [hB, sq]
  exact hsq

theorem derivative_hermiteR_mem_span (n : ℕ) :
    Polynomial.derivative (hermiteR n) ∈ Submodule.span ℝ (Set.range hermiteR) := by
  cases n with
  | zero => simp [hermiteR]
  | succ m =>
    have : Polynomial.derivative (hermiteR (m + 1)) = ((m : ℝ) + 1) • hermiteR m := by
      rw [derivative_hermiteR_succ, Polynomial.smul_eq_C_mul]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

theorem X_mul_mem_span (p : Polynomial ℝ) (hp : p ∈ Submodule.span ℝ (Set.range hermiteR)) :
    Polynomial.X * p ∈ Submodule.span ℝ (Set.range hermiteR) := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    have : Polynomial.X * hermiteR n = hermiteR (n + 1) + Polynomial.derivative (hermiteR n) := by
      rw [hermiteR_succ]; ring
    rw [this]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨n + 1, rfl⟩) (derivative_hermiteR_mem_span n)
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha

theorem hermiteR_span : Submodule.span ℝ (Set.range hermiteR) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  have hpow : ∀ k : ℕ, (Polynomial.X : Polynomial ℝ) ^ k ∈ Submodule.span ℝ (Set.range hermiteR) := by
    intro k
    induction k with
    | zero =>
      have : (1 : Polynomial ℝ) = hermiteR 0 := by simp [hermiteR]
      rw [pow_zero, this]; exact Submodule.subset_span (Set.mem_range_self 0)
    | succ k ih => rw [pow_succ']; exact X_mul_mem_span _ ih
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact Submodule.add_mem _ (hp trivial) (hq trivial)
  | monomial k a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul']
    exact Submodule.smul_mem _ _ (hpow k)

/-- Every real polynomial is a finite linear combination of the `He_j`. -/
theorem exists_hermite_expansion (q : Polynomial ℝ) :
    ∃ c : ℕ →₀ ℝ, ∀ y : ℝ, q.eval y = c.sum (fun j a => a * hermitePoly j y) := by
  have hq : q ∈ Submodule.span ℝ (Set.range hermiteR) := by rw [hermiteR_span]; trivial
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hq
  obtain ⟨c, hc⟩ := hq
  refine ⟨c, fun y => ?_⟩
  rw [← hc]
  simp [Finsupp.sum, Polynomial.eval_finsetSum, hermitePoly_eq_eval]

/-- Monomials `x^k` are finite linear combinations of the `He_j(√2 x)`. -/
theorem exists_pow_expansion (k : ℕ) :
    ∃ c : ℕ →₀ ℝ, ∀ x : ℝ, x ^ k = c.sum (fun j a => a * hermitePoly j (Real.sqrt 2 * x)) := by
  obtain ⟨c, hc⟩ := exists_hermite_expansion
    ((Polynomial.X ^ k).comp (Polynomial.C (Real.sqrt 2)⁻¹ * Polynomial.X))
  refine ⟨c, fun x => ?_⟩
  have := hc (Real.sqrt 2 * x)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  simpa [hs] using this

theorem hermite_gauss_polyfun (n : ℕ) :
    MemLp (fun x : ℝ => hermitePoly n (Real.sqrt 2 * x) * gauss x) 2 (volume : Measure ℝ) := by
  have h := memLp_hermiteFun n
  have hc : hermiteConst n ≠ 0 := by
    unfold hermiteConst
    have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    positivity
  have := h.const_mul (hermiteConst n)⁻¹
  convert this using 1
  funext x
  simp only [hermiteFun_eq]
  field_simp

/-- Completeness in `L²(ℝ)`: an `L²` function orthogonal to every `h_n` vanishes a.e.
(route: `f e^{-x²/2}` is then orthogonal to all monomials, hence has vanishing Fourier
transform, hence vanishes by Fourier inversion against Gaussian mollifiers). -/
theorem hermiteFun_complete (f : ℝ → ℝ) (hf : MemLp f 2 (volume : Measure ℝ))
    (horth : ∀ n, ∫ x, f x * hermiteFun n x = 0) : f =ᵐ[volume] 0 := by
  have h1 : ∀ n, ∫ x, f x * (hermitePoly n (Real.sqrt 2 * x) * gauss x) = 0 := by
    intro n
    have hc : hermiteConst n ≠ 0 := by
      unfold hermiteConst
      have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      positivity
    have := horth n
    have e : (fun x => f x * hermiteFun n x) =
        fun x => hermiteConst n * (f x * (hermitePoly n (Real.sqrt 2 * x) * gauss x)) := by
      funext x; rw [hermiteFun_eq]; ring
    rw [e, integral_const_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hc
  have h2 : ∀ k : ℕ, ∫ x, f x * x ^ k * gauss x = 0 := by
    intro k
    obtain ⟨c, hc⟩ := exists_pow_expansion k
    have e : (fun x => f x * x ^ k * gauss x) = fun x =>
        ∑ j ∈ c.support, c j * (f x * (hermitePoly j (Real.sqrt 2 * x) * gauss x)) := by
      funext x
      rw [hc x, Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, integral_finsetSum]
    · simp [integral_const_mul, h1]
    · intro j _
      exact (hf.integrable_mul (hermite_gauss_polyfun j)).const_mul _
  apply ae_eq_zero_of_gaussian_moments_eq_zero f hf
  intro k ξ
  have e : (fun x : ℝ => f x * (inner ℝ x ξ) ^ k * Real.exp (-(‖x‖ ^ 2 / 2))) =
      fun x => ξ ^ k * (f x * x ^ k * gauss x) := by
    funext x
    simp [gauss, mul_pow, mul_left_comm, mul_assoc]
  rw [e, integral_const_mul, h2, mul_zero]

/-- The `L²` elements `hermiteLp n` are orthonormal. -/
theorem hermiteLp_eq (n : ℕ) : hermiteLp n = (memLp_hermiteFun n).toLp (hermiteFun n) := by
  simp [hermiteLp, memLp_hermiteFun n]

theorem inner_hermiteLp (n m : ℕ) :
    inner ℝ (hermiteLp n) (hermiteLp m) = ∫ x, hermiteFun n x * hermiteFun m x := by
  rw [hermiteLp_eq, hermiteLp_eq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_hermiteFun n).coeFn_toLp, (memLp_hermiteFun m).coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem hermiteLp_orthonormal : Orthonormal ℝ hermiteLp := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_hermiteLp, hermiteFun_orthonormal]

/-- The span of the `hermiteLp n` is dense in `L²(ℝ)`. -/
theorem hermiteLp_dense :
    ⊤ ≤ (Submodule.span ℝ (Set.range hermiteLp)).topologicalClosure := by
  have : (Submodule.span ℝ (Set.range hermiteLp)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro g hg
    rw [Submodule.mem_orthogonal] at hg
    have horth : ∀ n, ∫ x, g x * hermiteFun n x = 0 := by
      intro n
      have h := hg (hermiteLp n) (Submodule.subset_span ⟨n, rfl⟩)
      rw [hermiteLp_eq, MeasureTheory.L2.inner_def] at h
      rw [← h]
      refine integral_congr_ae ?_
      filter_upwards [(memLp_hermiteFun n).coeFn_toLp] with x h1
      rw [h1]
      simp [mul_comm]
    have := hermiteFun_complete g (Lp.memLp g) horth
    exact (Lp.eq_zero_iff_ae_eq_zero).mpr this
  rw [this]

/-- The Hermite functions form a Hilbert basis of `L²(ℝ)` (`HilbertBasis.mk
hermiteLp_orthonormal hermiteLp_dense`; the construction is left to the proof workers since
both inputs are sorried). -/
theorem exists_hermiteHilbertBasis :
    ∃ b : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume : Measure ℝ)), ∀ n, b n = hermiteLp n :=
  ⟨HilbertBasis.mk hermiteLp_orthonormal hermiteLp_dense, fun n => by simp⟩

end OneDim

/-! ### Counting helpers -/

theorem exists_monotone_equiv_nat {ι : Type*} [Countable ι] [Infinite ι] (φ : ι → ℕ)
    (hfin : ∀ k, {i | φ i ≤ k}.Finite) : ∃ e : ℕ ≃ ι, Monotone (fun j => φ (e j)) := by
  classical
  obtain ⟨c, hc⟩ := Countable.exists_injective_nat ι
  let T : ℕ → ℕ := fun k => (hfin k).toFinset.sup c
  let B : ℕ → ℕ := fun k => ∑ k' ∈ Finset.range k, (T k' + 1)
  let key : ι → ℕ := fun i => B (φ i) + c i
  have hB : Monotone B := by
    intro a b hab
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)
  have hcT : ∀ i, c i ≤ T (φ i) := by
    intro i
    exact Finset.le_sup (f := c) (by simp)
  have hkey_lt : ∀ i j, φ i < φ j → key i < key j := by
    intro i j h
    have h1 : B (φ i + 1) ≤ B (φ j) := hB h
    have h2 : B (φ i + 1) = B (φ i) + (T (φ i) + 1) := by
      simp [B, Finset.sum_range_succ]
    have := hcT i
    simp only [key]
    omega
  have hkey_inj : Function.Injective key := by
    intro i j h
    rcases lt_trichotomy (φ i) (φ j) with h1 | h1 | h1
    · exact absurd h (hkey_lt i j h1).ne
    · apply hc
      simp only [key, h1] at h
      omega
    · exact absurd h (hkey_lt j i h1).ne'
  let s : Set ℕ := Set.range key
  have : Infinite s := (Set.infinite_range_of_injective hkey_inj).to_subtype
  let eqv : ι ≃ s := Equiv.ofInjective key hkey_inj
  let e : ℕ ≃ ι := (Nat.Subtype.orderIsoOfNat s).toEquiv.trans eqv.symm
  refine ⟨e, ?_⟩
  intro j j' hjj'
  by_contra hlt
  rw [not_le] at hlt
  have h1 := hkey_lt _ _ hlt
  have hk : ∀ j, key (e j) = (Nat.Subtype.orderIsoOfNat s j : ℕ) := by
    intro j
    have : eqv (e j) = Nat.Subtype.orderIsoOfNat s j := by
      simp [e]
    have h := congrArg Subtype.val this
    rw [show eqv (e j) = ⟨key (e j), _⟩ from Equiv.ofInjective_apply (f := key) (hf := hkey_inj) (e j)] at h
    exact h
  rw [hk, hk] at h1
  have := (Nat.Subtype.orderIsoOfNat s).monotone hjj'
  exact absurd h1 (not_lt.mpr this)

theorem multiIndex_sublevel_finite (d k : ℕ) : {α : MultiIndex d | α.degree ≤ k}.Finite := by
  refine (Fintype.piFinset (fun _ : Fin d => Finset.range (k + 1))).finite_toSet.subset ?_
  intro α hα
  have hα' : MultiIndex.degree α ≤ k := hα
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
  intro i
  have : α i ≤ MultiIndex.degree α := by
    unfold MultiIndex.degree
    exact Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega


theorem card_multiIndex_degree (d k : ℕ) :
    Nat.card {α : MultiIndex d // MultiIndex.degree α = k} = (d + k - 1).choose k := by
  have e : {α : MultiIndex d // MultiIndex.degree α = k} ≃ Sym (Fin d) k :=
    (Sym.equivNatSumOfFintype (Fin d) k).symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]


theorem summable_degree_iff {d : ℕ} (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    Summable (fun α : MultiIndex d => g (MultiIndex.degree α)) ↔
      Summable (fun k : ℕ => ((d + k - 1).choose k : ℝ) * g k) := by
  have hf : 0 ≤ (fun α : MultiIndex d => g (MultiIndex.degree α)) := fun α => hg _
  rw [summable_partition hf (s := fun k : ℕ => {α : MultiIndex d | MultiIndex.degree α = k})
    (fun α => ⟨MultiIndex.degree α, rfl, fun j hj => hj.symm⟩)]
  have hfinite : ∀ k, Finite {α : MultiIndex d | MultiIndex.degree α = k} := fun k =>
    ((multiIndex_sublevel_finite d k).subset (fun α hα => le_of_eq hα)).to_subtype
  have hconst : ∀ k, ∑' i : {α : MultiIndex d | MultiIndex.degree α = k}, g (MultiIndex.degree i.1)
      = ((d + k - 1).choose k : ℝ) * g k := by
    intro k
    have : ∀ i : {α : MultiIndex d | MultiIndex.degree α = k}, g (MultiIndex.degree i.1) = g k :=
      fun i => by rw [i.2]
    simp_rw [this]
    rw [tsum_const]
    have := card_multiIndex_degree d k
    simp only [nsmul_eq_mul]
    congr 1
    rw [← this]
    rfl
  constructor
  · rintro ⟨_, h⟩
    simpa only [hconst] using h
  · intro h
    exact ⟨fun k => by have := hfinite k; exact Summable.of_finite, by simpa only [hconst] using h⟩


theorem choose_lower (e k : ℕ) : ((k : ℝ) + 1) ^ e / (e.factorial : ℝ) ≤ ((e + k).choose k : ℝ) := by
  have h := Nat.pow_le_choose (α := ℝ) e (e + k)
  have e1 : e + k + 1 - e = k + 1 := by omega
  rw [e1] at h
  rw [show (e + k).choose k = (e + k).choose e from (Nat.choose_symm_add (a := e) (b := k)).symm]
  simpa using h

theorem choose_upper (e k : ℕ) : ((e + k).choose k : ℝ) ≤ (((e : ℝ) + 1) * ((k : ℝ) + 1)) ^ e := by
  have h := Nat.choose_le_pow_div (α := ℝ) e (e + k)
  rw [show (e + k).choose k = (e + k).choose e from (Nat.choose_symm_add (a := e) (b := k)).symm]
  refine h.trans ?_
  have hf : (1 : ℝ) ≤ e.factorial := by exact_mod_cast Nat.factorial_pos e
  have h1 : (((e + k : ℕ) : ℝ)) ≤ ((e : ℝ) + 1) * ((k : ℝ) + 1) := by
    push_cast
    nlinarith [(Nat.cast_nonneg e : (0:ℝ) ≤ e), (Nat.cast_nonneg k : (0:ℝ) ≤ k), mul_nonneg (Nat.cast_nonneg e : (0:ℝ) ≤ e) (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  calc ((e + k : ℕ) : ℝ) ^ e / e.factorial ≤ ((e + k : ℕ) : ℝ) ^ e := div_le_self (by positivity) hf
    _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 e


theorem summable_choose_mul_rpow_iff (e : ℕ) (m : ℝ) :
    Summable (fun k : ℕ => ((e + k).choose k : ℝ) * (2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1) ^ (-m)) ↔
      ((e + 1 : ℕ) : ℝ) < m := by
  have hpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hbase : ∀ k : ℕ, (k : ℝ) + 1 ≤ 2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1 := fun k => by
    push_cast; have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); have := (Nat.cast_nonneg e : (0:ℝ) ≤ e); linarith
  constructor
  · intro hs
    by_contra hm
    rw [not_lt] at hm
    -- lower bound by c / (k+1)
    set K : ℝ := (((e : ℝ) + 2) ^ (e + 1))⁻¹ / (e.factorial : ℝ) with hK
    have hKpos : 0 < K := by positivity
    have hlow : ∀ k : ℕ, K * (1 / ((k : ℝ) + 1)) ≤
        ((e + k).choose k : ℝ) * (2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1) ^ (-m) := by
      intro k
      have hx : (1 : ℝ) ≤ 2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1 := by
        have := hbase k; have := hpos k; linarith
      have h1 : (2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1) ^ (-((e + 1 : ℕ) : ℝ)) ≤
          (2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1) ^ (-m) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      have hle : 2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1 ≤ ((e : ℝ) + 2) * ((k : ℝ) + 1) := by
        push_cast
        have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); have := (Nat.cast_nonneg e : (0:ℝ) ≤ e)
        nlinarith [mul_nonneg (Nat.cast_nonneg e : (0:ℝ) ≤ e) (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have h2 : (((e : ℝ) + 2) * ((k : ℝ) + 1)) ^ (-((e + 1 : ℕ) : ℝ)) ≤
          (2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1) ^ (-((e + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by have := hpos k; have := (Nat.cast_nonneg e : (0:ℝ) ≤ e); positivity) hle
          (by have := Nat.cast_nonneg (α := ℝ) (e + 1); linarith)
      have h3 : (((e : ℝ) + 2) * ((k : ℝ) + 1)) ^ (-((e + 1 : ℕ) : ℝ)) =
          (((e : ℝ) + 2) ^ (e + 1))⁻¹ * (((k : ℝ) + 1) ^ (e + 1))⁻¹ := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast, mul_pow, mul_inv]
      have h4 := choose_lower e k
      have h5 : K * (1 / ((k : ℝ) + 1)) = ((k : ℝ) + 1) ^ e / (e.factorial : ℝ) *
          ((((e : ℝ) + 2) ^ (e + 1))⁻¹ * (((k : ℝ) + 1) ^ (e + 1))⁻¹) := by
        rw [hK]; have := hpos k; field_simp; ring
      rw [h5]
      calc _ ≤ ((e + k).choose k : ℝ) * (((e : ℝ) + 2) * ((k : ℝ) + 1)) ^ (-((e + 1 : ℕ) : ℝ)) := by
            rw [h3]
            refine mul_le_mul_of_nonneg_right h4 (by positivity)
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ((h2.trans h1)) (by positivity)
    have hs2 : Summable (fun k : ℕ => K * (1 / ((k : ℝ) + 1))) :=
      Summable.of_nonneg_of_le (fun k => by have := hpos k; positivity) hlow hs
    have hs3 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
      have := hs2.mul_left K⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hKpos.ne'] using this
    have hs4 : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
      rw [← summable_nat_add_iff 1]
      simpa using hs3
    exact Real.not_summable_one_div_natCast hs4
  · intro hm
    have hmm : (e : ℝ) + 1 < m := by simpa using hm
    have hup : ∀ k : ℕ, ((e + k).choose k : ℝ) * (2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1) ^ (-m) ≤
        ((e : ℝ) + 1) ^ e * (((k : ℝ) + 1) ^ ((e : ℝ) - m)) := by
      intro k
      have h1 : (2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1) ^ (-m) ≤ ((k : ℝ) + 1) ^ (-m) :=
        Real.rpow_le_rpow_of_nonpos (hpos k) (hbase k) (by linarith)
      have h2 := choose_upper e k
      have h3 : ((k : ℝ) + 1) ^ ((e : ℝ) - m) = ((k : ℝ) + 1) ^ e * ((k : ℝ) + 1) ^ (-m) := by
        rw [sub_eq_add_neg, Real.rpow_add (hpos k), Real.rpow_natCast]
      rw [h3]
      calc _ ≤ (((e : ℝ) + 1) * ((k : ℝ) + 1)) ^ e * ((k : ℝ) + 1) ^ (-m) :=
            mul_le_mul h2 h1 (Real.rpow_nonneg (by have := hbase k; have := hpos k; linarith) _)
              (by positivity)
        _ = _ := by rw [mul_pow]; ring
    have hsum : Summable (fun k : ℕ => ((e : ℝ) + 1) ^ e * (((k : ℝ) + 1) ^ ((e : ℝ) - m))) := by
      refine Summable.mul_left _ ?_
      have h := Real.summable_nat_rpow.mpr (show (e : ℝ) - m < -1 by linarith)
      rw [← summable_nat_add_iff 1] at h
      simpa using h
    exact Summable.of_nonneg_of_le (fun k => by
      have := hbase k; have := hpos k
      positivity) hup hsum



/-! ### Facts about the `d`-dimensional Hermite functions (work package SFOUND-01) -/

section MultiDim

variable {d : ℕ}

theorem integral_prod_euc {d : ℕ} (g : Fin d → ℝ → ℝ) :
    ∫ x : Euc d, ∏ i, g i (x i) = ∏ i, ∫ t, g i t := by
  have h := (PiLp.volume_preserving_ofLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
    (fun y : Fin d → ℝ => ∏ i, g i (y i))
  rw [← integral_fintype_prod_volume_eq_prod]
  exact h

theorem integrable_prod_euc {d : ℕ} (g : Fin d → ℝ → ℝ) (hg : ∀ i, Integrable (g i)) :
    Integrable (fun x : Euc d => ∏ i, g i (x i)) := by
  have h := (PiLp.volume_preserving_ofLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
    (g := fun y : Fin d → ℝ => ∏ i, g i (y i))
  exact h.mpr (Integrable.fintype_prod hg)

/-- `λ_α ≥ d + 1 ≥ 1`. -/
theorem oscEigenvalue_pos (α : MultiIndex d) : 0 < oscEigenvalue d α := by
  unfold oscEigenvalue
  have : (0 : ℝ) ≤ (α.degree : ℝ) := Nat.cast_nonneg _
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  linarith

theorem one_le_oscEigenvalue (α : MultiIndex d) : 1 ≤ oscEigenvalue d α := by
  unfold oscEigenvalue
  have : (0 : ℝ) ≤ (α.degree : ℝ) := Nat.cast_nonneg _
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  linarith

/-- `h_α` is smooth on `ℝ^d`. -/
theorem contDiff_hermiteFunD (α : MultiIndex d) : ContDiff ℝ ∞ (hermiteFunD α) := by
  unfold hermiteFunD
  refine contDiff_prod fun i _ => ?_
  exact (contDiff_hermiteFun (α i)).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

theorem iteratedFDeriv_two_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ)
    (hF : ContDiff ℝ 2 F) (x v : E) :
    iteratedFDeriv ℝ 2 F x ![v, v] = iteratedDeriv 2 (fun t : ℝ => F (x + t • v)) 0 := by
  let g : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hFa : ContDiff ℝ 2 (fun y => F (x + y)) := hF.comp (contDiff_const.add contDiff_id)
  have h := g.iteratedFDeriv_comp_right (f := fun y => F (x + y)) hFa 0 (i := 2) le_rfl
  have e : (fun t : ℝ => F (x + t • v)) = (fun y => F (x + y)) ∘ g := by
    funext t; simp [g]
  rw [e, iteratedDeriv_eq_iteratedFDeriv, h, iteratedFDeriv_comp_add_left]
  simp [g]
  congr 1
  funext i; fin_cases i <;> simp

theorem laplacian_prod_euc {d : ℕ} (g : Fin d → ℝ → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i)) (x : Euc d) :
    Laplacian.laplacian (fun y : Euc d => ∏ i, g i (y i)) x =
      ∑ i, (∏ j ∈ Finset.univ.erase i, g j (x j)) * iteratedDeriv 2 (g i) (x i) := by
  have hg2 : ∀ i, ContDiff ℝ 2 (g i) := fun i => (hg i).of_le (by simp)
  have hF : ContDiff ℝ 2 (fun y : Euc d => ∏ i, g i (y i)) := by
    refine contDiff_prod fun i _ => ?_
    exact (hg2 i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [EuclideanSpace.basisFun_apply]
  rw [iteratedFDeriv_two_diag _ hF]
  have e : (fun t : ℝ => ∏ j, g j ((x + t • EuclideanSpace.single i (1:ℝ)) j)) =
      fun t => (∏ j ∈ Finset.univ.erase i, g j (x j)) * g i (x i + t) := by
    funext t
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun j hj => ?_
      simp [Finset.ne_of_mem_erase hj]
    · simp
  rw [e]
  have := iteratedDeriv_const_mul (n := 2) (x := 0) (f := fun t => g i (x i + t))
    (∏ j ∈ Finset.univ.erase i, g j (x j)) (hg2 i |>.comp (contDiff_const.add contDiff_id)).contDiffAt
  rw [this, iteratedDeriv_comp_const_add]
  simp

/-- `𝓗 h_α = λ_α h_α` (source lines 289, 356), with `𝓗 = 1 - Δ + |x|²`. -/
theorem oscillatorOp_hermiteFunD (α : MultiIndex d) (x : Euc d) :
    oscillatorOp (hermiteFunD α) x = oscEigenvalue d α * hermiteFunD α x := by
  have hlap := laplacian_prod_euc (fun i => hermiteFun (α i))
    (fun i => contDiff_hermiteFun (α i)) x
  have hode : ∀ i, iteratedDeriv 2 (hermiteFun (α i)) (x i) =
      (x i ^ 2 - (2 * (α i : ℝ) + 1)) * hermiteFun (α i) (x i) := by
    intro i
    have := hermiteFun_ode (α i) (x i)
    linarith
  have hsplit : ∀ i, (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) *
      iteratedDeriv 2 (hermiteFun (α i)) (x i) =
      (x i ^ 2 - (2 * (α i : ℝ) + 1)) * hermiteFunD α x := by
    intro i
    rw [hode i, hermiteFunD, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    ring
  have hF : (Laplacian.laplacian (hermiteFunD α)) x =
      (∑ i, (x i ^ 2 - (2 * (α i : ℝ) + 1))) * hermiteFunD α x := by
    show Laplacian.laplacian (fun y : Euc d => ∏ i, hermiteFun (α i) (y i)) x = _
    rw [hlap, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hsplit i
  unfold oscillatorOp oscEigenvalue
  rw [hF, EuclideanSpace.real_norm_sq_eq]
  have h1 : ∑ i, (x i ^ 2 - (2 * (α i : ℝ) + 1)) =
      ∑ i, x i ^ 2 - (2 * (α.degree : ℝ) + d) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [MultiIndex.degree]
  rw [h1]
  ring

theorem integrable_hermiteFunD (α : MultiIndex d) :
    Integrable (hermiteFunD α) (volume : Measure (Euc d)) :=
  integrable_prod_euc (fun i => hermiteFun (α i)) fun i => integrable_hermiteFun (α i)

theorem integrable_hermiteFunD_mul (α β : MultiIndex d) :
    Integrable (fun x => hermiteFunD α x * hermiteFunD β x) (volume : Measure (Euc d)) := by
  have := integrable_prod_euc (d := d) (fun i t => hermiteFun (α i) t * hermiteFun (β i) t)
    fun i => integrable_hermiteFun_mul (α i) (β i)
  simpa [hermiteFunD, Finset.prod_mul_distrib] using this

theorem memLp_hermiteFunD (α : MultiIndex d) :
    MemLp (hermiteFunD α) 2 (volume : Measure (Euc d)) := by
  rw [memLp_two_iff_integrable_sq (contDiff_hermiteFunD α).continuous.aestronglyMeasurable]
  simpa [sq] using integrable_hermiteFunD_mul α α

/-- Orthonormality `∫ h_α h_β dx = δ_{αβ}` on `ℝ^d`. -/
theorem hermiteFunD_orthonormal (α β : MultiIndex d) :
    ∫ x, hermiteFunD α x * hermiteFunD β x = if α = β then 1 else 0 := by
  have e : (fun x : Euc d => hermiteFunD α x * hermiteFunD β x) =
      fun x => ∏ i, (fun i t => hermiteFun (α i) t * hermiteFun (β i) t) i (x i) := by
    funext x; simp [hermiteFunD, Finset.prod_mul_distrib]
  rw [e, integral_prod_euc (d := d) (fun i t => hermiteFun (α i) t * hermiteFun (β i) t)]
  simp_rw [hermiteFun_orthonormal]
  rw [Finset.prod_boole]
  simp [funext_iff]

/-- Uniform bound `sup_{α,x} |h_α(x)| ≤ C^d` (from `hermiteFun_uniform_bound`). -/
theorem hermiteFunD_uniform_bound : ∃ C : ℝ, ∀ (α : MultiIndex d) (x : Euc d), |hermiteFunD α x| ≤ C := by
  obtain ⟨C, hC⟩ := hermiteFun_uniform_bound
  refine ⟨(max C 1) ^ d, fun α x => ?_⟩
  unfold hermiteFunD
  rw [Finset.abs_prod]
  calc ∏ i, |hermiteFun (α i) (x i)| ≤ ∏ _i : Fin d, max C 1 :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => (hC _ _).trans (le_max_left _ _)
    _ = (max C 1) ^ d := by simp

theorem gaussD_eq (x : Euc d) : Real.exp (-(‖x‖ ^ 2 / 2)) = ∏ i, gauss (x i) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold gauss
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib, Finset.sum_div]

theorem hermiteConstD_ne (β : MultiIndex d) : ∏ i, hermiteConst (β i) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  unfold hermiteConst
  have : (0 : ℝ) < (β i).factorial := by exact_mod_cast Nat.factorial_pos _
  positivity

theorem hermiteFunD_eq (β : MultiIndex d) (x : Euc d) :
    hermiteFunD β x = (∏ i, hermiteConst (β i)) *
      ∏ i, (hermitePoly (β i) (Real.sqrt 2 * x i) * gauss (x i)) := by
  simp only [hermiteFunD, hermiteFun_eq, Finset.prod_mul_distrib]
  ring

theorem memLp_polyGaussD (β : MultiIndex d) :
    MemLp (fun x : Euc d => ∏ i, (hermitePoly (β i) (Real.sqrt 2 * x i) * gauss (x i))) 2
      (volume : Measure (Euc d)) := by
  have := (memLp_hermiteFunD β).const_mul (∏ i, hermiteConst (β i))⁻¹
  convert this using 1
  funext x
  rw [hermiteFunD_eq]
  have := hermiteConstD_ne β
  field_simp

/-- Completeness in `L²(ℝ^d)`. -/
theorem hermiteFunD_complete (f : Euc d → ℝ) (hf : MemLp f 2 (volume : Measure (Euc d)))
    (horth : ∀ α, ∫ x, f x * hermiteFunD α x = 0) : f =ᵐ[volume] 0 := by
  have h1 : ∀ β : MultiIndex d, ∫ x, f x *
      ∏ i, (hermitePoly (β i) (Real.sqrt 2 * x i) * gauss (x i)) = 0 := by
    intro β
    have := horth β
    have e : (fun x => f x * hermiteFunD β x) = fun x => (∏ i, hermiteConst (β i)) *
        (f x * ∏ i, (hermitePoly (β i) (Real.sqrt 2 * x i) * gauss (x i))) := by
      funext x; rw [hermiteFunD_eq]; ring
    rw [e, integral_const_mul] at this
    exact (mul_eq_zero.mp this).resolve_left (hermiteConstD_ne β)
  have h2 : ∀ α : MultiIndex d,
      Integrable (fun x : Euc d => f x * (∏ i, (x i) ^ (α i)) * Real.exp (-(‖x‖ ^ 2 / 2))) ∧
      ∫ x, f x * (∏ i, (x i) ^ (α i)) * Real.exp (-(‖x‖ ^ 2 / 2)) = 0 := by
    intro α
    choose c hc using fun i => exists_pow_expansion (α i)
    have e : (fun x : Euc d => f x * (∏ i, (x i) ^ (α i)) * Real.exp (-(‖x‖ ^ 2 / 2))) =
        fun x => ∑ β ∈ Fintype.piFinset (fun i => (c i).support),
          (∏ i, c i (β i)) * (f x *
            ∏ i, (hermitePoly (β i) (Real.sqrt 2 * x i) * gauss (x i))) := by
      funext x
      have : ∏ i, (x i) ^ (α i) = ∑ β ∈ Fintype.piFinset (fun i => (c i).support),
          ∏ i, (c i (β i) * hermitePoly (β i) (Real.sqrt 2 * x i)) := by
        rw [← Finset.prod_univ_sum (fun i => (c i).support)
          (fun i j => c i j * hermitePoly j (Real.sqrt 2 * x i))]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hc i (x i), Finsupp.sum]
      rw [gaussD_eq, this, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      ring
    have hint : ∀ β : MultiIndex d, Integrable (fun x : Euc d => (∏ i, c i (β i)) * (f x *
            ∏ i, (hermitePoly (β i) (Real.sqrt 2 * x i) * gauss (x i)))) :=
      fun β => (hf.integrable_mul (memLp_polyGaussD β)).const_mul _
    rw [e]
    refine ⟨integrable_finsetSum _ fun β _ => hint β, ?_⟩
    rw [integral_finsetSum _ fun β _ => hint β]
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [integral_const_mul, h1, mul_zero]
  apply ae_eq_zero_of_gaussian_moments_eq_zero f hf
  intro k ξ
  have e : (fun x : Euc d => f x * (inner ℝ x ξ) ^ k * Real.exp (-(‖x‖ ^ 2 / 2))) =
      fun x => ∑ α ∈ Finset.piAntidiag Finset.univ k,
        ((Nat.multinomial Finset.univ α : ℕ) * ∏ i, (ξ i) ^ (α i) : ℝ) *
          (f x * (∏ i, (x i) ^ (α i)) * Real.exp (-(‖x‖ ^ 2 / 2))) := by
    funext x
    have hin : inner ℝ x ξ = ∑ i, x i * ξ i := by
      simp [PiLp.inner_apply, mul_comm]
    rw [hin, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [mul_pow, Finset.prod_mul_distrib]
    ring
  rw [e, integral_finsetSum _ fun α _ => (h2 α).1.const_mul _]
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [integral_const_mul, (h2 α).2, mul_zero]

theorem hermiteLpD_eq (α : MultiIndex d) :
    hermiteLpD α = (memLp_hermiteFunD α).toLp (hermiteFunD α) := by
  simp [hermiteLpD, memLp_hermiteFunD α]

theorem inner_hermiteLpD (α β : MultiIndex d) :
    inner ℝ (hermiteLpD α) (hermiteLpD β) = ∫ x, hermiteFunD α x * hermiteFunD β x := by
  rw [hermiteLpD_eq, hermiteLpD_eq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_hermiteFunD α).coeFn_toLp, (memLp_hermiteFunD β).coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem hermiteLpD_orthonormal : Orthonormal ℝ (hermiteLpD (d := d)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_hermiteLpD, hermiteFunD_orthonormal]

theorem hermiteLpD_dense :
    ⊤ ≤ (Submodule.span ℝ (Set.range (hermiteLpD (d := d)))).topologicalClosure := by
  have : (Submodule.span ℝ (Set.range (hermiteLpD (d := d)))).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro g hg
    rw [Submodule.mem_orthogonal] at hg
    have horth : ∀ α, ∫ x, g x * hermiteFunD α x = 0 := by
      intro α
      have h := hg (hermiteLpD α) (Submodule.subset_span ⟨α, rfl⟩)
      rw [hermiteLpD_eq, MeasureTheory.L2.inner_def] at h
      rw [← h]
      refine integral_congr_ae ?_
      filter_upwards [(memLp_hermiteFunD α).coeFn_toLp] with x h1
      rw [h1]
      simp [mul_comm]
    have := hermiteFunD_complete g (Lp.memLp g) horth
    exact (Lp.eq_zero_iff_ae_eq_zero).mpr this
  rw [this]

/-- The `h_α` form a Hilbert basis of `L²(ℝ^d)` indexed by multi-indices. -/
theorem exists_hermiteHilbertBasisD :
    ∃ b : HilbertBasis (MultiIndex d) ℝ (Lp ℝ 2 (volume : Measure (Euc d))),
      ∀ α, b α = hermiteLpD α :=
  ⟨HilbertBasis.mk hermiteLpD_orthonormal hermiteLpD_dense, fun α => by simp⟩

/-- The eigenvalue sums `∑_α λ_α^{-m}` converge exactly when `m > d` (there are
`C(k+d-1, d-1) ≍ k^{d-1}` multi-indices of degree `k`).  This is the threshold for embedding
finite measures into `B_m`. -/
theorem summable_oscEigenvalue_rpow_iff (hd : 1 ≤ d) (m : ℝ) :
    (Summable fun α : MultiIndex d => oscEigenvalue d α ^ (-m)) ↔ (d : ℝ) < m := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have h := summable_degree_iff (d := e + 1)
    (fun k : ℕ => (2 * (k : ℝ) + ((e + 1 : ℕ) : ℝ) + 1) ^ (-m))
    (fun k => Real.rpow_nonneg (by positivity) _)
  have h2 := summable_choose_mul_rpow_iff e m
  have e1 : ∀ k : ℕ, e + 1 + k - 1 = e + k := fun k => by omega
  simp only [e1] at h
  exact h.trans h2

/-- The source's enumeration (line 288): the multi-indices can be enumerated by `ℕ` in
nondecreasing eigenvalue order.  No formula of the supplement depends on the choice of such an
enumeration (all sums over `j` are order-independent). -/
theorem exists_monotone_enumeration (hd : 1 ≤ d) :
    ∃ e : ℕ ≃ MultiIndex d, Monotone fun j => oscEigenvalue d (e j) := by
  have : Infinite (MultiIndex d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  obtain ⟨e, he⟩ := exists_monotone_equiv_nat (fun α : MultiIndex d => α.degree)
    (multiIndex_sublevel_finite d)
  refine ⟨e, fun j j' h => ?_⟩
  unfold oscEigenvalue
  have : ((e j).degree : ℝ) ≤ (e j').degree := by exact_mod_cast he h
  linarith

end MultiDim

end HRS.Whole
