import Mathlib

/-!
# HRS foundations I: the torus, configurations, smooth functions, Fourier modes

Source: HRS periodic main paper, Section 2.1 "Conventions, centerings, and the
linear equation" (source lines 416-528) and the introduction (lines 170-200).

This file fixes the Lean representation of the basic objects.  Everything here
is a genuine definition (no `sorry`).  Lemmas that record facts about these
representations are collected at the end and are `sorry`-ed (work package FOUND-01).

## Representation decisions (see `docs/PLAN.md` §(b))

* The torus `𝕋^d = ℝ^d/ℤ^d` is `HRS.Torus d := UnitAddTorus (Fin d)`, i.e.
  `Fin d → UnitAddCircle`; its `volume` is the product Haar measure, which has
  total mass one (the paper's "volume one").
* A configuration `X_N = (x_1,…,x_N)` is `Fin N → Torus d`.
* Smoothness, derivatives and `C_b^k` norms of a function `φ : Torus d → ℝ` are
  defined through its periodic lift `φ ∘ Torus.mk : EuclideanSpace ℝ (Fin d) → ℝ`.
  This makes `ContDiff`/`iteratedFDeriv` from Mathlib available (Mathlib has no
  smooth structure on `UnitAddTorus`).  Derivative norms are multilinear operator
  norms with respect to the Euclidean norm on `ℝ^d`, exactly as in the paper
  ("derivative norms are multilinear operator norms", source line 512).
* Fourier modes `e^{2πi k·x}` are Mathlib's `UnitAddTorus.mFourier k`.  The real
  orthonormal basis `e_k` of `L²_0(𝕋^d)` used by the paper (source lines 8274-8275)
  is `√2 cos(2π k·x)` for `k` in the lexicographically positive half-lattice and
  `√2 sin(2π k·x)` for `k` in the negative half.
* `⟨k⟩ = (1+4π²|k|²)^{1/2}` (source line 8129) is `Lattice.jp`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

/-- The flat torus `𝕋^d = ℝ^d/ℤ^d` of volume one. -/
abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)

/-- Euclidean `ℝ^d`; used for derivatives, lattice norms, and the covering map. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A configuration `X_N = (x_1, …, x_N)` of `N` particles on `𝕋^d`. -/
abbrev Config (d N : ℕ) := Fin N → Torus d

/-- The lattice `ℤ^d` of Fourier frequencies. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- `ℤ^d ∖ {0}`: frequencies of mean-zero objects. -/
abbrev NonzeroLattice (d : ℕ) := {k : Lattice d // k ≠ 0}

/-- The Haar measure on `ℝ/ℤ` has total mass one (Mathlib only records
`IsFiniteMeasure` globally). -/
instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨by simp⟩

example (d : ℕ) : IsProbabilityMeasure (volume : Measure (Torus d)) := inferInstance

namespace Torus

variable {d : ℕ}

/-- The covering map `ℝ^d → 𝕋^d`. -/
def mk (x : Euc d) : Torus d := fun i => ((x i : ℝ) : UnitAddCircle)

/-- The canonical representative in `[0,1)^d` of a point of the torus. -/
def rep (x : Torus d) : Euc d :=
  WithLp.toLp 2 fun i => ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)

/-- The periodic lift `φ ∘ mk : ℝ^d → E` of a function on the torus. -/
def lift {E : Type*} (φ : Torus d → E) : Euc d → E := φ ∘ mk

/-- `C^k` regularity of a function on the torus.  Beware Mathlib's order conventions for
`ContDiff`: `k = ((⊤ : ℕ∞) : WithTop ℕ∞)` (notation `∞` under `open scoped ContDiff`) is `C^∞`,
whereas `k = (⊤ : WithTop ℕ∞)` (notation `ω`) is *real-analytic*.  Use `IsSmooth` for `C^∞`. -/
def IsCk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : WithTop ℕ∞) (φ : Torus d → E) : Prop :=
  ContDiff ℝ k (lift φ)

/-- `C^∞` regularity of a function on the torus through the periodic lift
(`ContDiff ℝ ∞ (lift φ)`, not analyticity). -/
def IsSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : Torus d → E) : Prop :=
  IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) φ

/-- The `C_b^k` norm `∑_{j ≤ k} sup_x ‖D^j φ(x)‖` (source line 510, SUM over orders),
with multilinear operator norms of the Euclidean derivatives. -/
def cbNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (φ : Torus d → E) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (lift φ) x‖

/-- Sup norm `‖φ‖_∞`. -/
def supNorm {E : Type*} [NormedAddCommGroup E] (φ : Torus d → E) : ℝ :=
  ⨆ x : Torus d, ‖φ x‖

/-- Hölder seminorm `[φ]_{C^{0,α}}` with respect to the torus distance. -/
def holderSeminorm (α : ℝ) (φ : Torus d → ℝ) : ℝ :=
  ⨆ p : {p : Torus d × Torus d // p.1 ≠ p.2}, |φ p.1.1 - φ p.1.2| / ‖p.1.1 - p.1.2‖ ^ α

/-- Gradient `∇φ` of a scalar function on the torus, as a vector in `ℝ^d`. -/
def grad (φ : Torus d → ℝ) (x : Torus d) : Euc d := gradient (lift φ) (rep x)

/-- Laplacian `Δφ`. -/
def laplacian (φ : Torus d → ℝ) (x : Torus d) : ℝ :=
  Laplacian.laplacian (lift φ) (rep x)

/-- Divergence `Div v` of a vector field. -/
def div (v : Torus d → Euc d) (x : Torus d) : ℝ :=
  ∑ i, fderiv ℝ (lift v) (rep x) (EuclideanSpace.single i 1) i

/-- Partial derivative `∂_j φ`. -/
def partialDeriv (j : Fin d) (φ : Torus d → ℝ) (x : Torus d) : ℝ :=
  fderiv ℝ (lift φ) (rep x) (EuclideanSpace.single j 1)

/-- Translation of a function on the torus: `(translate a φ) x = φ (x - a)`. -/
def translate (a : Torus d) (φ : Torus d → ℝ) : Torus d → ℝ := fun x => φ (x - a)

/-- Apply a constant real matrix `M` to a vector in `ℝ^d`. -/
def matVec (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) : Euc d := Matrix.toEuclideanLin M v

/-- `Sym M = (M + Mᵀ)/2`. -/
def symPart (M : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := (1/2 : ℝ) • (M + M.transpose)

/-- `Sym M ≤ 0` (negative semidefinite symmetric part). -/
def SymNonpos (M : Matrix (Fin d) (Fin d) ℝ) : Prop := (-(symPart M)).PosSemidef

end Torus

namespace Lattice

variable {d : ℕ}

/-- `k ∈ ℤ^d` as a vector in `ℝ^d`. -/
def toEuc (k : Lattice d) : Euc d := WithLp.toLp 2 fun i => (k i : ℝ)

/-- Euclidean norm `|k|`. -/
def enorm (k : Lattice d) : ℝ := ‖toEuc k‖

/-- `⟨k⟩ = (1 + 4π²|k|²)^{1/2}` (source line 8129). -/
def jp (k : Lattice d) : ℝ := Real.sqrt (1 + 4 * Real.pi ^ 2 * enorm k ^ 2)

/-- The lexicographically positive half of `ℤ^d ∖ {0}`. -/
def IsPosHalf (k : Lattice d) : Prop := 0 < toLex k

/-- `k · x` for `k ∈ ℤ^d`, `x ∈ ℝ^d`. -/
def dot (k : Lattice d) (x : Euc d) : ℝ := ∑ i, (k i : ℝ) * x i

end Lattice

namespace Torus

variable {d : ℕ}

/-- The complex Fourier mode `e_k(x) = e^{2πi k·x}` (Mathlib's `UnitAddTorus.mFourier`). -/
def mode (k : Lattice d) (x : Torus d) : ℂ := UnitAddTorus.mFourier k x

/-- `cos(2π k·x)`. -/
def cosMode (k : Lattice d) (x : Torus d) : ℝ := (mode k x).re

/-- `sin(2π k·x)`. -/
def sinMode (k : Lattice d) (x : Torus d) : ℝ := (mode k x).im

open Classical in
/-- The real orthonormal basis `e_k` of `L²_0(𝕋^d)`, `k ≠ 0` (source lines 8274-8275):
`√2 cos(2π k·x)` on the positive half-lattice and `√2 sin(2π k·x)` on the negative half. -/
def realMode (k : NonzeroLattice d) (x : Torus d) : ℝ :=
  if Lattice.IsPosHalf k.1 then Real.sqrt 2 * cosMode k.1 x else Real.sqrt 2 * sinMode k.1 x

/-- Complex Fourier coefficient `μ̂(k) = ∫ e^{-2πi k·x} dμ(x)` of a finite measure. -/
def measureFourierCoeff (μ : Measure (Torus d)) (k : Lattice d) : ℂ :=
  ∫ x, mode (-k) x ∂μ

/-- Real Fourier coefficient `∫ e_k dμ` of a finite measure against the real basis. -/
def measureRealCoeff (μ : Measure (Torus d)) (k : NonzeroLattice d) : ℝ :=
  ∫ x, realMode k x ∂μ

/-- Complex Fourier coefficient `φ̂(k)` of a function (Mathlib's `mFourierCoeff`). -/
def funFourierCoeff (φ : Torus d → ℂ) (k : Lattice d) : ℂ := UnitAddTorus.mFourierCoeff φ k

/-- Real Fourier coefficient `∫ e_k φ dx` of a real function. -/
def funRealCoeff (φ : Torus d → ℝ) (k : NonzeroLattice d) : ℝ :=
  ∫ x, realMode k x * φ x

/-- Haar mean `∫ φ dx`. -/
def mean (φ : Torus d → ℝ) : ℝ := ∫ x, φ x

end Torus

/-- The empirical measure `μ_N = N⁻¹ ∑_i δ_{x_i}` (source line 192). -/
def empirical {d N : ℕ} (X : Config d N) : Measure (Torus d) :=
  ((N : ℝ≥0∞)⁻¹) • ∑ i : Fin N, Measure.dirac (X i)

/-- Pairing `μ(φ) = ∫ φ dμ`. -/
def pair {d : ℕ} (μ : Measure (Torus d)) (φ : Torus d → ℝ) : ℝ := ∫ x, φ x ∂μ

/-- The collision set `𝔇_N = {X : x_i = x_j for some i ≠ j}` (source line ~10115). -/
def collisionSet (d N : ℕ) : Set (Config d N) := {X | ∃ i j, i ≠ j ∧ X i = X j}

/-- `L²(μ)` inner product `⟨f, g⟩_{L²(μ)} = ∫ f g dμ`. -/
def l2Inner {d : ℕ} (μ : Measure (Torus d)) (f g : Torus d → ℝ) : ℝ := ∫ x, f x * g x ∂μ

/-- Projection modulo constants `P_μ f = f - μ(f)` (source line 936 region). -/
def projMean {d : ℕ} (μ : Measure (Torus d)) (f : Torus d → ℝ) : Torus d → ℝ :=
  fun x => f x - pair μ f

/-- The measure `μ = ρ dx` with density `ρ`. -/
def withDensityReal {d : ℕ} (ρ : Torus d → ℝ) : Measure (Torus d) :=
  volume.withDensity fun x => ENNReal.ofReal (ρ x)

/-- A probability density on the torus: nonnegative, measurable, integral one. -/
structure IsProbDensity {d : ℕ} (ρ : Torus d → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ρ x
  measurable : Measurable ρ
  integral_one : ∫ x, ρ x = 1

/-! ### Basic facts about the representation (work package FOUND-01) -/

namespace Torus

variable {d : ℕ}

/-- `mk` is surjective and `rep` is a right inverse. -/
theorem mk_rep (x : Torus d) : mk (rep x) = x := by
  funext i
  simp [mk, rep, AddCircle.coe_equivIco]

/-- The lift is `ℤ^d`-periodic. -/
theorem lift_periodic {E : Type*} (φ : Torus d → E) (x : Euc d) (k : Lattice d) :
    lift φ (x + Lattice.toEuc k) = lift φ x := by
  unfold lift
  simp only [Function.comp]
  congr 1
  funext i
  simp [mk, Lattice.toEuc]

/-- The modes are continuous (hence bounded, measurable). -/
theorem continuous_mode (k : Lattice d) : Continuous (mode k) := by
  exact (UnitAddTorus.mFourier k).continuous

theorem mode_mk (k : Lattice d) (x : Euc d) :
    mode k (mk x) = Complex.exp (((2 * Real.pi * Lattice.dot k x : ℝ) : ℂ) * Complex.I) := by
  simp only [mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk, mk, fourier_coe_apply,
    Lattice.dot]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, div_one]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- `cos(2πk·x)` is the real part of the complex mode: pointwise formula via the lift. -/
theorem cosMode_mk (k : Lattice d) (x : Euc d) :
    cosMode k (mk x) = Real.cos (2 * Real.pi * Lattice.dot k x) := by
  rw [cosMode, mode_mk, Complex.exp_ofReal_mul_I_re]

theorem sinMode_mk (k : Lattice d) (x : Euc d) :
    sinMode k (mk x) = Real.sin (2 * Real.pi * Lattice.dot k x) := by
  rw [sinMode, mode_mk, Complex.exp_ofReal_mul_I_im]

open scoped ComplexConjugate

theorem mode_add (k l : Lattice d) (x : Torus d) : mode (k + l) x = mode k x * mode l x :=
  UnitAddTorus.mFourier_add

theorem mode_neg (k : Lattice d) (x : Torus d) : mode (-k) x = conj (mode k x) :=
  UnitAddTorus.mFourier_neg

theorem mode_zero (x : Torus d) : mode (0 : Lattice d) x = 1 := by
  simp [mode, UnitAddTorus.mFourier_zero]

theorem volume_eq_pi_haar :
    (volume : Measure (Torus d)) = Measure.pi fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  show Measure.pi (fun _ => (volume : Measure UnitAddCircle)) = _
  congr 1
  funext _
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

theorem integral_mode (a : Lattice d) : ∫ x, mode a x = if a = 0 then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d)) 0 a
  simp only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg, ← UnitAddTorus.mFourier_add] at h
  have h' : (∫ x : Torus d, mode a x ∂(Measure.pi fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle))) = if a = 0 then 1 else 0 := by
    simp only [neg_zero, add_zero, @eq_comm _ (0 : Lattice d) a] at h
    exact h
  rw [volume_eq_pi_haar]
  exact h'

theorem integrable_mode (k : Lattice d) : Integrable (mode k) :=
  (continuous_mode k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_mode_mul (k l : Lattice d) :
    ∫ x, mode k x * mode l x = if k + l = 0 then 1 else 0 := by
  simp_rw [← mode_add]
  exact integral_mode _
theorem integrable_mode_mul (k l : Lattice d) : Integrable (fun x => mode k x * mode l x) :=
  ((continuous_mode k).mul (continuous_mode l)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
theorem isPosHalf_neg (k : Lattice d) (hk : k ≠ 0) :
    Lattice.IsPosHalf (-k) ↔ ¬ Lattice.IsPosHalf k := by
  unfold Lattice.IsPosHalf
  have : toLex (-k) = - toLex k := rfl
  rw [this, neg_pos]
  have h0 : toLex k ≠ 0 := fun h => hk (toLex.injective h)
  constructor
  · exact fun h => not_lt.mpr h.le
  · exact fun h => lt_of_le_of_ne (not_lt.mp h) h0

open Classical in
/-- coefficient of `e_k` in the expansion of `realMode k`. -/
def realCoef (k : Lattice d) : ℂ :=
  if Lattice.IsPosHalf k then ((Real.sqrt 2 / 2 : ℝ) : ℂ)
  else -Complex.I * ((Real.sqrt 2 / 2 : ℝ) : ℂ)

theorem realMode_cplx (k : NonzeroLattice d) (x : Torus d) :
    (realMode k x : ℂ) = realCoef k.1 * mode k.1 x + conj (realCoef k.1) * mode (-k.1) x := by
  rw [mode_neg]
  unfold realMode realCoef
  by_cases h : Lattice.IsPosHalf k.1
  · simp only [h, ite_true, cosMode]
    rw [Complex.ofReal_mul, Complex.re_eq_add_conj]
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  · simp only [h, ite_false, sinMode]
    rw [Complex.ofReal_mul, Complex.im_eq_sub_conj]
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    push_cast
    field_simp
    linear_combination (mode k.1 x - conj (mode k.1 x)) * Complex.I_sq

theorem integral_comb (a b a' b' : ℂ) (k l : Lattice d) :
    ∫ x, (a * mode k x + b * mode (-k) x) * (a' * mode l x + b' * mode (-l) x) =
      a * a' * (if k + l = 0 then 1 else 0) + a * b' * (if k = l then 1 else 0)
        + b * a' * (if k = l then 1 else 0) + b * b' * (if k + l = 0 then 1 else 0) := by
  have e : ∀ x, (a * mode k x + b * mode (-k) x) * (a' * mode l x + b' * mode (-l) x) =
      a * a' * (mode k x * mode l x) + a * b' * (mode k x * mode (-l) x)
        + b * a' * (mode (-k) x * mode l x) + b * b' * (mode (-k) x * mode (-l) x) := by
    intro x; ring
  have hint : ∀ (c : ℂ) (k l : Lattice d), Integrable (fun x => c * (mode k x * mode l x)) :=
    fun c k l => (integrable_mode_mul k l).const_mul c
  simp_rw [e]
  rw [integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_mode_mul, integral_mode_mul,
    integral_mode_mul, integral_mode_mul]
  · have h1 : k + -l = 0 ↔ k = l := add_neg_eq_zero
    have h2 : -k + l = 0 ↔ k = l := by rw [neg_add_eq_zero, eq_comm]
    have h3 : -k + -l = 0 ↔ k + l = 0 := by rw [← neg_add, neg_eq_zero]
    simp only [h1, h2, h3]
  all_goals repeat' (first | exact hint _ _ _ | apply Integrable.add)

theorem realCoef_pos {k : Lattice d} (h : Lattice.IsPosHalf k) :
    realCoef k = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  simp [realCoef, h]

theorem realCoef_neg {k : Lattice d} (h : ¬ Lattice.IsPosHalf k) :
    realCoef k = -Complex.I * ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  simp [realCoef, h]

theorem sqrt2_half_sq : ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul]
  have : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  rw [this]; push_cast; ring

theorem realCoef_mul_conj (k : Lattice d) : realCoef k * conj (realCoef k) = 1 / 2 := by
  by_cases h : Lattice.IsPosHalf k
  · rw [realCoef_pos h, Complex.conj_ofReal, sqrt2_half_sq]
  · rw [realCoef_neg h]
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    have := sqrt2_half_sq
    linear_combination (-(Complex.I * Complex.I)) * this + (-1/2 : ℂ) * Complex.I_sq

theorem realMode_orthonormal_aux (k l : NonzeroLattice d) :
    ∫ x, realMode k x * realMode l x = if k = l then 1 else 0 := by
  have h := integral_comb (realCoef k.1) (conj (realCoef k.1)) (realCoef l.1)
    (conj (realCoef l.1)) k.1 l.1
  have e : ∀ x, ((realMode k x * realMode l x : ℝ) : ℂ) =
      (realCoef k.1 * mode k.1 x + conj (realCoef k.1) * mode (-k.1) x) *
        (realCoef l.1 * mode l.1 x + conj (realCoef l.1) * mode (-l.1) x) := by
    intro x
    push_cast
    rw [realMode_cplx, realMode_cplx]
  apply Complex.ofReal_injective
  have hc : ((if k = l then (1:ℝ) else 0 : ℝ) : ℂ) = if k = l then 1 else 0 := by
    split_ifs <;> simp
  rw [hc, ← integral_complex_ofReal (f := fun x => realMode k x * realMode l x)]
  simp_rw [e]
  rw [h]
  have hcoe : ((k : Lattice d) = l) ↔ k = l := Subtype.coe_inj
  simp only [hcoe]
  by_cases hkl : k = l
  · subst hkl
    have hk2 : ¬ ((k : Lattice d) + k = 0) := by
      intro h0
      apply k.2
      funext i
      have := congrFun h0 i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      simp only [Pi.zero_apply]
      omega
    have := realCoef_mul_conj k.1
    simp only [hk2, ite_false, ite_true, mul_zero, zero_add, add_zero, mul_one]
    linear_combination 2 * this
  · simp only [hkl, ite_false, mul_zero, add_zero]
    by_cases hs : (k : Lattice d) + l = 0
    · have hl : (l : Lattice d) = -k := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hs
      have hneg := isPosHalf_neg k.1 k.2
      simp only [hs, ite_true, mul_one]
      by_cases hp : Lattice.IsPosHalf k.1
      · have hq : ¬ Lattice.IsPosHalf l.1 := by rw [hl]; exact fun h' => (hneg.mp h') hp
        rw [realCoef_pos hp, realCoef_neg hq]
        simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
        ring
      · have hq : Lattice.IsPosHalf l.1 := by rw [hl]; exact hneg.mpr hp
        rw [realCoef_neg hp, realCoef_pos hq]
        simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
        ring
    · simp [hs]

/-- The real modes `e_k`, `k ≠ 0`, are orthonormal in `L²(dx)`. -/
theorem realMode_orthonormal (k l : NonzeroLattice d) :
    ∫ x, realMode k x * realMode l x = if k = l then 1 else 0 := by
  exact realMode_orthonormal_aux k l

/-- The real modes have Haar mean zero. -/
theorem integral_realMode (k : NonzeroLattice d) : ∫ x, realMode k x = 0 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal (f := fun x => realMode k x)]
  simp_rw [realMode_cplx]
  rw [integral_add, integral_const_mul, integral_const_mul, integral_mode, integral_mode]
  · have h1 : k.1 ≠ 0 := k.2
    have h2 : -k.1 ≠ 0 := neg_ne_zero.mpr k.2
    simp [h1, h2]
  · exact (integrable_mode _).const_mul _
  · exact (integrable_mode _).const_mul _

/-- cosine coefficient `∫ cos(2πk·x) φ(x) dx`. -/
def cosCoeff (φ : Torus d → ℝ) (k : Lattice d) : ℝ := ∫ x, cosMode k x * φ x

/-- sine coefficient `∫ sin(2πk·x) φ(x) dx`. -/
def sinCoeff (φ : Torus d → ℝ) (k : Lattice d) : ℝ := ∫ x, sinMode k x * φ x

theorem continuous_cosMode (k : Lattice d) : Continuous (cosMode k) :=
  Complex.continuous_re.comp (continuous_mode k)

theorem continuous_sinMode (k : Lattice d) : Continuous (sinMode k) :=
  Complex.continuous_im.comp (continuous_mode k)

theorem norm_mode (k : Lattice d) (x : Torus d) : ‖mode k x‖ = 1 := by
  rw [← mk_rep x, mode_mk, Complex.norm_exp_ofReal_mul_I]

theorem norm_cosMode_le (k : Lattice d) (x : Torus d) : ‖cosMode k x‖ ≤ 1 := by
  rw [← norm_mode k x, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem norm_sinMode_le (k : Lattice d) (x : Torus d) : ‖sinMode k x‖ ≤ 1 := by
  rw [← norm_mode k x, Real.norm_eq_abs]
  exact Complex.abs_im_le_norm _

theorem integrable_cosMode_mul (k : Lattice d) {φ : Torus d → ℝ} (hφ : Integrable φ) :
    Integrable (fun x => cosMode k x * φ x) :=
  hφ.bdd_mul (continuous_cosMode k).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_cosMode_le k))

theorem integrable_sinMode_mul (k : Lattice d) {φ : Torus d → ℝ} (hφ : Integrable φ) :
    Integrable (fun x => sinMode k x * φ x) :=
  hφ.bdd_mul (continuous_sinMode k).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_sinMode_le k))

theorem cosMode_neg (k : Lattice d) (x : Torus d) : cosMode (-k) x = cosMode k x := by
  simp [cosMode, mode_neg]

theorem sinMode_neg (k : Lattice d) (x : Torus d) : sinMode (-k) x = - sinMode k x := by
  simp [sinMode, mode_neg]


theorem cosCoeff_neg (φ : Torus d → ℝ) (k : Lattice d) : cosCoeff φ (-k) = cosCoeff φ k := by
  simp [cosCoeff, cosMode_neg]

theorem sinCoeff_neg (φ : Torus d → ℝ) (k : Lattice d) : sinCoeff φ (-k) = - sinCoeff φ k := by
  simp [sinCoeff, sinMode_neg, integral_neg]

theorem integral_mode_mul_real {φ : Torus d → ℝ} (hφ : Integrable φ) (n : Lattice d) :
    ∫ x, mode (-n) x * (φ x : ℂ) = ((cosCoeff φ n : ℝ) : ℂ) + ((-sinCoeff φ n : ℝ) : ℂ) * Complex.I := by
  have e : ∀ x, mode (-n) x * (φ x : ℂ) =
      ((cosMode n x * φ x : ℝ) : ℂ) + ((-(sinMode n x * φ x) : ℝ) : ℂ) * Complex.I := by
    intro x
    apply Complex.ext <;> simp [mode_neg, cosMode, sinMode]
  simp_rw [e]
  rw [integral_add, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_neg]
  · rfl
  · exact (integrable_cosMode_mul n hφ).ofReal
  · exact ((integrable_sinMode_mul n hφ).neg.ofReal).mul_const _

theorem norm_sq_coeff {φ : Torus d → ℝ} (hφ : Integrable φ) (n : Lattice d) :
    ‖∫ x, mode (-n) x * (φ x : ℂ)‖ ^ 2 = cosCoeff φ n ^ 2 + sinCoeff φ n ^ 2 := by
  rw [integral_mode_mul_real hφ, Complex.sq_norm, Complex.normSq_add_mul_I]
  ring

open Classical in
theorem funRealCoeff_eq {φ : Torus d → ℝ} (k : NonzeroLattice d) :
    funRealCoeff φ k =
      if Lattice.IsPosHalf k.1 then Real.sqrt 2 * cosCoeff φ k.1 else Real.sqrt 2 * sinCoeff φ k.1 := by
  unfold funRealCoeff realMode cosCoeff sinCoeff
  by_cases h : Lattice.IsPosHalf k.1
  · simp only [h, ite_true, mul_assoc]
    rw [integral_const_mul]
  · simp only [h, ite_false, mul_assoc]
    rw [integral_const_mul]


theorem funRealCoeff_sq_add_neg {φ : Torus d → ℝ} (k : NonzeroLattice d) :
    funRealCoeff φ k ^ 2 + funRealCoeff φ ⟨-k.1, neg_ne_zero.mpr k.2⟩ ^ 2 =
      2 * (cosCoeff φ k.1 ^ 2 + sinCoeff φ k.1 ^ 2) := by
  rw [funRealCoeff_eq, funRealCoeff_eq]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hneg := isPosHalf_neg k.1 k.2
  by_cases hp : Lattice.IsPosHalf k.1
  · have hq : ¬ Lattice.IsPosHalf (-k.1) := fun h => (hneg.mp h) hp
    simp only [hp, hq, ite_true, ite_false, sinCoeff_neg, mul_pow, h2, neg_sq]
    ring
  · have hq : Lattice.IsPosHalf (-k.1) := hneg.mpr hp
    simp only [hp, hq, ite_true, ite_false, cosCoeff_neg, mul_pow, h2]
    ring


theorem hasSum_sq_coeff {φ : Torus d → ℝ} (hφ : MemLp φ 2 volume) :
    HasSum (fun n : Lattice d => cosCoeff φ n ^ 2 + sinCoeff φ n ^ 2) (∫ x, φ x ^ 2) := by
  have hφ1 : Integrable φ := hφ.integrable one_le_two
  have hH : MemLp (fun x => (φ x : ℂ)) 2
      (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    rw [← volume_eq_pi_haar]
    exact hφ.ofReal
  let f := hH.toLp (fun x => (φ x : ℂ))
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin d) f
  have e1 : ∀ n, UnitAddTorus.mFourierCoeff f n = ∫ x, mode (-n) x * (φ x : ℂ) := by
    intro n
    have h1 : UnitAddTorus.mFourierCoeff f n = UnitAddTorus.mFourierCoeff (fun x => (φ x : ℂ)) n := by
      unfold UnitAddTorus.mFourierCoeff
      refine integral_congr_ae ?_
      filter_upwards [hH.coeFn_toLp] with x hx
      rw [hx]
    rw [h1]
    unfold UnitAddTorus.mFourierCoeff
    rw [volume_eq_pi_haar]
    rfl
  have e2 : ∫ t : Torus d, ‖f t‖ ^ 2 ∂(Measure.pi fun _ : Fin d =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) = ∫ x, φ x ^ 2 := by
    have : ∫ t : Torus d, ‖f t‖ ^ 2 ∂(Measure.pi fun _ : Fin d =>
        (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
        ∫ t : Torus d, ‖(φ t : ℂ)‖ ^ 2 ∂(Measure.pi fun _ : Fin d =>
        (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
      refine integral_congr_ae ?_
      filter_upwards [hH.coeFn_toLp] with x hx
      rw [hx]
    rw [this, ← volume_eq_pi_haar]
    simp
  have h' : HasSum (fun n : Lattice d => ‖∫ x, mode (-n) x * (φ x : ℂ)‖ ^ 2) (∫ x, φ x ^ 2) := by
    convert h using 1
    · funext n
      rw [e1 n]
    · exact e2.symm
  convert h' using 2 with n
  rw [norm_sq_coeff hφ1]


/-- negation on the nonzero lattice -/
def negNZ (d : ℕ) : NonzeroLattice d ≃ NonzeroLattice d :=
  Equiv.subtypeEquiv (Equiv.neg (Lattice d)) (fun a => by simp)

theorem parseval_realCoeff_aux (φ : Torus d → ℝ) (hφ : MemLp φ 2 volume) :
    ∫ x, φ x ^ 2 = (mean φ) ^ 2 + ∑' k : NonzeroLattice d, funRealCoeff φ k ^ 2 := by
  classical
  set T : Lattice d → ℝ := fun n => cosCoeff φ n ^ 2 + sinCoeff φ n ^ 2 with hTdef
  have hT : HasSum T (∫ x, φ x ^ 2) := hasSum_sq_coeff hφ
  have hT0 : T 0 = (mean φ) ^ 2 := by
    have hc : cosCoeff φ 0 = mean φ := by
      simp [cosCoeff, mean, cosMode, mode_zero]
    have hs : sinCoeff φ 0 = 0 := by
      simp [sinCoeff, sinMode, mode_zero]
    simp [hTdef, hc, hs]
  have hTn : HasSum (fun k : NonzeroLattice d => T k.1) ((∫ x, φ x ^ 2) - T 0) := by
    have h1 := hT.update 0 0
    have h2 : HasSum (Function.update T 0 0) ((∫ x, φ x ^ 2) - T 0) := by
      convert h1 using 1
      ring
    rw [← (Subtype.val_injective (p := fun k : Lattice d => k ≠ 0)).hasSum_iff (f := Function.update T 0 0)] at h2
    · convert h2 using 1
      funext k
      simp [Function.update_of_ne k.2]
    · intro x hx
      have : x = 0 := by
        by_contra hne
        exact hx ⟨⟨x, hne⟩, rfl⟩
      simp [this]
  set S : NonzeroLattice d → ℝ := fun k => funRealCoeff φ k ^ 2 with hSdef
  have hpair : ∀ k, S k + S (negNZ d k) = 2 * T k.1 := by
    intro k
    exact funRealCoeff_sq_add_neg k
  have hTneg : ∀ k, T (negNZ d k).1 = T k.1 := by
    intro k
    simp [hTdef, negNZ, cosCoeff_neg, sinCoeff_neg]
  have hS0 : ∀ k, 0 ≤ S k := fun k => sq_nonneg _
  have hSsum : Summable S := by
    refine Summable.of_nonneg_of_le hS0 (fun k => ?_) (hTn.summable.mul_left 2)
    have := hpair k
    have := hS0 (negNZ d k)
    linarith
  have hSneg : Summable (fun k => S (negNZ d k)) := (negNZ d).summable_iff.mpr hSsum
  have hsum2 : ∑' k, (S k + S (negNZ d k)) = 2 * ∑' k : NonzeroLattice d, T k.1 := by
    simp_rw [hpair]
    rw [tsum_mul_left]
  rw [hSsum.tsum_add hSneg, Equiv.tsum_eq (negNZ d) S, hTn.tsum_eq] at hsum2
  rw [hT0] at hsum2
  linarith


/-- Parseval for mean-zero `L²` functions in the real basis. -/
theorem parseval_realCoeff (φ : Torus d → ℝ) (hφ : MemLp φ 2 volume) :
    ∫ x, φ x ^ 2 = (mean φ) ^ 2 + ∑' k : NonzeroLattice d, funRealCoeff φ k ^ 2 := by
  exact parseval_realCoeff_aux φ hφ

/-- bound on iterated derivatives of `g ∘ ℓ`. -/
theorem norm_iteratedFDeriv_comp_functional (g : ℝ → ℝ) (hg : ContDiff ℝ ⊤ g) (B : ℝ)
    (hB : ∀ (i : ℕ) (t : ℝ), ‖iteratedFDeriv ℝ i g t‖ ≤ B) (ℓ : Euc d →L[ℝ] ℝ) (i : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (g ∘ ℓ) x‖ ≤ B * ‖ℓ‖ ^ i := by
  rw [ℓ.iteratedFDeriv_comp_right hg x (le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact hB i _

theorem norm_iteratedFDeriv_scaled_trig (c : ℝ) (hc : 0 ≤ c) (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (fun s => c * Real.cos s) t‖ ≤ c ∧
    ‖iteratedFDeriv ℝ i (fun s => c * Real.sin s) t‖ ≤ c := by
  have h1 : (fun s => c * Real.cos s) = c • Real.cos := by funext s; simp
  have h2 : (fun s => c * Real.sin s) = c • Real.sin := by funext s; simp
  constructor
  · rw [h1, iteratedFDeriv_const_smul_apply Real.contDiff_cos.contDiffAt, norm_smul,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc]
    calc c * |iteratedDeriv i Real.cos t| ≤ c * 1 := by
          gcongr; exact Real.abs_iteratedDeriv_cos_le_one i t
      _ = c := mul_one c
  · rw [h2, iteratedFDeriv_const_smul_apply Real.contDiff_sin.contDiffAt, norm_smul,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc]
    calc c * |iteratedDeriv i Real.sin t| ≤ c * 1 := by
          gcongr; exact Real.abs_iteratedDeriv_sin_le_one i t
      _ = c := mul_one c

/-- the linear functional `x ↦ 2π k·x`. -/
def freqFunctional (k : Lattice d) : Euc d →L[ℝ] ℝ := (2 * Real.pi) • innerSL ℝ (Lattice.toEuc k)

theorem freqFunctional_apply (k : Lattice d) (x : Euc d) :
    freqFunctional k x = 2 * Real.pi * Lattice.dot k x := by
  simp [freqFunctional, Lattice.dot, Lattice.toEuc, PiLp.inner_apply, mul_comm]

theorem norm_freqFunctional_le (k : Lattice d) : ‖freqFunctional k‖ ≤ 2 * Real.pi * Lattice.enorm k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by unfold Lattice.enorm; positivity) fun x => ?_
  rw [freqFunctional]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, Real.norm_eq_abs]
  rw [abs_mul, abs_of_pos Real.two_pi_pos]
  have := abs_real_inner_le_norm (Lattice.toEuc k) x
  unfold Lattice.enorm
  nlinarith [Real.two_pi_pos]


theorem jp_ge_one (k : Lattice d) : 1 ≤ Lattice.jp k := by
  unfold Lattice.jp
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (Lattice.enorm k), sq_nonneg Real.pi]

theorem two_pi_enorm_le_jp (k : Lattice d) : 2 * Real.pi * Lattice.enorm k ≤ Lattice.jp k := by
  unfold Lattice.jp
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (Lattice.enorm k)]

theorem cbNorm_realMode_le_aux (j : ℕ) (k : NonzeroLattice d) :
    cbNorm j (realMode k) ≤ ((j + 1) * Real.sqrt 2) * Lattice.jp k.1 ^ j := by
  have hsq : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hjp := jp_ge_one k.1
  have key : ∀ (i : ℕ), i ≤ j → ∀ (x : Euc d),
      ‖iteratedFDeriv ℝ i (lift (realMode k)) x‖ ≤ Real.sqrt 2 * Lattice.jp k.1 ^ j := by
    intro i hij x
    have hbound : ∀ g : ℝ → ℝ, ContDiff ℝ ⊤ g → (∀ (i : ℕ) (t : ℝ), ‖iteratedFDeriv ℝ i g t‖ ≤ Real.sqrt 2) →
        lift (realMode k) = g ∘ freqFunctional k.1 →
        ‖iteratedFDeriv ℝ i (lift (realMode k)) x‖ ≤ Real.sqrt 2 * Lattice.jp k.1 ^ j := by
      intro g hg hB he
      rw [he]
      refine (norm_iteratedFDeriv_comp_functional g hg _ hB _ i x).trans ?_
      gcongr
      calc ‖freqFunctional k.1‖ ^ i ≤ Lattice.jp k.1 ^ i := by
            gcongr
            exact (norm_freqFunctional_le _).trans (two_pi_enorm_le_jp _)
        _ ≤ Lattice.jp k.1 ^ j := pow_le_pow_right₀ hjp hij
    by_cases hp : Lattice.IsPosHalf k.1
    · refine hbound (fun s => Real.sqrt 2 * Real.cos s) (contDiff_const.mul Real.contDiff_cos)
        (fun i t => (norm_iteratedFDeriv_scaled_trig _ hsq i t).1) ?_
      funext x
      simp [lift, realMode, hp, cosMode_mk, freqFunctional_apply]
    · refine hbound (fun s => Real.sqrt 2 * Real.sin s) (contDiff_const.mul Real.contDiff_sin)
        (fun i t => (norm_iteratedFDeriv_scaled_trig _ hsq i t).2) ?_
      funext x
      simp [lift, realMode, hp, sinMode_mk, freqFunctional_apply]
  unfold cbNorm
  calc ∑ i ∈ Finset.range (j + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ i (lift (realMode k)) x‖
      ≤ ∑ i ∈ Finset.range (j + 1), Real.sqrt 2 * Lattice.jp k.1 ^ j := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        apply Real.iSup_le _ (mul_nonneg hsq (pow_nonneg (by linarith) j))
        intro x
        exact key i hij x
    _ = _ := by simp; ring


theorem iteratedFDeriv_lift_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Torus d → E) (j : ℕ) (x : Euc d) (n : Lattice d) :
    iteratedFDeriv ℝ j (lift φ) (x + Lattice.toEuc n) = iteratedFDeriv ℝ j (lift φ) x := by
  rw [← iteratedFDeriv_comp_add_right]
  congr 2
  funext z
  exact lift_periodic φ z n

theorem bddAbove_norm_iteratedFDeriv_lift (j : ℕ) (φ : Torus d → ℝ) (h : ContDiff ℝ j (lift φ)) :
    BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ j (lift φ) x‖) := by
  have hc : Continuous fun x : Euc d => ‖iteratedFDeriv ℝ j (lift φ) x‖ :=
    (h.continuous_iteratedFDeriv le_rfl).norm
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc d) d).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨‖M‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  set m : Lattice d := fun i => ⌊x i⌋ with hm
  set y : Euc d := x + Lattice.toEuc (-m) with hy
  have hg : ‖iteratedFDeriv ℝ j (lift φ) x‖ = ‖iteratedFDeriv ℝ j (lift φ) y‖ := by
    rw [hy, iteratedFDeriv_lift_periodic]
  have hyc : ∀ i, 0 ≤ y i ∧ y i < 1 := by
    intro i
    have := Int.floor_le (x i)
    have h2 := Int.lt_floor_add_one (x i)
    simp only [hy, hm, Lattice.toEuc, PiLp.add_apply, Pi.neg_apply, Int.cast_neg]
    constructor <;> linarith
  have hyb : y ∈ Metric.closedBall (0 : Euc d) d := by
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_iff.mpr
    refine ⟨Nat.cast_nonneg d, ?_⟩
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs, sq_abs]
          have := hyc i
          nlinarith
      _ = d := by simp
      _ ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
            nlinarith
  show ‖iteratedFDeriv ℝ j (lift φ) x‖ ≤ ‖M‖
  rw [hg]
  have := hM y hyb
  rw [norm_norm] at this
  exact this.trans (Real.le_norm_self M)

theorem cbNorm_add_le_aux (k : ℕ) (φ ψ : Torus d → ℝ)
    (hφ : IsCk k φ) (hψ : IsCk k ψ) :
    cbNorm k (φ + ψ) ≤ cbNorm k φ + cbNorm k ψ := by
  unfold cbNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hφ' : ContDiff ℝ j (lift φ) := hφ.of_le (by exact_mod_cast hjk)
  have hψ' : ContDiff ℝ j (lift ψ) := hψ.of_le (by exact_mod_cast hjk)
  have b1 := bddAbove_norm_iteratedFDeriv_lift j φ hφ'
  have b2 := bddAbove_norm_iteratedFDeriv_lift j ψ hψ'
  apply ciSup_le
  intro x
  have : lift (φ + ψ) = lift φ + lift ψ := rfl
  rw [this, iteratedFDeriv_add_apply (hφ'.contDiffAt) (hψ'.contDiffAt)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact le_ciSup b1 x
  · exact le_ciSup b2 x


/-- The `C^j` norm of a mode is at most `C_j ⟨k⟩^j` (source line 8130). -/
theorem cbNorm_realMode_le (j : ℕ) :
    ∃ C : ℝ, ∀ k : NonzeroLattice d, cbNorm j (realMode k) ≤ C * Lattice.jp k.1 ^ j := by
  exact ⟨(j + 1) * Real.sqrt 2, fun k => cbNorm_realMode_le_aux j k⟩

/-- `cbNorm` is a norm-like functional: triangle inequality. -/
theorem cbNorm_add_le (k : ℕ) (φ ψ : Torus d → ℝ)
    (hφ : IsCk k φ) (hψ : IsCk k ψ) :
    cbNorm k (φ + ψ) ≤ cbNorm k φ + cbNorm k ψ := by
  exact cbNorm_add_le_aux k φ ψ hφ hψ

end Torus

/-- The empirical measure is a probability measure for `N ≥ 1`. -/
theorem empirical_isProbabilityMeasure {d N : ℕ} (hN : 0 < N) (X : Config d N) :
    IsProbabilityMeasure (empirical X) := by
  refine ⟨?_⟩
  have hN' : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  simp [empirical, ENNReal.inv_mul_cancel hN' (ENNReal.natCast_ne_top N)]

/-- `μ_N(φ) = N⁻¹ ∑_i φ(x_i)`. -/
theorem pair_empirical {d N : ℕ} (hN : 0 < N) (X : Config d N) (φ : Torus d → ℝ) :
    pair (empirical X) φ = (N : ℝ)⁻¹ * ∑ i, φ (X i) := by
  unfold pair empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv]
  · intro i _
    exact integrable_dirac (by simp)

section LatticeSums

variable {d : ℕ}

/-- The standard lattice `ℤ^d ⊂ ℝ^d` as a `ℤ`-submodule. -/
abbrev eucLattice (d : ℕ) : Submodule ℤ (Euc d) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)

theorem Lattice.toEuc_mem (k : Lattice d) : Lattice.toEuc k ∈ eucLattice d := by
  have : Lattice.toEuc k = ∑ i, (k i) • (EuclideanSpace.basisFun (Fin d) ℝ).toBasis i := by
    ext j
    simp [Lattice.toEuc, EuclideanSpace.basisFun_apply, Pi.single_apply, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem summable_enorm_rpow_aux (r : ℝ) (hr : r < -(d : ℝ)) :
    Summable fun k : NonzeroLattice d => Lattice.enorm k.1 ^ r := by
  have hrk : Module.finrank ℤ (eucLattice d) = d := by
    rw [ZLattice.rank ℝ (eucLattice d)]
    simp
  have hs : Summable fun z : eucLattice d => ‖z‖ ^ r := ZLattice.summable_norm_rpow (eucLattice d) r (by rw [hrk]; exact hr)
  let f : NonzeroLattice d → eucLattice d := fun k => ⟨Lattice.toEuc k.1, Lattice.toEuc_mem k.1⟩
  have hf : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    have := congrArg (fun z : eucLattice d => (z : Euc d) i) h
    simpa [f, Lattice.toEuc] using this
  have hs2 : Summable ((fun z : eucLattice d => ‖z‖ ^ r) ∘ f) := hs.comp_injective hf
  refine hs2.congr fun k => ?_
  simp only [Function.comp]
  rfl

theorem summable_jp_rpow_aux (m : ℝ) (hm : (d : ℝ) < 2 * m) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * m)) := by
  have hs := summable_enorm_rpow_aux (d := d) (-(2 * m)) (by linarith)
  refine Summable.of_nonneg_of_le (fun k => by unfold Lattice.jp; positivity)
    (fun k => ?_) (hs.mul_left ((2 * Real.pi) ^ (-(2 * m))))
  have he : 0 < Lattice.enorm k.1 := by
    unfold Lattice.enorm
    exact norm_pos_iff.mpr (fun h => k.2 (by
      funext i
      have := congrFun (congrArg WithLp.ofLp h) i
      simpa [Lattice.toEuc] using this))
  have h1 : 2 * Real.pi * Lattice.enorm k.1 ≤ Lattice.jp k.1 := by
    unfold Lattice.jp
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (Lattice.enorm k.1)]
  have hm0 : 0 < 2 * m := by
    have : (0:ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  calc Lattice.jp k.1 ^ (-(2 * m)) ≤ (2 * Real.pi * Lattice.enorm k.1) ^ (-(2 * m)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    _ = _ := Real.mul_rpow (by positivity) he.le

end LatticeSums

/-- Lattice sums `∑_{k ≠ 0} ⟨k⟩^{-2m}` converge exactly when `2m > d`. -/
theorem summable_jp_rpow {d : ℕ} (m : ℝ) (hm : (d : ℝ) < 2 * m) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * m)) := by
  exact summable_jp_rpow_aux m hm

/-- `|k| ≤ ⟨k⟩` and `⟨k⟩ ≤ (1 + 2π)|k|` for `k ≠ 0`. -/
theorem enorm_le_jp {d : ℕ} (k : Lattice d) : Lattice.enorm k ≤ Lattice.jp k := by
  unfold Lattice.jp
  apply Real.le_sqrt_of_sq_le
  have h1 : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [sq_nonneg (Lattice.enorm k)]

theorem jp_le_enorm {d : ℕ} (k : NonzeroLattice d) :
    Lattice.jp k.1 ≤ (1 + 2 * Real.pi) * Lattice.enorm k.1 := by
  have he : 1 ≤ Lattice.enorm k.1 := by
    obtain ⟨i, hi⟩ : ∃ i, k.1 i ≠ 0 := by
      by_contra h
      push Not at h
      exact k.2 (funext h)
    have h1 : (1 : ℝ) ≤ |(k.1 i : ℝ)| := by
      have : (1 : ℤ) ≤ |k.1 i| := Int.one_le_abs hi
      exact_mod_cast this
    calc (1 : ℝ) ≤ |(k.1 i : ℝ)| := h1
      _ = ‖(Lattice.toEuc k.1) i‖ := by simp [Lattice.toEuc]
      _ ≤ ‖Lattice.toEuc k.1‖ := PiLp.norm_apply_le _ i
  unfold Lattice.jp
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.pi_gt_three, mul_pos Real.pi_pos Real.pi_pos]

end HRS
