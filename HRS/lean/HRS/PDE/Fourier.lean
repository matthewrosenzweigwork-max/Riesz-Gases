import HRS.Torus.Sobolev
import HRS.Kernel.Riesz
import HRS.PDE.TorusCalculus

/-!
# Torus PDE layer I: Fourier-coefficient representation of functions and distributions

Source conventions (HRS periodic main paper): `B:sec:conv-fourier`, lines 10054–10071:
`û(k) = ∫ u(x) e^{-2πi k·x} dx`, plane waves `e_k(x) = e^{2πi k·x}` (`B:eq:plane-wave`),
`|∇|^a`, `⟨∇⟩^a` are the multipliers with symbols `(2π|ξ|)^a`, `(1+4π²|ξ|²)^{a/2}`, and the
Sobolev norm is **exactly** (`B:eq:sobolev-def`, lines 10060–10062)

  `‖u‖²_{H^m(𝕋^d)} = ∑_{k∈ℤ^d} (1+4π²|k|²)^m |û(k)|²`   (zero mode included).

## Representation decision (package ADJ-01/ADJ-02/MF-01; see `HRS/PDE/SPEC_NOTES.md` §1)

A distribution on `𝕋^d` *is* its Fourier coefficient sequence.  The PDE statements of
Section 3.2 and Section 5 are therefore formulated on `Coeff d := Lattice d → ℂ`:

* `sobWeight m k = (1+4π²|k|²)^m`; `MemHs m c` (= `c ∈ H^m`) is *summability* of the weighted
  squares, `hsNormSq m c` the sum (so `hsNorm m c = ‖c‖_{H^m}` exactly), `hsInner m` the inner
  product.  Summability is kept as an explicit predicate wherever a `tsum` would otherwise be a
  silent junk value `0`.
* `coeffOf φ` is the coefficient sequence of a real function (Mathlib's `mFourierCoeff`), `toFun c`
  the real function `x ↦ Re ∑_k c(k) e_k(x)` (for `c ∈ H^m`, `m > d/2`, absolutely convergent).
* Derivatives are multipliers: `derivCoeff j` (`∂_j ↦ 2πi k_j`), `laplaceCoeff` (`Δ ↦ -4π²|k|²`),
  `multiDerivCoeff α` (`∂^α`).  The Riesz kernel acts by `rieszMult` (`ĝ(k) = rieszCoeff d s k`),
  the force `∂_i g *` by `gradRieszCoeff i` (symbol `2πi k_i ĝ(k)`): this is the distributional
  convolution, which the source states agrees with the cancellation convention
  `B:eq:nabla-g-convolution` (lines 10096–10101).
* Multiplication by a function `a` is coefficient convolution `mulCoeff â û`
  (`(au)^(k) = ∑_j â(k-j) û(j)`), absolutely convergent for `a, u ∈ L²` (Cauchy–Schwarz) and equal
  to the coefficient of the product (Parseval); `summable_mulCoeff`, `coeffOf_mul` below.
* `truncCoeff n` is the Fourier projection onto `{|k|_∞ ≤ n}` (Galerkin), `IsTrigPoly n c` says
  `c` is supported there (a trigonometric polynomial).

Bridge lemmas to the real-basis objects of `HRS/Torus/Sobolev.lean` (`sobolevNorm`, `MemSobolev`)
and the calculus facts used by the PDE layer are stated at the end (auxiliary, all proved; see
SPEC_NOTES §3 for the worker split).  The file `HRS/PDE/TorusCalculus.lean` (written in parallel)
provides `funFourierCoeff_partialDeriv`, from which `coeffOf_partialDeriv` follows.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- Fourier coefficient sequences `(F̂(k))_{k ∈ ℤ^d}`: the representation of a distribution on
`𝕋^d` used by the PDE layer. -/
abbrev Coeff (d : ℕ) := Lattice d → ℂ

/-! ### Sobolev weights, norms, inner products (`B:eq:sobolev-def`) -/

/-- The Sobolev weight `(1 + 4π²|k|²)^m` of `B:eq:sobolev-def` (real index `m`). -/
def sobWeight (m : ℝ) (k : Lattice d) : ℝ := (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m

/-- `c ∈ H^m(𝕋^d)`: the weighted squares are summable. -/
def MemHs (m : ℝ) (c : Coeff d) : Prop := Summable fun k => sobWeight m k * ‖c k‖ ^ 2

/-- `‖c‖²_{H^m} = ∑_k (1+4π²|k|²)^m |c(k)|²` (`B:eq:sobolev-def`, lines 10060–10062; the value is
meaningful under `MemHs m c`). -/
def hsNormSq (m : ℝ) (c : Coeff d) : ℝ := ∑' k, sobWeight m k * ‖c k‖ ^ 2

/-- `‖c‖_{H^m}`, the exact norm of `B:eq:sobolev-def` (leading constants in Prop 3.9 refer to it). -/
def hsNorm (m : ℝ) (c : Coeff d) : ℝ := Real.sqrt (hsNormSq m c)

/-- The `H^m` inner product `⟨c, c'⟩_{H^m} = ∑_k (1+4π²|k|²)^m c(k) \overline{c'(k)}`. -/
def hsInner (m : ℝ) (c c' : Coeff d) : ℂ :=
  ∑' k, ((sobWeight m k : ℝ) : ℂ) * (c k * conj (c' k))

/-- A coefficient sequence is that of a real-valued distribution: `c(-k) = \overline{c(k)}`. -/
def IsRealCoeff (c : Coeff d) : Prop := ∀ k, c (-k) = conj (c k)

/-- The Fourier coefficients `φ̂(k) = ∫ φ(x) e^{-2πik·x} dx` of a real function (line 10055). -/
def coeffOf (φ : Torus d → ℝ) : Coeff d :=
  fun k => Torus.funFourierCoeff (fun x => (φ x : ℂ)) k

/-- The Fourier coefficients of a complex function. -/
def coeffOfC (φ : Torus d → ℂ) : Coeff d := fun k => Torus.funFourierCoeff φ k

/-- The coefficient sequence `δ_k` of the plane wave `e_k` (`B:eq:plane-wave`, line 10057). -/
def deltaCoeff (k₀ : Lattice d) : Coeff d := fun k => if k = k₀ then 1 else 0

/-- The Fourier series `∑_k c(k) e_k(x)` (a `tsum`; absolutely convergent when
`∑ |c(k)| < ∞`, e.g. for `c ∈ H^m`, `m > d/2`). -/
def series (c : Coeff d) (x : Torus d) : ℂ := ∑' k, c k * Torus.mode k x

/-- The real function `x ↦ Re ∑_k c(k) e_k(x)` represented by a coefficient sequence. -/
def toFun (c : Coeff d) (x : Torus d) : ℝ := (series c x).re

/-- The distributional pairing `⟨F, ψ⟩ = ∑_k F̂(k) \overline{ψ̂(k)}` of a coefficient sequence with
a real test function (equal to `∫ F ψ` for functions; used for "bounded in `𝒟'`" statements). -/
def distPairing (F : Coeff d) (ψ : Torus d → ℝ) : ℂ := ∑' k, F k * conj (coeffOf ψ k)

/-! ### Fourier multipliers: derivatives and the Riesz kernel -/

/-- `∂_j` as the multiplier `2πi k_j`. -/
def derivCoeff (j : Fin d) (c : Coeff d) : Coeff d :=
  fun k => (2 * Real.pi * Complex.I * (k j : ℂ)) * c k

/-- `∂^α` as the multiplier `∏_i (2πi k_i)^{α_i}`. -/
def multiDerivCoeff (α : Fin d → ℕ) (c : Coeff d) : Coeff d :=
  fun k => (∏ i, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ (α i)) * c k

/-- `Δ` as the multiplier `-4π²|k|²`. -/
def laplaceCoeff (c : Coeff d) : Coeff d :=
  fun k => -((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) * c k

/-- `g *` as the multiplier `ĝ(k) = rieszCoeff d s k` (`H:eq:kernel`, lines 421–423;
`ĝ(0) = 0`). -/
def rieszMult (d : ℕ) (s : ℝ) (c : Coeff d) : Coeff d :=
  fun k => ((rieszCoeff d s k : ℝ) : ℂ) * c k

/-- `∂_i g *` as the multiplier `2πi k_i ĝ(k)`: the distributional convolution with the force,
which agrees with the cancellation convention `B:eq:nabla-g-convolution` (lines 10092–10101). -/
def gradRieszCoeff (d : ℕ) (s : ℝ) (i : Fin d) (c : Coeff d) : Coeff d :=
  derivCoeff i (rieszMult d s c)

/-- The symbol `𝔪_q(k) = 4π² c_{d,s} (2π|k|)^{s-d} (q·k)² = (2π q·k)² ĝ(k)` of `K_q = -g * D_q²`,
`D_q = q·∇` (`B:eq:Kl-def`, lines 1831–1834; `𝔪(0) = 0` since `ĝ(0) = 0`). -/
def symbolK (d : ℕ) (s : ℝ) (q : Euc d) (k : Lattice d) : ℝ :=
  (2 * Real.pi * inner ℝ q (Lattice.toEuc k)) ^ 2 * rieszCoeff d s k

/-- The quadratic form `∑_k 𝔪(k) |c(k)|²` of a Fourier multiplier (`B(u,u) = ⟨Ku,u⟩`, line 1835;
meaningful when summable). -/
def quadForm (𝔪 : Lattice d → ℝ) (c : Coeff d) : ℝ := ∑' k, 𝔪 k * ‖c k‖ ^ 2

/-- The bilinear form `∑_k 𝔪(k) c(k) \overline{c'(k)}`. -/
def bilinForm (𝔪 : Lattice d → ℝ) (c c' : Coeff d) : ℂ :=
  ∑' k, ((𝔪 k : ℝ) : ℂ) * (c k * conj (c' k))

/-- Multiplication by a function with coefficients `a`: coefficient convolution
`(a u)^(k) = ∑_j a(k-j) u(j)` (absolutely convergent for `a, u ∈ ℓ²`, `summable_mulCoeff`). -/
def mulCoeff (a c : Coeff d) : Coeff d := fun k => ∑' j, a (k - j) * c j

/-! ### Finite lattice truncations (Galerkin) and multi-indices -/

/-- The box `{k : |k|_∞ ≤ n}`. -/
def InBox (n : ℕ) (k : Lattice d) : Prop := ∀ i, |k i| ≤ (n : ℤ)

instance (n : ℕ) (k : Lattice d) : Decidable (InBox n k) := by unfold InBox; infer_instance

/-- The Fourier projection `P_n` onto `{|k|_∞ ≤ n}`. -/
def truncCoeff (n : ℕ) (c : Coeff d) : Coeff d := fun k => if InBox n k then c k else 0

/-- `c` is a trigonometric polynomial of degree `≤ n` (supported in the box). -/
def IsTrigPoly (n : ℕ) (c : Coeff d) : Prop := ∀ k, c k ≠ 0 → InBox n k

/-- The multi-indices `α ∈ ℕ^d` with `|α| ≤ m`. -/
def multiIndices (d m : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.range (m + 1)).filter (fun α => ∑ i, α i ≤ m)

/-- The multinomial weight `w_α = m!/((m-|α|)! α!)` in
`(1+4π²|k|²)^m = ∑_{|α|≤m} w_α ∏_i (2πk_i)^{2α_i}`, so that
`‖F‖²_{H^m} = ∑_{|α|≤m} w_α ‖∂^αF‖²_{L²}` with `w_α ≥ 1`. -/
def multinomialWeight (m : ℕ) (α : Fin d → ℕ) : ℕ :=
  Nat.factorial m / (Nat.factorial (m - ∑ i, α i) * ∏ i, Nat.factorial (α i))

/-- `‖∂^α F‖²_{L²} = ∑_k ∏_i (2πk_i)^{2α_i} |F̂(k)|²`. -/
def derivL2Sq (α : Fin d → ℕ) (c : Coeff d) : ℝ :=
  ∑' k, (∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) * ‖c k‖ ^ 2

/-- `‖∇∂^α F‖²_{L²} = ∑_k 4π²|k|² ∏_i (2πk_i)^{2α_i} |F̂(k)|²`. -/
def gradDerivL2Sq (α : Fin d → ℕ) (c : Coeff d) : ℝ :=
  ∑' k, (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) *
    (∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) * ‖c k‖ ^ 2

/-! ### Continuity notions for coefficient paths -/

/-- `F ∈ C(S; H^m)`: `F(τ) ∈ H^m` on `S` and `τ ↦ F(τ)` is norm-continuous on `S` for `‖·‖_{H^m}`. -/
def ContinuousInHsOn (m : ℝ) (F : ℝ → Coeff d) (S : Set ℝ) : Prop :=
  (∀ τ ∈ S, MemHs m (F τ)) ∧
    ∀ τ₀ ∈ S, Tendsto (fun τ => hsNorm m (F τ - F τ₀)) (𝓝[S] τ₀) (𝓝 0)

/-- `F ∈ C([0,t]; H^m)`. -/
def ContinuousInHs (m : ℝ) (F : ℝ → Coeff d) (t : ℝ) : Prop :=
  ContinuousInHsOn m F (Set.Icc 0 t)

/-- `F ∈ C_w([0,t]; H^m)`: `F(τ) ∈ H^m` and `τ ↦ ⟨F(τ), G⟩_{H^m}` is continuous for every
`G ∈ H^m` (weak continuity; boundedness follows on the compact interval). -/
def WeakContinuousInHs (m : ℝ) (F : ℝ → Coeff d) (t : ℝ) : Prop :=
  (∀ τ ∈ Set.Icc 0 t, MemHs m (F τ)) ∧
    ∀ G : Coeff d, MemHs m G → ContinuousOn (fun τ => hsInner m (F τ) G) (Set.Icc 0 t)

/-! ### Auxiliary facts about the representation (proved; see SPEC_NOTES §3, unit F) -/

section Facts

/-- `mFourierCoeff` is computed with `haarAddCircle` on each factor; it agrees with the integral
against `volume` on the torus. -/
theorem funFourierCoeff_eq_int (f : Torus d → ℂ) (k : Lattice d) :
    Torus.funFourierCoeff f k = ∫ x, UnitAddTorus.mFourier (-k) x * f x := by
  unfold Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  have hm : (@volume (UnitAddTorus (Fin d))
      (@MeasureSpace.pi (Fin d) _ (fun _ => UnitAddCircle) fun _ => instMeasureSpaceUnitAddCircle)) =
      (volume : Measure (Torus d)) := by
    show Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))
    congr 1
    funext i
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hm]
  simp [smul_eq_mul]

/-- `m_* = ⌊d/2⌋ + 3` (`B:eq:mstar-def`, lines 10157–10159). -/
def mStar (d : ℕ) : ℕ := ⌊(d : ℝ) / 2⌋₊ + 3

/-- `(1+4π²|k|²)^m = ⟨k⟩^{2m}` with `⟨k⟩ = Lattice.jp k`. -/
theorem sobWeight_eq_jp (m : ℝ) (k : Lattice d) : sobWeight m k = Lattice.jp k ^ (2 * m) := by
  unfold sobWeight Lattice.jp
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem coeffOf_eq_fcoef (φ : Torus d → ℝ) (k : Lattice d) : coeffOf φ k = Torus.fcoef φ k := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  rfl

/-- Parseval bridge: for `φ ∈ L²`, the complex coefficient norm of `B:eq:sobolev-def` equals the
real-basis `sobolevNorm` of `HRS/Torus/Sobolev.lean` (zero mode included in both). -/
theorem hsNormSq_coeffOf (m : ℝ) (φ : Torus d → ℝ) (hφ : MemSobolev m φ) :
    MemHs m (coeffOf φ) ∧ hsNormSq m (coeffOf φ) = sobolevNorm m φ ^ 2 := by
  obtain ⟨hL2, hs⟩ := hφ
  obtain ⟨hs2, he⟩ := Torus.weighted_fcoef_sq (2 * m) (hL2.integrable one_le_two) hs
  have hsum : Summable fun k : Lattice d => sobWeight m k * ‖coeffOf φ k‖ ^ 2 := by
    rw [Torus.summable_lattice_iff]
    refine hs2.congr fun k => ?_
    simp only [coeffOf_eq_fcoef, sobWeight_eq_jp]
  have h0 : sobWeight m (0 : Lattice d) * ‖coeffOf φ 0‖ ^ 2 = (Torus.mean φ) ^ 2 := by
    rw [sobWeight_eq_jp, Torus.jp_zero, coeffOf_eq_fcoef, Torus.fcoef_zero]
    simp
  refine ⟨hsum, ?_⟩
  have hT : 0 ≤ (Torus.mean φ) ^ 2 +
      ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 :=
    add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
  unfold sobolevNorm
  rw [Real.sq_sqrt hT]
  unfold hsNormSq
  rw [Torus.tsum_lattice _ hsum, h0, ← he]
  congr 1
  refine tsum_congr fun k => ?_
  simp only [coeffOf_eq_fcoef, sobWeight_eq_jp]

/-- Converse bridge: a square-integrable `φ` whose coefficients lie in `H^m` is in `MemSobolev m`. -/
theorem memSobolev_of_memHs (m : ℝ) (φ : Torus d → ℝ) (hL2 : MemLp φ 2 volume)
    (h : MemHs m (coeffOf φ)) : MemSobolev m φ := by
  refine ⟨hL2, ?_⟩
  have hint : Integrable φ := hL2.integrable one_le_two
  set a : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2
    with ha
  have h2 : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * ‖Torus.fcoef φ k.1‖ ^ 2 := by
    refine ((Torus.summable_lattice_iff _).mp h).congr fun k => ?_
    simp only [coeffOf_eq_fcoef, sobWeight_eq_jp]
  have e : ∀ k : NonzeroLattice d, a k + a (Torus.negNZ d k) =
      2 * (Lattice.jp k.1 ^ (2 * m) * ‖Torus.fcoef φ k.1‖ ^ 2) := by
    intro k
    have h := Torus.two_mul_norm_fcoef_sq hint k
    have hj : Lattice.jp (Torus.negNZ d k).1 = Lattice.jp k.1 := Torus.jp_neg k.1
    simp only [ha, hj]
    linear_combination (Lattice.jp k.1 ^ (2 * m)) * (-h)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
    (sq_nonneg _)) (fun k => ?_) (h2.mul_left 2)
  have := e k
  have h3 : 0 ≤ a (Torus.negNZ d k) := mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
    (sq_nonneg _)
  show a k ≤ _
  linarith

/-- Coefficients of a real function are real-symmetric. -/
theorem isRealCoeff_coeffOf (φ : Torus d → ℝ) (hφ : Integrable φ) : IsRealCoeff (coeffOf φ) := by
  intro k
  unfold coeffOf
  rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h1 : UnitAddTorus.mFourier (- -k) x = conj (UnitAddTorus.mFourier (-k) x) :=
    Torus.mode_neg (-k) x
  simp only [map_mul, Complex.conj_ofReal]
  rw [h1]

/-- `H^m ⊂ ℓ¹` for `m > d/2` (Cauchy–Schwarz with `summable_jp_rpow`). -/
theorem summable_norm_of_memHs (m : ℝ) (hm : (d : ℝ) / 2 < m) (c : Coeff d) (hc : MemHs m c) :
    Summable fun k => ‖c k‖ := by
  rw [Torus.summable_lattice_iff]
  have hd : (d : ℝ) < 2 * m := by linarith
  set a : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-m) with ha
  set b : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ m * ‖c k.1‖ with hb
  have ha2 : Summable fun k => a k ^ 2 := by
    refine (summable_jp_rpow (d := d) m hd).congr fun k => ?_
    simp only [ha]; rw [Torus.jp_rpow_sq]; ring_nf
  have hb2 : Summable fun k => b k ^ 2 := by
    have := (Torus.summable_lattice_iff _).mp hc
    refine this.congr fun k => ?_
    simp only [hb]; rw [mul_pow, Torus.jp_rpow_sq, sobWeight_eq_jp]
  have hcs := Torus.cs_tsum a b (fun k => Real.rpow_nonneg (Torus.jp_pos _).le _)
    (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (norm_nonneg _)) ha2 hb2
  refine hcs.1.congr fun k => ?_
  simp only [ha, hb]
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

theorem summable_series_terms (c : Coeff d) (hs : Summable fun k => ‖c k‖) (x : Torus d) :
    Summable fun k => c k * Torus.mode k x :=
  Summable.of_norm (hs.congr fun k => by simp [Torus.norm_mode])

theorem series_conj (c : Coeff d) (hc : IsRealCoeff c) (hs : Summable fun k => ‖c k‖) (x : Torus d) :
    conj (series c x) = series c x := by
  have h := (summable_series_terms c hs x).hasSum
  have h2 : HasSum (fun k => c k * Torus.mode k x) (conj (series c x)) := by
    have h3 := (Complex.hasSum_conj'.mpr h)
    have h4 : (fun k => conj (c k * Torus.mode k x)) = fun k => c (-k) * Torus.mode (-k) x := by
      funext k
      rw [map_mul, ← hc k, Torus.mode_neg]
    rw [h4] at h3
    exact (Equiv.neg (Lattice d)).hasSum_iff.mp h3
  exact h2.unique h

theorem ofReal_toFun (c : Coeff d) (hc : IsRealCoeff c) (hs : Summable fun k => ‖c k‖)
    (x : Torus d) : ((toFun c x : ℝ) : ℂ) = series c x := by
  unfold toFun
  have := series_conj c hc hs x
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    have := congrArg Complex.im this
    simp only [Complex.conj_im] at this
    linarith

/-- The coefficients of the Fourier series of an absolutely summable sequence. -/
theorem coeffOfC_series (c : Coeff d) (hs : Summable fun k => ‖c k‖) :
    coeffOfC (series c) = c := by
  funext j
  rw [coeffOfC, funFourierCoeff_eq_int]
  have hint : ∀ k, Integrable fun x : Torus d => UnitAddTorus.mFourier (-j) x *
      (c k * Torus.mode k x) := fun k =>
    ((UnitAddTorus.mFourier (-j)).continuous.mul
      (continuous_const.mul (Torus.continuous_mode k))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnorm : ∀ k, ∫ x : Torus d, ‖UnitAddTorus.mFourier (-j) x * (c k * Torus.mode k x)‖ =
      ‖c k‖ := by
    intro k
    have : ∀ x : Torus d, ‖UnitAddTorus.mFourier (-j) x * (c k * Torus.mode k x)‖ = ‖c k‖ := by
      intro x
      have h1 : ‖UnitAddTorus.mFourier (-j) x‖ = 1 := Torus.norm_mode (-j) x
      rw [norm_mul, h1, norm_mul, Torus.norm_mode, one_mul, mul_one]
    simp_rw [this]
    simp
  have h := integral_tsum_of_summable_integral_norm hint (by simpa only [hnorm] using hs)
  have e : ∀ x : Torus d, UnitAddTorus.mFourier (-j) x * series c x =
      ∑' k, UnitAddTorus.mFourier (-j) x * (c k * Torus.mode k x) := by
    intro x
    unfold series
    rw [tsum_mul_left]
  simp_rw [e]
  rw [← h]
  rw [tsum_eq_single j]
  · have this : ∫ x : Torus d, UnitAddTorus.mFourier (-j) x * Torus.mode j x =
        if -j + j = 0 then 1 else 0 := Torus.integral_mode_mul (-j) j
    have h2 : ∀ x : Torus d, UnitAddTorus.mFourier (-j) x * (c j * Torus.mode j x) =
        c j * (UnitAddTorus.mFourier (-j) x * Torus.mode j x) := fun x => by ring
    simp_rw [h2]
    rw [integral_const_mul, this]
    simp
  · intro k hk
    have this : ∫ x : Torus d, UnitAddTorus.mFourier (-j) x * Torus.mode k x =
        if -j + k = 0 then 1 else 0 := Torus.integral_mode_mul (-j) k
    have h2 : ∀ x : Torus d, UnitAddTorus.mFourier (-j) x * (c k * Torus.mode k x) =
        c k * (UnitAddTorus.mFourier (-j) x * Torus.mode k x) := fun x => by ring
    simp_rw [h2]
    rw [integral_const_mul, this]
    have hne : ¬ (-j + k = 0) := fun h0 => hk (by rw [neg_add_eq_zero] at h0; exact h0.symm)
    simp [hne]

/-- Fourier inversion for continuous functions with absolutely summable coefficients. -/
theorem toFun_coeffOf (φ : Torus d → ℝ) (hφ : Continuous φ)
    (hs : Summable fun k => ‖coeffOf φ k‖) : toFun (coeffOf φ) = φ := by
  funext x
  have hs' : Summable fun k : Lattice d => ‖Torus.fcoef φ k‖ := by
    simpa only [coeffOf_eq_fcoef] using hs
  have h := Torus.hasSum_fcoef_series hφ hs' x
  unfold toFun series
  simp only [coeffOf_eq_fcoef]
  rw [h.tsum_eq]
  simp

/-- The coefficients of `toFun c` are `c` when `c` is real-symmetric and absolutely summable. -/
theorem coeffOf_toFun (c : Coeff d) (hc : IsRealCoeff c) (hs : Summable fun k => ‖c k‖) :
    coeffOf (toFun c) = c := by
  funext j
  have h1 : coeffOf (toFun c) j = coeffOfC (series c) j := by
    unfold coeffOf coeffOfC
    simp_rw [ofReal_toFun c hc hs]
  rw [h1, coeffOfC_series c hs]

/-- `∑ ⟨k⟩^i |c(k)| < ∞` for `c ∈ H^m`, `m > d/2 + i`. -/
theorem summable_jp_pow_norm (m : ℝ) (c : Coeff d) (hc : MemHs m c) (i : ℕ)
    (hm : (d : ℝ) / 2 + i < m) : Summable fun k => Lattice.jp k ^ i * ‖c k‖ := by
  rw [Torus.summable_lattice_iff]
  have hd : (d : ℝ) < 2 * (m - i) := by linarith
  set a : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(m - i)) with ha
  set b : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ m * ‖c k.1‖ with hb
  have ha2 : Summable fun k => a k ^ 2 := by
    refine (summable_jp_rpow (d := d) (m - i) hd).congr fun k => ?_
    simp only [ha]; rw [Torus.jp_rpow_sq]; ring_nf
  have hb2 : Summable fun k => b k ^ 2 := by
    have := (Torus.summable_lattice_iff _).mp hc
    refine this.congr fun k => ?_
    simp only [hb]; rw [mul_pow, Torus.jp_rpow_sq, sobWeight_eq_jp]
  have hcs := Torus.cs_tsum a b (fun k => Real.rpow_nonneg (Torus.jp_pos _).le _)
    (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (norm_nonneg _)) ha2 hb2
  refine hcs.1.congr fun k => ?_
  simp only [ha, hb]
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  have : -(m - (i : ℝ)) + m = i := by ring
  rw [this, Real.rpow_natCast]

theorem norm_iteratedFDeriv_trig_comb (a b : ℝ) (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (fun s => a * Real.cos s + b * Real.sin s) t‖ ≤ |a| + |b| := by
  have h1 : ‖iteratedFDeriv ℝ i (fun s => a * Real.cos s) t‖ ≤ |a| := by
    have : (fun s => a * Real.cos s) = a • Real.cos := by funext s; simp
    rw [this, iteratedFDeriv_const_smul_apply Real.contDiff_cos.contDiffAt, norm_smul,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |a| * |iteratedDeriv i Real.cos t| ≤ |a| * 1 := by
          gcongr; exact Real.abs_iteratedDeriv_cos_le_one i t
      _ = |a| := mul_one _
  have h2 : ‖iteratedFDeriv ℝ i (fun s => b * Real.sin s) t‖ ≤ |b| := by
    have : (fun s => b * Real.sin s) = b • Real.sin := by funext s; simp
    rw [this, iteratedFDeriv_const_smul_apply Real.contDiff_sin.contDiffAt, norm_smul,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |b| * |iteratedDeriv i Real.sin t| ≤ |b| * 1 := by
          gcongr; exact Real.abs_iteratedDeriv_sin_le_one i t
      _ = |b| := mul_one _
  have hc1 : ContDiff ℝ i (fun s => a * Real.cos s) := contDiff_const.mul Real.contDiff_cos
  have hc2 : ContDiff ℝ i (fun s => b * Real.sin s) := contDiff_const.mul Real.contDiff_sin
  have e : (fun s => a * Real.cos s + b * Real.sin s) =
      (fun s => a * Real.cos s) + (fun s => b * Real.sin s) := rfl
  rw [e, iteratedFDeriv_add_apply (hc1.contDiffAt) (hc2.contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- The `k`-th term of the Fourier series of `toFun c` as a function on `ℝ^d`. -/
def termFun (c : Coeff d) (k : Lattice d) : Euc d → ℝ :=
  (fun t => (c k).re * Real.cos t + (-(c k).im) * Real.sin t) ∘ Torus.freqFunctional k

theorem lift_toFun_eq_tsum (c : Coeff d) (hs : Summable fun k => ‖c k‖) :
    Torus.lift (toFun c) = fun y => ∑' k, termFun c k y := by
  funext y
  have h := (summable_series_terms c hs (Torus.mk y)).hasSum
  have h2 := Complex.reCLM.hasSum h
  have e : (fun k => termFun c k y) =
      fun k => Complex.reCLM (c k * Torus.mode k (Torus.mk y)) := by
    funext k
    simp only [termFun, Function.comp, Complex.reCLM_apply,
      Torus.mode_mk, Torus.freqFunctional_apply]
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have h3 : HasSum (fun k => termFun c k y) (toFun c (Torus.mk y)) := by
    rw [e]; exact h2
  exact h3.tsum_eq.symm

/-- Sobolev embedding `H^m ↪ C^j` for `m > d/2 + j` in coefficient form: `toFun c` is `C^j` and
`‖toFun c‖_{C^j} ≤ C ‖c‖_{H^m}` (the real-basis version is `cbNorm_le_sobolevNorm`). -/
theorem toFun_isCk_le (j : ℕ) (m : ℝ) (hm : (d : ℝ) / 2 + j < m) :
    ∃ C : ℝ, ∀ c : Coeff d, MemHs m c → IsRealCoeff c →
      Torus.IsCk j (toFun c) ∧ Torus.cbNorm j (toFun c) ≤ C * hsNorm m c := by
  obtain ⟨C, hC⟩ := cbNorm_le_sobolevNorm j m hm
  refine ⟨C, fun c hc hreal => ?_⟩
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd : (d : ℝ) / 2 < m := by linarith
  have hs := summable_norm_of_memHs m hd c hc
  have hjp : ∀ i : ℕ, i ≤ j → Summable fun k => Lattice.jp k ^ i * ‖c k‖ := fun i hi =>
    summable_jp_pow_norm m c hc i (by
      have : (i : ℝ) ≤ j := by exact_mod_cast hi
      linarith)
  have hcomb : ∀ k : Lattice d, ContDiff ℝ ⊤ (fun t : ℝ =>
      (c k).re * Real.cos t + (-(c k).im) * Real.sin t) := fun k =>
    (contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)
  have hCk : Torus.IsCk j (toFun c) := by
    unfold Torus.IsCk
    rw [lift_toFun_eq_tsum c hs]
    refine contDiff_tsum (N := (j : ℕ∞)) (v := fun i k => 2 * (Lattice.jp k ^ i * ‖c k‖)) ?_ ?_ ?_
    · intro k
      exact ((hcomb k).comp (Torus.freqFunctional k).contDiff).of_le le_top
    · intro i hi
      exact (hjp i (by exact_mod_cast hi)).mul_left 2
    · intro i k x hi
      have hb := Torus.norm_iteratedFDeriv_comp_functional _ (hcomb k) _
        (fun i t => norm_iteratedFDeriv_trig_comb ((c k).re) (-(c k).im) i t)
        (Torus.freqFunctional k) i x
      refine hb.trans ?_
      have h1 : |(c k).re| + |-(c k).im| ≤ 2 * ‖c k‖ := by
        rw [abs_neg]
        have := Complex.abs_re_le_norm (c k)
        have := Complex.abs_im_le_norm (c k)
        linarith
      have h2 : ‖Torus.freqFunctional k‖ ^ i ≤ Lattice.jp k ^ i := by
        gcongr
        exact (Torus.norm_freqFunctional_le _).trans (Torus.two_pi_enorm_le_jp _)
      calc (|(c k).re| + |-(c k).im|) * ‖Torus.freqFunctional k‖ ^ i
          ≤ (2 * ‖c k‖) * Lattice.jp k ^ i := by
            gcongr
        _ = _ := by ring
  refine ⟨hCk, ?_⟩
  have hcont : Continuous (toFun c) :=
    Torus.continuous_of_continuous_lift (hCk.continuous)
  have hL2 : MemLp (toFun c) 2 volume :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcoef : coeffOf (toFun c) = c := coeffOf_toFun c hreal hs
  have hmem : MemHs m (coeffOf (toFun c)) := by rw [hcoef]; exact hc
  have hS : MemSobolev m (toFun c) := memSobolev_of_memHs m _ hL2 hmem
  have hnorm : sobolevNorm m (toFun c) = hsNorm m c := by
    obtain ⟨_, h2⟩ := hsNormSq_coeffOf m (toFun c) hS
    rw [hcoef] at h2
    unfold hsNorm
    rw [h2, Real.sqrt_sq]
    unfold sobolevNorm
    exact Real.sqrt_nonneg _
  rw [← hnorm]
  exact hC _ hS hCk

/-- `(∂_j φ)^(k) = 2πi k_j φ̂(k)` (from `TorusCalculus.funFourierCoeff_partialDeriv`). -/
theorem coeffOf_partialDeriv (j : Fin d) (φ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ) :
    coeffOf (Torus.partialDeriv j φ) = derivCoeff j (coeffOf φ) := by
  funext k
  exact funFourierCoeff_partialDeriv j φ hφ k

/-- The lift of `∂_j φ` is `y ↦ D(lift φ)(y) e_j`. -/
theorem lift_partialDeriv (j : Fin d) (φ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ) :
    Torus.lift (Torus.partialDeriv j φ) =
      fun y => fderiv ℝ (Torus.lift φ) y (EuclideanSpace.single j 1) := by
  funext y
  exact partialDeriv_mk j φ hφ y

theorem isCk_one_partialDeriv (j : Fin d) (φ : Torus d → ℝ) (hφ : Torus.IsCk 2 φ) :
    Torus.IsCk 1 (Torus.partialDeriv j φ) := by
  have h1 : Torus.IsCk 1 φ := hφ.of_le (by norm_num)
  unfold Torus.IsCk
  rw [lift_partialDeriv j φ h1]
  have : ContDiff ℝ 1 (fderiv ℝ (Torus.lift φ)) := hφ.fderiv_right (by norm_num)
  exact this.clm_apply contDiff_const

theorem partialDeriv_partialDeriv (j : Fin d) (φ : Torus d → ℝ) (hφ : Torus.IsCk 2 φ) (x : Torus d) :
    Torus.partialDeriv j (Torus.partialDeriv j φ) x =
      fderiv ℝ (fderiv ℝ (Torus.lift φ)) (Torus.rep x) (EuclideanSpace.single j 1)
        (EuclideanSpace.single j 1) := by
  have h1 : Torus.IsCk 1 φ := hφ.of_le (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ (Torus.lift φ)) (Torus.rep x) :=
    ((hφ.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ (Torus.lift φ)))).differentiable
      one_ne_zero _
  have e : Torus.partialDeriv j (Torus.partialDeriv j φ) x =
      fderiv ℝ (Torus.lift (Torus.partialDeriv j φ)) (Torus.rep x) (EuclideanSpace.single j 1) := rfl
  rw [e, lift_partialDeriv j φ h1, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem laplacian_eq_sum (φ : Torus d → ℝ) (hφ : Torus.IsCk 2 φ) (x : Torus d) :
    Torus.laplacian φ x = ∑ j, Torus.partialDeriv j (Torus.partialDeriv j φ) x := by
  unfold Torus.laplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift φ)
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialDeriv_partialDeriv j φ hφ x, iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

/-- `(Δφ)^(k) = -4π²|k|² φ̂(k)`. -/
theorem coeffOf_laplacian (φ : Torus d → ℝ) (hφ : Torus.IsCk 2 φ) :
    coeffOf (Torus.laplacian φ) = laplaceCoeff (coeffOf φ) := by
  funext k
  have h1 : Torus.IsCk 1 φ := hφ.of_le (by norm_num)
  have hcont : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j φ)) := fun j =>
    continuous_partialDeriv j _ (isCk_one_partialDeriv j φ hφ)
  have hint : ∀ j, Integrable fun x => UnitAddTorus.mFourier (-k) x *
      ((Torus.partialDeriv j (Torus.partialDeriv j φ) x : ℝ) : ℂ) := fun j =>
    ((UnitAddTorus.mFourier (-k)).continuous.mul
      (Complex.continuous_ofReal.comp (hcont j))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e1 : coeffOf (Torus.laplacian φ) k =
      ∑ j, coeffOf (Torus.partialDeriv j (Torus.partialDeriv j φ)) k := by
    unfold coeffOf
    simp only [funFourierCoeff_eq_int]
    simp_rw [laplacian_eq_sum φ hφ, Complex.ofReal_sum, Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ => hint j]
  rw [e1]
  have e2 : ∀ j, coeffOf (Torus.partialDeriv j (Torus.partialDeriv j φ)) k =
      (2 * Real.pi * Complex.I * (k j : ℂ)) * ((2 * Real.pi * Complex.I * (k j : ℂ)) *
        coeffOf φ k) := by
    intro j
    rw [coeffOf_partialDeriv j _ (isCk_one_partialDeriv j φ hφ), coeffOf_partialDeriv j φ h1]
    rfl
  simp_rw [e2]
  unfold laplaceCoeff
  have hn : Lattice.enorm k ^ 2 = ∑ j, ((k j : ℤ) : ℝ) ^ 2 := by
    unfold Lattice.enorm Lattice.toEuc
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [hn]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * ((k j : ℤ) : ℂ) ^ 2 * coeffOf φ k) * hI

theorem sobWeight_zero (k : Lattice d) : sobWeight 0 k = 1 := by
  simp [sobWeight]

theorem memHs_zero_iff (c : Coeff d) : MemHs 0 c ↔ Summable fun k => ‖c k‖ ^ 2 := by
  simp [MemHs, sobWeight_zero]

/-- The coefficient convolution converges absolutely for `ℓ²` sequences (Cauchy–Schwarz). -/
theorem summable_mulCoeff (a c : Coeff d) (ha : MemHs 0 a) (hc : MemHs 0 c) (k : Lattice d) :
    Summable fun j => a (k - j) * c j := by
  rw [memHs_zero_iff] at ha hc
  have ha' : Summable fun j => ‖a (k - j)‖ ^ 2 := (Equiv.subLeft k).summable_iff.mpr ha
  have := (Torus.cs_tsum (fun j => ‖a (k - j)‖) (fun j => ‖c j‖) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) ha' hc).1
  exact Summable.of_norm (this.congr fun j => (norm_mul _ _).symm)

/-- Parseval for complex `L²` functions on the torus, in terms of `Torus.funFourierCoeff`. -/
theorem hasSum_parseval (F G : Torus d → ℂ) (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
    HasSum (fun n : Lattice d => conj (Torus.funFourierCoeff F n) * Torus.funFourierCoeff G n)
      (∫ t, conj (F t) * G t) := by
  have hF' : MemLp F 2 (Measure.pi fun _ : Fin d =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    rw [← Torus.volume_eq_pi_haar]; exact hF
  have hG' : MemLp G 2 (Measure.pi fun _ : Fin d =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    rw [← Torus.volume_eq_pi_haar]; exact hG
  let f := hF'.toLp F
  let g := hG'.toLp G
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff (d := Fin d) f g
  have e1 : ∀ (H : Torus d → ℂ) (hH : MemLp H 2 (Measure.pi fun _ : Fin d =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle))) (n : Lattice d),
      UnitAddTorus.mFourierCoeff (hH.toLp H) n = Torus.funFourierCoeff H n := by
    intro H hH n
    unfold UnitAddTorus.mFourierCoeff Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hH.coeFn_toLp] with x hx
    rw [hx]
  have h' : HasSum (fun n : Lattice d => conj (UnitAddTorus.mFourierCoeff f n) *
      UnitAddTorus.mFourierCoeff g n)
      (∫ t, conj (f t) * g t ∂(Measure.pi fun _ : Fin d =>
        (AddCircle.haarAddCircle : Measure UnitAddCircle))) := h
  have e2 : ∫ t, conj (f t) * g t ∂(Measure.pi fun _ : Fin d =>
        (AddCircle.haarAddCircle : Measure UnitAddCircle)) = ∫ t, conj (F t) * G t := by
    rw [Torus.volume_eq_pi_haar]
    refine integral_congr_ae ?_
    filter_upwards [hF'.coeFn_toLp, hG'.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
  rw [← e2]
  have e3 : ∀ n : Lattice d, conj (UnitAddTorus.mFourierCoeff f n) * UnitAddTorus.mFourierCoeff g n
      = conj (Torus.funFourierCoeff F n) * Torus.funFourierCoeff G n := by
    intro n
    rw [e1 F hF' n, e1 G hG' n]
  simp_rw [← e3]
  exact h'

/-- Coefficients of a product of `L²` functions are the convolution of the coefficients
(Parseval). -/
theorem coeffOf_mul (a u : Torus d → ℝ) (ha : MemLp a 2 volume) (hu : MemLp u 2 volume) :
    coeffOf (fun x => a x * u x) = mulCoeff (coeffOf a) (coeffOf u) := by
  funext k
  set F : Torus d → ℂ := fun x => (a x : ℂ) with hF
  set G : Torus d → ℂ := fun x => Torus.mode (-k) x * (u x : ℂ) with hG
  have hFm : MemLp F 2 volume := ha.ofReal
  have hGm : MemLp G 2 volume := by
    refine (hu.ofReal (K := ℂ)).of_le_mul (c := 1)
      ((Torus.continuous_mode (-k)).aestronglyMeasurable.mul hu.ofReal.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp [hG, Torus.norm_mode]
  have hP := hasSum_parseval F G hFm hGm
  have e1 : ∀ n : Lattice d, conj (Torus.funFourierCoeff F n) * Torus.funFourierCoeff G n =
      coeffOf a (k - (n + k)) * coeffOf u (n + k) := by
    intro n
    have h1 : Torus.funFourierCoeff F n = coeffOf a n := rfl
    have h2 : Torus.funFourierCoeff G n = coeffOf u (n + k) := by
      unfold coeffOf
      rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have := Torus.mode_add (-n) (-k) x
      rw [← neg_add] at this
      simp only [hG, Torus.mode] at this ⊢
      rw [← mul_assoc, ← this]
    have h3 : conj (coeffOf a n) = coeffOf a (-n) := (isRealCoeff_coeffOf a (ha.integrable one_le_two) n).symm
    rw [h1, h2, h3]
    congr 2
    abel
  have e2 : ∫ t, conj (F t) * G t = coeffOf (fun x => a x * u x) k := by
    unfold coeffOf
    rw [funFourierCoeff_eq_int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF, hG, Torus.mode, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  simp_rw [e1, e2] at hP
  have hP2 : HasSum (fun j : Lattice d => coeffOf a (k - j) * coeffOf u j)
      (coeffOf (fun x => a x * u x) k) :=
    (Equiv.addRight k).hasSum_iff.mp hP
  exact hP2.tsum_eq.symm

theorem enorm_sq_eq_sum (k : Lattice d) : Lattice.enorm k ^ 2 = ∑ j, ((k j : ℤ) : ℝ) ^ 2 := by
  unfold Lattice.enorm Lattice.toEuc
  rw [EuclideanSpace.norm_sq_eq]
  simp

theorem one_le_multinomialWeight_aux (m : ℕ) (α : Fin d → ℕ) (hα : α ∈ multiIndices d m) :
    1 ≤ multinomialWeight m α := by
  have hle : ∑ i, α i ≤ m := (Finset.mem_filter.mp hα).2
  have h1 : (∏ i, Nat.factorial (α i)) ∣ Nat.factorial (∑ i, α i) :=
    Nat.prod_factorial_dvd_factorial_sum _ _
  have h2 : Nat.factorial (∑ i, α i) * Nat.factorial (m - ∑ i, α i) ∣ Nat.factorial m :=
    Nat.factorial_mul_factorial_dvd_factorial hle
  have h3 : Nat.factorial (m - ∑ i, α i) * ∏ i, Nat.factorial (α i) ∣ Nat.factorial m :=
    (mul_comm (Nat.factorial (m - ∑ i, α i)) _ ▸
      (mul_dvd_mul h1 (dvd_refl (Nat.factorial (m - ∑ i, α i))))).trans h2 |>.trans (dvd_refl _)
  unfold multinomialWeight
  exact Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) h3)
    (Nat.mul_pos (Nat.factorial_pos _) (Finset.prod_pos fun i _ => Nat.factorial_pos _))

theorem multinomialWeight_eq (m : ℕ) (α : Fin d → ℕ) (hα : ∑ i, α i ≤ m) :
    multinomialWeight m α = Nat.choose m (∑ i, α i) * Nat.multinomial Finset.univ α := by
  unfold multinomialWeight
  set j := ∑ i, α i with hj
  have hP : 0 < ∏ i, Nat.factorial (α i) := Finset.prod_pos fun i _ => Nat.factorial_pos _
  have hf : 0 < Nat.factorial (m - j) := Nat.factorial_pos _
  apply Nat.div_eq_of_eq_mul_left (Nat.mul_pos hf hP)
  have h1 := Nat.multinomial_spec (Finset.univ : Finset (Fin d)) α
  have h2 : Nat.choose m j * Nat.factorial j * Nat.factorial (m - j) = Nat.factorial m :=
    Nat.choose_mul_factorial_mul_factorial hα
  rw [← hj] at h1
  calc Nat.factorial m = Nat.choose m j * Nat.factorial j * Nat.factorial (m - j) := h2.symm
    _ = Nat.choose m j * ((∏ i, Nat.factorial (α i)) * Nat.multinomial Finset.univ α) *
        Nat.factorial (m - j) := by rw [h1]
    _ = _ := by ring

/-- Multinomial expansion `(1 + ∑ x_i)^m = ∑_{|α| ≤ m} w_α ∏ x_i^{α_i}`. -/
theorem one_add_sum_pow (m : ℕ) (x : Fin d → ℝ) :
    (1 + ∑ i, x i) ^ m =
      ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * ∏ i, x i ^ α i := by
  classical
  rw [add_comm, add_pow]
  have hmaps : ∀ α ∈ multiIndices d m, (∑ i, α i) ∈ Finset.range (m + 1) := by
    intro α hα
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hα).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hset : (multiIndices d m).filter (fun α => ∑ i, α i = j) = Finset.piAntidiag Finset.univ j := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true,
      multiIndices, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, _⟩, h⟩; exact h
    · intro h
      refine ⟨⟨fun i => ?_, h ▸ hjm⟩, h⟩
      have h' : ∑ i, α i = j := h
      have : α i ≤ ∑ i, α i := Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
  rw [hset, Finset.sum_pow_eq_sum_piAntidiag]
  simp only [one_pow, mul_one]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hsum : ∑ i, α i = j := (Finset.mem_piAntidiag.mp hα).1
  rw [multinomialWeight_eq m α (hsum ▸ hjm), hsum]
  push_cast
  ring

/-- `‖F‖²_{H^m} = ∑_{|α|≤m} w_α ‖∂^αF‖²_{L²}` (multinomial expansion of the weight). -/
theorem hsNormSq_eq_sum_derivL2Sq (m : ℕ) (c : Coeff d) (hc : MemHs m c) :
    hsNormSq m c = ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * derivL2Sq α c := by
  set g : (Fin d → ℕ) → Lattice d → ℝ :=
    fun α k => (∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) * ‖c k‖ ^ 2 with hg
  have hg0 : ∀ α k, 0 ≤ g α k := fun α k => by
    refine mul_nonneg ?_ (sq_nonneg _)
    refine Finset.prod_nonneg fun i _ => ?_
    rw [pow_mul]; positivity
  have hpt : ∀ k : Lattice d, sobWeight (m : ℝ) k * ‖c k‖ ^ 2 =
      ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * g α k := by
    intro k
    have h1 : sobWeight (m : ℝ) k =
        (1 + ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2) ^ m := by
      unfold sobWeight
      rw [Real.rpow_natCast, enorm_sq_eq_sum]
      congr 2
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, one_add_sum_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hg]
    rw [mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul]
  have hsumg : ∀ α ∈ multiIndices d m, Summable (g α) := by
    intro α hα
    refine Summable.of_nonneg_of_le (hg0 α) (fun k => ?_) hc
    rw [hpt k]
    have hw : (1 : ℝ) ≤ multinomialWeight m α := by exact_mod_cast one_le_multinomialWeight_aux m α hα
    calc g α k ≤ (multinomialWeight m α : ℝ) * g α k := by nlinarith [hg0 α k]
      _ ≤ _ := Finset.single_le_sum (f := fun α => (multinomialWeight m α : ℝ) * g α k)
          (fun α' _ => mul_nonneg (Nat.cast_nonneg _) (hg0 α' k)) hα
  unfold hsNormSq derivL2Sq
  simp_rw [hpt]
  rw [Summable.tsum_finsetSum (fun α hα => (hsumg α hα).mul_left _)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [tsum_mul_left]

/-- `w_α ≥ 1` for `|α| ≤ m`. -/
theorem one_le_multinomialWeight (m : ℕ) (α : Fin d → ℕ) (hα : α ∈ multiIndices d m) :
    1 ≤ multinomialWeight m α :=
  one_le_multinomialWeight_aux m α hα

/-- Hölder interpolation for nonnegative summable sequences: for `θ ∈ (0,1)`,
`∑ f^(1-θ) g^θ ≤ (∑ f)^(1-θ) (∑ g)^θ`. -/
theorem summable_tsum_rpow_mul_rpow_le {ι : Type*} (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hfs : Summable f) (hgs : Summable g) (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) :
    Summable (fun i => f i ^ (1 - θ) * g i ^ θ) ∧
      ∑' i, f i ^ (1 - θ) * g i ^ θ ≤ (∑' i, f i) ^ (1 - θ) * (∑' i, g i) ^ θ := by
  have h1θ : 0 < 1 - θ := by linarith
  have hc : ((1 - θ)⁻¹).HolderConjugate (θ⁻¹) :=
    Real.HolderConjugate.inv_inv h1θ h0 (by ring)
  have e1 : ∀ i, (f i ^ (1 - θ)) ^ (1 - θ)⁻¹ = f i := fun i =>
    Real.rpow_rpow_inv (hf i) h1θ.ne'
  have e2 : ∀ i, (g i ^ θ) ^ θ⁻¹ = g i := fun i => Real.rpow_rpow_inv (hg i) h0.ne'
  have := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hc
    (f := fun i => f i ^ (1 - θ)) (g := fun i => g i ^ θ)
    (fun i => Real.rpow_nonneg (hf i) _) (fun i => Real.rpow_nonneg (hg i) _)
    (by simpa only [e1] using hfs) (by simpa only [e2] using hgs)
  simp only [e1, e2, one_div, inv_inv] at this
  exact this

/-- Fourier–Hölder interpolation `‖v‖²_{H^σ} ≤ ‖v‖^{2(1-λ)}_{H^a} ‖v‖^{2λ}_{H^b}` for
`σ = (1-θ)a + θb`, `θ ∈ [0,1]` (used in regime R3, line 1933, and in Prop 5.1). -/
theorem hsNormSq_interpolation (a b θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (c : Coeff d)
    (ha : MemHs a c) (hb : MemHs b c) :
    MemHs ((1 - θ) * a + θ * b) c ∧
      hsNormSq ((1 - θ) * a + θ * b) c ≤ hsNormSq a c ^ (1 - θ) * hsNormSq b c ^ θ := by
  rcases hθ0.eq_or_lt with rfl | hpos
  · simp only [sub_zero, one_mul, zero_mul, add_zero, Real.rpow_one, Real.rpow_zero, mul_one]
    exact ⟨ha, le_rfl⟩
  rcases hθ1.eq_or_lt with rfl | hlt
  · simp only [sub_self, zero_mul, zero_add, one_mul, Real.rpow_one, Real.rpow_zero]
    exact ⟨hb, le_rfl⟩
  have hW : ∀ k : Lattice d, 0 < 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := fun k => by positivity
  have hw : ∀ (m : ℝ) (k : Lattice d), 0 ≤ sobWeight m k := fun m k =>
    Real.rpow_nonneg (hW k).le _
  have hpt : ∀ k : Lattice d, sobWeight ((1 - θ) * a + θ * b) k * ‖c k‖ ^ 2 =
      (sobWeight a k * ‖c k‖ ^ 2) ^ (1 - θ) * (sobWeight b k * ‖c k‖ ^ 2) ^ θ := by
    intro k
    have hx : 0 ≤ ‖c k‖ ^ 2 := sq_nonneg _
    rw [Real.mul_rpow (hw a k) hx, Real.mul_rpow (hw b k) hx]
    have hxx : ‖c k‖ ^ 2 = (‖c k‖ ^ 2) ^ (1 - θ) * (‖c k‖ ^ 2) ^ θ := by
      rw [← Real.rpow_add' hx (by norm_num)]; simp
    have hww : sobWeight ((1 - θ) * a + θ * b) k = sobWeight a k ^ (1 - θ) * sobWeight b k ^ θ := by
      unfold sobWeight
      rw [← Real.rpow_mul (hW k).le, ← Real.rpow_mul (hW k).le, ← Real.rpow_add (hW k)]
      congr 1; ring
    rw [hww]
    nth_rewrite 1 [hxx]
    ring
  obtain ⟨hs, hle⟩ := summable_tsum_rpow_mul_rpow_le (fun k : Lattice d => sobWeight a k * ‖c k‖ ^ 2)
    (fun k => sobWeight b k * ‖c k‖ ^ 2) (fun k => mul_nonneg (hw a k) (sq_nonneg _))
    (fun k => mul_nonneg (hw b k) (sq_nonneg _)) ha hb θ hpos hlt
  refine ⟨?_, ?_⟩
  · unfold MemHs
    simpa only [hpt] using hs
  · unfold hsNormSq
    simp only [hpt]
    exact hle

/-- The truncation `P_n c → c` in `H^m` as `n → ∞` for `c ∈ H^m`, and `‖P_n c‖_{H^m} ≤ ‖c‖_{H^m}`. -/
theorem truncCoeff_tendsto (m : ℝ) (c : Coeff d) (hc : MemHs m c) :
    (∀ n, hsNormSq m (truncCoeff n c) ≤ hsNormSq m c) ∧
      Tendsto (fun n => hsNorm m (c - truncCoeff n c)) atTop (𝓝 0) := by
  have hw : ∀ k : Lattice d, 0 ≤ sobWeight m k := fun k => by
    unfold sobWeight; positivity
  have hf0 : ∀ k : Lattice d, 0 ≤ sobWeight m k * ‖c k‖ ^ 2 := fun k =>
    mul_nonneg (hw k) (sq_nonneg _)
  refine ⟨fun n => ?_, ?_⟩
  · unfold hsNormSq
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ hc
    · unfold truncCoeff
      split_ifs <;> simp [hf0 k]
    · refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hw k) (sq_nonneg _)) (fun k => ?_) hc
      unfold truncCoeff
      split_ifs <;> simp [hf0 k]
  · have hdom : Tendsto (fun n : ℕ => ∑' k, sobWeight m k * ‖(c - truncCoeff n c) k‖ ^ 2) atTop
        (𝓝 (∑' k : Lattice d, (0 : ℝ))) := by
      refine tendsto_tsum_of_dominated_convergence (bound := fun k => sobWeight m k * ‖c k‖ ^ 2)
        hc (fun k => ?_) (Filter.Eventually.of_forall fun n k => ?_)
      · have hev : ∀ᶠ n : ℕ in atTop, InBox n k := by
          unfold InBox
          rw [Filter.eventually_all]
          intro i
          filter_upwards [Filter.eventually_ge_atTop (k i).natAbs] with n hn
          have : ((k i).natAbs : ℤ) ≤ n := by exact_mod_cast hn
          rwa [Int.natCast_natAbs] at this
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        simp [truncCoeff, hn]
      · rw [Real.norm_of_nonneg (mul_nonneg (hw k) (sq_nonneg _))]
        simp only [Pi.sub_apply, truncCoeff]
        split_ifs <;> simp [hf0 k]
    simp only [tsum_zero] at hdom
    have := (Real.continuous_sqrt.tendsto 0).comp hdom
    simpa [hsNorm, hsNormSq, Function.comp_def] using this

/-- The coefficient of the plane wave: `coeffOfC (e_k) = δ_k`. -/
theorem coeffOfC_mode (k : Lattice d) : coeffOfC (Torus.mode k) = deltaCoeff k := by
  funext j
  rw [coeffOfC, funFourierCoeff_eq_int]
  have h := Torus.integral_mode_mul (-j) k
  simp only [Torus.mode] at h ⊢
  rw [h]
  simp only [deltaCoeff]
  have : (-j + k = 0) ↔ (j = k) := by
    rw [neg_add_eq_zero, eq_comm]
  simp only [this]

/-- `‖δ_k‖_{H^m} = (1+4π²|k|²)^{m/2}` (line 10063). -/
theorem hsNorm_deltaCoeff (m : ℝ) (k : Lattice d) :
    hsNorm m (deltaCoeff k) = (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (m / 2) := by
  have h : hsNormSq m (deltaCoeff k) = sobWeight m k := by
    unfold hsNormSq
    rw [tsum_eq_single k]
    · simp [deltaCoeff]
    · intro j hj
      simp [deltaCoeff, hj]
  unfold hsNorm
  rw [h, sobWeight, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

end Facts

end HRS.PDE
