import HRS.Torus.Basic
import HRS.Kernel.ResponseAux

/-!
# The periodic Riesz / logarithmic kernel and the equilibrium operators

Source: HRS periodic main paper.
* Kernel normalisation `H:eq:kernel` (source lines 425-430):
  `ĝ(0) = 0`, `ĝ(k) = c_{d,s}(2π|k|)^{s-d} > 0` for `k ≠ 0`, with `c_{d,s}` chosen so
  that the local singularity is `|x|^{-s}` (`s > 0`) or `-log|x|` (`s = 0`)
  (`H:eq:intro-kernel`, lines 181-186: `g(x) = |x|^{-s} + O(1)`, resp. `-log|x| + O(1)`,
  regular part smooth near the origin; "the positive-power kernel is not divided by `s`").
* Equilibrium operators `H:eq:equilibrium-operators` (lines 922-938):
  `A_β = β^{-1} I + K_{μ_β}`, `L_β = -ρ_β^{-1} Div(ρ_β ∇)`, `R_{β,μ} = (I + βK_μ)^{-1}` on
  `L²_0(μ_β)`, with `K_μ f = P_μ[g * (f μ)]` and `P_μ f = f - μ(f)`
  (`O:eq:negative-cov`, line 5517 and surrounding text).
* Susceptibility covariance `H:eq:susceptibility` (lines 931-935):
  `C_β(φ,ψ) = ⟨P_μ φ, R_{β,μ} P_μ ψ⟩_{L²(μ)}`.

## Representation

The Fourier coefficients are not absolutely summable (`∑_{k≠0} |k|^{s-d} = ∞` for
`0 ≤ s < d`), so the kernel is *defined* pointwise by heat regularisation:
`g(x) = lim_{ε↓0} ∑_{k≠0} ĝ(k) e^{-ε|k|²} cos(2π k·x)`.  This limit exists for `x ≠ 0`
and equals the periodic Riesz/log kernel with the stated normalisation; at `x = 0` the
value is a junk real (`limUnder` of a divergent family), which is never used: all
formulas (modulated energy, Gibbs weights) use `g` only off the particle diagonal or
integrated against a measure.  The constant `c_{d,s}` is given by its classical closed
form (Stein, *Singular integrals*, Ch. V §1, Lemma 1, in the convention
`∫ |x|^{-s} e^{-2πi x·ξ} dx = π^{s-d/2} Γ((d-s)/2)/Γ(s/2) |ξ|^{s-d}`):

  `c_{d,s} = 2^{d-s} π^{d/2} Γ((d-s)/2) / Γ(s/2)`  (0 < s < d),
  `c_{d,0} = 2^{d-1} π^{d/2} Γ(d/2)`  (s = 0, from `-log|x| = ∂_s |x|^{-s}|_{s=0}`).

The identification of this constant with the paper's prescription "local singularity
is `|x|^{-s}` / `-log|x|`" is theorem `KERN-01` (`periodicRiesz_local_singularity`),
not an assumption; see `docs/ISSUES.md` §K1.

Convolutions `g * μ` are Bochner integrals `∫ g(x - y) dμ(y)` (junk `0` if not
integrable; integrability is part of the hypotheses where it matters, cf. source
line 431: "convolutions with a nonintegrable force are interpreted distributionally").
The inverse `R_{β,μ} = (I + βK_μ)^{-1}` is represented by the *response equation*
`h + β K_μ h = P_μ ψ`, `μ(h) = 0`; `responseInverse` picks the unique solution.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

/-- The normalising constant `c_{d,s}` of `H:eq:kernel`. -/
def rieszConst (d : ℕ) (s : ℝ) : ℝ :=
  if s = 0 then 2 ^ ((d : ℝ) - 1) * Real.pi ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)
  else 2 ^ ((d : ℝ) - s) * Real.pi ^ ((d : ℝ) / 2) * Real.Gamma (((d : ℝ) - s) / 2) / Real.Gamma (s / 2)

open Classical in
/-- `ĝ(k)`: `0` at `k = 0`, `c_{d,s}(2π|k|)^{s-d}` otherwise (source lines 425-430). -/
def rieszCoeff (d : ℕ) (s : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else rieszConst d s * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ))

/-- Heat-regularised partial kernel `g_ε(x) = ∑_{k} ĝ(k) e^{-ε|k|²} cos(2πk·x)`. -/
def heatRiesz (d : ℕ) (s : ℝ) (ε : ℝ) (x : Torus d) : ℝ :=
  ∑' k : Lattice d, rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) * Torus.cosMode k x

/-- The periodic Riesz (`0 < s < d`) / logarithmic (`s = 0`) kernel `g` of `H:eq:kernel`,
as the `ε ↓ 0` limit of the heat-regularised kernel. -/
def periodicRiesz (d : ℕ) (s : ℝ) (x : Torus d) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => heatRiesz d s ε x

/-- Heat-regularised gradient `∇g_ε(x) = -∑_k ĝ(k) e^{-ε|k|²} 2π k sin(2πk·x)`. -/
def heatRieszGrad (d : ℕ) (s : ℝ) (ε : ℝ) (x : Torus d) : Euc d :=
  ∑' k : Lattice d,
    (-(rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) * 2 * Real.pi * Torus.sinMode k x)) •
      Lattice.toEuc k

/-- The force `∇g` (pointwise limit of the regularised gradients; junk at `x = 0`). -/
def periodicRieszGrad (d : ℕ) (s : ℝ) (x : Torus d) : Euc d :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => heatRieszGrad d s ε x

/-- `g_+ := max(g, 0)` (used in the equilibrium estimates, Lemma 4.5). -/
def rieszPos (d : ℕ) (s : ℝ) (x : Torus d) : ℝ := max (periodicRiesz d s x) 0

/-- Convolution `g * μ (x) = ∫ g(x - y) dμ(y)`. -/
def convMeasure {d : ℕ} (g : Torus d → ℝ) (μ : Measure (Torus d)) (x : Torus d) : ℝ :=
  ∫ y, g (x - y) ∂μ

/-- Convolution with a function against `dx`: `g * f (x) = ∫ g(x - y) f(y) dy`. -/
def convFun {d : ℕ} (g : Torus d → ℝ) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, g (x - y) * f y

/-- Vector convolution `∇g * μ (x) = ∫ ∇g(x - y) dμ(y)`. -/
def convGradMeasure {d : ℕ} (G : Torus d → Euc d) (μ : Measure (Torus d)) (x : Torus d) : Euc d :=
  ∫ y, G (x - y) ∂μ

/-- Energy pairing `⟨g * ν, ν'⟩ = ∬ g(x-y) dν(x) dν'(y)` (Bochner double integral). -/
def energyPairing {d : ℕ} (g : Torus d → ℝ) (ν ν' : Measure (Torus d)) : ℝ :=
  ∫ x, ∫ y, g (x - y) ∂ν' ∂ν

/-- `K_μ f = P_μ[g * (f μ)]` (source line 5517 and text after it). -/
def Kop {d : ℕ} (g : Torus d → ℝ) (μ : Measure (Torus d)) (f : Torus d → ℝ) : Torus d → ℝ :=
  projMean μ fun x => ∫ y, g (x - y) * f y ∂μ

/-- The response equation defining `h = R_{β,μ} P_μ ψ = (I + βK_μ)^{-1} P_μ ψ` on `L²_0(μ)`:
`h + β K_μ h = P_μ ψ` and `μ(h) = 0` (`H:eq:equilibrium-operators`, line 924). -/
def IsResponse {d : ℕ} (g : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ)
    (ψ h : Torus d → ℝ) : Prop :=
  MemLp h 2 μ ∧ pair μ h = 0 ∧ ∀ᵐ x ∂μ, h x + β * Kop g μ h x = projMean μ ψ x

open Classical in
/-- `R_{β,μ} P_μ ψ`: the solution of the response equation (`0` if it does not exist). -/
def responseInverse {d : ℕ} (g : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ)
    (ψ : Torus d → ℝ) : Torus d → ℝ :=
  if h : ∃ h, IsResponse g μ β ψ h then h.choose else 0

/-- The susceptibility covariance form `C_{β,μ}(φ,ψ) = ⟨P_μ φ, R_{β,μ} P_μ ψ⟩_{L²(μ)}`
(`H:eq:susceptibility`, lines 931-935; `O:eq:negative-cov`, line 5517). -/
def susceptibilityCov {d : ℕ} (g : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ)
    (φ ψ : Torus d → ℝ) : ℝ :=
  l2Inner μ (projMean μ φ) (responseInverse g μ β ψ)

/-- `A_β = β^{-1} I + K_{μ_β}` acting on functions. -/
def Aop {d : ℕ} (g : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ) (f : Torus d → ℝ) :
    Torus d → ℝ :=
  fun x => β⁻¹ * f x + Kop g μ f x

/-- `L_β f = -ρ^{-1} Div(ρ ∇f)` for `μ = ρ dx`. -/
def Lop {d : ℕ} (ρ : Torus d → ℝ) (f : Torus d → ℝ) : Torus d → ℝ :=
  fun x => -(ρ x)⁻¹ * Torus.div (fun y => ρ y • Torus.grad f y) x

/-- The quadratic form `B(u,v) = ⟨K u, v⟩` of a Fourier multiplier with symbol `𝔪`
(Lemma C.3, `M:B:lem:quadratic-toolbox`). -/
def multiplierForm {d : ℕ} (𝔪 : Lattice d → ℝ) (u v : Torus d → ℝ) : ℝ :=
  ∑' k : NonzeroLattice d, 𝔪 k.1 * Torus.funRealCoeff u k * Torus.funRealCoeff v k

/-! ### Facts about the kernel (work package KERN-01) -/

section KernelHelpers

/-- Product of summable nonnegative functions over `Fin n → ℤ`. -/
theorem pi_prod_summable {f : ℤ → ℝ} (hf : Summable f) (h0 : 0 ≤ f) :
    ∀ n : ℕ, Summable fun k : Fin n → ℤ => ∏ i, f (k i)
  | 0 => by
    simpa using (summable_of_hasFiniteSupport (f := fun _ : Fin 0 → ℤ => (1:ℝ))
      (Set.toFinite _))
  | n + 1 => by
    have ih := pi_prod_summable hf h0 n
    have h := hf.mul_of_nonneg ih h0 (fun k => Finset.prod_nonneg fun i _ => h0 _)
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).summable_iff]
    refine h.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem summable_exp_sq (ε : ℝ) (hε : 0 < ε) :
    Summable fun m : ℤ => Real.exp (-ε * (m:ℝ)^2) := by
  have hN : Summable fun n : ℕ => Real.exp (-ε * (n:ℝ)^2) := by
    refine (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hε)).of_nonneg_of_le
      (fun _ => (Real.exp_pos _).le) fun n => ?_
    apply Real.exp_le_exp.mpr
    have : (n:ℝ) ≤ (n:ℝ)^2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1:ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith
  exact Summable.of_nat_of_neg hN (by simpa using hN)

theorem enorm_sq {d : ℕ} (k : Lattice d) : Lattice.enorm k ^ 2 = ∑ i, ((k i : ℤ) : ℝ)^2 := by
  simp [Lattice.enorm, Lattice.toEuc, EuclideanSpace.norm_sq_eq]

theorem enorm_neg {d : ℕ} (k : Lattice d) : Lattice.enorm (-k) = Lattice.enorm k := by
  have h : Lattice.toEuc (-k) = -Lattice.toEuc k := by
    ext i; simp [Lattice.toEuc]
  simp [Lattice.enorm, h]

theorem one_le_enorm {d : ℕ} (k : Lattice d) (hk : k ≠ 0) : 1 ≤ Lattice.enorm k := by
  have : ∃ i, k i ≠ 0 := by
    by_contra h
    exact hk (funext fun i => not_not.mp (not_exists.mp h i))
  obtain ⟨i, hi⟩ := this
  have h1 : (1:ℝ) ≤ ((k i : ℤ):ℝ)^2 := by
    have : (1:ℤ) ≤ (k i)^2 := by nlinarith [sq_pos_of_ne_zero hi, Int.one_le_abs hi, sq_abs (k i)]
    exact_mod_cast this
  have h2 : ((k i:ℤ):ℝ)^2 ≤ Lattice.enorm k ^ 2 := by
    rw [enorm_sq]
    exact Finset.single_le_sum (f := fun j => ((k j : ℤ):ℝ)^2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [show 0 ≤ Lattice.enorm k from norm_nonneg _]

theorem summable_gauss_lattice (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Summable fun k : Lattice d => Real.exp (-ε * Lattice.enorm k ^ 2) := by
  have := pi_prod_summable (summable_exp_sq ε hε) (fun m => (Real.exp_pos _).le) d
  refine this.congr fun k => ?_
  rw [enorm_sq, Finset.mul_sum, Real.exp_sum]

theorem norm_mode {d : ℕ} (k : Lattice d) (x : Torus d) : ‖Torus.mode k x‖ = 1 := by
  simp [Torus.mode, UnitAddTorus.mFourier, norm_prod]

theorem abs_cosMode_le {d : ℕ} (k : Lattice d) (x : Torus d) : |Torus.cosMode k x| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (norm_mode k x).le

theorem cosMode_neg {d : ℕ} (k : Lattice d) (x : Torus d) :
    Torus.cosMode k (-x) = Torus.cosMode k x := by
  simp only [Torus.cosMode, Torus.mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    Pi.neg_apply]
  simp [← map_prod]

theorem rieszConst_pos {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    0 < rieszConst d s := by
  have hd' : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold rieszConst
  split_ifs with h
  · exact mul_pos (mul_pos (by positivity) (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    exact div_pos (mul_pos (mul_pos (by positivity) (by positivity))
      (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))

end KernelHelpers

section KernelLimit

open Complex Set
open scoped Real

theorem theta_eq (u y : ℝ) (hu : 0 < u) :
    ∑' n : ℤ, Complex.exp (2 * π * I * n * y - u * (n:ℂ)^2) =
      ((Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u)) : ℝ) : ℂ) := by
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu' : (u:ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have h1 : (∑' n : ℤ, Complex.exp (2 * π * I * n * y - u * (n:ℂ)^2)) = jacobiTheta₂ (y:ℂ) (I * u / π) := by
    unfold jacobiTheta₂ jacobiTheta₂_term
    refine tsum_congr fun n => ?_
    congr 1
    field_simp
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [h1, jacobiTheta₂_functional_equation]
  unfold jacobiTheta₂ jacobiTheta₂_term
  have h2 : (-I * (I * u / π) : ℂ) = ((u / π : ℝ) : ℂ) := by
    push_cast; field_simp; simp [Complex.I_sq]
  have h3 : (((u / π : ℝ) : ℂ)) ^ (1/2 : ℂ) = ((Real.sqrt (u / π) : ℝ) : ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  rw [h2, h3]
  have hs : Real.sqrt (u / π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs' : (1:ℂ) / ((Real.sqrt (u / π) : ℝ) : ℂ) = ((Real.sqrt (π / u) : ℝ) : ℂ) := by
    have : Real.sqrt (π / u) = 1 / Real.sqrt (u / π) := by
      rw [one_div, ← Real.sqrt_inv, inv_div]
    rw [this]; push_cast; rfl
  rw [hs', Complex.ofReal_mul, Complex.ofReal_tsum, mul_assoc, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_add]
  push_cast
  congr 1
  field_simp
  ring_nf

theorem pi_hasSum : ∀ (n : ℕ) (f : Fin n → ℤ → ℂ), (∀ i, Summable fun m => ‖f i m‖) →
    Summable (fun k : Fin n → ℤ => ‖∏ i, f i (k i)‖) ∧
      HasSum (fun k : Fin n → ℤ => ∏ i, f i (k i)) (∏ i, ∑' m, f i m)
  | 0, f, hf => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact ⟨by simpa using (summable_of_hasFiniteSupport (f := fun _ : Fin 0 → ℤ => (1:ℝ)) (Set.toFinite _)),
      by simp⟩
  | n + 1, f, hf => by
    obtain ⟨ih1, ih2⟩ := pi_hasSum n (fun i => f i.succ) (fun i => hf _)
    have hs0 : Summable fun m => f 0 m := (hf 0).of_norm
    have hsum : Summable fun p : ℤ × (Fin n → ℤ) => ‖f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)‖ := by
      refine (Summable.mul_norm (hf 0) ih1).congr fun p => ?_
      simp
    have hmul := hs0.hasSum.mul ih2 hsum.of_norm
    have e := (Fin.consEquiv (fun _ : Fin (n+1) => ℤ))
    constructor
    · rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).summable_iff]
      refine hsum.congr fun p => ?_
      simp [Fin.consEquiv, Fin.prod_univ_succ]
    · rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).hasSum_iff, Fin.prod_univ_succ]
      convert hmul using 2 with p
      simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem sq_sub_ge (y : ℝ) (hy : |y| ≤ 1/2) (n : ℤ) : (n:ℝ)^2 / 4 ≤ ((n:ℝ) - y)^2 := by
  rcases eq_or_ne n 0 with h | h
  · simp [h, sq_nonneg]
  · have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
      have := Int.one_le_abs h
      exact_mod_cast this
    have h2 : |(n:ℝ)| - |y| ≤ |(n:ℝ) - y| := by
      have := abs_sub_abs_le_abs_sub (n:ℝ) y
      exact this
    have h3 : |(n:ℝ)| / 2 ≤ |(n:ℝ) - y| := by linarith
    have h4 : ((n:ℝ))^2 / 4 = (|(n:ℝ)| / 2)^2 := by rw [div_pow, sq_abs]; norm_num
    rw [h4, ← sq_abs ((n:ℝ) - y)]
    exact pow_le_pow_left₀ (by positivity) h3 2

theorem theta_bound (u y δ : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (hy : |y| ≤ 1/2)
    (hδ : ∀ n : ℤ, δ^2 ≤ ((n:ℝ) - y)^2) :
    ‖∑' n : ℤ, Complex.exp (2 * π * I * n * y - u * (n:ℂ)^2)‖ ≤
      Real.sqrt (π / u) * (∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2)) *
        Real.exp (-(π^2 * δ^2 / (2 * u))) := by
  rw [theta_eq u y hu, Complex.norm_real, Real.norm_eq_abs]
  have hB : Summable fun n : ℤ => Real.exp (-(π^2 / 8) * (n:ℝ)^2) :=
    summable_exp_sq _ (by positivity)
  have hterm : ∀ n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u)) ≤
      Real.exp (-(π^2 * δ^2 / (2 * u))) * Real.exp (-(π^2 / 8) * (n:ℝ)^2) := by
    intro n
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := sq_sub_ge y hy n
    have h2 := hδ n
    have hπ : 0 < π^2 := by positivity
    have : π^2 * δ^2 / (2*u) + π^2/8 * (n:ℝ)^2 ≤ π^2 * ((n:ℝ) - y)^2 / u := by
      have e1 : π^2 * δ^2 / (2*u) ≤ π^2 * ((n:ℝ) - y)^2 / (2*u) := by gcongr
      have e2 : π^2 * ((n:ℝ)^2/4) / (2*u) ≤ π^2 * ((n:ℝ) - y)^2 / (2*u) := by gcongr
      have e3 : π^2 / 8 * (n:ℝ)^2 ≤ π^2 * ((n:ℝ)^2/4) / (2*u) := by
        rw [le_div_iff₀ (by positivity)]
        have : 0 ≤ π^2 * (n:ℝ)^2 := by positivity
        nlinarith
      have e4 : π^2 * ((n:ℝ) - y)^2 / u = π^2 * ((n:ℝ) - y)^2 / (2*u) + π^2 * ((n:ℝ) - y)^2 / (2*u) := by
        field_simp; ring
      linarith
    linarith
  have hsum : Summable fun n : ℤ => Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u)) :=
    (hB.mul_left (Real.exp (-(π^2 * δ^2 / (2 * u))))).of_nonneg_of_le
      (fun _ => (Real.exp_pos _).le) hterm
  have hT : ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u)) ≤
      Real.exp (-(π^2 * δ^2 / (2 * u))) * ∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2) := by
    rw [← tsum_mul_left]
    exact hsum.tsum_le_tsum hterm (hB.mul_left _)
  have h0 : 0 ≤ ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u)) := tsum_nonneg fun _ => (Real.exp_pos _).le
  rw [abs_of_nonneg (by positivity)]
  calc Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u))
      ≤ Real.sqrt (π / u) * (Real.exp (-(π^2 * δ^2 / (2 * u))) * ∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2)) := by
        gcongr
    _ = _ := by ring
theorem exists_rep (z : UnitAddCircle) : ∃ y : ℝ, |y| ≤ 1/2 ∧ z = ((y:ℝ) : UnitAddCircle) := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  refine ⟨w - round w, abs_sub_round w, ?_⟩
  rw [AddCircle.coe_sub]
  have : ((round w : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨round w, by simp⟩
  rw [this, sub_zero]

theorem pow_exp_bound (c : ℝ) (hc : 0 < c) (d : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    v^d * Real.exp (-(c*v)) ≤ (d.factorial : ℝ) / c^d := by
  have h := Real.pow_div_factorial_le_exp (c*v) (by positivity) d
  have hf : (0:ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  rw [div_le_iff₀ hf] at h
  rw [le_div_iff₀ (by positivity), Real.exp_neg]
  have : v^d * c^d = (c*v)^d := by ring
  rw [mul_assoc, mul_comm (Real.exp (c*v))⁻¹, ← mul_assoc, this, mul_inv_le_iff₀ (Real.exp_pos _)]
  linarith [mul_comm (Real.exp (c*v)) (d.factorial : ℝ)]

theorem mode_eq_prod {d : ℕ} (k : Lattice d) (y : Fin d → ℝ) :
    Torus.mode k (fun i => ((y i : ℝ) : UnitAddCircle)) =
      ∏ i, Complex.exp (2 * π * I * (k i : ℤ) * (y i : ℝ)) := by
  simp only [Torus.mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  simp

theorem theta_dim_bound {d : ℕ} (x : Torus d) (hx : x ≠ 0) :
    ∃ M : ℝ, ∀ u : ℝ, 0 < u → u ≤ 1 →
      |∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x| ≤ M := by
  choose y hy1 hy2 using fun i => exists_rep (x i)
  have hxy : x = fun i => ((y i : ℝ) : UnitAddCircle) := funext hy2
  obtain ⟨i0, hi0⟩ : ∃ i0, y i0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    rw [hxy]
    funext i
    simp [h i]
  set B := ∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2) with hBdef
  have hB0 : 0 ≤ B := tsum_nonneg fun _ => (Real.exp_pos _).le
  set c := π^2 * |y i0|^2 / 2 with hc
  have hcpos : 0 < c := by
    have : 0 < |y i0| := abs_pos.mpr hi0
    positivity
  refine ⟨(π * B)^d * ((d.factorial : ℝ) / c^d), fun u hu hu1 => ?_⟩
  -- the complex terms
  set S : Fin d → ℂ := fun i => ∑' n : ℤ, Complex.exp (2 * π * I * n * (y i) - u * (n:ℂ)^2) with hS
  set f : Fin d → ℤ → ℂ := fun i n => Complex.exp (2 * π * I * n * (y i) - u * (n:ℂ)^2) with hf
  have hfn : ∀ i, Summable fun m => ‖f i m‖ := by
    intro i
    refine (summable_exp_sq u hu).congr fun m => ?_
    simp only [hf]
    rw [Complex.norm_exp]
    congr 1
    rw [show ((m:ℂ)) = ((m:ℝ):ℂ) by simp]
    simp [pow_two, Complex.mul_re]
  obtain ⟨hsum, hhas⟩ := pi_hasSum d f hfn
  have hterm : ∀ k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x =
      (∏ i, f i (k i)).re := by
    intro k
    have h1 : ∏ i, f i (k i) = ((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) * Torus.mode k x := by
      rw [hxy, mode_eq_prod]
      have h2 : ∏ i, f i (k i) = (∏ i, Complex.exp (-((u:ℂ) * ((k i : ℤ):ℂ)^2))) *
          ∏ i, Complex.exp (2 * π * I * (k i : ℤ) * (y i : ℝ)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [hf]
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [h2, ← Complex.exp_sum, Complex.ofReal_exp, enorm_sq]
      congr 2
      push_cast
      rw [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [h1, Complex.re_ofReal_mul]
    rfl
  have hδ : ∀ i (n : ℤ), |y i|^2 ≤ ((n:ℝ) - y i)^2 := by
    intro i n
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
        have := Int.one_le_abs h
        exact_mod_cast this
      have h2 : |(n:ℝ)| - |y i| ≤ |(n:ℝ) - y i| := abs_sub_abs_le_abs_sub (n:ℝ) (y i)
      have h3 := hy1 i
      have h4 : |y i| ≤ |(n:ℝ) - y i| := by linarith
      rw [← sq_abs ((n:ℝ) - y i)]
      exact pow_le_pow_left₀ (abs_nonneg _) h4 2
  have hre : ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x =
      (∏ i, S i).re := by
    simp_rw [hterm]
    rw [← Complex.re_tsum hsum.of_norm, hhas.tsum_eq]
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_prod]
  have hbd : ∀ i, ‖S i‖ ≤ Real.sqrt (π / u) * B * Real.exp (-(π^2 * |y i|^2 / (2 * u))) :=
    fun i => theta_bound u (y i) |y i| hu hu1 (hy1 i) (hδ i)
  refine (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hbd i)).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  have hsq : Real.sqrt (π / u) * B ≤ π * B * (1 / u) := by
    have h1 : 1 ≤ π / u := by
      rw [le_div_iff₀ hu]; linarith [Real.pi_gt_three]
    have h2 : Real.sqrt (π / u) ≤ π / u := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    calc Real.sqrt (π / u) * B ≤ (π / u) * B := by gcongr
      _ = _ := by ring
  have hexp : Real.exp (-∑ i, π^2 * |y i|^2 / (2 * u)) ≤ Real.exp (-(c * (1 / u))) := by
    apply Real.exp_le_exp.mpr
    have : π^2 * |y i0|^2 / (2 * u) ≤ ∑ i, π^2 * |y i|^2 / (2 * u) :=
      Finset.single_le_sum (f := fun i => π^2 * |y i|^2 / (2 * u)) (fun i _ => by positivity)
        (Finset.mem_univ i0)
    have e : c * (1 / u) = π^2 * |y i0|^2 / (2 * u) := by rw [hc]; field_simp
    rw [e]; linarith
  have hexp' : Real.exp (∑ i, -(π^2 * |y i|^2 / (2 * u))) ≤ Real.exp (-(c * (1 / u))) := by
    rw [Finset.sum_neg_distrib]; exact hexp
  have h0 : 0 ≤ Real.sqrt (π / u) * B := mul_nonneg (Real.sqrt_nonneg _) hB0
  calc (Real.sqrt (π / u) * B)^d * Real.exp (∑ i, -(π^2 * |y i|^2 / (2 * u)))
      ≤ (π * B * (1 / u))^d * Real.exp (-(c * (1 / u))) :=
        mul_le_mul (pow_le_pow_left₀ h0 hsq d) hexp' (Real.exp_pos _).le (by positivity)
    _ = (π * B)^d * ((1 / u)^d * Real.exp (-(c * (1 / u)))) := by rw [mul_pow]; ring
    _ ≤ (π * B)^d * ((d.factorial : ℝ) / c^d) := by
        gcongr
        exact pow_exp_bound c hcpos d (1 / u) (by positivity)

theorem single_k_integral {d : ℕ} {s : ℝ} (hsd : s < d) (ε : ℝ) (x : Torus d) (k : Lattice d)
    (hk : k ≠ 0) :
    ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) *
        (Real.exp (-((t + ε) * Lattice.enorm k ^ 2)) * Torus.cosMode k x) =
      Torus.cosMode k x * Real.exp (-ε * Lattice.enorm k ^ 2) *
        (Lattice.enorm k ^ (s - d) * Real.Gamma (((d:ℝ) - s) / 2)) := by
  have ha : 0 < ((d:ℝ) - s) / 2 := by linarith
  have hm : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (one_le_enorm k hk)
  have hr : 0 < Lattice.enorm k ^ 2 := by positivity
  have h1 := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  have h2 : ∀ t : ℝ, t ^ (((d:ℝ) - s) / 2 - 1) *
        (Real.exp (-((t + ε) * Lattice.enorm k ^ 2)) * Torus.cosMode k x) =
      (Torus.cosMode k x * Real.exp (-ε * Lattice.enorm k ^ 2)) *
        (t ^ (((d:ℝ) - s) / 2 - 1) * Real.exp (-(Lattice.enorm k ^ 2 * t))) := by
    intro t
    have : Real.exp (-((t + ε) * Lattice.enorm k ^ 2)) =
        Real.exp (-ε * Lattice.enorm k ^ 2) * Real.exp (-(Lattice.enorm k ^ 2 * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  simp_rw [h2]
  rw [integral_const_mul, h1]
  congr 2
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hm.le]
  rw [← Real.rpow_neg hm.le]
  congr 1
  push_cast; ring

/-- `Ψ(u) = ∑_{k≠0} e^{-u|k|²} cos(2πk·x)`. -/
def psiFn {d : ℕ} (x : Torus d) (u : ℝ) : ℝ :=
  ∑' k : Lattice d, if k = 0 then 0 else Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x

theorem psi_summable {d : ℕ} (x : Torus d) {u : ℝ} (hu : 0 < u) :
    Summable fun k : Lattice d => if k = 0 then 0 else Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x := by
  refine Summable.of_norm_bounded (summable_gauss_lattice d u hu) fun k => ?_
  by_cases hk : k = 0
  · simp [hk, (Real.exp_pos _).le]
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ Real.exp (-u * Lattice.enorm k ^ 2) * 1 := by gcongr; exact abs_cosMode_le k x
      _ = _ := mul_one _

/-- the integrand for fixed `k` -/
def gInt {d : ℕ} (a ε : ℝ) (x : Torus d) (k : Lattice d) (t : ℝ) : ℝ :=
  t ^ (a - 1) * (if k = 0 then 0 else Real.exp (-(t + ε) * Lattice.enorm k ^ 2) * Torus.cosMode k x)

theorem gInt_bound {d : ℕ} (a ε : ℝ) (x : Torus d) (k : Lattice d) (hk : k ≠ 0) (t : ℝ) (ht : 0 < t) :
    ‖gInt a ε x k t‖ ≤ Real.exp (-ε * Lattice.enorm k ^ 2) *
      (t ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * t))) := by
  unfold gInt
  simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.rpow_pos_of_pos ht _)]
  have : Real.exp (-(t + ε) * Lattice.enorm k ^ 2) =
        Real.exp (-ε * Lattice.enorm k ^ 2) * Real.exp (-(Lattice.enorm k ^ 2 * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  have hc := abs_cosMode_le k x
  have hp : 0 ≤ t ^ (a - 1) := (Real.rpow_pos_of_pos ht _).le
  calc t ^ (a - 1) * (Real.exp (-ε * Lattice.enorm k ^ 2) * Real.exp (-(Lattice.enorm k ^ 2 * t)) * |Torus.cosMode k x|)
      ≤ t ^ (a - 1) * (Real.exp (-ε * Lattice.enorm k ^ 2) * Real.exp (-(Lattice.enorm k ^ 2 * t)) * 1) := by gcongr
    _ = _ := by ring

theorem integrable_majorant {d : ℕ} {a : ℝ} (ha : 0 < a) (k : Lattice d) (hk : k ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * t))) (Ioi 0) := by
  have hm : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (one_le_enorm k hk)
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := Lattice.enorm k ^ 2)
    (by linarith) one_pos (by positivity)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring_nf

theorem gInt_integrable {d : ℕ} {a : ℝ} (ha : 0 < a) (ε : ℝ) (x : Torus d) (k : Lattice d) :
    IntegrableOn (gInt a ε x k) (Ioi 0) := by
  by_cases hk : k = 0
  · have : gInt a ε x k = 0 := by funext t; simp [gInt, hk]
    rw [this]; exact integrableOn_zero
  · refine Integrable.mono' ((integrable_majorant ha k hk).const_mul (Real.exp (-ε * Lattice.enorm k ^ 2)))
      ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      unfold gInt
      simp only [hk, ite_false]
      fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      exact gInt_bound a ε x k hk t ht

theorem gInt_norm_summable {d : ℕ} {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) (x : Torus d) :
    Summable fun k : Lattice d => ∫ t in Ioi (0:ℝ), ‖gInt a ε x k t‖ := by
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
    (fun k => ?_) ((summable_gauss_lattice d ε hε).mul_left (Real.Gamma a))
  by_cases hk : k = 0
  · have : ∀ t, ‖gInt a ε x k t‖ = 0 := fun t => by simp [gInt, hk]
    simp only [this, integral_zero]
    exact mul_nonneg (Real.Gamma_pos_of_pos ha).le (Real.exp_pos _).le
  · have hm : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (one_le_enorm k hk)
    have hr : 0 < Lattice.enorm k ^ 2 := by positivity
    have hint := (integrable_majorant ha k hk).const_mul (Real.exp (-ε * Lattice.enorm k ^ 2))
    calc ∫ t in Ioi (0:ℝ), ‖gInt a ε x k t‖
        ≤ ∫ t in Ioi (0:ℝ), Real.exp (-ε * Lattice.enorm k ^ 2) *
            (t ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * t))) := by
          refine setIntegral_mono_on (gInt_integrable ha ε x k).norm hint measurableSet_Ioi ?_
          intro t ht
          exact gInt_bound a ε x k hk t ht
      _ = Real.exp (-ε * Lattice.enorm k ^ 2) * ((1 / Lattice.enorm k ^ 2) ^ a * Real.Gamma a) := by
          rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
      _ ≤ Real.exp (-ε * Lattice.enorm k ^ 2) * (1 * Real.Gamma a) := by
          have h1 : (1 / Lattice.enorm k ^ 2) ^ a ≤ 1 := by
            apply Real.rpow_le_one (by positivity) _ ha.le
            have := one_le_enorm k hk
            rw [div_le_one hr]; nlinarith
          have := (Real.Gamma_pos_of_pos ha).le
          gcongr
      _ = _ := by ring

theorem heatRiesz_eq_integral {d : ℕ} {s : ℝ} (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (x : Torus d) :
    heatRiesz d s ε x = rieszConst d s * (2 * π) ^ (s - d) / Real.Gamma (((d:ℝ) - s) / 2) *
      ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn x (t + ε) := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  set A := rieszConst d s * (2 * π) ^ (s - d) / Real.Gamma a with hA
  have hterm : ∀ k : Lattice d, rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) * Torus.cosMode k x =
      A * ∫ t in Ioi (0:ℝ), gInt a ε x k t := by
    intro k
    by_cases hk : k = 0
    · have : gInt a ε x k = fun _ => 0 := by funext t; simp [gInt, hk]
      rw [this]; simp [rieszCoeff, hk]
    · have h := single_k_integral (x := x) hsd ε k hk
      have : (fun t => gInt a ε x k t) = fun t => t ^ (a - 1) *
          (Real.exp (-((t + ε) * Lattice.enorm k ^ 2)) * Torus.cosMode k x) := by
        funext t; simp only [gInt, hk, ite_false, neg_mul]
      rw [this, h]
      have hm : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (one_le_enorm k hk)
      have : rieszCoeff d s k = rieszConst d s * ((2 * π) ^ (s - d) * Lattice.enorm k ^ (s - d)) := by
        unfold rieszCoeff
        simp only [hk, ite_false]
        rw [Real.mul_rpow (by positivity) hm.le]
      rw [this, hA]
      field_simp
      rfl
  have hsw : ∑' k : Lattice d, ∫ t in Ioi (0:ℝ), gInt a ε x k t =
      ∫ t in Ioi (0:ℝ), ∑' k : Lattice d, gInt a ε x k t :=
    integral_tsum_of_summable_integral_norm (gInt_integrable ha ε x) (gInt_norm_summable ha hε x)
  have hpt : ∀ t : ℝ, 0 < t → ∑' k : Lattice d, gInt a ε x k t = t ^ (a - 1) * psiFn x (t + ε) := by
    intro t ht
    unfold gInt psiFn
    rw [tsum_mul_left]
  unfold heatRiesz
  simp_rw [hterm]
  rw [tsum_mul_left, hsw]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t ht

theorem psi_continuousOn {d : ℕ} (x : Torus d) : ContinuousOn (psiFn x) (Ioi 0) := by
  have key : ∀ u0 : ℝ, 0 < u0 → ContinuousOn (psiFn x) (Ici u0) := by
    intro u0 hu0
    unfold psiFn
    refine continuousOn_tsum (u := fun k : Lattice d => Real.exp (-u0 * Lattice.enorm k ^ 2))
      (fun k => ?_) (summable_gauss_lattice d u0 hu0) ?_
    · by_cases hk : k = 0
      · simp only [hk, ite_true]; exact continuousOn_const
      · simp only [hk, ite_false]
        exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-u * Lattice.enorm k ^ 2) *
          Torus.cosMode k x).continuousOn
    · intro k u hu
      by_cases hk : k = 0
      · simp [hk, (Real.exp_pos _).le]
      · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hu' : u0 ≤ u := hu
        calc _ ≤ Real.exp (-u * Lattice.enorm k ^ 2) * 1 := by gcongr; exact abs_cosMode_le k x
          _ ≤ _ := by
            rw [mul_one]
            apply Real.exp_le_exp.mpr
            have : 0 ≤ Lattice.enorm k ^ 2 := by positivity
            nlinarith
  intro u hu
  have hu' : (0:ℝ) < u := hu
  have := (key (u/2) (by positivity)).continuousAt (Ici_mem_nhds (show u / 2 < u by linarith))
  exact this.continuousWithinAt

theorem cosMode_zero {d : ℕ} (x : Torus d) : Torus.cosMode 0 x = 1 := by
  simp [Torus.cosMode, Torus.mode, UnitAddTorus.mFourier]

theorem psi_eq {d : ℕ} (x : Torus d) {u : ℝ} (hu : 0 < u) :
    ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x = 1 + psiFn x u := by
  have hs : Summable fun k : Lattice d => Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x := by
    refine Summable.of_norm_bounded (summable_gauss_lattice d u hu) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ Real.exp (-u * Lattice.enorm k ^ 2) * 1 := by gcongr; exact abs_cosMode_le k x
      _ = _ := mul_one _
  rw [hs.tsum_eq_add_tsum_ite 0]
  have h0 : Lattice.enorm (0 : Lattice d) = 0 := by
    simp [Lattice.enorm, Lattice.toEuc]
    rfl
  simp [h0, cosMode_zero, psiFn]

theorem psi_bound {d : ℕ} (x : Torus d) (hx : x ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, 0 < u → |psiFn x u| ≤ M * Real.exp (-u) := by
  obtain ⟨M0, hM0⟩ := theta_dim_bound x hx
  set G := ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) with hG
  have hG0 : 0 ≤ G := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hM0' : 0 ≤ M0 := by
    have := hM0 1 one_pos le_rfl
    exact (abs_nonneg _).trans this
  refine ⟨Real.exp 1 * G + (M0 + 1) * Real.exp 1, by positivity, fun u hu => ?_⟩
  rcases le_total 1 u with h1 | h1
  · -- large u
    have hb : ∀ k : Lattice d, ‖if k = 0 then 0 else Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x‖
        ≤ Real.exp (-u) * Real.exp 1 * Real.exp (-1 * Lattice.enorm k ^ 2) := by
      intro k
      by_cases hk : k = 0
      · simp only [hk, ite_true, norm_zero]; positivity
      · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hm := one_le_enorm k hk
        calc Real.exp (-u * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
            ≤ Real.exp (-u * Lattice.enorm k ^ 2) * 1 := by gcongr; exact abs_cosMode_le k x
          _ = Real.exp (-u * Lattice.enorm k ^ 2) := mul_one _
          _ ≤ Real.exp (-u + 1 + -1 * Lattice.enorm k ^ 2) := by
              apply Real.exp_le_exp.mpr
              nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (show (1:ℝ) ≤ Lattice.enorm k ^ 2 by nlinarith))]
          _ = _ := by rw [Real.exp_add, Real.exp_add]
    have hsum := ((summable_gauss_lattice d 1 one_pos).mul_left
      (Real.exp (-u) * Real.exp 1)).hasSum
    have h2 := tsum_of_norm_bounded hsum hb
    rw [tsum_mul_left, ← hG] at h2
    have h3 : |psiFn x u| ≤ Real.exp (-u) * Real.exp 1 * G := by
      rw [← Real.norm_eq_abs]; exact h2
    refine h3.trans ?_
    have : 0 ≤ (M0 + 1) * Real.exp 1 * Real.exp (-u) := by positivity
    nlinarith [Real.exp_pos (-u), Real.exp_pos 1]
  · -- small u
    have h2 := hM0 u hu h1
    rw [psi_eq x hu] at h2
    have h3 : |psiFn x u| ≤ M0 + 1 := by
      have := abs_sub_abs_le_abs_sub (1 + psiFn x u) 1
      have h4 : |psiFn x u| = |1 + psiFn x u - 1| := by ring_nf
      rw [h4]
      calc |1 + psiFn x u - 1| ≤ |1 + psiFn x u| + |(1:ℝ)| := abs_sub _ _
        _ ≤ M0 + 1 := by rw [abs_one]; linarith
    have h5 : 1 ≤ Real.exp 1 * Real.exp (-u) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; linarith
    have h6 : M0 + 1 ≤ (M0 + 1) * Real.exp 1 * Real.exp (-u) := by
      rw [mul_assoc]; nlinarith
    have : 0 ≤ Real.exp 1 * G * Real.exp (-u) := by positivity
    nlinarith


theorem heat_limit_exists {d : ℕ} {s : ℝ} (hsd : s < d) (x : Torus d) (hx : x ≠ 0) :
    ∃ L : ℝ, Tendsto (fun ε => heatRiesz d s ε x) (𝓝[>] 0) (𝓝 L) := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  obtain ⟨M, hM0, hM⟩ := psi_bound x hx
  have hcont := psi_continuousOn x
  have hmeas : ∀ ε : ℝ, 0 ≤ ε → AEStronglyMeasurable (fun t : ℝ => t ^ (a - 1) * psiFn x (t + ε))
      (volume.restrict (Ioi 0)) := by
    intro ε hε
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) ?_
    refine hcont.comp (continuousOn_id.add continuousOn_const) fun t ht => ?_
    simp only [mem_Ioi] at ht ⊢
    linarith
  have hlim : Tendsto (fun ε => ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x (t + ε)) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => M * (Real.exp (-t) * t ^ (a - 1))) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε using hmeas ε (le_of_lt hε)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have hε' : 0 < ε := hε
      have ht' : 0 < t := ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
      have h1 := hM (t + ε) (by linarith)
      have h2 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
      have h3 := Real.rpow_pos_of_pos ht' (a - 1)
      calc t ^ (a - 1) * |psiFn x (t + ε)| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = _ := by ring
    · exact (Real.GammaIntegral_convergent ha).const_mul M
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have ht' : 0 < t := ht
      refine Tendsto.const_mul _ ?_
      have h1 : Tendsto (fun ε : ℝ => t + ε) (𝓝[>] 0) (𝓝 t) := by
        have : Tendsto (fun ε : ℝ => t + ε) (𝓝 0) (𝓝 (t + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 : ContinuousAt (psiFn x) t :=
        (hcont t ht').continuousAt (Ioi_mem_nhds ht')
      exact h2.tendsto.comp h1
  refine ⟨rieszConst d s * (2 * π) ^ (s - d) / Real.Gamma a *
    ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x t, ?_⟩
  refine (hlim.const_mul _).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (heatRiesz_eq_integral hsd hε x).symm

end KernelLimit

section KernelFacts

variable {d : ℕ} {s : ℝ}

/-- `ĝ(k) > 0` for `k ≠ 0`, `0 ≤ s < d`, `d ≥ 2` (source line 427). -/
theorem rieszCoeff_pos (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) (hk : k ≠ 0) :
    0 < rieszCoeff d s k := by
  have h1 := one_le_enorm k hk
  have h2 := rieszConst_pos hd hs0 hsd
  unfold rieszCoeff
  simp only [hk, ite_false]
  exact mul_pos h2 (Real.rpow_pos_of_pos (by positivity) _)

/-- `ĝ` is even. -/
theorem rieszCoeff_neg (k : Lattice d) : rieszCoeff d s (-k) = rieszCoeff d s k := by
  unfold rieszCoeff
  simp [enorm_neg]

/-- The heat-regularised series converges absolutely for `ε > 0`. -/
theorem summable_heatRiesz (hsd : s < d) (ε : ℝ) (hε : 0 < ε) (x : Torus d) :
    Summable fun k : Lattice d =>
      rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) * Torus.cosMode k x := by
  refine Summable.of_norm_bounded ((summable_gauss_lattice d ε hε).mul_left |rieszConst d s|) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hc := abs_cosMode_le k x
  have hexp := (Real.exp_pos (-ε * Lattice.enorm k ^ 2)).le
  have hcoef : |rieszCoeff d s k| ≤ |rieszConst d s| := by
    unfold rieszCoeff
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ite_false]; rw [abs_mul]
      have h1 := one_le_enorm k hk
      have hb : (2 * Real.pi * Lattice.enorm k) ^ (s - (d:ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three]) (by linarith)
      have hp : 0 ≤ (2 * Real.pi * Lattice.enorm k) ^ (s - (d:ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      rw [abs_of_nonneg hp]
      nlinarith [abs_nonneg (rieszConst d s)]
  calc |rieszCoeff d s k| * Real.exp (-ε * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
      ≤ |rieszConst d s| * Real.exp (-ε * Lattice.enorm k ^ 2) * 1 := by
        gcongr
    _ = _ := by ring

/-- The limit defining `g(x)` exists for every `x ≠ 0` (KERN-01). -/
theorem periodicRiesz_tendsto (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (x : Torus d) (hx : x ≠ 0) :
    Tendsto (fun ε => heatRiesz d s ε x) (𝓝[>] 0) (𝓝 (periodicRiesz d s x)) := by
  obtain ⟨L, hL⟩ := heat_limit_exists hsd x hx
  have : periodicRiesz d s x = L := hL.limUnder_eq
  rw [this]; exact hL

/-- `g` is even and has Haar mean zero (KERN-01). -/
theorem periodicRiesz_neg (x : Torus d) : periodicRiesz d s (-x) = periodicRiesz d s x := by
  have : (fun ε => heatRiesz d s ε (-x)) = fun ε => heatRiesz d s ε x := by
    funext ε
    simp only [heatRiesz, cosMode_neg]
  unfold periodicRiesz
  rw [this]

end KernelFacts

section KernelBox

open Complex Set
open scoped Real

namespace KernelAux

/-- The torus point with coordinates `y`. -/
abbrev boxPt {d : ℕ} (y : Fin d → ℝ) : Torus d := fun i => ((y i : ℝ) : UnitAddCircle)

theorem theta_prod {d : ℕ} (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k (boxPt y) =
      ∏ i, (Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u))) := by
  set S : Fin d → ℂ := fun i => ∑' n : ℤ, Complex.exp (2 * π * I * n * (y i) - u * (n:ℂ)^2) with hS
  set f : Fin d → ℤ → ℂ := fun i n => Complex.exp (2 * π * I * n * (y i) - u * (n:ℂ)^2) with hf
  have hfn : ∀ i, Summable fun m => ‖f i m‖ := by
    intro i
    refine (summable_exp_sq u hu).congr fun m => ?_
    simp only [hf]
    rw [Complex.norm_exp]
    congr 1
    rw [show ((m:ℂ)) = ((m:ℝ):ℂ) by simp]
    simp [pow_two, Complex.mul_re]
  obtain ⟨hsum, hhas⟩ := pi_hasSum d f hfn
  have hterm : ∀ k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k (boxPt y) =
      (∏ i, f i (k i)).re := by
    intro k
    have h1 : ∏ i, f i (k i) = ((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) * Torus.mode k (boxPt y) := by
      rw [mode_eq_prod]
      have h2 : ∏ i, f i (k i) = (∏ i, Complex.exp (-((u:ℂ) * ((k i : ℤ):ℂ)^2))) *
          ∏ i, Complex.exp (2 * π * I * (k i : ℤ) * (y i : ℝ)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [hf]
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [h2, ← Complex.exp_sum, Complex.ofReal_exp, enorm_sq]
      congr 2
      push_cast
      rw [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [h1, Complex.re_ofReal_mul]
    rfl
  have hre : ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k (boxPt y) =
      (∏ i, S i).re := by
    simp_rw [hterm]
    rw [← Complex.re_tsum hsum.of_norm, hhas.tsum_eq]
  rw [hre]
  have hSi : ∀ i, S i = ((Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u)) : ℝ) : ℂ) :=
    fun i => theta_eq u (y i) hu
  simp_rw [hSi]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]


theorem abs_sq_le_sub_sq (y : ℝ) (hy : |y| ≤ 1/2) (n : ℤ) : |y|^2 ≤ ((n:ℝ) - y)^2 := by
  rcases eq_or_ne n 0 with h | h
  · simp [h]
  · have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
      have := Int.one_le_abs h
      exact_mod_cast this
    have h2 : |(n:ℝ)| - |y| ≤ |(n:ℝ) - y| := abs_sub_abs_le_abs_sub (n:ℝ) y
    have h4 : |y| ≤ |(n:ℝ) - y| := by linarith
    rw [← sq_abs ((n:ℝ) - y)]
    exact pow_le_pow_left₀ (abs_nonneg _) h4 2

/-- the 1-d theta factor, real form -/
theorem theta_factor_bound (y : ℝ) (hy : |y| ≤ 1/2) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    0 ≤ Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u)) ∧
    Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u)) ≤
      Real.sqrt (π / u) * (∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2)) *
        Real.exp (-(π^2 * y^2 / (2 * u))) := by
  have h0 : 0 ≤ Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u)) :=
    mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg fun _ => (Real.exp_pos _).le)
  refine ⟨h0, ?_⟩
  have h := theta_bound u y |y| hu hu1 hy (fun n => abs_sq_le_sub_sq y hy n)
  rw [theta_eq u y hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, sq_abs] at h
  exact h


/-- Gaussian majorant of the periodised theta function on the box, `u ≤ 1`. -/
theorem theta_gauss_bound {d : ℕ} (y : Fin d → ℝ) (hy : ∀ i, |y i| ≤ 1/2) {u : ℝ} (hu : 0 < u)
    (hu1 : u ≤ 1) (j : Fin d) :
    0 ≤ ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k (boxPt y) ∧
    ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k (boxPt y) ≤
      (Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2))^d *
        Real.exp (-(π^2 * (y j)^2 / (2 * u))) := by
  rw [theta_prod y hu]
  refine ⟨Finset.prod_nonneg fun i _ => (theta_factor_bound (y i) (hy i) hu hu1).1, ?_⟩
  refine (Finset.prod_le_prod₀ (fun i _ => (theta_factor_bound (y i) (hy i) hu hu1).1)
    (fun i _ => (theta_factor_bound (y i) (hy i) hu hu1).2)).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  have hB : 0 ≤ (Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2)) :=
    mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg fun _ => (Real.exp_pos _).le)
  gcongr
  rw [Finset.sum_neg_distrib, neg_le_neg_iff]
  exact Finset.single_le_sum (f := fun i => π^2 * (y i)^2 / (2 * u)) (fun i _ => by positivity)
    (Finset.mem_univ j)


theorem rpow_mul_exp_le {q : ℝ} (hq : 0 < q) {v : ℝ} (hv : 0 < v) :
    v ^ q * Real.exp (-v) ≤ q ^ q * Real.exp (-q) := by
  have h1 : Real.log (v / q) ≤ v / q - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hv.ne' hq.ne'] at h1
  have h2 : q * Real.log v - v ≤ q * Real.log q - q := by
    have := mul_le_mul_of_nonneg_left h1 hq.le
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ hq.ne'] at this
    linarith
  rw [Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hq, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [mul_comm (Real.log v) q, mul_comm (Real.log q) q]

theorem exp_neg_le_rpow {q : ℝ} (hq : 0 < q) {v : ℝ} (hv : 0 < v) :
    Real.exp (-v) ≤ (q ^ q * Real.exp (-q)) * v ^ (-q) := by
  have h := rpow_mul_exp_le hq hv
  rw [Real.rpow_neg hv.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hv q)]
  linarith [mul_comm (Real.exp (-v)) (v ^ q)]

/-- uniform decay of `Ψ` for `u ≥ 1`. -/
theorem psi_large {d : ℕ} (x : Torus d) {u : ℝ} (hu : 1 ≤ u) :
    |psiFn x u| ≤ (Real.exp 1 * ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)) * Real.exp (-u) := by
  set G := ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) with hG
  have hb : ∀ k : Lattice d, ‖if k = 0 then 0 else Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x‖
      ≤ Real.exp (-u) * Real.exp 1 * Real.exp (-1 * Lattice.enorm k ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp only [hk, ite_true, norm_zero]; positivity
    · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hm := one_le_enorm k hk
      calc Real.exp (-u * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
          ≤ Real.exp (-u * Lattice.enorm k ^ 2) * 1 := by gcongr; exact abs_cosMode_le k x
        _ = Real.exp (-u * Lattice.enorm k ^ 2) := mul_one _
        _ ≤ Real.exp (-u + 1 + -1 * Lattice.enorm k ^ 2) := by
            apply Real.exp_le_exp.mpr
            nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr (show (1:ℝ) ≤ Lattice.enorm k ^ 2 by nlinarith))]
        _ = _ := by rw [Real.exp_add, Real.exp_add]
  have hsum := ((summable_gauss_lattice d 1 one_pos).mul_left
    (Real.exp (-u) * Real.exp 1)).hasSum
  have h2 := tsum_of_norm_bounded hsum hb
  rw [tsum_mul_left, ← hG] at h2
  have h3 : |psiFn x u| ≤ Real.exp (-u) * Real.exp 1 * G := by
    rw [← Real.norm_eq_abs]; exact h2
  calc |psiFn x u| ≤ Real.exp (-u) * Real.exp 1 * G := h3
    _ = _ := by ring


theorem sqrt_div_pow_eq (d : ℕ) {u : ℝ} (hu : 0 < u) :
    Real.sqrt (π / u) ^ d = Real.sqrt π ^ d * u ^ (-(d:ℝ)/2) := by
  have h1 : Real.sqrt u ^ d = u ^ ((d:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]; congr 1; ring
  rw [Real.sqrt_div Real.pi_pos.le, div_pow, h1, div_eq_mul_inv, neg_div, Real.rpow_neg hu.le]

theorem psi_small_bound {d : ℕ} (y : Fin d → ℝ) (hy : ∀ i, |y i| ≤ 1/2) (j : Fin d) (hj : y j ≠ 0)
    {q : ℝ} (hq : 0 < q) (hqd : q < (d:ℝ)/2) {t ε : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hε : 0 < ε) :
    |psiFn (boxPt y) (t + ε)| ≤
      ((Real.sqrt π * ∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2))^d * (q^q * Real.exp (-q)) *
          (π^2 * (y j)^2 / 2)^(-q) + 1 +
        (Real.exp 1 * ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2))) * t ^ (q - (d:ℝ)/2) := by
  set B := ∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2) with hB
  set G := ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) with hG
  have hB0 : 0 ≤ B := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hG0 : 0 ≤ G := tsum_nonneg fun _ => (Real.exp_pos _).le
  set r := q - (d:ℝ)/2 with hr
  have hr0 : r < 0 := by rw [hr]; linarith
  have ht1' : 1 ≤ t ^ r := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 hr0.le
  have hu : 0 < t + ε := by linarith
  have hM1 : 0 ≤ Real.exp 1 * G := by positivity
  have hb : 0 < π^2 * (y j)^2 / 2 := by
    have : 0 < (y j)^2 := by positivity
    positivity
  set Kc := (Real.sqrt π * B)^d * (q^q * Real.exp (-q)) * (π^2 * (y j)^2 / 2)^(-q) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have hfinal : ∀ z : ℝ, 0 ≤ z → z ≤ Kc * t ^ r + 1 ∨ z ≤ Real.exp 1 * G →
      z ≤ (Kc + 1 + Real.exp 1 * G) * t ^ r := by
    intro z hz h
    have h0 : 0 ≤ t ^ r := by linarith
    rcases h with h | h
    · nlinarith
    · nlinarith
  apply hfinal _ (abs_nonneg _)
  by_cases hu1 : t + ε ≤ 1
  · left
    obtain ⟨hΘ0, hΘ⟩ := theta_gauss_bound y hy hu hu1 j
    have hpsi := psi_eq (boxPt y) hu
    have h1 : |psiFn (boxPt y) (t + ε)| ≤ (∑' k : Lattice d, Real.exp (-(t + ε) * Lattice.enorm k ^ 2) * Torus.cosMode k (boxPt y)) + 1 := by
      rw [hpsi]
      have : psiFn (boxPt y) (t + ε) = (1 + psiFn (boxPt y) (t + ε)) - 1 := by ring
      calc |psiFn (boxPt y) (t + ε)| = |(1 + psiFn (boxPt y) (t + ε)) - 1| := by rw [← this]
        _ ≤ |1 + psiFn (boxPt y) (t + ε)| + |(1:ℝ)| := abs_sub _ _
        _ = _ := by
          rw [abs_one, abs_of_nonneg (by rw [← hpsi]; exact hΘ0)]
    have h2 : (Real.sqrt (π / (t + ε)) * B) ^ d * Real.exp (-(π ^ 2 * y j ^ 2 / (2 * (t + ε)))) ≤
        Kc * (t + ε) ^ r := by
      rw [mul_pow, sqrt_div_pow_eq d hu]
      have hv : (π ^ 2 * y j ^ 2 / (2 * (t + ε))) = (π^2 * (y j)^2 / 2) / (t + ε) := by
        field_simp
      have he := exp_neg_le_rpow hq (v := (π^2 * (y j)^2 / 2) / (t + ε)) (by positivity)
      have hbu : ((π^2 * (y j)^2 / 2) / (t + ε)) ^ (-q) = (π^2 * (y j)^2 / 2) ^ (-q) * (t + ε) ^ q := by
        rw [Real.div_rpow hb.le hu.le, Real.rpow_neg hu.le, div_inv_eq_mul]
      rw [hbu] at he
      rw [hv]
      calc (Real.sqrt π ^ d * (t + ε) ^ (-(d:ℝ)/2) * B ^ d) * Real.exp (-((π^2 * (y j)^2 / 2) / (t + ε)))
          ≤ (Real.sqrt π ^ d * (t + ε) ^ (-(d:ℝ)/2) * B ^ d) *
            ((q ^ q * Real.exp (-q)) * ((π^2 * (y j)^2 / 2) ^ (-q) * (t + ε) ^ q)) := by
            gcongr
        _ = Kc * ((t + ε) ^ (-(d:ℝ)/2) * (t + ε) ^ q) := by rw [hKc, mul_pow]; ring
        _ = Kc * (t + ε) ^ r := by
            rw [← Real.rpow_add hu]; congr 2; rw [hr]; ring
    have h3 : (t + ε) ^ r ≤ t ^ r := Real.rpow_le_rpow_of_nonpos ht (by linarith) hr0.le
    calc |psiFn (boxPt y) (t + ε)| ≤ _ := h1
      _ ≤ Kc * (t + ε) ^ r + 1 := by linarith
      _ ≤ Kc * t ^ r + 1 := by gcongr
  · right
    push Not at hu1
    have h := psi_large (boxPt y) hu1.le
    refine h.trans ?_
    have : Real.exp (-(t + ε)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith


theorem heat_eps_bound {d : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ (y : Fin d → ℝ), (∀ i, |y i| ≤ 1/2) → ∀ j, y j ≠ 0 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        |heatRiesz d s ε (boxPt y)| ≤ C1 * |y j| ^ (-((s + d)/2)) + C2 := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set q : ℝ := (s + d) / 4 with hq_def
  have hd0 : (0:ℝ) < d := by linarith
  have hq : 0 < q := by rw [hq_def]; linarith
  have hqd : q < (d:ℝ)/2 := by rw [hq_def]; linarith
  set r : ℝ := q - (d:ℝ)/2 with hr
  have hr_eq : a - 1 + r = a / 2 - 1 := by rw [hr, hq_def, ha_def]; ring
  set B := ∑' n : ℤ, Real.exp (-(π^2 / 8) * (n:ℝ)^2) with hB
  set G := ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) with hG
  have hB0 : 0 ≤ B := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hG0 : 0 ≤ G := tsum_nonneg fun _ => (Real.exp_pos _).le
  set M1 := Real.exp 1 * G with hM1
  have hM10 : 0 ≤ M1 := by positivity
  set A := rieszConst d s * (2 * π) ^ (s - d) / Real.Gamma a with hA
  set f1 : ℝ → ℝ := (Ioc (0:ℝ) 1).indicator (fun t => t ^ (a / 2 - 1)) with hf1
  set f2 : ℝ → ℝ := fun t => t ^ (a - 1) * Real.exp (-t) with hf2
  have hf1i : Integrable f1 := by
    have : IntegrableOn (fun t : ℝ => t ^ (a / 2 - 1)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := a / 2 - 1)
        (by linarith))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    exact this.integrable_indicator measurableSet_Ioc
  have hf2i : IntegrableOn f2 (Ioi 0) := by
    have := Real.GammaIntegral_convergent ha
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hf2]; ring
  set c1 := ∫ t in Ioi (0:ℝ), f1 t with hc1
  set c2 := ∫ t in Ioi (0:ℝ), f2 t with hc2
  have hf10 : ∀ t, 0 ≤ f1 t := by
    intro t
    simp only [hf1, indicator]
    split_ifs with h
    · exact (Real.rpow_pos_of_pos h.1 _).le
    · exact le_rfl
  have hf20 : ∀ t, 0 < t → 0 ≤ f2 t := fun t ht => by
    simp only [hf2]; exact mul_nonneg (Real.rpow_pos_of_pos ht _).le (Real.exp_pos _).le
  have hc10 : 0 ≤ c1 := setIntegral_nonneg measurableSet_Ioi fun t _ => hf10 t
  have hc20 : 0 ≤ c2 := setIntegral_nonneg measurableSet_Ioi fun t ht => hf20 t ht
  -- constants
  set κ := (Real.sqrt π * B)^d * (q^q * Real.exp (-q)) * (π^2 / 2) ^ (-q) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨|A| * c1 * κ, |A| * (c1 * (1 + M1) + M1 * c2), by positivity, by positivity, ?_⟩
  intro y hy j hj ε hε hε1
  rw [heatRiesz_eq_integral hsd hε (boxPt y)]
  set m := |y j| with hm
  have hm0 : 0 < m := abs_pos.mpr hj
  set Kc := (Real.sqrt π * B)^d * (q^q * Real.exp (-q)) * (π^2 * (y j)^2 / 2)^(-q) with hKc
  have hKc_eq : Kc = κ * m ^ (-((s + d)/2)) := by
    rw [hKc, hκ]
    have : (π^2 * (y j)^2 / 2) = (π^2 / 2) * (y j)^2 := by ring
    rw [this, Real.mul_rpow (by positivity) (by positivity)]
    have h2 : ((y j)^2) ^ (-q) = m ^ (-((s + d)/2)) := by
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      rw [hq_def]; push_cast; ring
    rw [h2]; ring
  have hKc0 : 0 ≤ Kc := by rw [hKc_eq]; positivity
  set K := Kc + 1 + M1 with hK
  have hK0 : 0 ≤ K := by positivity
  -- pointwise bound
  have hpt : ∀ t ∈ Ioi (0:ℝ), ‖t ^ (a - 1) * psiFn (boxPt y) (t + ε)‖ ≤ K * f1 t + M1 * f2 t := by
    intro t ht
    have ht' : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    by_cases ht1 : t ≤ 1
    · have h := psi_small_bound y hy j hj hq hqd ht' ht1 hε
      have hf1t : f1 t = t ^ (a / 2 - 1) := by
        simp only [hf1, indicator, mem_Ioc, ht', ht1, and_self, ite_true]
      rw [hf1t]
      have h2 : t ^ (a - 1) * |psiFn (boxPt y) (t + ε)| ≤ t ^ (a - 1) * (K * t ^ r) := by
        gcongr
      refine h2.trans ?_
      have : t ^ (a - 1) * (K * t ^ r) = K * t ^ (a / 2 - 1) := by
        rw [← hr_eq, Real.rpow_add ht']; ring
      rw [this]
      have : 0 ≤ M1 * f2 t := mul_nonneg hM10 (hf20 t ht')
      linarith
    · push Not at ht1
      have hf1t : f1 t = 0 := by
        simp only [hf1, indicator, mem_Ioc]
        simp [not_le.mpr ht1]
      rw [hf1t]
      have h := psi_large (boxPt y) (u := t + ε) (by linarith)
      have h2 : t ^ (a - 1) * |psiFn (boxPt y) (t + ε)| ≤ t ^ (a - 1) * (M1 * Real.exp (-t)) := by
        gcongr
        refine h.trans ?_
        gcongr
        linarith
      refine h2.trans ?_
      simp only [hf2]
      nlinarith [Real.exp_pos (-t), Real.rpow_pos_of_pos ht' (a - 1)]
  have hint : Integrable (fun t => K * f1 t + M1 * f2 t) (volume.restrict (Ioi 0)) :=
    (hf1i.integrableOn.const_mul K).add (hf2i.const_mul M1)
  have hI := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0:ℝ))) hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpt))
  rw [integral_add (hf1i.integrableOn.const_mul K) (hf2i.const_mul M1), integral_const_mul,
    integral_const_mul] at hI
  rw [abs_mul]
  rw [Real.norm_eq_abs] at hI
  calc |A| * |∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn (boxPt y) (t + ε)|
      ≤ |A| * (K * c1 + M1 * c2) := by gcongr
    _ = |A| * c1 * κ * m ^ (-((s + d)/2)) + |A| * (c1 * (1 + M1) + M1 * c2) := by
        rw [hK, hKc_eq]; ring


/-- the fundamental box `(-1/2, 1/2]^d`. -/
def Box (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Ioc (-1/2 : ℝ) (-1/2 + 1)}

theorem measurableSet_Box (d : ℕ) : MeasurableSet (Box d) :=
  MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)

theorem Box_abs_le {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ Box d) (i : Fin d) : |y i| ≤ 1/2 := by
  have := hy i
  simp only [mem_Ioc] at this
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

theorem Box_norm_le {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ Box d) : ‖y‖ ≤ 1/2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  rw [Real.norm_eq_abs]; exact Box_abs_le hy i

theorem Box_subset_ball (d : ℕ) : Box d ⊆ Metric.ball 0 1 := by
  intro y hy
  rw [mem_ball_zero_iff]
  linarith [Box_norm_le hy]

theorem boxPt_eq_zero {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ Box d) (h : boxPt y = 0) : y = 0 := by
  funext i
  have hi : ((y i : ℝ) : UnitAddCircle) = 0 := congrFun h i
  rw [AddCircle.coe_eq_zero_iff] at hi
  obtain ⟨n, hn⟩ := hi
  have h1 := hy i
  simp only [mem_Ioc] at h1
  have hn' : (n:ℝ) = y i := by simpa using hn
  have : n = 0 := by
    have h2 : (-1:ℝ) < n := by rw [hn']; linarith [h1.1]
    have h3 : (n:ℝ) < 1 := by rw [hn']; linarith [h1.2]
    have h2' : -1 < n := by exact_mod_cast h2
    have h3' : n < 1 := by exact_mod_cast h3
    omega
  simp [← hn', this]

theorem exists_argmax {d : ℕ} (hd : 0 < d) (y : Fin d → ℝ) : ∃ j, ‖y‖ = |y j| := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d)) (fun i => |y i|)
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  refine ⟨j, le_antisymm ?_ ?_⟩
  · refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]; exact hj i (Finset.mem_univ i)
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y j

theorem integrableOn_Box_rpow {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : α < d) :
    IntegrableOn (fun y : Fin d → ℝ => ‖y‖ ^ (-α)) (Box d) := by
  have hfin : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  have h := integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure (Fin d → ℝ)))
    (f := fun y : Fin d → ℝ => ‖y‖ ^ (-α)) (C := 1) (α := α) (r := 1)
    (by rw [hfin]; exact hd) (by rw [hfin]; exact hα)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, one_mul]
      exact (abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)).le)
    (Measurable.aestronglyMeasurable (measurable_norm.pow_const _))
  exact h.mono_set (Box_subset_ball d)

theorem measure_Box_ne_top (d : ℕ) : (volume : Measure (Fin d → ℝ)) (Box d) ≠ ∞ :=
  ((measure_mono (Box_subset_ball d)).trans_lt measure_ball_lt_top).ne


theorem abs_rieszCoeff_le (d : ℕ) (s : ℝ) (hsd : s < d) (k : Lattice d) :
    |rieszCoeff d s k| ≤ |rieszConst d s| := by
  unfold rieszCoeff
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false]; rw [abs_mul]
    have h1 := one_le_enorm k hk
    have hb : (2 * Real.pi * Lattice.enorm k) ^ (s - (d:ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three]) (by linarith)
    have hp : 0 ≤ (2 * Real.pi * Lattice.enorm k) ^ (s - (d:ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    rw [abs_of_nonneg hp]
    nlinarith [abs_nonneg (rieszConst d s)]

theorem norm_term_le {d : ℕ} {s : ℝ} (hsd : s < d) (ε : ℝ) (x : Torus d) (k : Lattice d) :
    ‖rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) * Torus.cosMode k x‖ ≤
      |rieszConst d s| * Real.exp (-ε * Lattice.enorm k ^ 2) := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hc := abs_cosMode_le k x
  have hexp := (Real.exp_pos (-ε * Lattice.enorm k ^ 2)).le
  have := abs_rieszCoeff_le d s hsd k
  calc |rieszCoeff d s k| * Real.exp (-ε * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
      ≤ |rieszConst d s| * Real.exp (-ε * Lattice.enorm k ^ 2) * 1 := by gcongr
    _ = _ := by ring

theorem continuous_heatRiesz {d : ℕ} {s : ℝ} (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    Continuous (heatRiesz d s ε) := by
  unfold heatRiesz
  refine continuous_tsum (u := fun k : Lattice d => |rieszConst d s| * Real.exp (-ε * Lattice.enorm k ^ 2))
    (fun k => ?_) ((summable_gauss_lattice d ε hε).mul_left _) (fun k x => norm_term_le hsd ε x k)
  exact continuous_const.mul (Torus.continuous_cosMode k)

theorem cosMode_cast {d : ℕ} (l : Lattice d) (x : Torus d) :
    ((Torus.cosMode l x : ℝ) : ℂ) = (Torus.mode l x + Torus.mode (-l) x) / 2 := by
  rw [Torus.mode_neg, Torus.cosMode, Complex.re_eq_add_conj]


theorem integral_mode_cos {d : ℕ} (k l : Lattice d) :
    ∫ x : Torus d, Torus.mode (-k) x * ((Torus.cosMode l x : ℝ) : ℂ) =
      ((if l = k then 1 else 0) + (if l = -k then 1 else 0)) / 2 := by
  have h1 : ∀ x : Torus d, Torus.mode (-k) x * ((Torus.cosMode l x : ℝ) : ℂ) =
      (Torus.mode (-k) x * Torus.mode l x + Torus.mode (-k) x * Torus.mode (-l) x) / 2 := by
    intro x; rw [cosMode_cast]; ring
  simp_rw [h1]
  rw [integral_div, integral_add (Torus.integrable_mode_mul _ _) (Torus.integrable_mode_mul _ _),
    Torus.integral_mode_mul, Torus.integral_mode_mul]
  have e1 : (-k + l = 0) ↔ l = k := by constructor <;> intro h <;> [exact (neg_add_eq_zero.mp h).symm; (rw [h]; simp)]
  have e2 : (-k + -l = 0) ↔ l = -k := by
    constructor
    · intro h
      have : -l = k := by
        have := congrArg (fun z => z + k) h
        simpa [add_comm, add_left_comm] using this
      simpa using congrArg Neg.neg this
    · intro h; rw [h]; simp
  simp only [e1, e2]

theorem integral_heat_mode {d : ℕ} {s : ℝ} (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (k : Lattice d) :
    ∫ x : Torus d, Torus.mode (-k) x * ((heatRiesz d s ε x : ℝ) : ℂ) =
      ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ) := by
  set c : Lattice d → ℝ := fun l => rieszCoeff d s l * Real.exp (-ε * Lattice.enorm l ^ 2) with hc
  set F : Lattice d → Torus d → ℂ := fun l x => Torus.mode (-k) x * (((c l * Torus.cosMode l x : ℝ)) : ℂ) with hF
  have hFcont : ∀ l, Continuous (F l) := fun l =>
    (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (Torus.continuous_cosMode l)))
  have hFint : ∀ l, Integrable (F l) := fun l =>
    (hFcont l).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFnorm : ∀ l x, ‖F l x‖ ≤ |rieszConst d s| * Real.exp (-ε * Lattice.enorm l ^ 2) := by
    intro l x
    simp only [hF]
    rw [norm_mul, norm_mode, one_mul, Complex.norm_real]
    exact norm_term_le hsd ε x l
  have hsumF : Summable fun l => ∫ x, ‖F l x‖ := by
    refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun x => norm_nonneg _) (fun l => ?_)
      ((summable_gauss_lattice d ε hε).mul_left |rieszConst d s|)
    calc ∫ x, ‖F l x‖ ≤ ∫ x : Torus d, |rieszConst d s| * Real.exp (-ε * Lattice.enorm l ^ 2) :=
          integral_mono (hFint l).norm (integrable_const _) (fun x => hFnorm l x)
      _ = _ := by simp
  have hsw := integral_tsum_of_summable_integral_norm hFint hsumF
  have hpt : ∀ x : Torus d, ∑' l, F l x = Torus.mode (-k) x * ((heatRiesz d s ε x : ℝ) : ℂ) := by
    intro x
    have hs := summable_heatRiesz hsd ε hε x
    simp only [hF]
    rw [tsum_mul_left, ← Complex.ofReal_tsum]
    rfl
  simp_rw [← hpt]
  rw [← hsw]
  have hl : ∀ l, ∫ x, F l x = (c l : ℂ) * (((if l = k then 1 else 0) + (if l = -k then 1 else 0)) / 2) := by
    intro l
    simp only [hF]
    have : ∀ x : Torus d, Torus.mode (-k) x * (((c l * Torus.cosMode l x : ℝ)) : ℂ) =
        (c l : ℂ) * (Torus.mode (-k) x * ((Torus.cosMode l x : ℝ) : ℂ)) := by
      intro x; push_cast; ring
    simp_rw [this]
    rw [integral_const_mul, integral_mode_cos]
  simp_rw [hl]
  have hneg : c (-k) = c k := by simp [hc, rieszCoeff_neg, enorm_neg]
  have hsplit : ∀ l, (c l : ℂ) * (((if l = k then 1 else 0) + (if l = -k then 1 else 0)) / 2) =
      (if l = k then (c k : ℂ) / 2 else 0) + (if l = -k then (c (-k) : ℂ) / 2 else 0) := by
    intro l
    split_ifs with h1 h2 h2
    · rw [h1, hneg]; ring
    · rw [h1]; ring
    · rw [h2]; ring
    · simp
  simp_rw [hsplit]
  rw [((hasSum_ite_eq k ((c k : ℂ) / 2)).add (hasSum_ite_eq (-k) ((c (-k) : ℂ) / 2))).tsum_eq, hneg]
  simp only [hc]
  push_cast
  ring


theorem continuous_boxPt (d : ℕ) : Continuous (boxPt : (Fin d → ℝ) → Torus d) :=
  continuous_pi fun i => (AddCircle.continuous_mk' _).comp (continuous_apply i)

theorem integral_torus_box {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Torus d → E) : ∫ x : Torus d, f x = ∫ y in Box d, f (boxPt y) := by
  rw [Torus.volume_eq_pi_haar]
  exact UnitAddTorus.integral_preimage f (fun _ => (-1/2 : ℝ))

theorem integral_periodicRiesz_mode {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (k : Lattice d) :
    ∫ x : Torus d, Torus.mode (-k) x * ((periodicRiesz d s x : ℝ) : ℂ) = ((rieszCoeff d s k : ℝ) : ℂ) := by
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := heat_eps_bound hs0 hsd
  set μ : Measure (Fin d → ℝ) := volume.restrict (Box d) with hμ
  set G : (Fin d → ℝ) → ℝ := fun y => C1 * ‖y‖ ^ (-((s + d)/2)) + C2 with hG
  set Fε : ℝ → (Fin d → ℝ) → ℂ := fun ε y =>
    Torus.mode (-k) (boxPt y) * ((heatRiesz d s ε (boxPt y) : ℝ) : ℂ) with hFε
  set F0 : (Fin d → ℝ) → ℂ := fun y =>
    Torus.mode (-k) (boxPt y) * ((periodicRiesz d s (boxPt y) : ℝ) : ℂ) with hF0
  have hne : ∀ᵐ y ∂μ, y ≠ 0 := by
    have h1 : ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), y ≠ 0 := by
      rw [ae_iff]; simp
    exact ae_restrict_of_ae h1
  have hmem : ∀ᵐ y ∂μ, y ∈ Box d := ae_restrict_mem (measurableSet_Box d)
  have hdom := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0:ℝ))
    (F := Fε) (f := F0) G ?_ ?_ ?_ ?_
  · -- identify the limit
    have h1 : ∀ ε : ℝ, 0 < ε → ∫ y, Fε ε y ∂μ =
        ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ) := by
      intro ε hε
      rw [← integral_heat_mode hsd hε k]
      exact (integral_torus_box (fun x : Torus d => Torus.mode (-k) x * ((heatRiesz d s ε x : ℝ) : ℂ))).symm
    have h2 : Tendsto (fun ε : ℝ => ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 ((rieszCoeff d s k : ℝ) : ℂ)) := by
      have : Continuous fun ε : ℝ => ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ) := by
        fun_prop
      have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa using this
    have h3 : Tendsto (fun ε : ℝ => ∫ y, Fε ε y ∂μ) (𝓝[>] 0) (𝓝 ((rieszCoeff d s k : ℝ) : ℂ)) :=
      h2.congr' (by filter_upwards [self_mem_nhdsWithin] with ε hε using (h1 ε hε).symm)
    have h4 := tendsto_nhds_unique hdom h3
    rw [← h4]
    exact integral_torus_box (fun x : Torus d => Torus.mode (-k) x * ((periodicRiesz d s x : ℝ) : ℂ))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    refine Continuous.aestronglyMeasurable ?_
    exact ((Torus.continuous_mode _).comp (continuous_boxPt d)).mul
      (Complex.continuous_ofReal.comp ((continuous_heatRiesz hsd hε').comp (continuous_boxPt d)))
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hne, hmem] with y hy hyB
    have hy0 : boxPt y ≠ 0 := fun h => hy (boxPt_eq_zero hyB h)
    obtain ⟨j, hj⟩ := exists_argmax hd0 y
    have hyj : y j ≠ 0 := by
      intro h0
      apply hy
      have : ‖y‖ = 0 := by rw [hj, h0, abs_zero]
      exact norm_eq_zero.mp this
    have := hbd y (Box_abs_le hyB) j hyj ε hε.1 hε.2.le
    simp only [hFε, norm_mul, norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs, hG, hj]
    exact this
  · have hI : IntegrableOn (fun y : Fin d → ℝ => ‖y‖ ^ (-((s + d)/2))) (Box d) :=
      integrableOn_Box_rpow hd0 (by linarith)
    exact (hI.const_mul C1).add (integrableOn_const (measure_Box_ne_top d))
  · filter_upwards [hne, hmem] with y hy hyB
    have hy0 : boxPt y ≠ 0 := fun h => hy (boxPt_eq_zero hyB h)
    have := periodicRiesz_tendsto hd hs0 hsd (boxPt y) hy0
    exact (Complex.continuous_ofReal.tendsto _ |>.comp this).const_mul _


theorem lintegral_torus_box {d : ℕ} (f : Torus d → ℝ≥0∞) :
    ∫⁻ x : Torus d, f x = ∫⁻ y in Box d, f (boxPt y) := by
  rw [Torus.volume_eq_pi_haar]
  exact UnitAddTorus.lintegral_preimage f (fun _ => (-1/2 : ℝ))

theorem ae_ne_pi {d : ℕ} (hd : 0 < d) : ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), y ≠ 0 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [ae_iff]; simp

theorem torus_ae_ne {d : ℕ} (hd : 0 < d) : ∀ᵐ x : Torus d, x ≠ 0 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [ae_iff]
  simp only [ne_eq, not_not]
  show (volume : Measure (Torus d)) {0} = 0
  have h := lintegral_torus_box (d := d) (({0} : Set (Torus d)).indicator 1)
  have h1 : ∫⁻ x : Torus d, ({0} : Set (Torus d)).indicator 1 x = (volume : Measure (Torus d)) {0} := by
    rw [lintegral_indicator_one (measurableSet_singleton _)]
  have h2 : ∫⁻ y in Box d, ({0} : Set (Torus d)).indicator 1 (boxPt y) = 0 := by
    have : ∀ᵐ y ∂(volume.restrict (Box d)), ({0} : Set (Torus d)).indicator (1 : Torus d → ℝ≥0∞) (boxPt y) = 0 := by
      filter_upwards [ae_restrict_of_ae (ae_ne_pi hd), ae_restrict_mem (measurableSet_Box d)] with y hy hyB
      have hn : boxPt y ∉ ({0} : Set (Torus d)) := fun h => hy (boxPt_eq_zero hyB h)
      exact Set.indicator_of_notMem hn _
    rw [lintegral_congr_ae this]; simp
  rw [← h1, h, h2]

theorem periodicRiesz_box_bound {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ y : Fin d → ℝ, y ∈ Box d → y ≠ 0 →
      |periodicRiesz d s (boxPt y)| ≤ C1 * ‖y‖ ^ (-((s + d)/2)) + C2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := heat_eps_bound hs0 hsd
  refine ⟨C1, C2, hC1, hC2, fun y hyB hy => ?_⟩
  have hy0 : boxPt y ≠ 0 := fun h => hy (boxPt_eq_zero hyB h)
  obtain ⟨j, hj⟩ := exists_argmax hd0 y
  have hyj : y j ≠ 0 := by
    intro h0
    apply hy
    have : ‖y‖ = 0 := by rw [hj, h0, abs_zero]
    exact norm_eq_zero.mp this
  have hlim := (periodicRiesz_tendsto hd hs0 hsd (boxPt y) hy0).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  have := hbd y (Box_abs_le hyB) j hyj ε hε.1 hε.2.le
  rwa [← hj] at this

theorem aestronglyMeasurable_periodicRiesz {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    AEStronglyMeasurable (periodicRiesz d s) (volume : Measure (Torus d)) := by
  have hd0 : 0 < d := by omega
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun n : ℕ => heatRiesz d s (1 / ((n:ℝ) + 1)))
    (fun n => (continuous_heatRiesz hsd (by positivity)).aestronglyMeasurable) ?_
  filter_upwards [torus_ae_ne hd0] with x hx
  have h := periodicRiesz_tendsto hd hs0 hsd x hx
  refine h.comp ?_
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun n => ?_⟩
  simp only [mem_Ioi]; positivity

theorem integrable_periodicRiesz {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := periodicRiesz_box_bound hd hs0 hsd
  refine ⟨aestronglyMeasurable_periodicRiesz hd hs0 hsd, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_torus_box (fun x => ‖periodicRiesz d s x‖ₑ)]
  have hI : IntegrableOn (fun y : Fin d → ℝ => C1 * ‖y‖ ^ (-((s + d)/2)) + C2) (Box d) :=
    ((integrableOn_Box_rpow hd0 (by linarith)).const_mul C1).add
      (integrableOn_const (measure_Box_ne_top d))
  have hne : ∀ᵐ y ∂(volume.restrict (Box d)), y ≠ 0 := by
    exact ae_restrict_of_ae (ae_ne_pi hd0)
  calc ∫⁻ y in Box d, ‖periodicRiesz d s (boxPt y)‖ₑ
      ≤ ∫⁻ y in Box d, ENNReal.ofReal (C1 * ‖y‖ ^ (-((s + d)/2)) + C2) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hne, ae_restrict_mem (measurableSet_Box d)] with y hy hyB
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (hbd y hyB hy)
    _ = ∫⁻ y in Box d, ‖C1 * ‖y‖ ^ (-((s + d)/2)) + C2‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [Real.enorm_of_nonneg (by positivity)]
    _ < ∞ := hI.2

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- the constant `A = c (2π)^{s-d} / Γ((d-s)/2)` of the subordination formula -/
def subA (d : ℕ) (s : ℝ) : ℝ := rieszConst d s * (2 * π) ^ (s - d) / Real.Gamma (((d:ℝ) - s) / 2)

theorem integrableOn_psi {d : ℕ} {s : ℝ} (hsd : s < d) (x : Torus d) (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (((d:ℝ) - s) / 2 - 1) * psiFn x t) (Ioi 0) := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  obtain ⟨M, hM0, hM⟩ := psi_bound x hx
  have hcont := psi_continuousOn x
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (a - 1) * psiFn x t) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) hcont
  refine Integrable.mono' ((Real.GammaIntegral_convergent ha).const_mul M) hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have ht' : 0 < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
  have h1 := hM t ht'
  calc t ^ (a - 1) * |psiFn x t| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by gcongr
    _ = _ := by ring

theorem periodicRiesz_eq_integral {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (x : Torus d) (hx : x ≠ 0) :
    periodicRiesz d s x = subA d s * ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn x t := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  obtain ⟨M, hM0, hM⟩ := psi_bound x hx
  have hcont := psi_continuousOn x
  have hmeas : ∀ ε : ℝ, 0 ≤ ε → AEStronglyMeasurable (fun t : ℝ => t ^ (a - 1) * psiFn x (t + ε))
      (volume.restrict (Ioi 0)) := by
    intro ε hε
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) ?_
    refine hcont.comp (continuousOn_id.add continuousOn_const) fun t ht => ?_
    simp only [mem_Ioi] at ht ⊢
    linarith
  have hlim : Tendsto (fun ε => ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x (t + ε)) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => M * (Real.exp (-t) * t ^ (a - 1))) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε using hmeas ε (le_of_lt hε)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have hε' : 0 < ε := hε
      have ht' : 0 < t := ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
      have h1 := hM (t + ε) (by linarith)
      have h2 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
      have h3 := Real.rpow_pos_of_pos ht' (a - 1)
      calc t ^ (a - 1) * |psiFn x (t + ε)| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = _ := by ring
    · exact (Real.GammaIntegral_convergent ha).const_mul M
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have ht' : 0 < t := ht
      refine Tendsto.const_mul _ ?_
      have h1 : Tendsto (fun ε : ℝ => t + ε) (𝓝[>] 0) (𝓝 t) := by
        have : Tendsto (fun ε : ℝ => t + ε) (𝓝 0) (𝓝 (t + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 : ContinuousAt (psiFn x) t :=
        (hcont t ht').continuousAt (Ioi_mem_nhds ht')
      exact h2.tendsto.comp h1
  have h2 : Tendsto (fun ε => heatRiesz d s ε x) (𝓝[>] 0)
      (𝓝 (subA d s * ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x t)) := by
    refine (hlim.const_mul _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (heatRiesz_eq_integral hsd hε x).symm
  exact tendsto_nhds_unique (periodicRiesz_tendsto hd hs0 hsd x hx) h2


theorem pi_hasSum_real (n : ℕ) (f : Fin n → ℤ → ℝ) (hf : ∀ i, Summable fun m => |f i m|) :
    HasSum (fun k : Fin n → ℤ => ∏ i, f i (k i)) (∏ i, ∑' m, f i m) := by
  have h := (pi_hasSum n (fun i m => (f i m : ℂ)) (fun i => by simpa using hf i)).2
  have e1 : (fun k : Fin n → ℤ => ∏ i, ((f i (k i) : ℝ) : ℂ)) = fun k => (((∏ i, f i (k i)) : ℝ) : ℂ) := by
    funext k; push_cast; rfl
  have e2 : (∏ i, ∑' m, ((f i m : ℝ) : ℂ)) = (((∏ i, ∑' m, f i m) : ℝ) : ℂ) := by
    push_cast; simp
  rw [e1, e2] at h
  exact Complex.hasSum_ofReal.mp h

theorem summable_shift_gauss {c : ℝ} (hc : 0 < c) (y : ℝ) :
    Summable fun n : ℤ => Real.exp (-c * ((n:ℝ) - y)^2) := by
  refine ((summable_exp_sq (c/2) (by positivity)).mul_left (Real.exp (c * y^2))).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le) fun n => ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ((n:ℝ) / 2 - y), sq_nonneg ((n:ℝ) - 2 * y)]

theorem theta_images {d : ℕ} (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k (boxPt y) =
      Real.sqrt (π / u) ^ d *
        ∑' m : Lattice d, Real.exp (-(π^2 * ∑ i, (((m i : ℤ) : ℝ) - y i)^2 / u)) := by
  rw [theta_prod y hu, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  have hs : ∀ i, Summable fun n : ℤ => |Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u))| := by
    intro i
    simp_rw [abs_of_pos (Real.exp_pos _)]
    -- Gaussian summable
    have : Summable fun n : ℤ => Real.exp (-(π^2 / u) * ((n:ℝ) - y i)^2) :=
      summable_shift_gauss (by positivity) _
    refine this.congr fun n => ?_
    congr 1; ring
  have h := (pi_hasSum_real d (fun i n => Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u))) hs).tsum_eq
  rw [← h]
  refine tsum_congr fun m => ?_
  rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc, Finset.sum_div]


/-! ### The function `W_s(w) = ∫_0^1 t^{-s/2-1} e^{-w/t} dt` -/

def Wfun (s w : ℝ) : ℝ := ∫ t in Ioc (0:ℝ) 1, t ^ (-s/2 - 1) * Real.exp (-w / t)

def Wmeas (s : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (0:ℝ) 1)).withDensity (fun t => ENNReal.ofReal (t ^ (-s/2 - 1)))

theorem t_pow_exp_bound {N θ : ℝ} (hN : 0 < N) (hθ : 0 < θ) {t : ℝ} (ht : 0 < t) :
    t ^ (-N) * Real.exp (-θ / t) ≤ (N ^ N * Real.exp (-N)) * θ ^ (-N) := by
  have h := exp_neg_le_rpow hN (v := θ / t) (by positivity)
  rw [Real.div_rpow hθ.le ht.le, Real.rpow_neg hθ.le, Real.rpow_neg ht.le, div_inv_eq_mul,
    ← neg_div] at h
  rw [Real.rpow_neg ht.le]
  calc (t ^ N)⁻¹ * Real.exp (-θ / t) ≤ (t ^ N)⁻¹ * ((N ^ N * Real.exp (-N)) * ((θ ^ N)⁻¹ * t ^ N)) := by
        gcongr
    _ = _ := by
        have : t ^ N ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
        rw [Real.rpow_neg hθ.le]
        field_simp

theorem integrableOn_W_integrand (s : ℝ) (hs : 0 ≤ s) {w : ℝ} (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => t ^ (-s/2 - 1) * Real.exp (-w / t)) (Ioc 0 1) := by
  have hN : 0 < s/2 + 1 := by linarith
  have hb := fun t (ht : 0 < t) => t_pow_exp_bound hN hw ht
  refine Measure.integrableOn_of_bounded (M := (( s/2+1) ^ (s/2+1) * Real.exp (-(s/2+1))) * w ^ (-(s/2+1)))
    (by simp) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := ht.1; positivity)]
    have := hb t ht.1
    have e : -s/2 - 1 = -(s/2+1) := by ring
    rw [e]; exact this

theorem Wfun_eq_mgf (s w : ℝ) :
    Wfun s w = ProbabilityTheory.mgf (fun t : ℝ => -1/t) (Wmeas s) w := by
  unfold Wfun ProbabilityTheory.mgf Wmeas
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ht.1 _).le, smul_eq_mul]
  congr 2
  ring


theorem Wfun_eq_mgf' (s : ℝ) : Wfun s = ProbabilityTheory.mgf (fun t : ℝ => -1/t) (Wmeas s) :=
  funext (Wfun_eq_mgf s)

theorem Ioi_subset_integrableExpSet (s : ℝ) (hs : 0 ≤ s) :
    Ioi (0:ℝ) ⊆ interior (ProbabilityTheory.integrableExpSet (fun t : ℝ => -1/t) (Wmeas s)) := by
  refine isOpen_Ioi.subset_interior_iff.mpr fun θ hθ => ?_
  have hθ' : 0 < θ := hθ
  show Integrable (fun t : ℝ => Real.exp (θ * (-1/t))) (Wmeas s)
  unfold Wmeas
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (integrableOn_W_integrand s hs hθ').congr_fun_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ht.1 _).le, smul_eq_mul]
  congr 2; ring

theorem contDiffOn_Wfun (s : ℝ) (hs : 0 ≤ s) : ContDiffOn ℝ ∞' (Wfun s) (Ioi 0) := by
  rw [Wfun_eq_mgf']
  have := (ProbabilityTheory.analyticOn_mgf (X := fun t : ℝ => -1/t) (μ := Wmeas s)).mono
    (Ioi_subset_integrableExpSet s hs)
  exact (this.contDiffOn isOpen_Ioi.uniqueDiffOn).of_le (by exact_mod_cast le_top)

theorem iteratedDeriv_Wfun (s : ℝ) (hs : 0 ≤ s) (i : ℕ) {w : ℝ} (hw : 0 < w) :
    iteratedDeriv i (Wfun s) w =
      ∫ t in Ioc (0:ℝ) 1, t ^ (-s/2 - 1) * ((-1/t) ^ i * Real.exp (-w / t)) := by
  rw [Wfun_eq_mgf', ProbabilityTheory.iteratedDeriv_mgf (Ioi_subset_integrableExpSet s hs hw)]
  unfold Wmeas
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ht.1 _).le, smul_eq_mul]
  congr 3; ring


theorem W_deriv_bound (s : ℝ) (hs : 0 ≤ s) (i : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℝ, 1 ≤ w → |iteratedDeriv i (Wfun s) w| ≤ B * Real.exp (-w / 2) := by
  set g : ℝ → ℝ := fun t => t ^ (-s/2 - 1) * ((1 / t) ^ i * Real.exp (-(1/2) / t)) with hg
  have hN : 0 < s/2 + 1 + i := by positivity
  have hgeq : ∀ t, 0 < t → g t = t ^ (-(s/2 + 1 + i)) * Real.exp (-(1/2) / t) := by
    intro t ht
    simp only [hg]
    rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← mul_assoc,
      ← Real.rpow_add ht]
    congr 2; ring
  have hgi : IntegrableOn g (Ioc 0 1) := by
    refine Measure.integrableOn_of_bounded (M := ((s/2+1+i) ^ (s/2+1+i) * Real.exp (-(s/2+1+i))) * (1/2) ^ (-(s/2+1+i)))
      (by simp) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      simp only [hg]; fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, hgeq t ht.1, abs_of_nonneg (by have := ht.1; positivity)]
      exact t_pow_exp_bound hN (by norm_num) ht.1
  refine ⟨∫ t in Ioc (0:ℝ) 1, g t, setIntegral_nonneg measurableSet_Ioc fun t ht => ?_, fun w hw => ?_⟩
  · have := ht.1; simp only [hg]; positivity
  · have hw0 : 0 < w := by linarith
    rw [iteratedDeriv_Wfun s hs i hw0, ← Real.norm_eq_abs, mul_comm, ← integral_const_mul]
    refine (norm_integral_le_of_norm_le (g := fun t => Real.exp (-w / 2) * g t) (hgi.const_mul _) ?_).trans_eq ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have ht0 := ht.1
      have ht1 := ht.2
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_pow,
        abs_of_pos (Real.exp_pos _)]
      have h1 : |(-1/t)| = 1 / t := by
        rw [abs_div, abs_neg, abs_one, abs_of_pos ht0]
      rw [h1]
      simp only [hg]
      have h2 : Real.exp (-w / t) ≤ Real.exp (-w / 2) * Real.exp (-(1/2) / t) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h3 : w / 2 / t ≥ w / 2 := by
          rw [ge_iff_le, le_div_iff₀ ht0]; nlinarith
        have h4 : w / 2 / t ≥ (1/2) / t := by
          apply div_le_div_of_nonneg_right (by linarith) ht0.le
        have e1 : -w / t = -(w/2/t) + -(w/2/t) := by ring
        have e2 : -(1/2) / t = -((1/2)/t) := by ring
        rw [e1, e2]; linarith
      have hp : 0 ≤ t ^ (-s/2 - 1) * (1 / t) ^ i := by positivity
      calc t ^ (-s/2 - 1) * ((1 / t) ^ i * Real.exp (-w / t))
          ≤ t ^ (-s/2 - 1) * ((1 / t) ^ i * (Real.exp (-w / 2) * Real.exp (-(1/2) / t))) := by gcongr
        _ = Real.exp (-w / 2) * (t ^ (-s/2 - 1) * ((1 / t) ^ i * Real.exp (-(1/2) / t))) := by ring
    · rw [integral_const_mul]


/-- squared distance `|y - m|²` from the lattice point `m` -/
def wsq {d : ℕ} (y : Fin d → ℝ) (m : Lattice d) : ℝ := ∑ i, (((m i : ℤ) : ℝ) - y i)^2

theorem wsq_nonneg {d : ℕ} (y : Fin d → ℝ) (m : Lattice d) : 0 ≤ wsq y m :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem eventually_one_le_wsq {d : ℕ} (y : Fin d → ℝ) :
    ∀ᶠ m in (Filter.cofinite : Filter (Lattice d)), 1 ≤ π^2 * wsq y m := by
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_Icc (fun i => ⌊y i⌋ - 1) (fun i => ⌈y i⌉ + 1)) ?_
  intro m hm
  simp only [Set.mem_ofPred_eq, not_le] at hm
  have hlt : wsq y m < 1 := by
    have : π^2 > 1 := by nlinarith [Real.pi_gt_three]
    by_contra h
    push Not at h
    nlinarith [wsq_nonneg y m]
  have hi : ∀ i, |((m i : ℤ) : ℝ) - y i| < 1 := by
    intro i
    have h1 : (((m i : ℤ) : ℝ) - y i)^2 ≤ wsq y m :=
      Finset.single_le_sum (f := fun i => (((m i : ℤ) : ℝ) - y i)^2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    have : (((m i : ℤ) : ℝ) - y i)^2 < 1 := h1.trans_lt hlt
    exact abs_lt_of_sq_lt_sq' (by simpa using this) zero_le_one |> fun h => abs_lt.mpr h
  constructor
  · intro i
    have := abs_lt.mp (hi i)
    have h2 : ((⌊y i⌋ - 1 : ℤ) : ℝ) ≤ ((m i : ℤ) : ℝ) := by
      push_cast
      have := Int.floor_le (y i)
      have := Int.lt_floor_add_one (y i)
      linarith [(abs_lt.mp (hi i)).1]
    exact_mod_cast h2
  · intro i
    have h2 : ((m i : ℤ) : ℝ) ≤ ((⌈y i⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      have := Int.le_ceil (y i)
      have := Int.ceil_lt_add_one (y i)
      linarith [(abs_lt.mp (hi i)).2]
    exact_mod_cast h2


theorem Wfun_nonneg (s w : ℝ) : 0 ≤ Wfun s w :=
  setIntegral_nonneg measurableSet_Ioc fun t ht => by
    have := ht.1; positivity

theorem summable_gauss_wsq {d : ℕ} (y : Fin d → ℝ) {c : ℝ} (hc : 0 < c) :
    Summable fun m : Lattice d => Real.exp (-(c * wsq y m)) := by
  have hs : ∀ i, Summable fun n : ℤ => |Real.exp (-c * ((n:ℝ) - y i)^2)| := by
    intro i
    simp_rw [abs_of_pos (Real.exp_pos _)]
    exact summable_shift_gauss hc _
  have := (pi_hasSum_real d (fun i n => Real.exp (-c * ((n:ℝ) - y i)^2)) hs).summable
  refine this.congr fun m => ?_
  rw [← Real.exp_sum, wsq, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

theorem summable_Wfun_wsq {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (y : Fin d → ℝ) :
    Summable fun m : Lattice d => Wfun s (π^2 * wsq y m) := by
  obtain ⟨B, hB0, hB⟩ := W_deriv_bound s hs 0
  refine Summable.of_norm_bounded_eventually (g := fun m : Lattice d => B * Real.exp (-(π^2 / 2 * wsq y m)))
    ((summable_gauss_wsq y (by positivity)).mul_left B) ?_
  filter_upwards [eventually_one_le_wsq y] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (Wfun_nonneg _ _)]
  have := hB (π^2 * wsq y m) hm
  rw [iteratedDeriv_zero, abs_of_nonneg (Wfun_nonneg _ _)] at this
  refine this.trans (le_of_eq ?_)
  congr 2; ring


theorem theta_images_wsq {d : ℕ} (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k (boxPt y) =
      Real.sqrt (π / u) ^ d * ∑' m : Lattice d, Real.exp (-(π^2 * wsq y m / u)) := by
  rw [theta_images y hu]
  congr 2
  funext m
  unfold wsq
  rw [← Finset.sum_div, ← mul_div_assoc]

theorem boxPt_ne_zero_of_wsq {d : ℕ} {y : Fin d → ℝ} (hy : ∀ m : Lattice d, 0 < wsq y m) :
    boxPt y ≠ 0 := by
  intro h
  have : ∀ i, ∃ n : ℤ, (n:ℝ) = y i := by
    intro i
    have hi : ((y i : ℝ) : UnitAddCircle) = 0 := congrFun h i
    rw [AddCircle.coe_eq_zero_iff] at hi
    obtain ⟨n, hn⟩ := hi
    exact ⟨n, by simpa using hn⟩
  choose m hm using this
  have := hy m
  have h0 : wsq y m = 0 := by
    unfold wsq
    exact Finset.sum_eq_zero fun i _ => by rw [hm i]; simp
  linarith

theorem int_Ioc_psi {d : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (y : Fin d → ℝ)
    (hy : ∀ m : Lattice d, 0 < wsq y m) :
    ∫ t in Ioc (0:ℝ) 1, t ^ (((d:ℝ) - s)/2 - 1) * psiFn (boxPt y) t =
      π ^ ((d:ℝ)/2) * ∑' m : Lattice d, Wfun s (π^2 * wsq y m) - 1 / (((d:ℝ) - s)/2) := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set F : Lattice d → ℝ → ℝ := fun m t => t ^ (-s/2 - 1) * Real.exp (-(π^2 * wsq y m) / t) with hF
  have hF_int : ∀ m, Integrable (F m) (volume.restrict (Ioc (0:ℝ) 1)) := fun m =>
    integrableOn_W_integrand s hs0 (by have := hy m; positivity)
  have hF_sum : Summable fun m => ∫ t, ‖F m t‖ ∂(volume.restrict (Ioc (0:ℝ) 1)) := by
    refine (summable_Wfun_wsq hs0 y).congr fun m => ?_
    unfold Wfun
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [hF]
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := ht.1; positivity)]
  have hsw := integral_tsum_of_summable_integral_norm hF_int hF_sum
  have hW : ∀ m, ∫ t, F m t ∂(volume.restrict (Ioc (0:ℝ) 1)) = Wfun s (π^2 * wsq y m) := fun m => rfl
  have hx0 : boxPt y ≠ 0 := boxPt_ne_zero_of_wsq hy
  have hpsi_int : IntegrableOn (fun t : ℝ => t ^ (a - 1) * psiFn (boxPt y) t) (Ioc 0 1) :=
    (integrableOn_psi hsd (boxPt y) hx0).mono_set Ioc_subset_Ioi_self
  have hpow_int : IntegrableOn (fun t : ℝ => t ^ (a - 1)) (Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := a - 1) (by linarith))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
  have hpt : ∀ t ∈ Ioc (0:ℝ) 1, t ^ (a - 1) * psiFn (boxPt y) t + t ^ (a - 1) =
      π ^ ((d:ℝ)/2) * ∑' m, F m t := by
    intro t ht
    have ht0 := ht.1
    have h1 := psi_eq (boxPt y) ht0
    rw [theta_images_wsq y ht0] at h1
    have h3 : 1 + psiFn (boxPt y) t =
        Real.sqrt (π / t) ^ d * ∑' m : Lattice d, Real.exp (-(π^2 * wsq y m / t)) :=
      h1.symm
    have hc0 : t ^ (a - 1) * (Real.sqrt π ^ d * t ^ (-(d:ℝ)/2)) = π ^ ((d:ℝ)/2) * t ^ (-s/2 - 1) := by
      have e1 : Real.sqrt π ^ d = π ^ ((d:ℝ)/2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
        congr 1; ring
      rw [e1, ← mul_assoc, mul_comm (t ^ (a - 1)), mul_assoc, ← Real.rpow_add ht0]
      congr 2
      rw [ha_def]; ring
    calc t ^ (a - 1) * psiFn (boxPt y) t + t ^ (a - 1) = t ^ (a - 1) * (1 + psiFn (boxPt y) t) := by ring
      _ = t ^ (a - 1) * (Real.sqrt (π / t) ^ d * ∑' m : Lattice d, Real.exp (-(π^2 * wsq y m / t))) := by rw [h3]
      _ = (t ^ (a - 1) * (Real.sqrt π ^ d * t ^ (-(d:ℝ)/2))) * ∑' m : Lattice d, Real.exp (-(π^2 * wsq y m / t)) := by
          rw [sqrt_div_pow_eq d ht0]; ring
      _ = π ^ ((d:ℝ)/2) * ∑' m, F m t := by
          rw [hc0, mul_assoc, ← tsum_mul_left]
          congr 1
          refine tsum_congr fun m => ?_
          simp only [hF, neg_div]
  -- integrate
  have hint1 : Integrable (fun t => t ^ (a - 1) * psiFn (boxPt y) t + t ^ (a - 1)) (volume.restrict (Ioc (0:ℝ) 1)) :=
    hpsi_int.add hpow_int
  have hI1 : ∫ t in Ioc (0:ℝ) 1, (t ^ (a - 1) * psiFn (boxPt y) t + t ^ (a - 1)) =
      π ^ ((d:ℝ)/2) * ∑' m, Wfun s (π^2 * wsq y m) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht => hpt t ht), integral_const_mul, ← hsw]
    rfl
  rw [integral_add hpsi_int hpow_int] at hI1
  have hI2 : ∫ t in Ioc (0:ℝ) 1, t ^ (a - 1) = 1 / a := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
    simp [Real.zero_rpow ha.ne']
  linarith


/-! ### The large-time part `F2` -/

/-- Fourier coefficients of the large-time part. -/
def coefF2 (d : ℕ) (s : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else
    subA d s * ∫ t in Ioi (1:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * Real.exp (-t * Lattice.enorm k ^ 2)

theorem exp_le_large {t m : ℝ} (ht : 1 ≤ t) (hm : 1 ≤ m) :
    Real.exp (-t * m) ≤ Real.exp (-m / 2) * Real.exp (-t / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hm)]

theorem integrable_gamma_half {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t / 2)) (Ioi 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := 1/2)
    (by linarith) one_pos (by norm_num)
  refine (h.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  congr 2; ring

theorem coefF2_bound {d : ℕ} {s : ℝ} (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Lattice d, |coefF2 d s k| ≤ C * Real.exp (-Lattice.enorm k ^ 2 / 2) := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set c3 := ∫ t in Ioi (1:ℝ), t ^ (a - 1) * Real.exp (-t / 2) with hc3
  have hc3_0 : 0 ≤ c3 := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : 0 < t := lt_trans zero_lt_one ht
    positivity
  refine ⟨|subA d s| * c3, by positivity, fun k => ?_⟩
  unfold coefF2
  by_cases hk : k = 0
  · simp [hk]; positivity
  · simp only [hk, ite_false]
    have hm := one_le_enorm k hk
    have hm2 : 1 ≤ Lattice.enorm k ^ 2 := by nlinarith
    have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t * Lattice.enorm k ^ 2)) (Ioi 1) := by
      refine Integrable.mono' ((integrable_gamma_half ha).const_mul (Real.exp (-Lattice.enorm k ^ 2 / 2))) ?_ ?_
      · refine Measurable.aestronglyMeasurable ?_
        fun_prop
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
        have ht1 : 1 ≤ t := le_of_lt ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := exp_le_large ht1 hm2
        calc t ^ (a - 1) * Real.exp (-t * Lattice.enorm k ^ 2)
            ≤ t ^ (a - 1) * (Real.exp (-Lattice.enorm k ^ 2 / 2) * Real.exp (-t / 2)) := by gcongr
          _ = _ := by ring
    rw [abs_mul]
    have h2 : |∫ t in Ioi (1:ℝ), t ^ (a - 1) * Real.exp (-t * Lattice.enorm k ^ 2)| ≤
        Real.exp (-Lattice.enorm k ^ 2 / 2) * c3 := by
      rw [← Real.norm_eq_abs, hc3, ← integral_const_mul]
      refine norm_integral_le_of_norm_le ((integrable_gamma_half ha).const_mul _) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have ht1 : 1 ≤ t := le_of_lt ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have := exp_le_large ht1 hm2
      calc t ^ (a - 1) * Real.exp (-t * Lattice.enorm k ^ 2)
          ≤ t ^ (a - 1) * (Real.exp (-Lattice.enorm k ^ 2 / 2) * Real.exp (-t / 2)) := by gcongr
        _ = _ := by ring
    calc |subA d s| * |∫ t in Ioi (1:ℝ), t ^ (a - 1) * Real.exp (-t * Lattice.enorm k ^ 2)|
        ≤ |subA d s| * (Real.exp (-Lattice.enorm k ^ 2 / 2) * c3) := by gcongr
      _ = _ := by ring


theorem F2_eq {d : ℕ} {s : ℝ} (hsd : s < d) (x : Torus d) :
    subA d s * ∫ t in Ioi (1:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn x t =
      ∑' k : Lattice d, coefF2 d s k * Torus.cosMode k x := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set G : Lattice d → ℝ → ℝ := fun k t =>
    t ^ (a - 1) * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x) with hG
  set c3 := ∫ t in Ioi (1:ℝ), t ^ (a - 1) * Real.exp (-t / 2) with hc3
  have hc3_0 : 0 ≤ c3 := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : 0 < t := lt_trans zero_lt_one ht
    positivity
  have hbd : ∀ k : Lattice d, k ≠ 0 → ∀ t ∈ Ioi (1:ℝ),
      ‖G k t‖ ≤ Real.exp (-Lattice.enorm k ^ 2 / 2) * (t ^ (a - 1) * Real.exp (-t / 2)) := by
    intro k hk t ht
    have ht1 : 1 ≤ t := le_of_lt ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hm := one_le_enorm k hk
    have hm2 : 1 ≤ Lattice.enorm k ^ 2 := by nlinarith
    simp only [hG, hk, ite_false]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _),
      abs_of_pos (Real.exp_pos _)]
    have := exp_le_large ht1 hm2
    have hc := abs_cosMode_le k x
    calc t ^ (a - 1) * (Real.exp (-t * Lattice.enorm k ^ 2) * |Torus.cosMode k x|)
        ≤ t ^ (a - 1) * (Real.exp (-t * Lattice.enorm k ^ 2) * 1) := by gcongr
      _ ≤ t ^ (a - 1) * (Real.exp (-Lattice.enorm k ^ 2 / 2) * Real.exp (-t / 2)) := by
          rw [mul_one]; gcongr
      _ = _ := by ring
  have hGint : ∀ k, Integrable (G k) (volume.restrict (Ioi (1:ℝ))) := by
    intro k
    by_cases hk : k = 0
    · have : G k = fun _ => 0 := by funext t; simp [hG, hk]
      rw [this]; exact integrable_zero _ _ _
    · refine Integrable.mono' ((integrable_gamma_half ha).const_mul (Real.exp (-Lattice.enorm k ^ 2 / 2))) ?_ ?_
      · refine Measurable.aestronglyMeasurable ?_
        simp only [hG, hk, ite_false]
        fun_prop
      · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => hbd k hk t ht)
  have hGsum : Summable fun k => ∫ t, ‖G k t‖ ∂(volume.restrict (Ioi (1:ℝ))) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) (fun k => ?_)
      ((summable_gauss_lattice d (1/2) (by norm_num)).mul_left c3)
    by_cases hk : k = 0
    · have : ∀ t, ‖G k t‖ = 0 := fun t => by simp [hG, hk]
      simp only [this, integral_zero]
      exact mul_nonneg hc3_0 (Real.exp_pos _).le
    · calc ∫ t, ‖G k t‖ ∂(volume.restrict (Ioi (1:ℝ)))
          ≤ ∫ t in Ioi (1:ℝ), Real.exp (-Lattice.enorm k ^ 2 / 2) * (t ^ (a - 1) * Real.exp (-t / 2)) :=
            setIntegral_mono_on (hGint k).norm ((integrable_gamma_half ha).const_mul _)
              measurableSet_Ioi (fun t ht => hbd k hk t ht)
        _ = _ := by
            rw [integral_const_mul]
            have : -(1/2:ℝ) * Lattice.enorm k ^ 2 = -Lattice.enorm k ^ 2 / 2 := by ring
            rw [this]; ring
  have hsw := integral_tsum_of_summable_integral_norm hGint hGsum
  have hpt : ∀ t : ℝ, ∑' k, G k t = t ^ (a - 1) * psiFn x t := by
    intro t
    simp only [hG, psiFn]
    rw [tsum_mul_left]
  have hk : ∀ k, subA d s * ∫ t, G k t ∂(volume.restrict (Ioi (1:ℝ))) = coefF2 d s k * Torus.cosMode k x := by
    intro k
    by_cases hk0 : k = 0
    · have : G k = fun _ => 0 := by funext t; simp [hG, hk0]
      rw [this]; simp [coefF2, hk0]
    · simp only [coefF2, hk0, ite_false]
      have : ∀ t, G k t = (t ^ (a - 1) * Real.exp (-t * Lattice.enorm k ^ 2)) * Torus.cosMode k x := by
        intro t; simp only [hG, hk0, ite_false]; ring
      simp_rw [this]
      rw [integral_mul_const]; ring
  simp_rw [hpt] at hsw
  rw [← hsw, ← tsum_mul_left]
  exact tsum_congr hk


theorem norm_iteratedFDeriv_c_cos (c : ℝ) (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (fun s => c * Real.cos s) t‖ ≤ |c| := by
  have h1 : (fun s => c * Real.cos s) = c • Real.cos := by funext s; simp
  rw [h1, iteratedFDeriv_const_smul_apply Real.contDiff_cos.contDiffAt, norm_smul,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |c| * |iteratedDeriv i Real.cos t| ≤ |c| * 1 := by
        gcongr; exact Real.abs_iteratedDeriv_cos_le_one i t
    _ = |c| := mul_one _

theorem enorm_pow_gauss_bound (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ e : ℝ, 0 ≤ e →
    e ^ n * Real.exp (-e ^ 2 / 2) ≤ M * Real.exp (-(1/4) * e ^ 2) := by
  refine ⟨1 + (n.factorial : ℝ) / (1/4) ^ n, by positivity, fun e he => ?_⟩
  have h1 : e ^ n ≤ 1 + (e ^ 2) ^ n := by
    rcases le_total e 1 with h | h
    · have : e ^ n ≤ 1 := pow_le_one₀ he h
      have : 0 ≤ (e ^ 2) ^ n := by positivity
      linarith
    · have : e ^ n ≤ (e ^ 2) ^ n := by
        rw [← pow_mul]; exact pow_le_pow_right₀ h (by omega)
      linarith
  have h2 := pow_exp_bound (1/4) (by norm_num) n (e ^ 2) (by positivity)
  have h3 : Real.exp (-e ^ 2 / 2) = Real.exp (-(1/4) * e ^ 2) * Real.exp (-(1/4) * e ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-(1/4) * e ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg e]
  have h5 : Real.exp (-(1/4) * e ^ 2) = Real.exp (-((1/4) * e ^ 2)) := by congr 1; ring
  rw [h3]
  have hp := Real.exp_pos (-(1/4) * e ^ 2)
  calc e ^ n * (Real.exp (-(1/4) * e ^ 2) * Real.exp (-(1/4) * e ^ 2))
      = (e ^ n * Real.exp (-(1/4) * e ^ 2)) * Real.exp (-(1/4) * e ^ 2) := by ring
    _ ≤ ((1 + (e ^ 2) ^ n) * Real.exp (-(1/4) * e ^ 2)) * Real.exp (-(1/4) * e ^ 2) := by gcongr
    _ = ((Real.exp (-(1/4) * e ^ 2) + (e ^ 2) ^ n * Real.exp (-((1/4) * e ^ 2)))) * Real.exp (-(1/4) * e ^ 2) := by
        rw [h5]; ring
    _ ≤ (1 + (n.factorial : ℝ) / (1/4) ^ n) * Real.exp (-(1/4) * e ^ 2) := by
        gcongr

theorem contDiff_F2 {d : ℕ} {s : ℝ} (hsd : s < d) :
    ContDiff ℝ ∞' (fun x : Euc d => ∑' k : Lattice d, coefF2 d s k * Torus.cosMode k (Torus.mk x)) := by
  obtain ⟨C, hC0, hC⟩ := coefF2_bound hsd
  have hterm : ∀ k : Lattice d, (fun x : Euc d => coefF2 d s k * Torus.cosMode k (Torus.mk x)) =
      (fun u : ℝ => coefF2 d s k * Real.cos u) ∘ Torus.freqFunctional k := by
    intro k; funext x
    simp [Torus.cosMode_mk, Torus.freqFunctional_apply]
  set v : ℕ → Lattice d → ℝ := fun n k => C * Real.exp (-Lattice.enorm k ^ 2 / 2) * (2 * π * Lattice.enorm k) ^ n
    with hv
  refine contDiff_tsum (v := v) (fun k => ?_) (fun n _ => ?_) (fun n k x _ => ?_)
  · rw [hterm k]
    exact ((contDiff_const.mul Real.contDiff_cos).comp (Torus.freqFunctional k).contDiff).of_le le_top
  · obtain ⟨M, hM0, hM⟩ := enorm_pow_gauss_bound n
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      ((summable_gauss_lattice d (1/4) (by norm_num)).mul_left (C * (2 * π) ^ n * M))
    · have he : 0 ≤ Lattice.enorm k := norm_nonneg _
      simp only [hv]; positivity
    · have he : 0 ≤ Lattice.enorm k := norm_nonneg _
      have := hM _ he
      simp only [hv]
      calc C * Real.exp (-Lattice.enorm k ^ 2 / 2) * (2 * π * Lattice.enorm k) ^ n
          = C * (2 * π) ^ n * (Lattice.enorm k ^ n * Real.exp (-Lattice.enorm k ^ 2 / 2)) := by
            rw [mul_pow]; ring
        _ ≤ C * (2 * π) ^ n * (M * Real.exp (-(1/4) * Lattice.enorm k ^ 2)) := by gcongr
        _ = _ := by ring
  · rw [hterm k]
    have hcd : ContDiff ℝ ⊤ (fun u : ℝ => coefF2 d s k * Real.cos u) := contDiff_const.mul Real.contDiff_cos
    refine (Torus.norm_iteratedFDeriv_comp_functional (fun u : ℝ => coefF2 d s k * Real.cos u)
      hcd |coefF2 d s k| (fun i t => norm_iteratedFDeriv_c_cos _ i t) _ n x).trans ?_
    have h1 : ‖Torus.freqFunctional k‖ ^ n ≤ (2 * π * Lattice.enorm k) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (Torus.norm_freqFunctional_le k) n
    have h2 := hC k
    show _ ≤ C * Real.exp (-Lattice.enorm k ^ 2 / 2) * (2 * π * Lattice.enorm k) ^ n
    exact mul_le_mul h2 h1 (by positivity) (by positivity)



theorem integral_Ici_one_inv (g : ℝ → ℝ) :
    ∫ v in Ici (1:ℝ), g v = ∫ t in Ioc (0:ℝ) 1, (t ^ 2)⁻¹ * g t⁻¹ := by
  have himg : (fun t : ℝ => t⁻¹) '' Ioc 0 1 = Ici 1 := by
    ext v
    simp only [mem_image, mem_Ioc, mem_Ici]
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      exact (one_le_inv₀ ht0).mpr ht1
    · intro hv
      have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
      exact ⟨v⁻¹, ⟨inv_pos.mpr hv0, inv_le_one_of_one_le₀ hv⟩, inv_inv v⟩
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun t : ℝ => t⁻¹)
    (f' := fun t => -(t ^ 2)⁻¹) (s := Ioc 0 1) measurableSet_Ioc
    (fun x hx => (hasDerivAt_inv hx.1.ne').hasDerivWithinAt) inv_injective.injOn g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  simp [abs_neg, abs_of_pos (inv_pos.mpr (pow_pos ht.1 2))]

theorem Wfun_eq_Ici (s w : ℝ) :
    Wfun s w = ∫ v in Ici (1:ℝ), v ^ (s/2 - 1) * Real.exp (-(w * v)) := by
  rw [integral_Ici_one_inv]
  unfold Wfun
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have ht0 := ht.1
  rw [Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le, ← mul_assoc]
  congr 1
  · rw [← Real.rpow_natCast, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]
    congr 1; push_cast; ring
  · congr 1; rw [div_eq_mul_inv]; ring


/-! ### `H_p(w) = ∫_0^1 v^p e^{-wv} dv`, entire in `w` -/

def Hp (p w : ℝ) : ℝ := ∫ v in Ioc (0:ℝ) 1, v ^ p * Real.exp (-(w * v))

def Hmeas (p : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (0:ℝ) 1)).withDensity (fun v => ENNReal.ofReal (v ^ p))

theorem integrableOn_pow_Ioc {p : ℝ} (hp : -1 < p) : IntegrableOn (fun v : ℝ => v ^ p) (Ioc 0 1) := by
  have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := p) hp)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this

theorem integrableOn_Hp_integrand {p : ℝ} (hp : -1 < p) (w : ℝ) :
    IntegrableOn (fun v : ℝ => v ^ p * Real.exp (-(w * v))) (Ioc 0 1) := by
  refine Integrable.mono' ((integrableOn_pow_Ioc hp).mul_const (Real.exp |w|)) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hv.1 _), abs_of_pos (Real.exp_pos _)]
    have : |w * v| ≤ |w| := by
      rw [abs_mul, abs_of_pos hv.1]
      nlinarith [abs_nonneg w, hv.2, hv.1]
    have h2 : Real.exp (-(w * v)) ≤ Real.exp |w| :=
      Real.exp_le_exp.mpr (by linarith [neg_le_abs (w * v)])
    have := Real.rpow_pos_of_pos hv.1 p
    exact mul_le_mul_of_nonneg_left h2 this.le

theorem Hp_eq_mgf (p w : ℝ) :
    Hp p w = ProbabilityTheory.mgf (fun v : ℝ => -v) (Hmeas p) w := by
  unfold Hp ProbabilityTheory.mgf Hmeas
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ht.1 _).le, smul_eq_mul]
  congr 2
  ring

theorem univ_subset_integrableExpSet_H {p : ℝ} (hp : -1 < p) :
    (univ : Set ℝ) ⊆ interior (ProbabilityTheory.integrableExpSet (fun v : ℝ => -v) (Hmeas p)) := by
  refine isOpen_univ.subset_interior_iff.mpr fun θ _ => ?_
  show Integrable (fun v : ℝ => Real.exp (θ * (-v))) (Hmeas p)
  unfold Hmeas
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (integrableOn_Hp_integrand hp θ).congr_fun_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ht.1 _).le, smul_eq_mul]
  congr 2; ring

theorem contDiff_Hp {p : ℝ} (hp : -1 < p) : ContDiff ℝ ∞' (Hp p) := by
  have h1 : Hp p = ProbabilityTheory.mgf (fun v : ℝ => -v) (Hmeas p) := funext (Hp_eq_mgf p)
  rw [h1]
  have := (ProbabilityTheory.analyticOn_mgf (X := fun v : ℝ => -v) (μ := Hmeas p)).mono
    (univ_subset_integrableExpSet_H hp)
  rw [← contDiffOn_univ]
  exact (this.contDiffOn uniqueDiffOn_univ).of_le (by exact_mod_cast le_top)


theorem integrableOn_gamma_w {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    IntegrableOn (fun v : ℝ => v ^ (a - 1) * Real.exp (-(w * v))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := w)
    (by linarith) one_pos hw
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  congr 2; ring

theorem Wfun_pos_eq {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    Wfun s w = Real.Gamma (s/2) * w ^ (-(s/2)) - Hp (s/2 - 1) w := by
  have ha : 0 < s/2 := by linarith
  have hint := integrableOn_gamma_w ha hw
  have h1 : ∫ v in Ioi (0:ℝ), v ^ (s/2 - 1) * Real.exp (-(w * v)) =
      Real.Gamma (s/2) * w ^ (-(s/2)) := by
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hw, one_div, Real.inv_rpow hw.le,
      ← Real.rpow_neg hw.le, mul_comm]
  have hsplit : ∫ v in Ioi (0:ℝ), v ^ (s/2 - 1) * Real.exp (-(w * v)) =
      (∫ v in Ioc (0:ℝ) 1, v ^ (s/2 - 1) * Real.exp (-(w * v))) +
      ∫ v in Ioi (1:ℝ), v ^ (s/2 - 1) * Real.exp (-(w * v)) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ?_ ?_
    · exact hint.mono_set (Ioc_subset_Ioi_self)
    · exact hint.mono_set (Ioi_subset_Ioi zero_le_one)
  rw [Wfun_eq_Ici, integral_Ici_eq_integral_Ioi, Hp]
  linarith


theorem hasDerivAt_Wfun_zero {w : ℝ} (hw : 0 < w) :
    HasDerivAt (Wfun 0) (-(Real.exp (-w) / w)) w := by
  have hd : DifferentiableAt ℝ (Wfun 0) w :=
    ((contDiffOn_Wfun 0 le_rfl).differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hw)
  have h := hd.hasDerivAt
  have e1 : deriv (Wfun 0) w = -(Real.exp (-w) / w) := by
    rw [← iteratedDeriv_one, iteratedDeriv_Wfun 0 le_rfl 1 hw]
    have e2 : ∀ t ∈ Ioc (0:ℝ) 1, t ^ (-(0:ℝ)/2 - 1) * ((-1/t) ^ 1 * Real.exp (-w / t)) =
        -((t ^ 2)⁻¹ * Real.exp (-(w * t⁻¹))) := by
      intro t ht
      have ht0 := ht.1
      have : t ^ (-(0:ℝ)/2 - 1) = t⁻¹ := by
        rw [show -(0:ℝ)/2 - 1 = -1 by norm_num, Real.rpow_neg_one]
      rw [this]
      have : -w / t = -(w * t⁻¹) := by rw [div_eq_mul_inv]; ring
      rw [this]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioc e2, integral_neg,
      ← integral_Ici_one_inv (fun v => Real.exp (-(w * v))), integral_Ici_eq_integral_Ioi]
    have := integral_exp_mul_Ioi (a := -w) (by linarith) 1
    simp only [neg_mul] at this
    rw [this]
    simp only [mul_one]
    rw [neg_div_neg_eq]
  rw [e1] at h
  exact h


theorem Hp_zero_pos {w : ℝ} (hw : 0 < w) : Hp 0 w = (1 - Real.exp (-w)) / w := by
  unfold Hp
  simp only [Real.rpow_zero, one_mul]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have : ∀ v : ℝ, Real.exp (-(w * v)) = Real.exp ((-w) * v) := fun v => by rw [neg_mul]
  simp_rw [this]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (by linarith : -w ≠ 0)]
  simp only [integral_exp, smul_eq_mul, mul_one, mul_zero, Real.exp_zero]
  field_simp
  ring

def Phi (w : ℝ) : ℝ := ∫ u in (0:ℝ)..w, Hp 0 u

theorem hasDerivAt_Phi (w : ℝ) : HasDerivAt Phi (Hp 0 w) w :=
  ((contDiff_Hp (p := 0) (by norm_num)).continuous.integral_hasStrictDerivAt 0 w).hasDerivAt

theorem contDiff_Phi : ContDiff ℝ ∞' Phi := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun w => (hasDerivAt_Phi w).differentiableAt, ?_⟩
  have : deriv Phi = Hp 0 := funext fun w => (hasDerivAt_Phi w).deriv
  rw [this]
  exact contDiff_Hp (by norm_num)

theorem Wfun_zero_eq : ∃ S : ℝ → ℝ, ContDiff ℝ ∞' S ∧ ∀ w, 0 < w → Wfun 0 w = -Real.log w + S w := by
  set D : ℝ → ℝ := fun w => Wfun 0 w + Real.log w - Phi w with hD
  have hder : ∀ w ∈ Ioi (0:ℝ), HasDerivAt D 0 w := by
    intro w hw
    have hw' : 0 < w := hw
    have h1 := ((hasDerivAt_Wfun_zero hw').add (Real.hasDerivAt_log hw'.ne')).sub (hasDerivAt_Phi w)
    convert h1 using 1
    rw [Hp_zero_pos hw']
    field_simp
    ring
  have hconst : ∀ w ∈ Ioi (0:ℝ), D w = D 1 := by
    intro w hw
    refine isOpen_Ioi.is_const_of_deriv_eq_zero (isPreconnected_Ioi) ?_ ?_ hw (by simp : (1:ℝ) ∈ Ioi 0)
    · exact fun x hx => (hder x hx).differentiableAt.differentiableWithinAt
    · exact fun x hx => (hder x hx).deriv
  refine ⟨fun w => Phi w + D 1, contDiff_Phi.add contDiff_const, fun w hw => ?_⟩
  have := hconst w hw
  simp only [hD] at this
  linarith


/-! ### Globalised `W` -/

def thetaCut (w : ℝ) : ℝ := Real.smoothTransition (4 * w - 1)

theorem contDiff_thetaCut : ContDiff ℝ ∞' thetaCut :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem thetaCut_eq_one {w : ℝ} (hw : 1/2 ≤ w) : thetaCut w = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem thetaCut_eq_zero {w : ℝ} (hw : w ≤ 1/4) : thetaCut w = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

def Wt (s w : ℝ) : ℝ := thetaCut w * Wfun s w

theorem contDiff_Wt (s : ℝ) (hs : 0 ≤ s) : ContDiff ℝ ∞' (Wt s) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : 0 < w
  · exact contDiff_thetaCut.contDiffAt.mul ((contDiffOn_Wfun s hs).contDiffAt (Ioi_mem_nhds hw))
  · have : Wt s =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show w < 1/4 by linarith)] with v hv
      simp [Wt, thetaCut_eq_zero (le_of_lt hv)]
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem Wt_eventuallyEq {s w : ℝ} (hw : 1/2 < w) : Wt s =ᶠ[𝓝 w] Wfun s := by
  filter_upwards [Ioi_mem_nhds hw] with v hv
  simp [Wt, thetaCut_eq_one hv.le]

theorem Wt_deriv_bound (s : ℝ) (hs : 0 ≤ s) (i : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℝ, 1 ≤ w → ‖iteratedFDeriv ℝ i (Wt s) w‖ ≤ B * Real.exp (-w / 2) := by
  obtain ⟨B, hB0, hB⟩ := W_deriv_bound s hs i
  refine ⟨B, hB0, fun w hw => ?_⟩
  have h1 : iteratedFDeriv ℝ i (Wt s) w = iteratedFDeriv ℝ i (Wfun s) w :=
    ((Wt_eventuallyEq (s := s) (by linarith)).iteratedFDeriv ℝ i).self_of_nhds
  rw [h1, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact hB w hw


/-! ### The quadratic `q_m` and its derivative bounds -/

def qm {d : ℕ} (m : Lattice d) (x : Euc d) : ℝ := π ^ 2 * ‖x - Lattice.toEuc m‖ ^ 2

theorem norm_iteratedFDeriv_sub_const_le {d : ℕ} (c : Euc d) (i : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (fun y : Euc d => y - c) x‖ ≤ 1 + ‖x - c‖ := by
  cases i with
  | zero =>
    rw [norm_iteratedFDeriv_zero]; linarith
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have : fderiv ℝ (fun y : Euc d => y - c) = fun _ => ContinuousLinearMap.id ℝ (Euc d) := by
      funext y; rw [fderiv_sub_const, fderiv_fun_id]
    rw [this]
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Euc d)
      linarith [norm_nonneg (x - c)]
    | succ j =>
      rw [iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iteratedFDeriv_qm_le {d : ℕ} (m : Lattice d) (n : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (qm m) x‖ ≤ π ^ 2 * 2 ^ n * (1 + ‖x - Lattice.toEuc m‖) ^ 2 := by
  set B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ := (π ^ 2) • (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) with hB
  have hq : qm m = fun y => B (y - Lattice.toEuc m) (y - Lattice.toEuc m) := by
    funext y
    simp only [qm, B, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  have hf : ContDiff ℝ ∞' (fun y : Euc d => y - Lattice.toEuc m) := contDiff_id.sub contDiff_const
  rw [hq]
  have h1 := B.norm_iteratedFDeriv_le_of_bilinear hf hf x (n := n) (by exact_mod_cast le_top)
  have hBn : ‖B‖ ≤ π ^ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hB]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
    rw [innerSL_apply_apply, abs_of_nonneg (by positivity : (0:ℝ) ≤ π^2), mul_assoc]
    gcongr
    exact abs_real_inner_le_norm u v
  set R := 1 + ‖x - Lattice.toEuc m‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : Euc d => y - Lattice.toEuc m) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : Euc d => y - Lattice.toEuc m) x‖ ≤ 2 ^ n * R ^ 2 := by
    calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (R * R) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mul_assoc]
          gcongr
          · exact norm_iteratedFDeriv_sub_const_le _ _ _
          · exact norm_iteratedFDeriv_sub_const_le _ _ _
      _ = 2 ^ n * R ^ 2 := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast; ring
  calc _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : Euc d => y - Lattice.toEuc m) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : Euc d => y - Lattice.toEuc m) x‖ := h1
    _ ≤ π ^ 2 * (2 ^ n * R ^ 2) := by gcongr
    _ = _ := by ring


/-! ### The cutoff `χ` -/

def bump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1/16, 1/8, by norm_num, by norm_num⟩

def chi (d : ℕ) : Euc d → ℝ := fun x => bump d x

theorem contDiff_chi {d : ℕ} : ContDiff ℝ ∞' (chi d) := (bump d).contDiff

theorem chi_one {d : ℕ} {x : Euc d} (hx : ‖x‖ ≤ 1/16) : chi d x = 1 :=
  (bump d).one_of_mem_closedBall (by simpa [bump] using hx)

theorem chi_zero {d : ℕ} {x : Euc d} (hx : 1/8 ≤ ‖x‖) : chi d x = 0 :=
  (bump d).zero_of_le_dist (by simpa [bump] using hx)

theorem iteratedFDeriv_chi_mul_eq_zero {d : ℕ} (G : Euc d → ℝ) {x : Euc d} (hx : 1/8 < ‖x‖) (i : ℕ) :
    iteratedFDeriv ℝ i (fun y => chi d y * G y) x = 0 := by
  have h : (fun y => chi d y * G y) =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    have : {y : Euc d | 1/8 < ‖y‖} ∈ 𝓝 x :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hx
    filter_upwards [this] with y hy
    simp [chi_zero (le_of_lt hy)]
  rw [(h.iteratedFDeriv ℝ i).self_of_nhds]
  simp

theorem chi_deriv_bound {d : ℕ} (i : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ i (chi d) x‖ ≤ M := by
  have : BddAbove (range fun x => ‖iteratedFDeriv ℝ i (chi d) x‖) := by
    apply ((contDiff_chi (d := d)).continuous_iteratedFDeriv
      (mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
    apply HasCompactSupport.comp_left _ norm_zero
    exact ((bump d).hasCompactSupport).iteratedFDeriv i
  obtain ⟨M, hM⟩ := this
  exact ⟨max M 0, le_max_right _ _, fun x => (hM (mem_range_self x)).trans (le_max_left _ _)⟩

/-! ### Derivative bounds for the image terms -/

theorem image_comp_bound {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : Lattice d, m ≠ 0 → ∀ x : Euc d, ‖x‖ ≤ 1/4 → ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j (fun y => Wt s (qm m y)) x‖ ≤
        K * (Lattice.enorm m ^ (2 * n) * Real.exp (-2 * Lattice.enorm m ^ 2)) := by
  choose B hB0 hB using Wt_deriv_bound s hs
  set BS := ∑ i ∈ Finset.range (n + 1), B i with hBS
  have hBS0 : 0 ≤ BS := Finset.sum_nonneg fun i _ => hB0 i
  have hπ : (9:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  refine ⟨(n.factorial : ℝ) * BS * (18 * π ^ 2) ^ n, by positivity, fun m hm x hx j hj => ?_⟩
  set e := Lattice.enorm m with he
  have he1 : 1 ≤ e := one_le_enorm m hm
  set w := qm m x with hw
  set R := 1 + ‖x - Lattice.toEuc m‖ with hR
  have hdist1 : e - 1/4 ≤ ‖x - Lattice.toEuc m‖ := by
    have := norm_sub_norm_le (Lattice.toEuc m) x
    rw [norm_sub_rev] at this
    have : e = ‖Lattice.toEuc m‖ := rfl
    linarith
  have hdist2 : ‖x - Lattice.toEuc m‖ ≤ e + 1/4 := by
    have := norm_sub_le x (Lattice.toEuc m)
    have : e = ‖Lattice.toEuc m‖ := rfl
    linarith
  have hw4 : 4 * e ^ 2 ≤ w := by
    have h1 : 3/4 * e ≤ ‖x - Lattice.toEuc m‖ := by linarith
    have h2 : (3/4 * e) ^ 2 ≤ ‖x - Lattice.toEuc m‖ ^ 2 := by gcongr
    simp only [hw, qm]
    nlinarith
  have hw1 : 1 ≤ w := by nlinarith
  have hR1 : 1 ≤ R := by simp only [hR]; linarith [norm_nonneg (x - Lattice.toEuc m)]
  have hR3 : R ≤ 3 * e := by simp only [hR]; linarith
  -- Faa di Bruno
  have hC : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i (Wt s) (qm m x)‖ ≤ BS * Real.exp (-w / 2) := by
    intro i hi
    refine (hB i w hw1).trans ?_
    gcongr
    exact Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_range.mpr (by omega))
  have hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i (qm m) x‖ ≤ (2 * π ^ 2 * R ^ 2) ^ i := by
    intro i hi _
    have h1 : 1 ≤ π ^ 2 * R ^ 2 := by nlinarith
    have h2 : π ^ 2 * 2 ^ i * R ^ 2 ≤ (2 * π ^ 2 * R ^ 2) ^ i := by
      rw [show 2 * π ^ 2 * R ^ 2 = 2 * (π ^ 2 * R ^ 2) by ring, mul_pow]
      calc π ^ 2 * 2 ^ i * R ^ 2 = 2 ^ i * (π ^ 2 * R ^ 2) := by ring
        _ ≤ 2 ^ i * (π ^ 2 * R ^ 2) ^ i := by gcongr; exact le_self_pow₀ h1 (by omega)
    exact (norm_iteratedFDeriv_qm_le m i x).trans h2
  have hqm : ContDiff ℝ ∞' (qm m) := by
    unfold qm
    exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hFB := norm_iteratedFDeriv_comp_le (contDiff_Wt s hs) hqm (n := j) (by exact_mod_cast le_top) x hC hD
  refine (le_of_eq_of_le rfl hFB).trans ?_
  have hexp : Real.exp (-w / 2) ≤ Real.exp (-2 * e ^ 2) := by
    rw [Real.exp_le_exp]; linarith
  have hpow : (2 * π ^ 2 * R ^ 2) ^ j ≤ (18 * π ^ 2) ^ n * e ^ (2 * n) := by
    have hb : 1 ≤ 18 * π ^ 2 * e ^ 2 := by nlinarith
    have hR9 : R ^ 2 ≤ 9 * e ^ 2 := by nlinarith
    have hbase : 2 * π ^ 2 * R ^ 2 ≤ 18 * π ^ 2 * e ^ 2 := by
      calc 2 * π ^ 2 * R ^ 2 ≤ 2 * π ^ 2 * (9 * e ^ 2) := by gcongr
        _ = 18 * π ^ 2 * e ^ 2 := by ring
    calc (2 * π ^ 2 * R ^ 2) ^ j ≤ (18 * π ^ 2 * e ^ 2) ^ j :=
          pow_le_pow_left₀ (by positivity) hbase j
      _ ≤ (18 * π ^ 2 * e ^ 2) ^ n := pow_le_pow_right₀ hb hj
      _ = (18 * π ^ 2) ^ n * e ^ (2 * n) := by rw [mul_pow, pow_mul]
  have hfact : (j.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hj
  calc (j.factorial : ℝ) * (BS * Real.exp (-w / 2)) * (2 * π ^ 2 * R ^ 2) ^ j
      ≤ (n.factorial : ℝ) * (BS * Real.exp (-2 * e ^ 2)) * ((18 * π ^ 2) ^ n * e ^ (2 * n)) := by
        gcongr
    _ = _ := by ring


theorem image_term_bound {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : Lattice d, m ≠ 0 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ n (fun y => chi d y * Wt s (qm m y)) x‖ ≤
        K * (Lattice.enorm m ^ (2 * n) * Real.exp (-2 * Lattice.enorm m ^ 2)) := by
  obtain ⟨K, hK0, hK⟩ := image_comp_bound (d := d) hs n
  choose M hM0 hM using fun i => chi_deriv_bound (d := d) i
  set MS := ∑ i ∈ Finset.range (n + 1), M i with hMS
  have hMS0 : 0 ≤ MS := Finset.sum_nonneg fun i _ => hM0 i
  refine ⟨2 ^ n * MS * K, by positivity, fun m hm x => ?_⟩
  set E := Lattice.enorm m ^ (2 * n) * Real.exp (-2 * Lattice.enorm m ^ 2) with hE
  have hE0 : 0 ≤ E := by
    have : 0 ≤ Lattice.enorm m := norm_nonneg _
    positivity
  by_cases hx : 1/8 < ‖x‖
  · rw [iteratedFDeriv_chi_mul_eq_zero _ hx, norm_zero]
    positivity
  · push Not at hx
    have hx4 : ‖x‖ ≤ 1/4 := by linarith
    have hqm : ContDiff ℝ ∞' (qm m) := by
      unfold qm
      exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
    have hG : ContDiff ℝ ∞' (fun y => Wt s (qm m y)) := (contDiff_Wt s hs).comp hqm
    refine (norm_iteratedFDeriv_mul_le contDiff_chi hG x (n := n) (by exact_mod_cast le_top)).trans ?_
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (chi d) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => Wt s (qm m y)) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * MS * (K * E) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          gcongr
          · exact (hM i x).trans (Finset.single_le_sum (f := M) (fun k _ => hM0 k) hi)
          · exact hK m hm x hx4 (n - i) (Nat.sub_le n i)
      _ = 2 ^ n * MS * K * E := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast; ring

/-- the image terms (with the cutoff), indexed by all of `ℤ^d` (the `m = 0` term is `0`) -/
def Tm (d : ℕ) (s : ℝ) (m : Lattice d) (y : Euc d) : ℝ :=
  if m = 0 then 0 else chi d y * Wt s (qm m y)

theorem contDiff_images {d : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞' (fun y : Euc d => ∑' m : Lattice d, Tm d s m y) := by
  choose K hK0 hK using fun n => image_term_bound (d := d) hs n
  choose M hM0 hM using fun n => enorm_pow_gauss_bound (2 * n)
  set v : ℕ → Lattice d → ℝ := fun n m =>
    K n * (Lattice.enorm m ^ (2 * n) * Real.exp (-2 * Lattice.enorm m ^ 2)) with hv
  have hqm : ∀ m : Lattice d, ContDiff ℝ ∞' (qm m) := by
    intro m
    unfold qm
    exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  refine contDiff_tsum (v := v) (fun m => ?_) (fun n _ => ?_) (fun n m x _ => ?_)
  · by_cases hm : m = 0
    · have : Tm d s m = fun _ => 0 := by funext y; simp [Tm, hm]
      rw [this]; exact contDiff_const
    · have : Tm d s m = fun y => chi d y * Wt s (qm m y) := by funext y; simp [Tm, hm]
      rw [this]; exact contDiff_chi.mul ((contDiff_Wt s hs).comp (hqm m))
  · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      ((summable_gauss_lattice d (1/4) (by norm_num)).mul_left (K n * M n))
    · have : 0 ≤ Lattice.enorm m := norm_nonneg _
      simp only [hv]
      have := hK0 n
      positivity
    · have he : 0 ≤ Lattice.enorm m := norm_nonneg _
      have h1 := hM n _ he
      have h2 : Real.exp (-2 * Lattice.enorm m ^ 2) ≤ Real.exp (-Lattice.enorm m ^ 2 / 2) := by
        rw [Real.exp_le_exp]; nlinarith [sq_nonneg (Lattice.enorm m)]
      simp only [hv]
      calc K n * (Lattice.enorm m ^ (2 * n) * Real.exp (-2 * Lattice.enorm m ^ 2))
          ≤ K n * (Lattice.enorm m ^ (2 * n) * Real.exp (-Lattice.enorm m ^ 2 / 2)) := by
            have := hK0 n
            gcongr
        _ ≤ K n * (M n * Real.exp (-(1/4) * Lattice.enorm m ^ 2)) := by
            have := hK0 n
            gcongr
        _ = _ := by ring
  · by_cases hm : m = 0
    · have : Tm d s m = fun _ => 0 := by funext y; simp [Tm, hm]
      rw [this]
      simp only [hv]
      rw [iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply, norm_zero]
      have : 0 ≤ Lattice.enorm m := norm_nonneg _
      have := hK0 n
      positivity
    · have : Tm d s m = fun y => chi d y * Wt s (qm m y) := by funext y; simp [Tm, hm]
      rw [this]
      exact hK n m hm x


/-! ### Periodisation of a function supported near `0` -/

theorem toEuc_add {d : ℕ} (a b : Lattice d) :
    Lattice.toEuc (a + b) = Lattice.toEuc a + Lattice.toEuc b := by
  ext i; simp [Lattice.toEuc]

theorem rep_mk_eq {d : ℕ} (y : Euc d) :
    ∃ m0 : Lattice d, Torus.rep (Torus.mk y) = y + Lattice.toEuc m0 := by
  have h := Torus.mk_rep (Torus.mk y)
  have : ∀ i, ∃ n : ℤ, (n : ℝ) = Torus.rep (Torus.mk y) i - y i := by
    intro i
    have hi := congrFun h i
    simp only [Torus.mk] at hi
    have : ((Torus.rep (Torus.mk y) i - y i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hi, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp this
    exact ⟨n, by simpa using hn⟩
  choose m0 hm0 using this
  refine ⟨m0, ?_⟩
  ext i
  simp [Lattice.toEuc, hm0]

theorem finite_near {d : ℕ} (y0 : Euc d) :
    {n : Lattice d | ‖y0 + Lattice.toEuc n‖ < 1/4}.Finite := by
  have h := Filter.eventually_cofinite.mp (eventually_one_le_wsq (d := d) (fun i => -y0 i))
  refine h.subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro h1
  have hw : wsq (fun i => -y0 i) n = ‖y0 + Lattice.toEuc n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    unfold wsq
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Lattice.toEuc, Real.norm_eq_abs, sq_abs]
    ring
  rw [hw] at h1
  have : ‖y0 + Lattice.toEuc n‖ ^ 2 < 1/16 := by
    have h0 := norm_nonneg (y0 + Lattice.toEuc n)
    nlinarith
  have hπ : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  nlinarith [sq_nonneg ‖y0 + Lattice.toEuc n‖]

/-- periodisation `P f (y) = ∑_n f(y + n)` -/
def perz {d : ℕ} (f : Euc d → ℝ) (y : Euc d) : ℝ := ∑' n : Lattice d, f (y + Lattice.toEuc n)

theorem contDiff_perz {d : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ ∞' f)
    (hsupp : ∀ y, 1/8 ≤ ‖y‖ → f y = 0) : ContDiff ℝ ∞' (perz f) := by
  rw [contDiff_iff_contDiffAt]
  intro y0
  set S := (finite_near y0).toFinset with hS
  have heq : perz f =ᶠ[𝓝 y0] fun y => ∑ n ∈ S, f (y + Lattice.toEuc n) := by
    filter_upwards [Metric.ball_mem_nhds y0 (by norm_num : (0:ℝ) < 1/8)] with y hy
    unfold perz
    refine tsum_eq_sum fun n hn => hsupp _ ?_
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hn
    have h1 : dist y y0 < 1/8 := hy
    rw [dist_eq_norm] at h1
    have : y0 + Lattice.toEuc n = (y + Lattice.toEuc n) - (y - y0) := by abel
    have h2 := norm_sub_le (y + Lattice.toEuc n) (y - y0)
    rw [← this] at h2
    linarith
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  refine ContDiff.contDiffAt ?_
  exact ContDiff.sum fun n _ => hf.comp (contDiff_id.add contDiff_const)

theorem perz_eq {d : ℕ} {f : Euc d → ℝ} (hsupp : ∀ y, 1/8 ≤ ‖y‖ → f y = 0) {x : Euc d}
    (hx : ‖x‖ < 1/2) : perz f x = f x := by
  unfold perz
  rw [tsum_eq_single 0]
  · have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    rw [this, add_zero]
  · intro n hn
    refine hsupp _ ?_
    have h1 := one_le_enorm n hn
    have h2 := norm_sub_norm_le (Lattice.toEuc n) (-x)
    have : Lattice.toEuc n - -x = x + Lattice.toEuc n := by abel
    rw [this, norm_neg] at h2
    have : Lattice.enorm n = ‖Lattice.toEuc n‖ := rfl
    linarith

theorem periodize {d : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ ∞' f)
    (hsupp : ∀ y, 1/8 ≤ ‖y‖ → f y = 0) :
    ∃ r : Torus d → ℝ, Torus.IsSmooth r ∧ ∀ x : Euc d, ‖x‖ < 1/2 → r (Torus.mk x) = f x := by
  refine ⟨fun z => perz f (Torus.rep z), ?_, ?_⟩
  · have : Torus.lift (fun z => perz f (Torus.rep z)) = perz f := by
      funext y
      obtain ⟨m0, hm0⟩ := rep_mk_eq y
      simp only [Torus.lift, Function.comp]
      rw [hm0]
      unfold perz
      rw [← (Equiv.addLeft m0).tsum_eq (fun n => f (y + Lattice.toEuc n))]
      refine tsum_congr fun n => ?_
      simp only [Equiv.coe_addLeft, toEuc_add, add_assoc]
    unfold Torus.IsSmooth Torus.IsCk
    rw [this]
    exact contDiff_perz hf hsupp
  · intro x hx
    obtain ⟨m0, hm0⟩ := rep_mk_eq x
    show perz f (Torus.rep (Torus.mk x)) = f x
    rw [hm0]
    have : perz f (x + Lattice.toEuc m0) = perz f x := by
      unfold perz
      rw [← (Equiv.addLeft m0).tsum_eq (fun n => f (x + Lattice.toEuc n))]
      refine tsum_congr fun n => ?_
      simp only [Equiv.coe_addLeft, toEuc_add, add_assoc]
    rw [this, perz_eq hsupp hx]


/-! ### Assembly of the local decomposition -/

theorem wsq_eq_qm {d : ℕ} (y : Euc d) (m : Lattice d) :
    π ^ 2 * wsq (fun i => y i) m = qm m y := by
  unfold qm wsq
  rw [EuclideanSpace.norm_sq_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Lattice.toEuc, Real.norm_eq_abs, sq_abs]
  ring

theorem decomp1 {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (y : Euc d)
    (hy : ∀ m : Lattice d, 0 < wsq (fun i => y i) m) :
    periodicRiesz d s (Torus.mk y) =
      subA d s * (π ^ ((d:ℝ)/2) * ∑' m : Lattice d, Wfun s (π^2 * wsq (fun i => y i) m)
        - 1 / (((d:ℝ) - s)/2)) +
      ∑' k : Lattice d, coefF2 d s k * Torus.cosMode k (Torus.mk y) := by
  have hmk : Torus.mk y = boxPt (fun i => y i) := rfl
  have hx0 : Torus.mk y ≠ 0 := by rw [hmk]; exact boxPt_ne_zero_of_wsq hy
  rw [periodicRiesz_eq_integral hd hs0 hsd _ hx0]
  have hint := integrableOn_psi hsd (Torus.mk y) hx0
  have hsplit : ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn (Torus.mk y) t =
      (∫ t in Ioc (0:ℝ) 1, t ^ (((d:ℝ) - s) / 2 - 1) * psiFn (Torus.mk y) t) +
      ∫ t in Ioi (1:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn (Torus.mk y) t := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [hsplit, mul_add, F2_eq hsd, hmk, int_Ioc_psi hs0 hsd _ hy]

theorem qm_ge {d : ℕ} {m : Lattice d} (hm : m ≠ 0) {y : Euc d} (hy : ‖y‖ ≤ 1/16) :
    1/2 ≤ qm m y := by
  have h1 := one_le_enorm m hm
  have h2 := norm_sub_norm_le (Lattice.toEuc m) y
  rw [norm_sub_rev] at h2
  have : Lattice.enorm m = ‖Lattice.toEuc m‖ := rfl
  have h3 : 15/16 ≤ ‖y - Lattice.toEuc m‖ := by linarith
  have hπ : (9:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  unfold qm
  nlinarith [mul_le_mul h3 h3 (by norm_num) (norm_nonneg _)]

theorem decomp2 {d : ℕ} {s : ℝ} (hs0 : 0 ≤ s) {y : Euc d} (hy : ‖y‖ ≤ 1/16) :
    ∑' m : Lattice d, Wfun s (π^2 * wsq (fun i => y i) m) =
      Wfun s (π ^ 2 * ‖y‖ ^ 2) + ∑' m : Lattice d, Tm d s m y := by
  rw [(summable_Wfun_wsq hs0 (fun i => y i)).tsum_eq_add_tsum_ite 0]
  congr 1
  · rw [wsq_eq_qm]
    have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    simp only [qm, this, sub_zero]
  · refine tsum_congr fun m => ?_
    by_cases hm : m = 0
    · simp [Tm, hm]
    · simp only [Tm, hm, if_false]
      rw [chi_one hy, one_mul, wsq_eq_qm, Wt, thetaCut_eq_one (qm_ge hm hy), one_mul]


theorem wsq_pos_small {d : ℕ} {x : Euc d} (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1/16) (m : Lattice d) :
    0 < wsq (fun i => x i) m := by
  have hπ : 0 < π ^ 2 := by positivity
  have h := wsq_eq_qm x m
  by_cases hm : m = 0
  · have h0 : Lattice.toEuc m = 0 := by ext i; simp [Lattice.toEuc, hm]
    have : 0 < qm m x := by
      unfold qm; rw [h0, sub_zero]
      have := norm_pos_iff.mpr hx0
      positivity
    rw [← h] at this
    exact pos_of_mul_pos_right this hπ.le
  · have := qm_ge hm hx
    rw [← h] at this
    exact pos_of_mul_pos_right (by linarith) hπ.le

theorem local_decomp {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (S : ℝ → ℝ) (hS : ContDiff ℝ ∞' S) (c : ℝ) (sing : ℝ → ℝ)
    (hsing : ∀ y : Euc d, y ≠ 0 → ‖y‖ ≤ 1/16 →
      subA d s * π ^ ((d:ℝ)/2) * Wfun s (π ^ 2 * ‖y‖ ^ 2) = sing ‖y‖ + S (π ^ 2 * ‖y‖ ^ 2) + c) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 → periodicRiesz d s (Torus.mk x) = sing ‖x‖ + r (Torus.mk x) := by
  set K0 := subA d s * π ^ ((d:ℝ)/2) with hK0
  set F2e : Euc d → ℝ := fun y => ∑' k : Lattice d, coefF2 d s k * Torus.cosMode k (Torus.mk y)
    with hF2e
  set f : Euc d → ℝ := fun y =>
    chi d y * (S (π ^ 2 * ‖y‖ ^ 2) + c - subA d s * (1 / (((d:ℝ) - s)/2)) + F2e y) +
      K0 * ∑' m : Lattice d, Tm d s m y with hf
  have hfC : ContDiff ℝ ∞' f := by
    have h1 : ContDiff ℝ ∞' (fun y : Euc d => S (π ^ 2 * ‖y‖ ^ 2)) :=
      hS.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
    have h2 : ContDiff ℝ ∞' F2e := contDiff_F2 hsd
    exact (contDiff_chi.mul (((h1.add contDiff_const).sub contDiff_const).add h2)).add
      (contDiff_const.mul (contDiff_images hs0))
  have hfs : ∀ y, 1/8 ≤ ‖y‖ → f y = 0 := by
    intro y hy
    have hc := chi_zero (d := d) hy
    have hT : ∀ m, Tm d s m y = 0 := fun m => by simp [Tm, hc]
    simp only [hf, hc, hT, tsum_zero, zero_mul, mul_zero, add_zero]
  obtain ⟨r, hr, hrf⟩ := periodize hfC hfs
  refine ⟨r, 1/16, by norm_num, hr, fun x hx hx0 => ?_⟩
  have hx' : ‖x‖ ≤ 1/16 := hx.le
  rw [hrf x (by linarith), decomp1 hd hs0 hsd x (wsq_pos_small hx0 hx'), decomp2 hs0 hx']
  have hsx := hsing x hx0 hx'
  simp only [hf, hF2e, chi_one hx', one_mul]
  rw [hK0] at hsx ⊢
  linear_combination hsx


theorem subA_const_pos {d : ℕ} {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    subA d s * π ^ ((d:ℝ)/2) * Real.Gamma (s/2) * π ^ (-s) = 1 := by
  have hG1 : 0 < Real.Gamma (((d:ℝ) - s) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : (2:ℝ) ^ ((d:ℝ) - s) * 2 ^ (s - d) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have hπ : π ^ ((d:ℝ)/2) * π ^ ((d:ℝ)/2) * π ^ (s - d) * π ^ (-s) = 1 := by
    rw [← Real.rpow_add Real.pi_pos, ← Real.rpow_add Real.pi_pos, ← Real.rpow_add Real.pi_pos]
    ring_nf; simp
  unfold subA rieszConst
  rw [if_neg (ne_of_gt hs), Real.mul_rpow (by norm_num) Real.pi_pos.le]
  field_simp
  linear_combination (π ^ ((d:ℝ)/2) * π ^ ((d:ℝ)/2) * π ^ (s - d) * π ^ (-s)) * h2 + hπ

theorem subA_const_zero {d : ℕ} (hd : 0 < d) :
    subA d 0 * π ^ ((d:ℝ)/2) = 1/2 := by
  have hG : 0 < Real.Gamma ((d:ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : (2:ℝ) ^ ((d:ℝ) - 1) * 2 ^ ((0:ℝ) - d) = 1/2 := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf; rw [Real.rpow_neg_one]; norm_num
  have hπ : π ^ ((d:ℝ)/2) * π ^ ((0:ℝ) - d) * π ^ ((d:ℝ)/2) = 1 := by
    rw [← Real.rpow_add Real.pi_pos, ← Real.rpow_add Real.pi_pos]
    ring_nf; simp
  unfold subA rieszConst
  rw [if_pos rfl, Real.mul_rpow (by norm_num) Real.pi_pos.le, sub_zero]
  field_simp
  linear_combination 2 * (π ^ ((d:ℝ)/2) * π ^ ((0:ℝ) - d) * π ^ ((d:ℝ)/2)) * h2 + hπ


theorem periodicRiesz_local_singularity' {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d s (Torus.mk x) = ‖x‖ ^ (-s) + r (Torus.mk x) := by
  set K0 := subA d s * π ^ ((d:ℝ)/2) with hK0
  refine local_decomp hd hs0.le hsd (fun w => -(K0 * Hp (s/2 - 1) w))
    (contDiff_const.mul (contDiff_Hp (by linarith))).neg 0 (fun r => r ^ (-s)) ?_
  intro y hy0 _
  have hy : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hw : 0 < π ^ 2 * ‖y‖ ^ 2 := by positivity
  rw [Wfun_pos_eq hs0 hw]
  have hpow : (π ^ 2 * ‖y‖ ^ 2) ^ (-(s/2)) = π ^ (-s) * ‖y‖ ^ (-s) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul hy.le]
    congr 2 <;> push_cast <;> ring
  rw [hpow]
  have hc := subA_const_pos hs0 hsd
  rw [← hK0] at hc
  linear_combination ‖y‖ ^ (-s) * hc

theorem periodicLog_local_singularity' {d : ℕ} (hd : 2 ≤ d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d 0 (Torus.mk x) = -Real.log ‖x‖ + r (Torus.mk x) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨S0, hS0, hW⟩ := Wfun_zero_eq
  refine local_decomp hd le_rfl hd0 (fun w => (1/2) * S0 w) (contDiff_const.mul hS0)
    (-Real.log π) (fun r => -Real.log r) ?_
  intro y hy0 _
  have hy : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hw : 0 < π ^ 2 * ‖y‖ ^ 2 := by positivity
  rw [hW _ hw, subA_const_zero (by omega),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring



theorem theta_deriv_eq (u y : ℝ) (hu : 0 < u) :
    ∑' n : ℤ, 2 * π * I * n * Complex.exp (2 * π * I * n * y - u * (n:ℂ)^2) =
      ((Real.sqrt (π / u) * (2 * π ^ 2 / u) *
        ∑' n : ℤ, ((n:ℝ) - y) * Real.exp (-(π^2 * ((n:ℝ) - y)^2 / u)) : ℝ) : ℂ) := by
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu' : (u:ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  set τ : ℂ := I * u / π with hτ
  have hτ0 : τ ≠ 0 := by rw [hτ]; simp [hπ, hu', Complex.I_ne_zero]
  have h1 : (∑' n : ℤ, 2 * π * I * n * Complex.exp (2 * π * I * n * y - u * (n:ℂ)^2)) =
      jacobiTheta₂' (y:ℂ) τ := by
    unfold jacobiTheta₂' jacobiTheta₂'_term jacobiTheta₂_term
    refine tsum_congr fun n => ?_
    congr 2
    rw [hτ]
    field_simp
    ring_nf
    simp [Complex.I_sq]
    ring
  have him : 0 < (-1 / τ).im := by
    rw [hτ]
    have : (-1 / (I * (u:ℂ) / π)) = ((π / u : ℝ) : ℂ) * I := by
      field_simp
      rw [Complex.ofReal_div]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    rw [this]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    simp only [mul_one, zero_mul, add_zero]
    positivity
  have hsum := ((hasSum_jacobiTheta₂'_term ((y:ℂ) / τ) him).sub
    ((hasSum_jacobiTheta₂_term ((y:ℂ) / τ) him).mul_left (2 * π * I * y))).tsum_eq
  rw [h1, jacobiTheta₂'_functional_equation]
  rw [← hsum, ← tsum_mul_left]
  have h2 : (-I * τ : ℂ) = ((u / π : ℝ) : ℂ) := by
    rw [hτ]; push_cast; field_simp; simp [Complex.I_sq]
  have h3 : (((u / π : ℝ) : ℂ)) ^ (1/2 : ℂ) = ((Real.sqrt (u / π) : ℝ) : ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  rw [h2, h3]
  have hs : Real.sqrt (u / π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs' : (1:ℂ) / ((Real.sqrt (u / π) : ℝ) : ℂ) = ((Real.sqrt (π / u) : ℝ) : ℂ) := by
    have : Real.sqrt (π / u) = 1 / Real.sqrt (u / π) := by
      rw [one_div, ← Real.sqrt_inv, inv_div]
    rw [this]; push_cast; rfl
  rw [hs', Complex.ofReal_mul, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  unfold jacobiTheta₂'_term jacobiTheta₂_term
  push_cast
  have e1 : Complex.exp (-π * I * (y:ℂ) ^ 2 / τ) * Complex.exp (2 * π * I * n * ((y:ℂ) / τ) + π * I * (n:ℂ) ^ 2 * (-1 / τ))
      = Complex.exp (-(π ^ 2 * ((n:ℂ) - y) ^ 2 / u)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hτ]
    field_simp
    ring_nf
  have e2 : (1:ℂ) / τ = -(I * π / u) := by
    rw [hτ]; field_simp; ring_nf; simp [Complex.I_sq]
  calc ((Real.sqrt (π / u) : ℝ) : ℂ) * Complex.exp (-π * I * (y:ℂ) ^ 2 / τ) / τ *
        (2 * π * I * n * Complex.exp (2 * π * I * n * ((y:ℂ) / τ) + π * I * (n:ℂ) ^ 2 * (-1 / τ)) -
          2 * π * I * y * Complex.exp (2 * π * I * n * ((y:ℂ) / τ) + π * I * (n:ℂ) ^ 2 * (-1 / τ)))
      = ((Real.sqrt (π / u) : ℝ) : ℂ) * (2 * π * I * ((n:ℂ) - y)) * ((1:ℂ) / τ) *
        (Complex.exp (-π * I * (y:ℂ) ^ 2 / τ) * Complex.exp (2 * π * I * n * ((y:ℂ) / τ) + π * I * (n:ℂ) ^ 2 * (-1 / τ))) := by
        field_simp
    _ = _ := by
        rw [e1, e2]
        field_simp
        ring_nf
        simp [Complex.I_sq]
        ring


theorem prod_cexp_eq {d : ℕ} (k : Lattice d) (y : Fin d → ℝ) (u : ℝ) :
    ∏ i, Complex.exp (2 * π * I * ((k i : ℤ) : ℂ) * (y i : ℝ) - u * ((k i : ℤ) : ℂ)^2) =
      ((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) * Torus.mode k (boxPt y) := by
  rw [mode_eq_prod]
  have h2 : ∏ i, Complex.exp (2 * π * I * ((k i : ℤ) : ℂ) * (y i : ℝ) - u * ((k i : ℤ) : ℂ)^2) =
      (∏ i, Complex.exp (-((u:ℂ) * ((k i : ℤ):ℂ)^2))) *
        ∏ i, Complex.exp (2 * π * I * (k i : ℤ) * (y i : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [h2, ← Complex.exp_sum, Complex.ofReal_exp, enorm_sq]
  congr 2
  push_cast
  rw [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]

theorem abs_mul_exp_le {c : ℝ} (hc : 0 < c) (v : ℝ) :
    |v| * Real.exp (-c * v ^ 2) ≤ (1 + 2 / c) * Real.exp (-(c / 2) * v ^ 2) := by
  have h1 : |v| ≤ 1 + v ^ 2 := by nlinarith [sq_abs v, sq_nonneg (|v| - 1/2), abs_nonneg v]
  have h2 := pow_exp_bound (c / 2) (by positivity) 1 (v ^ 2) (by positivity)
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h2
  have h3 : Real.exp (-c * v ^ 2) = Real.exp (-(c / 2) * v ^ 2) * Real.exp (-(c / 2 * v ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-(c / 2 * v ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 ≤ c / 2 * v ^ 2 := by positivity
    linarith
  rw [h3]
  have hE := Real.exp_pos (-(c / 2) * v ^ 2)
  have hE2 := Real.exp_pos (-(c / 2 * v ^ 2))
  calc |v| * (Real.exp (-(c / 2) * v ^ 2) * Real.exp (-(c / 2 * v ^ 2)))
      ≤ (1 + v ^ 2) * (Real.exp (-(c / 2) * v ^ 2) * Real.exp (-(c / 2 * v ^ 2))) := by gcongr
    _ = Real.exp (-(c / 2) * v ^ 2) * (Real.exp (-(c / 2 * v ^ 2)) + v ^ 2 * Real.exp (-(c / 2 * v ^ 2))) := by
        ring
    _ ≤ Real.exp (-(c / 2) * v ^ 2) * (1 + 1 / (c / 2)) := by gcongr
    _ = _ := by rw [one_div_div]; ring

/-- the `j`-th component of the gradient of the heat semigroup part -/
def psiG {d : ℕ} (j : Fin d) (x : Torus d) (u : ℝ) : ℝ :=
  ∑' k : Lattice d, -(Real.exp (-u * Lattice.enorm k ^ 2) * (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k x)

theorem summable_lin_shift_gauss {c : ℝ} (hc : 0 < c) (y : ℝ) :
    Summable fun n : ℤ => |((n:ℝ) - y) * Real.exp (-c * ((n:ℝ) - y) ^ 2)| := by
  refine ((summable_shift_gauss (c := c/2) (by positivity) y).mul_left (1 + 2 / c)).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun n => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have := abs_mul_exp_le hc ((n:ℝ) - y)
  convert this using 3

theorem psiG_images {d : ℕ} (j : Fin d) (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    psiG j (boxPt y) u = Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
      ∑' m : Lattice d, (((m j : ℤ) : ℝ) - y j) * Real.exp (-(π ^ 2 * wsq y m / u)) := by
  set f : Fin d → ℤ → ℂ := fun i n => (if i = j then 2 * π * I * n else 1) *
    Complex.exp (2 * π * I * n * (y i) - u * (n:ℂ)^2) with hf
  have hnorm : ∀ i (m : ℤ), ‖Complex.exp (2 * π * I * m * (y i) - u * (m:ℂ)^2)‖ = Real.exp (-u * (m:ℝ)^2) := by
    intro i m
    rw [Complex.norm_exp]
    congr 1
    rw [show ((m:ℂ)) = ((m:ℝ):ℂ) by simp]
    simp [pow_two, Complex.mul_re]
  have hfn : ∀ i, Summable fun m => ‖f i m‖ := by
    intro i
    by_cases hij : i = j
    · have h1 : Summable fun m : ℤ => |(m:ℝ) - 0| * Real.exp (-u * ((m:ℝ) - 0)^2) := by
        refine (summable_lin_shift_gauss hu 0).congr fun m => ?_
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      refine (h1.mul_left (2 * π)).congr fun m => ?_
      simp only [hf, hij, if_true, norm_mul, hnorm]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
      ring
    · refine (summable_exp_sq u hu).congr fun m => ?_
      simp only [hf, hij, if_false, one_mul, hnorm]
  obtain ⟨hsum, hhas⟩ := pi_hasSum d f hfn
  have hterm : ∀ k : Lattice d,
      -(Real.exp (-u * Lattice.enorm k ^ 2) * (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k (boxPt y)) =
      (∏ i, f i (k i)).re := by
    intro k
    have h1 : ∏ i, f i (k i) = (2 * π * I * ((k j : ℤ) : ℂ)) *
        (((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) * Torus.mode k (boxPt y)) := by
      simp only [hf]
      rw [Finset.prod_mul_distrib, prod_cexp_eq]
      congr 1
      rw [Finset.prod_ite_eq' Finset.univ j (fun i => 2 * π * I * ((k i : ℤ) : ℂ))]
      simp
    rw [h1]
    simp only [Torus.sinMode, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    push_cast
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring
  set T : Fin d → ℝ := fun i => if i = j then
      Real.sqrt (π / u) * (2 * π ^ 2 / u) * ∑' n : ℤ, ((n:ℝ) - y i) * Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u))
    else Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u)) with hT
  have hfac : ∀ i, ∑' n, f i n = ((T i : ℝ) : ℂ) := by
    intro i
    by_cases hij : i = j
    · simp only [hf, hT, hij, if_true]
      rw [← theta_deriv_eq u (y j) hu]
    · simp only [hf, hT, hij, if_false, one_mul]
      rw [theta_eq u (y i) hu]
  have hpsi : psiG j (boxPt y) u = ∏ i, T i := by
    unfold psiG
    simp_rw [hterm]
    rw [← Complex.re_tsum hsum.of_norm, hhas.tsum_eq]
    simp_rw [hfac]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  -- product of real sums
  set g : Fin d → ℤ → ℝ := fun i n => Real.sqrt (π / u) *
    ((if i = j then (2 * π ^ 2 / u) * ((n:ℝ) - y i) else 1) * Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u))) with hg
  have hgs : ∀ i, Summable fun m => |g i m| := by
    intro i
    have hc : 0 < π ^ 2 / u := by positivity
    have e : ∀ n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u)) = Real.exp (-(π ^ 2 / u) * ((n:ℝ) - y i)^2) := by
      intro n; congr 1; ring
    by_cases hij : i = j
    · refine ((summable_lin_shift_gauss hc (y i)).mul_left (Real.sqrt (π / u) * (2 * π ^ 2 / u))).congr fun n => ?_
      simp only [hg, hij, if_true, e, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_pos (by positivity : (0:ℝ) < 2 * π ^ 2 / u)]
      ring
    · refine ((summable_shift_gauss hc (y i)).mul_left (Real.sqrt (π / u))).congr fun n => ?_
      simp only [hg, hij, if_false, one_mul, e]
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.exp_pos _)]
  have hpr := (pi_hasSum_real d g hgs).tsum_eq
  have hTg : ∀ i, T i = ∑' n, g i n := by
    intro i
    by_cases hij : i = j
    · simp only [hT, hg, hij, if_true]
      rw [← tsum_mul_left]
      exact tsum_congr fun n => by ring
    · simp only [hT, hg, hij, if_false, one_mul]
      rw [tsum_mul_left]
  rw [hpsi]
  simp_rw [hTg]
  rw [← hpr, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [hg]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j, ← Real.exp_sum]
  simp only [Finset.mem_univ, if_true]
  have : ∑ i, -(π ^ 2 * (((m i : ℤ) : ℝ) - y i) ^ 2 / u) = -(π ^ 2 * wsq y m / u) := by
    unfold wsq
    rw [Finset.sum_neg_distrib, ← Finset.sum_div, Finset.mul_sum]
  rw [this]
  ring


theorem pow_gauss_le {c : ℝ} (hc : 0 < c) (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ e : ℝ, 0 ≤ e →
    e ^ n * Real.exp (-c * e ^ 2) ≤ M * Real.exp (-(c/2) * e ^ 2) := by
  refine ⟨1 + (n.factorial : ℝ) / (c/2) ^ n, by positivity, fun e he => ?_⟩
  have h1 : e ^ n ≤ 1 + (e ^ 2) ^ n := by
    rcases le_total e 1 with h | h
    · have : e ^ n ≤ 1 := pow_le_one₀ he h
      have : 0 ≤ (e ^ 2) ^ n := by positivity
      linarith
    · have : e ^ n ≤ (e ^ 2) ^ n := by
        rw [← pow_mul]; exact pow_le_pow_right₀ h (by omega)
      linarith
  have h2 := pow_exp_bound (c/2) (by positivity) n (e ^ 2) (by positivity)
  have h3 : Real.exp (-c * e ^ 2) = Real.exp (-(c/2) * e ^ 2) * Real.exp (-(c/2) * e ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-(c/2) * e ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 ≤ c/2 * e^2 := by positivity
    linarith
  have h5 : Real.exp (-(c/2) * e ^ 2) = Real.exp (-((c/2) * e ^ 2)) := by congr 1; ring
  rw [h3]
  have hp := Real.exp_pos (-(c/2) * e ^ 2)
  calc e ^ n * (Real.exp (-(c/2) * e ^ 2) * Real.exp (-(c/2) * e ^ 2))
      = (e ^ n * Real.exp (-(c/2) * e ^ 2)) * Real.exp (-(c/2) * e ^ 2) := by ring
    _ ≤ ((1 + (e ^ 2) ^ n) * Real.exp (-(c/2) * e ^ 2)) * Real.exp (-(c/2) * e ^ 2) := by gcongr
    _ = ((Real.exp (-(c/2) * e ^ 2) + (e ^ 2) ^ n * Real.exp (-((c/2) * e ^ 2)))) *
          Real.exp (-(c/2) * e ^ 2) := by rw [h5]; ring
    _ ≤ (1 + (n.factorial : ℝ) / (c/2) ^ n) * Real.exp (-(c/2) * e ^ 2) := by
        gcongr

theorem summable_pow_gauss_lattice (d : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Summable fun k : Lattice d => Lattice.enorm k ^ n * Real.exp (-c * Lattice.enorm k ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := pow_gauss_le hc n
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => hM _ (norm_nonneg _))
    ((summable_gauss_lattice d (c/2) (by positivity)).mul_left M)
  have : 0 ≤ Lattice.enorm k := norm_nonneg _
  positivity

theorem abs_coord_le_enorm {d : ℕ} (k : Lattice d) (j : Fin d) : |((k j : ℤ) : ℝ)| ≤ Lattice.enorm k := by
  have h2 : ((k j:ℤ):ℝ)^2 ≤ Lattice.enorm k ^ 2 := by
    rw [enorm_sq]
    exact Finset.single_le_sum (f := fun i => ((k i : ℤ):ℝ)^2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  exact abs_le_of_sq_le_sq' h2 (norm_nonneg _) |> fun h => abs_le.mpr h

theorem heatRieszGrad_apply {d : ℕ} {s : ℝ} (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (x : Torus d)
    (j : Fin d) :
    heatRieszGrad d s ε x j = ∑' k : Lattice d,
      -(rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) * 2 * π * Torus.sinMode k x) *
        ((k j : ℤ) : ℝ) := by
  set v : Lattice d → Euc d := fun k =>
    (-(rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) * 2 * π * Torus.sinMode k x)) •
      Lattice.toEuc k with hv
  have hsum : Summable v := by
    refine Summable.of_norm_bounded ((summable_pow_gauss_lattice d hε 1).mul_left
      (|rieszConst d s| * 2 * π)) fun k => ?_
    simp only [hv, norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos Real.pi_pos]
    have h1 := abs_rieszCoeff_le d s hsd k
    have h2 : |Torus.sinMode k x| ≤ 1 := (Complex.abs_im_le_norm _).trans (norm_mode k x).le
    have h3 : ‖Lattice.toEuc k‖ = Lattice.enorm k := rfl
    rw [h3, pow_one]
    have : 0 ≤ Lattice.enorm k := norm_nonneg _
    calc |rieszCoeff d s k| * Real.exp (-ε * Lattice.enorm k ^ 2) * |(2:ℝ)| * π * |Torus.sinMode k x| *
          Lattice.enorm k ≤ |rieszConst d s| * Real.exp (-ε * Lattice.enorm k ^ 2) * 2 * π * 1 *
          Lattice.enorm k := by
          rw [abs_two]; gcongr
      _ = _ := by ring
  have h : (∑' k, v k) j = ∑' k, v k j := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).map_tsum hsum
  unfold heatRieszGrad
  rw [h]
  refine tsum_congr fun k => ?_
  simp [hv, Lattice.toEuc]


theorem single_k_integral_c {d : ℕ} {s : ℝ} (hsd : s < d) (ε c : ℝ) (k : Lattice d) (hk : k ≠ 0) :
    ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * (Real.exp (-((t + ε) * Lattice.enorm k ^ 2)) * c) =
      c * Real.exp (-ε * Lattice.enorm k ^ 2) *
        (Lattice.enorm k ^ (s - d) * Real.Gamma (((d:ℝ) - s) / 2)) := by
  have ha : 0 < ((d:ℝ) - s) / 2 := by linarith
  have hm : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (one_le_enorm k hk)
  have hr : 0 < Lattice.enorm k ^ 2 := by positivity
  have h1 := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  have h2 : ∀ t : ℝ, t ^ (((d:ℝ) - s) / 2 - 1) * (Real.exp (-((t + ε) * Lattice.enorm k ^ 2)) * c) =
      (c * Real.exp (-ε * Lattice.enorm k ^ 2)) *
        (t ^ (((d:ℝ) - s) / 2 - 1) * Real.exp (-(Lattice.enorm k ^ 2 * t))) := by
    intro t
    have : Real.exp (-((t + ε) * Lattice.enorm k ^ 2)) =
        Real.exp (-ε * Lattice.enorm k ^ 2) * Real.exp (-(Lattice.enorm k ^ 2 * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  simp_rw [h2]
  rw [integral_const_mul, h1]
  congr 2
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hm.le]
  rw [← Real.rpow_neg hm.le]
  congr 1
  push_cast; ring

/-- the integrand for the gradient component -/
def gG {d : ℕ} (j : Fin d) (a ε : ℝ) (x : Torus d) (k : Lattice d) (t : ℝ) : ℝ :=
  t ^ (a - 1) * -(Real.exp (-(t + ε) * Lattice.enorm k ^ 2) * (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k x)

theorem gG_zero {d : ℕ} (j : Fin d) (a ε : ℝ) (x : Torus d) : gG j a ε x 0 = fun _ => 0 := by
  funext t; simp [gG]

theorem gG_bound {d : ℕ} (j : Fin d) (a ε : ℝ) (x : Torus d) (k : Lattice d) (t : ℝ) (ht : 0 < t) :
    ‖gG j a ε x k t‖ ≤ (2 * π * Lattice.enorm k * Real.exp (-ε * Lattice.enorm k ^ 2)) *
      (t ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * t))) := by
  unfold gG
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _),
    abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  have : Real.exp (-(t + ε) * Lattice.enorm k ^ 2) =
        Real.exp (-ε * Lattice.enorm k ^ 2) * Real.exp (-(Lattice.enorm k ^ 2 * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  have h1 := abs_coord_le_enorm k j
  have h2 : |Torus.sinMode k x| ≤ 1 := (Complex.abs_im_le_norm _).trans (norm_mode k x).le
  have hp : 0 ≤ t ^ (a - 1) := (Real.rpow_pos_of_pos ht _).le
  have he : 0 ≤ Lattice.enorm k := norm_nonneg _
  calc t ^ (a - 1) * (Real.exp (-ε * Lattice.enorm k ^ 2) * Real.exp (-(Lattice.enorm k ^ 2 * t)) *
        (2 * π * |((k j : ℤ) : ℝ)|) * |Torus.sinMode k x|)
      ≤ t ^ (a - 1) * (Real.exp (-ε * Lattice.enorm k ^ 2) * Real.exp (-(Lattice.enorm k ^ 2 * t)) *
        (2 * π * Lattice.enorm k) * 1) := by gcongr
    _ = _ := by ring

theorem gG_integrable {d : ℕ} (j : Fin d) {a : ℝ} (ha : 0 < a) (ε : ℝ) (x : Torus d) (k : Lattice d) :
    IntegrableOn (gG j a ε x k) (Ioi 0) := by
  by_cases hk : k = 0
  · rw [hk, gG_zero]; exact integrableOn_zero
  · refine Integrable.mono' ((integrable_majorant ha k hk).const_mul
      (2 * π * Lattice.enorm k * Real.exp (-ε * Lattice.enorm k ^ 2))) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      unfold gG
      fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      exact gG_bound j a ε x k t ht

theorem gG_norm_summable {d : ℕ} (j : Fin d) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) (x : Torus d) :
    Summable fun k : Lattice d => ∫ t in Ioi (0:ℝ), ‖gG j a ε x k t‖ := by
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
    (fun k => ?_) ((summable_pow_gauss_lattice d hε 1).mul_left (2 * π * Real.Gamma a))
  have he : 0 ≤ Lattice.enorm k := norm_nonneg _
  by_cases hk : k = 0
  · rw [hk, gG_zero]
    simp only [norm_zero, integral_zero]
    have := Real.Gamma_pos_of_pos ha
    exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le)
  · have hm : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (one_le_enorm k hk)
    have hr : 0 < Lattice.enorm k ^ 2 := by positivity
    have hint := (integrable_majorant ha k hk).const_mul
      (2 * π * Lattice.enorm k * Real.exp (-ε * Lattice.enorm k ^ 2))
    calc ∫ t in Ioi (0:ℝ), ‖gG j a ε x k t‖
        ≤ ∫ t in Ioi (0:ℝ), (2 * π * Lattice.enorm k * Real.exp (-ε * Lattice.enorm k ^ 2)) *
            (t ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * t))) := by
          refine setIntegral_mono_on (gG_integrable j ha ε x k).norm hint measurableSet_Ioi ?_
          intro t ht
          exact gG_bound j a ε x k t ht
      _ = (2 * π * Lattice.enorm k * Real.exp (-ε * Lattice.enorm k ^ 2)) *
            ((1 / Lattice.enorm k ^ 2) ^ a * Real.Gamma a) := by
          rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
      _ ≤ (2 * π * Lattice.enorm k * Real.exp (-ε * Lattice.enorm k ^ 2)) * (1 * Real.Gamma a) := by
          have h1 : (1 / Lattice.enorm k ^ 2) ^ a ≤ 1 := by
            apply Real.rpow_le_one (by positivity) _ ha.le
            have := one_le_enorm k hk
            rw [div_le_one hr]; nlinarith
          have := (Real.Gamma_pos_of_pos ha).le
          gcongr
      _ = _ := by ring

theorem heatRieszGrad_eq_integral {d : ℕ} {s : ℝ} (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (x : Torus d)
    (j : Fin d) :
    heatRieszGrad d s ε x j = rieszConst d s * (2 * π) ^ (s - d) / Real.Gamma (((d:ℝ) - s) / 2) *
      ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiG j x (t + ε) := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  set A := rieszConst d s * (2 * π) ^ (s - d) / Real.Gamma a with hA
  have hterm : ∀ k : Lattice d,
      -(rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) * 2 * π * Torus.sinMode k x) *
        ((k j : ℤ) : ℝ) = A * ∫ t in Ioi (0:ℝ), gG j a ε x k t := by
    intro k
    by_cases hk : k = 0
    · rw [hk, gG_zero]; simp [rieszCoeff]
    · have h := single_k_integral_c hsd ε (-(2 * π * ((k j : ℤ) : ℝ) * Torus.sinMode k x)) k hk
      have : (fun t => gG j a ε x k t) = fun t => t ^ (a - 1) *
          (Real.exp (-((t + ε) * Lattice.enorm k ^ 2)) * -(2 * π * ((k j : ℤ) : ℝ) * Torus.sinMode k x)) := by
        funext t; simp only [gG, neg_mul]; ring
      rw [this, h]
      have hm : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (one_le_enorm k hk)
      have : rieszCoeff d s k = rieszConst d s * ((2 * π) ^ (s - d) * Lattice.enorm k ^ (s - d)) := by
        unfold rieszCoeff
        simp only [hk, ite_false]
        rw [Real.mul_rpow (by positivity) hm.le]
      rw [this, hA]
      field_simp
      rfl
  have hsw : ∑' k : Lattice d, ∫ t in Ioi (0:ℝ), gG j a ε x k t =
      ∫ t in Ioi (0:ℝ), ∑' k : Lattice d, gG j a ε x k t :=
    integral_tsum_of_summable_integral_norm (gG_integrable j ha ε x) (gG_norm_summable j ha hε x)
  have hpt : ∀ t : ℝ, ∑' k : Lattice d, gG j a ε x k t = t ^ (a - 1) * psiG j x (t + ε) := by
    intro t
    unfold gG psiG
    rw [tsum_mul_left]
  rw [heatRieszGrad_apply hsd hε x j]
  simp_rw [hterm]
  rw [tsum_mul_left, hsw]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => hpt t)


theorem psiG_term_bound {d : ℕ} (j : Fin d) (x : Torus d) (k : Lattice d) (u : ℝ) :
    ‖-(Real.exp (-u * Lattice.enorm k ^ 2) * (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k x)‖ ≤
      2 * π * Lattice.enorm k * Real.exp (-u * Lattice.enorm k ^ 2) := by
  rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  have h1 := abs_coord_le_enorm k j
  have h2 : |Torus.sinMode k x| ≤ 1 := (Complex.abs_im_le_norm _).trans (norm_mode k x).le
  have he : 0 ≤ Lattice.enorm k := norm_nonneg _
  calc Real.exp (-u * Lattice.enorm k ^ 2) * (2 * π * |((k j : ℤ) : ℝ)|) * |Torus.sinMode k x|
      ≤ Real.exp (-u * Lattice.enorm k ^ 2) * (2 * π * Lattice.enorm k) * 1 := by gcongr
    _ = _ := by ring

theorem psiG_continuousOn {d : ℕ} (j : Fin d) (x : Torus d) : ContinuousOn (psiG j x) (Ioi 0) := by
  have key : ∀ u0 : ℝ, 0 < u0 → ContinuousOn (psiG j x) (Ici u0) := by
    intro u0 hu0
    unfold psiG
    refine continuousOn_tsum (u := fun k : Lattice d => 2 * π * (Lattice.enorm k ^ 1 *
      Real.exp (-u0 * Lattice.enorm k ^ 2)))
      (fun k => ?_) ((summable_pow_gauss_lattice d hu0 1).mul_left (2 * π)) ?_
    · exact (by fun_prop : Continuous fun u : ℝ => -(Real.exp (-u * Lattice.enorm k ^ 2) *
          (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k x)).continuousOn
    · intro k u hu
      have hu' : u0 ≤ u := hu
      refine (psiG_term_bound j x k u).trans ?_
      have he : 0 ≤ Lattice.enorm k := norm_nonneg _
      rw [pow_one, ← mul_assoc]
      gcongr
  intro u hu
  have hu' : (0:ℝ) < u := hu
  have := (key (u/2) (by positivity)).continuousAt (Ici_mem_nhds (show u / 2 < u by linarith))
  exact this.continuousWithinAt

theorem psiG_large_bound {d : ℕ} (j : Fin d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (x : Torus d) (u : ℝ), 1 ≤ u → |psiG j x u| ≤ M * Real.exp (-u) := by
  set G := ∑' k : Lattice d, 2 * π * Real.exp 1 * (Lattice.enorm k ^ 1 * Real.exp (-1 * Lattice.enorm k ^ 2))
    with hG
  have hGs : Summable fun k : Lattice d => 2 * π * Real.exp 1 *
      (Lattice.enorm k ^ 1 * Real.exp (-1 * Lattice.enorm k ^ 2)) :=
    (summable_pow_gauss_lattice d one_pos 1).mul_left _
  have hG0 : 0 ≤ G := tsum_nonneg fun k => by
    have : 0 ≤ Lattice.enorm k := norm_nonneg _
    positivity
  refine ⟨G, hG0, fun x u hu => ?_⟩
  have hb : ∀ k : Lattice d,
      ‖-(Real.exp (-u * Lattice.enorm k ^ 2) * (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k x)‖ ≤
        Real.exp (-u) * (2 * π * Real.exp 1 * (Lattice.enorm k ^ 1 * Real.exp (-1 * Lattice.enorm k ^ 2))) := by
    intro k
    refine (psiG_term_bound j x k u).trans ?_
    have he : 0 ≤ Lattice.enorm k := norm_nonneg _
    by_cases hk : k = 0
    · have h0 : Lattice.enorm k = 0 := by
        rw [hk]; simp [Lattice.enorm, Lattice.toEuc]; rfl
      rw [h0]; simp
    · have hm := one_le_enorm k hk
      have : Real.exp (-u * Lattice.enorm k ^ 2) ≤ Real.exp (-u) * Real.exp 1 * Real.exp (-1 * Lattice.enorm k ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr (show (1:ℝ) ≤ Lattice.enorm k ^ 2 by nlinarith))]
      calc 2 * π * Lattice.enorm k * Real.exp (-u * Lattice.enorm k ^ 2)
          ≤ 2 * π * Lattice.enorm k * (Real.exp (-u) * Real.exp 1 * Real.exp (-1 * Lattice.enorm k ^ 2)) := by
            gcongr
        _ = _ := by ring
  have h2 := tsum_of_norm_bounded (hGs.mul_left (Real.exp (-u))).hasSum hb
  rw [tsum_mul_left, ← hG] at h2
  rw [← Real.norm_eq_abs, mul_comm]
  exact h2


theorem wsq_ge_enorm {d : ℕ} (x : Euc d) (hx : ∀ i, |x i| ≤ 1/2) (m : Lattice d) :
    Lattice.enorm m ^ 2 / 4 ≤ wsq (fun i => x i) m := by
  rw [enorm_sq, Finset.sum_div]
  unfold wsq
  exact Finset.sum_le_sum fun i _ => sq_sub_ge (x i) (hx i) (m i)

theorem psiG_small_bound {d : ℕ} (j : Fin d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Euc d, (∀ i, |x i| ≤ 1/2) → ∀ u : ℝ, 0 < u → u ≤ 1 →
      |psiG j (Torus.mk x) u| ≤ Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
        (‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) + K * Real.exp (-(π ^ 2 / (8 * u)))) := by
  set c : Lattice d → ℝ := fun m => (Lattice.enorm m + 1) * Real.exp (-(π ^ 2 / 8) * Lattice.enorm m ^ 2)
    with hc
  have hcs : Summable c := by
    have h1 := (summable_pow_gauss_lattice d (c := π ^ 2 / 8) (by positivity) 1).add
      (summable_gauss_lattice d (π ^ 2 / 8) (by positivity))
    refine h1.congr fun m => ?_
    simp only [hc, pow_one]; ring
  have hc0 : ∀ m, 0 ≤ c m := fun m => by
    have : 0 ≤ Lattice.enorm m := norm_nonneg _
    simp only [hc]; positivity
  refine ⟨∑' m, c m, tsum_nonneg hc0, fun x hx u hu hu1 => ?_⟩
  have hmk : Torus.mk x = boxPt (fun i => x i) := rfl
  rw [hmk, psiG_images j _ hu]
  set a : Lattice d → ℝ := fun m => (((m j : ℤ) : ℝ) - x j) * Real.exp (-(π ^ 2 * wsq (fun i => x i) m / u))
    with ha
  have hcoord : ∀ m : Lattice d, |((m j : ℤ) : ℝ) - x j| ≤ Lattice.enorm m + 1 := by
    intro m
    have h1 := abs_coord_le_enorm m j
    have h2 := hx j
    calc |((m j : ℤ) : ℝ) - x j| ≤ |((m j : ℤ) : ℝ)| + |x j| := abs_sub _ _
      _ ≤ _ := by linarith
  have hπ8 : (0:ℝ) < π ^ 2 := by positivity
  have habs : ∀ m, |a m| ≤ c m := by
    intro m
    simp only [ha, hc]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hw := wsq_ge_enorm x hx m
    have hw0 := wsq_nonneg (fun i => x i) m
    have hexp : Real.exp (-(π ^ 2 * wsq (fun i => x i) m / u)) ≤
        Real.exp (-(π ^ 2 / 8) * Lattice.enorm m ^ 2) := by
      rw [Real.exp_le_exp]
      have h1 : π ^ 2 * wsq (fun i => x i) m ≤ π ^ 2 * wsq (fun i => x i) m / u := by
        rw [le_div_iff₀ hu]
        have := mul_le_mul_of_nonneg_left hu1 (mul_nonneg hπ8.le hw0)
        linarith
      nlinarith
    have he : 0 ≤ Lattice.enorm m := norm_nonneg _
    exact mul_le_mul (hcoord m) hexp (Real.exp_pos _).le (by positivity)
  have hsa : Summable a := Summable.of_norm_bounded hcs (fun m => by rw [Real.norm_eq_abs]; exact habs m)
  rw [hsa.tsum_eq_add_tsum_ite 0]
  have h0 : |a 0| ≤ ‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) := by
    simp only [ha]
    have e : π ^ 2 * wsq (fun i => x i) 0 = π ^ 2 * ‖x‖ ^ 2 := by
      rw [wsq_eq_qm]
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      simp only [qm, this, sub_zero]
    rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
    gcongr
    simp only [Pi.zero_apply, Int.cast_zero, zero_sub, abs_neg]
    have := PiLp.norm_apply_le x j
    rwa [Real.norm_eq_abs] at this
  have hrest : |∑' m, (if m = 0 then 0 else a m)| ≤ (∑' m, c m) * Real.exp (-(π ^ 2 / (8 * u))) := by
    have hb : ∀ m : Lattice d, ‖(if m = 0 then 0 else a m)‖ ≤ Real.exp (-(π ^ 2 / (8 * u))) * c m := by
      intro m
      by_cases hm : m = 0
      · simp only [hm, if_true, norm_zero]
        exact mul_nonneg (Real.exp_pos _).le (hc0 _)
      · simp only [hm, if_false, Real.norm_eq_abs, ha, hc]
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have he := one_le_enorm m hm
        have hw := wsq_ge_enorm x hx m
        have hexp : Real.exp (-(π ^ 2 * wsq (fun i => x i) m / u)) ≤
            Real.exp (-(π ^ 2 / (8 * u))) * Real.exp (-(π ^ 2 / 8) * Lattice.enorm m ^ 2) := by
          rw [← Real.exp_add, Real.exp_le_exp]
          have h1 : 1 / 4 ≤ wsq (fun i => x i) m := by nlinarith
          have h2 : wsq (fun i => x i) m / (2 * u) ≥ 1 / (8 * u) := by
            rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
          have h3 : wsq (fun i => x i) m / (2 * u) ≥ Lattice.enorm m ^ 2 / 8 := by
            rw [ge_iff_le, le_div_iff₀ (by positivity)]; nlinarith
          have e1 : π ^ 2 * wsq (fun i => x i) m / u =
              π ^ 2 * (wsq (fun i => x i) m / (2 * u)) + π ^ 2 * (wsq (fun i => x i) m / (2 * u)) := by
            field_simp; ring
          have e2 : π ^ 2 / (8 * u) = π ^ 2 * (1 / (8 * u)) := by ring
          rw [e1, e2]
          nlinarith [mul_le_mul_of_nonneg_left h2 hπ8.le, mul_le_mul_of_nonneg_left h3 hπ8.le]
        calc |((m j : ℤ) : ℝ) - x j| * Real.exp (-(π ^ 2 * wsq (fun i => x i) m / u))
            ≤ (Lattice.enorm m + 1) * (Real.exp (-(π ^ 2 / (8 * u))) *
                Real.exp (-(π ^ 2 / 8) * Lattice.enorm m ^ 2)) := by
              gcongr
              exact hcoord m
          _ = _ := by ring
    have h2 := tsum_of_norm_bounded (hcs.mul_left (Real.exp (-(π ^ 2 / (8 * u))))).hasSum hb
    rw [tsum_mul_left] at h2
    rw [← Real.norm_eq_abs, mul_comm]
    exact h2
  rw [abs_mul]
  have hpre : 0 ≤ Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) := by positivity
  rw [abs_of_nonneg hpre]
  gcongr
  calc |a 0 + ∑' m, (if m = 0 then 0 else a m)| ≤ |a 0| + |∑' m, (if m = 0 then 0 else a m)| :=
        abs_add_le _ _
    _ ≤ _ := by linarith


theorem psiG_bound {d : ℕ} (j : Fin d) (x : Euc d) (hx : ∀ i, |x i| ≤ 1/2) (hx0 : x ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, 0 < u → |psiG j (Torus.mk x) u| ≤ M * Real.exp (-u) := by
  obtain ⟨K, hK0, hK⟩ := psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := psiG_large_bound (d := d) j
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set c0 := min (π ^ 2 * ‖x‖ ^ 2) (π ^ 2 / 8) with hc0
  have hc0p : 0 < c0 := lt_min (by positivity) (by positivity)
  set M0 := π ^ d * (2 * π ^ 2) * (‖x‖ + K) * (((d + 1).factorial : ℝ) / c0 ^ (d + 1)) with hM0
  have hM00 : 0 ≤ M0 := by positivity
  refine ⟨M0 * Real.exp 1 + M1, by positivity, fun u hu => ?_⟩
  rcases le_total u 1 with h1 | h1
  · refine (hK x hx u hu h1).trans ?_
    set w := 1 / u with hw
    have hw0 : 0 < w := by positivity
    have hsq : Real.sqrt (π / u) ≤ π * w := by
      have h2 : 1 ≤ π / u := by rw [le_div_iff₀ hu]; linarith [Real.pi_gt_three]
      have h3 : Real.sqrt (π / u) ≤ π / u := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      calc Real.sqrt (π / u) ≤ π / u := h3
        _ = π * w := by rw [hw]; ring
    have he1 : Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) ≤ Real.exp (-(c0 * w)) := by
      rw [Real.exp_le_exp, hw]
      have : c0 ≤ π ^ 2 * ‖x‖ ^ 2 := min_le_left _ _
      have : c0 * (1 / u) ≤ π ^ 2 * ‖x‖ ^ 2 * (1 / u) := by gcongr
      have e : π ^ 2 * ‖x‖ ^ 2 / u = π ^ 2 * ‖x‖ ^ 2 * (1 / u) := by ring
      linarith
    have he2 : Real.exp (-(π ^ 2 / (8 * u))) ≤ Real.exp (-(c0 * w)) := by
      rw [Real.exp_le_exp, hw]
      have : c0 ≤ π ^ 2 / 8 := min_le_right _ _
      have : c0 * (1 / u) ≤ π ^ 2 / 8 * (1 / u) := by gcongr
      have e : π ^ 2 / (8 * u) = π ^ 2 / 8 * (1 / u) := by field_simp
      linarith
    have hpe := pow_exp_bound c0 hc0p (d + 1) w hw0.le
    have hfin : Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
        (‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) + K * Real.exp (-(π ^ 2 / (8 * u)))) ≤ M0 := by
      calc Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
            (‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) + K * Real.exp (-(π ^ 2 / (8 * u))))
          ≤ (π * w) ^ d * (2 * π ^ 2 * w) * (‖x‖ * Real.exp (-(c0 * w)) + K * Real.exp (-(c0 * w))) := by
            have e : 2 * π ^ 2 / u = 2 * π ^ 2 * w := by rw [hw]; ring
            rw [e]
            gcongr
        _ = π ^ d * (2 * π ^ 2) * (‖x‖ + K) * (w ^ (d + 1) * Real.exp (-(c0 * w))) := by ring
        _ ≤ M0 := by rw [hM0]; gcongr
    have : 1 ≤ Real.exp 1 * Real.exp (-u) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; linarith
    nlinarith [Real.exp_pos (-u), Real.exp_pos 1]
  · refine (hM1 _ u h1).trans ?_
    have : 0 ≤ M0 * Real.exp 1 * Real.exp (-u) := by positivity
    nlinarith [Real.exp_pos (-u)]


/-- the candidate gradient component `A ∫_0^∞ t^{a-1} ∂_j Ψ(t, x) dt` -/
def gradComp {d : ℕ} (s : ℝ) (j : Fin d) (x : Torus d) : ℝ :=
  subA d s * ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiG j x t

theorem heatGrad_comp_tendsto {d : ℕ} {s : ℝ} (hsd : s < d) (x : Euc d) (hx : ∀ i, |x i| ≤ 1/2)
    (hx0 : x ≠ 0) (j : Fin d) :
    Tendsto (fun ε => heatRieszGrad d s ε (Torus.mk x) j) (𝓝[>] 0) (𝓝 (gradComp s j (Torus.mk x))) := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  obtain ⟨M, hM0, hM⟩ := psiG_bound j x hx hx0
  have hcont := psiG_continuousOn j (Torus.mk x)
  have hmeas : ∀ ε : ℝ, 0 ≤ ε → AEStronglyMeasurable (fun t : ℝ => t ^ (a - 1) * psiG j (Torus.mk x) (t + ε))
      (volume.restrict (Ioi 0)) := by
    intro ε hε
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) ?_
    refine hcont.comp (continuousOn_id.add continuousOn_const) fun t ht => ?_
    simp only [mem_Ioi] at ht ⊢
    linarith
  have hlim : Tendsto (fun ε => ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiG j (Torus.mk x) (t + ε)) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiG j (Torus.mk x) t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => M * (Real.exp (-t) * t ^ (a - 1))) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε using hmeas ε (le_of_lt hε)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have hε' : 0 < ε := hε
      have ht' : 0 < t := ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
      have h1 := hM (t + ε) (by linarith)
      have h2 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
      have h3 := Real.rpow_pos_of_pos ht' (a - 1)
      calc t ^ (a - 1) * |psiG j (Torus.mk x) (t + ε)| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = _ := by ring
    · exact (Real.GammaIntegral_convergent ha).const_mul M
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have ht' : 0 < t := ht
      refine Tendsto.const_mul _ ?_
      have h1 : Tendsto (fun ε : ℝ => t + ε) (𝓝[>] 0) (𝓝 t) := by
        have : Tendsto (fun ε : ℝ => t + ε) (𝓝 0) (𝓝 (t + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 : ContinuousAt (psiG j (Torus.mk x)) t :=
        (hcont t ht').continuousAt (Ioi_mem_nhds ht')
      exact h2.tendsto.comp h1
  refine (hlim.const_mul (subA d s)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [heatRieszGrad_eq_integral hsd hε]
  rfl

theorem periodicRieszGrad_eq {d : ℕ} {s : ℝ} (hsd : s < d) (x : Euc d) (hx : ∀ i, |x i| ≤ 1/2)
    (hx0 : x ≠ 0) :
    periodicRieszGrad d s (Torus.mk x) = WithLp.toLp 2 (fun j => gradComp s j (Torus.mk x)) := by
  unfold periodicRieszGrad
  apply Tendsto.limUnder_eq
  have h : Tendsto (fun ε => WithLp.ofLp (heatRieszGrad d s ε (Torus.mk x))) (𝓝[>] 0)
      (𝓝 (fun j => gradComp s j (Torus.mk x))) :=
    tendsto_pi_nhds.mpr fun j => heatGrad_comp_tendsto hsd x hx hx0 j
  exact ((PiLp.continuous_toLp 2 _).tendsto _).comp h


theorem integrableOn_pow_exp_Ioc {N θ : ℝ} (hN : 0 < N) (hθ : 0 < θ) :
    IntegrableOn (fun t : ℝ => t ^ (-N) * Real.exp (-θ / t)) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := (N ^ N * Real.exp (-N)) * θ ^ (-N)) (by simp) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := ht.1; positivity)]
    exact t_pow_exp_bound hN hθ ht.1

theorem int_Ioc_pow_exp_le {N θ : ℝ} (hN : 1 < N) (hθ : 0 < θ) :
    ∫ t in Ioc (0:ℝ) 1, t ^ (-N) * Real.exp (-θ / t) ≤ Real.Gamma (N - 1) * θ ^ (-(N - 1)) := by
  have hb : 0 < N - 1 := by linarith
  have e1 : ∫ t in Ioc (0:ℝ) 1, t ^ (-N) * Real.exp (-θ / t) =
      ∫ v in Ici (1:ℝ), v ^ ((N - 1) - 1) * Real.exp (-(θ * v)) := by
    rw [integral_Ici_one_inv]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 := ht.1
    rw [Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le, ← mul_assoc]
    congr 1
    · rw [← Real.rpow_natCast, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]
      congr 1; push_cast; ring
    · congr 1; rw [div_eq_mul_inv]; ring
  rw [e1]
  have hint := integrableOn_gamma_w hb hθ
  have h2 : ∫ v in Ici (1:ℝ), v ^ ((N - 1) - 1) * Real.exp (-(θ * v)) ≤
      ∫ v in Ioi (0:ℝ), v ^ ((N - 1) - 1) * Real.exp (-(θ * v)) := by
    rw [integral_Ici_eq_integral_Ioi]
    refine setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall (Ioi_subset_Ioi zero_le_one))
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun v hv => ?_)
    have : (0:ℝ) < v := hv
    positivity
  refine h2.trans (le_of_eq ?_)
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hb hθ, one_div, Real.inv_rpow hθ.le,
    ← Real.rpow_neg hθ.le, mul_comm]


theorem subA_nonneg {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) : 0 ≤ subA d s := by
  unfold subA
  have := rieszConst_pos hd hs0 hsd
  have := Real.Gamma_pos_of_pos (show 0 < ((d:ℝ) - s) / 2 by linarith)
  have : 0 < (2 * π) ^ (s - d) := Real.rpow_pos_of_pos (by positivity) _
  positivity

theorem gradComp_bound {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ x : Euc d, (∀ i, |x i| ≤ 1/2) → x ≠ 0 →
      |gradComp s j (Torus.mk x)| ≤ C1 * ‖x‖ ^ (-s - 1) + C2 := by
  obtain ⟨K, hK0, hK⟩ := psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := psiG_large_bound (d := d) j
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set N : ℝ := s / 2 + 2 with hN
  have hN1 : 1 < N := by rw [hN]; linarith
  set P : ℝ := 2 * π ^ 2 * Real.sqrt π ^ d with hP
  have hP0 : 0 ≤ P := by positivity
  set A := subA d s with hA
  have hA0 : 0 ≤ A := subA_nonneg hd hs0 hsd
  set θ2 : ℝ := π ^ 2 / 8 with hθ2
  have hθ2p : 0 < θ2 := by positivity
  have hG1 : 0 ≤ Real.Gamma (N - 1) := (Real.Gamma_pos_of_pos (by linarith)).le
  refine ⟨A * (P * Real.Gamma (N - 1) * π ^ (-(s + 2))),
    A * (P * K * (Real.Gamma (N - 1) * θ2 ^ (-(N - 1))) + M1 * Real.Gamma a),
    by positivity, by positivity, fun x hx hx0 => ?_⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set θ1 : ℝ := π ^ 2 * ‖x‖ ^ 2 with hθ1
  have hθ1p : 0 < θ1 := by positivity
  set b1 : ℝ → ℝ := fun t => P * ‖x‖ * (t ^ (-N) * Real.exp (-θ1 / t)) +
    P * K * (t ^ (-N) * Real.exp (-θ2 / t)) with hb1
  have hb1i : IntegrableOn b1 (Ioc 0 1) :=
    ((integrableOn_pow_exp_Ioc (by linarith) hθ1p).const_mul _).add
      ((integrableOn_pow_exp_Ioc (by linarith) hθ2p).const_mul _)
  set B : ℝ → ℝ := fun t => (Ioc (0:ℝ) 1).indicator b1 t + M1 * (Real.exp (-t) * t ^ (a - 1)) with hB
  have hBi : IntegrableOn B (Ioi 0) :=
    (hb1i.integrable_indicator measurableSet_Ioc).integrableOn.add
      ((Real.GammaIntegral_convergent ha).const_mul M1)
  have hpt : ∀ t ∈ Ioi (0:ℝ), ‖t ^ (a - 1) * psiG j (Torus.mk x) t‖ ≤ B t := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    rcases le_or_gt t 1 with h1 | h1
    · have hmem : t ∈ Ioc (0:ℝ) 1 := ⟨ht0, h1⟩
      simp only [hB, Set.indicator_of_mem hmem]
      have h2 := hK x hx t ht0 h1
      have hpow : t ^ (a - 1) * (Real.sqrt (π / t) ^ d * (2 * π ^ 2 / t)) = P * t ^ (-N) := by
        rw [sqrt_div_pow_eq d ht0, hP, div_eq_mul_inv (2 * π ^ 2), ← Real.rpow_neg_one t]
        have : t ^ (a - 1) * (Real.sqrt π ^ d * t ^ (-(d:ℝ)/2) * (2 * π ^ 2 * t ^ (-1:ℝ))) =
            2 * π ^ 2 * Real.sqrt π ^ d * (t ^ (a - 1) * t ^ (-(d:ℝ)/2) * t ^ (-1:ℝ)) := by ring
        rw [this, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
        congr 2
        rw [hN, ha_def]; ring
      have e1 : Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / t)) = Real.exp (-θ1 / t) := by rw [hθ1, neg_div]
      have e2 : Real.exp (-(π ^ 2 / (8 * t))) = Real.exp (-θ2 / t) := by
        rw [hθ2]; congr 1; field_simp
      rw [e1, e2] at h2
      have hp := Real.rpow_pos_of_pos ht0 (a - 1)
      calc t ^ (a - 1) * |psiG j (Torus.mk x) t|
          ≤ t ^ (a - 1) * (Real.sqrt (π / t) ^ d * (2 * π ^ 2 / t) *
              (‖x‖ * Real.exp (-θ1 / t) + K * Real.exp (-θ2 / t))) := by gcongr
        _ = (t ^ (a - 1) * (Real.sqrt (π / t) ^ d * (2 * π ^ 2 / t))) *
              (‖x‖ * Real.exp (-θ1 / t) + K * Real.exp (-θ2 / t)) := by ring
        _ = b1 t := by rw [hpow, hb1]; ring
        _ ≤ b1 t + M1 * (Real.exp (-t) * t ^ (a - 1)) := by
            have : 0 ≤ M1 * (Real.exp (-t) * t ^ (a - 1)) := by positivity
            linarith
    · have hnmem : t ∉ Ioc (0:ℝ) 1 := fun h => by linarith [h.2]
      simp only [hB, Set.indicator_of_notMem hnmem, zero_add]
      have h2 := hM1 (Torus.mk x) t h1.le
      have hp := Real.rpow_pos_of_pos ht0 (a - 1)
      calc t ^ (a - 1) * |psiG j (Torus.mk x) t| ≤ t ^ (a - 1) * (M1 * Real.exp (-t)) := by gcongr
        _ = _ := by ring
  have hint : |∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiG j (Torus.mk x) t| ≤ ∫ t in Ioi (0:ℝ), B t := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hBi
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpt))
  have hBint : ∫ t in Ioi (0:ℝ), B t = (∫ t in Ioc (0:ℝ) 1, b1 t) + M1 * Real.Gamma a := by
    simp only [hB]
    rw [integral_add (hb1i.integrable_indicator measurableSet_Ioc).integrableOn
      ((Real.GammaIntegral_convergent ha).const_mul M1), integral_const_mul,
      ← Real.Gamma_eq_integral ha, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Ioc_subset_Ioi_self]
  have hb1int : ∫ t in Ioc (0:ℝ) 1, b1 t ≤
      P * ‖x‖ * (Real.Gamma (N - 1) * θ1 ^ (-(N - 1))) + P * K * (Real.Gamma (N - 1) * θ2 ^ (-(N - 1))) := by
    simp only [hb1]
    rw [integral_add ((integrableOn_pow_exp_Ioc (by linarith) hθ1p).const_mul _)
      ((integrableOn_pow_exp_Ioc (by linarith) hθ2p).const_mul _), integral_const_mul, integral_const_mul]
    gcongr
    · exact int_Ioc_pow_exp_le hN1 hθ1p
    · exact int_Ioc_pow_exp_le hN1 hθ2p
  have hθ1pow : ‖x‖ * θ1 ^ (-(N - 1)) = π ^ (-(s + 2)) * ‖x‖ ^ (-s - 1) := by
    rw [hθ1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul hxn.le]
    have e3 : ‖x‖ * (π ^ ((2:ℕ) * -(N - 1) : ℝ) * ‖x‖ ^ ((2:ℕ) * -(N - 1) : ℝ)) =
        π ^ ((2:ℕ) * -(N - 1) : ℝ) * (‖x‖ ^ (1:ℝ) * ‖x‖ ^ ((2:ℕ) * -(N - 1) : ℝ)) := by
      rw [Real.rpow_one]; ring
    rw [e3, ← Real.rpow_add hxn]
    congr 2 <;> push_cast <;> rw [hN] <;> ring
  unfold gradComp
  rw [← hA, abs_mul, abs_of_nonneg hA0]
  calc A * |∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiG j (Torus.mk x) t|
      ≤ A * ((P * ‖x‖ * (Real.Gamma (N - 1) * θ1 ^ (-(N - 1))) +
          P * K * (Real.Gamma (N - 1) * θ2 ^ (-(N - 1)))) + M1 * Real.Gamma a) := by
        gcongr
        exact hint.trans (hBint ▸ by linarith)
    _ = A * (P * Real.Gamma (N - 1) * (‖x‖ * θ1 ^ (-(N - 1)))) +
          A * (P * K * (Real.Gamma (N - 1) * θ2 ^ (-(N - 1))) + M1 * Real.Gamma a) := by ring
    _ = _ := by rw [hθ1pow]; ring


theorem norm_toLp_le_sum {d : ℕ} (v : Fin d → ℝ) :
    ‖(WithLp.toLp 2 v : Euc d)‖ ≤ ∑ j, |v j| := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun j _ => abs_nonneg _)]
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun j => |v j|)
    (fun j _ => abs_nonneg _)
  simpa [Real.norm_eq_abs, sq_abs] using this

theorem periodicRiesz_grad_bound' {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ x : Euc d, x ≠ 0 → (∀ i, |x i| ≤ 1 / 2) →
      ‖periodicRieszGrad d s (Torus.mk x)‖ ≤ C * (‖x‖ ^ (-s - 1) + 1) := by
  choose C1 C2 hC1 hC2 hC using fun j => gradComp_bound hd hs0 hsd j
  refine ⟨∑ j, (C1 j + C2 j), fun x hx0 hx => ?_⟩
  rw [periodicRieszGrad_eq hsd x hx hx0]
  refine (norm_toLp_le_sum _).trans ?_
  have hr : 0 ≤ ‖x‖ ^ (-s - 1) := Real.rpow_nonneg (norm_nonneg _) _
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => (hC j x hx hx0).trans ?_
  have := hC1 j
  have := hC2 j
  nlinarith


end KernelAux

end KernelBox

section KernelFacts2

variable {d : ℕ} {s : ℝ}

open KernelAux

theorem integral_periodicRiesz (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s) ∧ ∫ x, periodicRiesz d s x = 0 := by
  refine ⟨integrable_periodicRiesz hd hs0 hsd, ?_⟩
  have h := integral_periodicRiesz_mode hd hs0 hsd 0
  simp only [neg_zero, Torus.mode_zero, one_mul] at h
  rw [integral_complex_ofReal] at h
  have h0 : rieszCoeff d s 0 = 0 := by simp [rieszCoeff]
  rw [h0] at h
  exact_mod_cast h


/-- `g` is smooth away from `0` and its Fourier coefficients are `ĝ` (KERN-01). -/
theorem periodicRiesz_fourierCoeff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) :
    Torus.funFourierCoeff (fun x => (periodicRiesz d s x : ℂ)) k = rieszCoeff d s k := by
  have h := integral_periodicRiesz_mode hd hs0 hsd k
  unfold Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  rw [Torus.volume_eq_pi_haar] at h
  simp only [smul_eq_mul]
  exact h


/-- Local normalisation `H:eq:intro-kernel` (lines 181-186): `g(x) = |x|^{-s} + O(1)` for
`0 < s < d`, with the regular part smooth near the origin (KERN-01). -/
theorem periodicRiesz_local_singularity (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d s (Torus.mk x) = ‖x‖ ^ (-s) + r (Torus.mk x) :=
  periodicRiesz_local_singularity' hd hs0 hsd

/-- Local normalisation in the logarithmic case: `g(x) = -log|x| + O(1)` (KERN-01). -/
theorem periodicLog_local_singularity (hd : 2 ≤ d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d 0 (Torus.mk x) = -Real.log ‖x‖ + r (Torus.mk x) :=
  periodicLog_local_singularity' hd

/-- Global bounds `|∇^{⊗n} g(x)| ≤ C_n (|x|^{-s-n} + 1)` away from `0`, for the
representative in `(-1/2, 1/2]^d` (KERN-01; cf. Lemma C.2 for the mollified version). -/
theorem periodicRiesz_grad_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ x : Euc d, x ≠ 0 → (∀ i, |x i| ≤ 1 / 2) →
      ‖periodicRieszGrad d s (Torus.mk x)‖ ≤ C * (‖x‖ ^ (-s - 1) + 1) :=
  periodicRiesz_grad_bound' hd hs0 hsd

namespace KernelAux2

theorem lintegral_sub_left_torus (F : Torus d → ℝ≥0∞) (x : Torus d) :
    ∫⁻ y, F (x - y) = ∫⁻ y, F y := by
  have : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  exact lintegral_sub_left_eq_self F x

theorem withDensityReal_le (ρ : Torus d → ℝ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    withDensityReal ρ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := by
  unfold withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hΛ x))

/-- A function whose absolute value has finite lintegral against `volume`. -/
theorem lintegral_conv_le (ρ : Torus d → ℝ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) (F : Torus d → ℝ≥0∞) (x : Torus d) :
    ∫⁻ y, F (x - y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal Λ * ∫⁻ y, F y := by
  calc ∫⁻ y, F (x - y) ∂(withDensityReal ρ)
      ≤ ∫⁻ y, F (x - y) ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
        lintegral_mono' (withDensityReal_le ρ Λ hΛ) le_rfl
    _ = ENNReal.ofReal Λ * ∫⁻ y, F y := by
        rw [lintegral_smul_measure, lintegral_sub_left_torus, smul_eq_mul]

theorem convMeasure_bounded' (g : Torus d → ℝ) (hg : Integrable g) (ρ : Torus d → ℝ)
    (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    ∃ C, ∀ x, |convMeasure g (withDensityReal ρ) x| ≤ C := by
  refine ⟨(ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal ‖g y‖).toReal, fun x => ?_⟩
  have h1 := norm_integral_le_lintegral_norm (μ := withDensityReal ρ) (fun y => g (x - y))
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (ENNReal.toReal_mono ?_ (lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal ‖g z‖) x))
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  have := hg.hasFiniteIntegral
  unfold HasFiniteIntegral at this
  simp only [← ofReal_norm] at this
  exact this.ne

theorem norm_toLp_le_card_mul (h : 0 < d) (y : Fin d → ℝ) : ‖(WithLp.toLp 2 y : Euc d)‖ ≤ d * ‖y‖ := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ∀ i, ‖(WithLp.toLp 2 y : Euc d) i‖ ^ 2 ≤ ‖y‖ ^ 2 := fun i => by
    have := norm_le_pi_norm y i
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have h2 : ∑ i, ‖(WithLp.toLp 2 y : Euc d) i‖ ^ 2 ≤ (d : ℝ) * ‖y‖ ^ 2 := by
    calc _ ≤ ∑ _i : Fin d, ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => h1 i
      _ = _ := by simp
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h
  calc Real.sqrt _ ≤ Real.sqrt ((d : ℝ) ^ 2 * ‖y‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg ‖y‖, mul_nonneg (sq_nonneg ‖y‖) (sub_nonneg.2 hd1)]
    _ = d * ‖y‖ := by
        rw [← mul_pow, Real.sqrt_sq (by positivity)]

theorem norm_le_norm_toLp (y : Fin d → ℝ) : ‖y‖ ≤ ‖(WithLp.toLp 2 y : Euc d)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := PiLp.norm_apply_le (WithLp.toLp 2 y : Euc d) i
  simpa using this

theorem lintegral_exp_abs_log_lt_top (hd : 2 ≤ d) {a : ℝ} (ha0 : 0 < a) (had : a < d) :
    ∫⁻ x : Torus d, ENNReal.ofReal (Real.exp (a * |periodicRiesz d 0 x|)) < ∞ := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicLog_local_singularity (d := d) hd
  obtain ⟨R, hR⟩ := (isCompact_closedBall (0 : Euc d) 1).exists_bound_of_continuousOn
    (f := Torus.lift r) (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous.continuousOn
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := periodicRiesz_box_bound (d := d) (s := 0) hd le_rfl
    (by exact_mod_cast hd0)
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  set θ : ℝ := δ' / d with hθ
  have hθ0 : 0 < θ := by positivity
  set M : ℝ := C1 * θ ^ (-((0 + (d:ℝ)) / 2)) + C2 with hM
  set B : ℝ := Real.exp (a * M) + Real.exp (a * R) * 1 with hB
  have hI : IntegrableOn (fun y : Fin d → ℝ => Real.exp (a * M) + Real.exp (a * R) * ‖y‖ ^ (-a)) (Box d) :=
    (integrableOn_const (measure_Box_ne_top d)).add
      ((integrableOn_Box_rpow hd0 had).const_mul _)
  have hne : ∀ᵐ y ∂(volume.restrict (Box d)), y ≠ 0 := ae_restrict_of_ae (ae_ne_pi hd0)
  rw [lintegral_torus_box (fun x => ENNReal.ofReal (Real.exp (a * |periodicRiesz d 0 x|)))]
  calc ∫⁻ y in Box d, ENNReal.ofReal (Real.exp (a * |periodicRiesz d 0 (boxPt y)|))
      ≤ ∫⁻ y in Box d, ENNReal.ofReal (Real.exp (a * M) + Real.exp (a * R) * ‖y‖ ^ (-a)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hne, ae_restrict_mem (measurableSet_Box d)] with y hy hyB
        refine ENNReal.ofReal_le_ofReal ?_
        have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
        have hrp : 0 ≤ Real.exp (a * R) * ‖y‖ ^ (-a) :=
          mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (norm_nonneg _) _)
        by_cases hcase : θ ≤ ‖y‖
        · -- away from the origin
          have h1 := hbd y hyB hy
          have h2 : ‖y‖ ^ (-((0 + (d:ℝ)) / 2)) ≤ θ ^ (-((0 + (d:ℝ)) / 2)) :=
            Real.rpow_le_rpow_of_nonpos hθ0 hcase (by have : (0:ℝ) ≤ (0 + (d:ℝ))/2 := by positivity
                                                      linarith)
          have h3 : |periodicRiesz d 0 (boxPt y)| ≤ M := by
            refine h1.trans ?_
            rw [hM]
            have := mul_le_mul_of_nonneg_left h2 hC1
            linarith
          have h4 : Real.exp (a * |periodicRiesz d 0 (boxPt y)|) ≤ Real.exp (a * M) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h3 ha0.le)
          linarith
        · -- near the origin
          replace hcase := not_le.1 hcase
          set x : Euc d := WithLp.toLp 2 y with hx
          have hxn : ‖x‖ < δ' := by
            have := norm_toLp_le_card_mul hd0 y
            have hdpos : (0:ℝ) < d := by positivity
            calc ‖x‖ ≤ d * ‖y‖ := this
              _ < d * θ := by gcongr
              _ = δ' := by rw [hθ]; field_simp
          have hx0 : x ≠ 0 := by
            intro h0
            apply hy
            ext i
            have := congrArg (fun z : Euc d => z i) h0
            simpa [hx] using this
          have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
          have hxδ : ‖x‖ < δ := lt_of_lt_of_le hxn (min_le_left _ _)
          have hx1 : ‖x‖ < 1 := lt_of_lt_of_le hxn (min_le_right _ _)
          have hg : periodicRiesz d 0 (boxPt y) = -Real.log ‖x‖ + r (Torus.mk x) := by
            have := hloc x hxδ hx0
            exact this
          have hrR : |r (Torus.mk x)| ≤ R := by
            have := hR x (by simpa using hx1.le)
            simpa [Torus.lift, Real.norm_eq_abs] using this
          have hlog : Real.log ‖x‖ < 0 := Real.log_neg hxpos hx1
          have habs : |periodicRiesz d 0 (boxPt y)| ≤ -Real.log ‖x‖ + R := by
            rw [hg]
            have := abs_le.1 hrR
            rw [abs_le]; constructor <;> linarith [this.1, this.2]
          have h4 : Real.exp (a * |periodicRiesz d 0 (boxPt y)|) ≤
              Real.exp (a * R) * ‖x‖ ^ (-a) := by
            calc _ ≤ Real.exp (a * (-Real.log ‖x‖ + R)) :=
                  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left habs ha0.le)
              _ = Real.exp (a * R) * ‖x‖ ^ (-a) := by
                  rw [Real.rpow_def_of_pos hxpos, ← Real.exp_add]
                  congr 1; ring
          have h5 : ‖x‖ ^ (-a) ≤ ‖y‖ ^ (-a) :=
            Real.rpow_le_rpow_of_nonpos hypos (norm_le_norm_toLp y) (by linarith)
          have h6 := mul_le_mul_of_nonneg_left h5 (Real.exp_pos (a * R)).le
          have := Real.exp_pos (a * M)
          linarith
    _ = ∫⁻ y in Box d, ‖Real.exp (a * M) + Real.exp (a * R) * ‖y‖ ^ (-a)‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [Real.enorm_of_nonneg (by positivity)]
    _ < ∞ := hI.2

end KernelAux2

/-- `g * μ` is bounded and continuous for a bounded density `μ` (`0 ≤ s < d`). -/
theorem convMeasure_bounded (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ρ : Torus d → ℝ)
    (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    ∃ C, ∀ x, |convMeasure (periodicRiesz d s) (withDensityReal ρ) x| ≤ C :=
  KernelAux2.convMeasure_bounded' _ (integrable_periodicRiesz hd hs0 hsd) ρ Λ hΛ

/-- Positive definiteness: `∬ g(x-y) dν(x) dν(y) ≥ 0` for finite signed measures with
zero mass having finite energy (expressed through Fourier coefficients). -/
theorem energy_nonneg_fourier (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c : Lattice d → ℝ) :
    0 ≤ ∑' k : Lattice d, rieszCoeff d s k * c k ^ 2 := by
  refine tsum_nonneg fun k => ?_
  by_cases hk : k = 0
  · simp [rieszCoeff, hk]
  · exact mul_nonneg (rieszCoeff_pos hd hs0 hsd k hk).le (sq_nonneg _)

/-- Lemma 4.24 `M:lem:periodic-log-row` (source lines 5572-5578): for `μ` with a bounded
density on `𝕋^d` and `a ∈ (0,d)`, the canonically centered periodic logarithmic kernel
satisfies `sup_x ∫ e^{a|g_μ(x,y)|} dμ(y) < ∞`.  Here the canonically centered kernel is
`g_μ(x,y) = g(x-y) - g*μ(x) - g*μ(y) + ∬ g dμ dμ`. -/
def centeredKernel {d : ℕ} (g : Torus d → ℝ) (μ : Measure (Torus d)) (x y : Torus d) : ℝ :=
  g (x - y) - convMeasure g μ x - convMeasure g μ y + energyPairing g μ μ

theorem periodic_log_row (hd : 2 ≤ d) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ)
    (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) (a : ℝ) (ha0 : 0 < a) (had : a < d) :
    ∃ C : ℝ, ∀ x, ∫⁻ y, ENNReal.ofReal
      (Real.exp (a * |centeredKernel (periodicRiesz d 0) (withDensityReal ρ) x y|))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal C := by
  have hd0 : 0 < d := by omega
  obtain ⟨C0, hC0⟩ := convMeasure_bounded (s := 0) hd le_rfl (by exact_mod_cast hd0) ρ hρ Λ hΛ
  set I : ℝ≥0∞ := ∫⁻ z : Torus d, ENNReal.ofReal (Real.exp (a * |periodicRiesz d 0 z|)) with hI
  have hIt : I ≠ ∞ := (KernelAux2.lintegral_exp_abs_log_lt_top hd ha0 had).ne
  set E : ℝ := energyPairing (periodicRiesz d 0) (withDensityReal ρ) (withDensityReal ρ) with hE
  set K : ℝ := 2 * C0 + |E| with hK
  refine ⟨(ENNReal.ofReal Λ * (ENNReal.ofReal (Real.exp (a * K)) * I)).toReal, fun x => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIt))]
  have hpt : ∀ y, ENNReal.ofReal
      (Real.exp (a * |centeredKernel (periodicRiesz d 0) (withDensityReal ρ) x y|)) ≤
      ENNReal.ofReal (Real.exp (a * K)) *
        ENNReal.ofReal (Real.exp (a * |periodicRiesz d 0 (x - y)|)) := by
    intro y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : |centeredKernel (periodicRiesz d 0) (withDensityReal ρ) x y| ≤
        |periodicRiesz d 0 (x - y)| + K := by
      unfold centeredKernel
      have hx := hC0 x
      have hy := hC0 y
      rw [← hE]
      calc _ ≤ |periodicRiesz d 0 (x - y) - convMeasure (periodicRiesz d 0) (withDensityReal ρ) x
              - convMeasure (periodicRiesz d 0) (withDensityReal ρ) y| + |E| := abs_add_le _ _
        _ ≤ |periodicRiesz d 0 (x - y) - convMeasure (periodicRiesz d 0) (withDensityReal ρ) x|
              + |convMeasure (periodicRiesz d 0) (withDensityReal ρ) y| + |E| := by
            gcongr; exact abs_sub _ _
        _ ≤ |periodicRiesz d 0 (x - y)| + |convMeasure (periodicRiesz d 0) (withDensityReal ρ) x|
              + |convMeasure (periodicRiesz d 0) (withDensityReal ρ) y| + |E| := by
            gcongr; exact abs_sub _ _
        _ ≤ _ := by rw [hK]; linarith
    nlinarith
  calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (a * K)) *
        ENNReal.ofReal (Real.exp (a * |periodicRiesz d 0 (x - y)|)) ∂(withDensityReal ρ) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (a * K)) *
        ∫⁻ y, ENNReal.ofReal (Real.exp (a * |periodicRiesz d 0 (x - y)|)) ∂(withDensityReal ρ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (a * K)) * (ENNReal.ofReal Λ * I) := by
        gcongr
        exact KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (Real.exp (a * |periodicRiesz d 0 z|))) x
    _ = _ := by ring


end KernelFacts2

/-! ### The response inverse (work package KERN-02) -/

section Response

variable {d : ℕ} {s : ℝ}

/-- General form of `exists_unique_response`: any integrable kernel with real nonnegative
Fourier coefficients. -/
theorem exists_unique_response_of_kernel {g : Torus d → ℝ} (hgi : Integrable g)
    (ĝ : Lattice d → ℝ) (hĝ : ∀ n, 0 ≤ ĝ n)
    (hcoef : ∀ n, Torus.funFourierCoeff (fun x => (g x : ℂ)) n = (ĝ n : ℂ))
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ)
    (β : ℝ) (hβ : 0 ≤ β) (ψ : Torus d → ℝ) (hψ : MemLp ψ 2 (withDensityReal ρ)) :
    ∃ h, IsResponse g (withDensityReal ρ) β ψ h ∧
      ∀ h', IsResponse g (withDensityReal ρ) β ψ h' → h' =ᵐ[withDensityReal ρ] h :=
  ResponseAux.exists_unique_respEq_general hgi ĝ hĝ
    (ResponseAux.hcoef_of_funFourierCoeff hcoef) hρ hΛ hβ hψ

/-- General form of `susceptibilityCov_bounds`. -/
theorem susceptibilityCov_bounds_of_kernel {g : Torus d → ℝ} (hgi : Integrable g)
    (ĝ : Lattice d → ℝ) (hĝ : ∀ n, 0 ≤ ĝ n)
    (hcoef : ∀ n, Torus.funFourierCoeff (fun x => (g x : ℂ)) n = (ĝ n : ℂ))
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ)
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c C : ℝ, 0 < c ∧ ∀ φ : Torus d → ℝ, MemLp φ 2 (withDensityReal ρ) →
      c * l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
          (projMean (withDensityReal ρ) φ) ≤
        susceptibilityCov g (withDensityReal ρ) β φ φ ∧
      susceptibilityCov g (withDensityReal ρ) β φ φ ≤
        C * l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
          (projMean (withDensityReal ρ) φ) := by
  obtain ⟨c, hc, H⟩ := ResponseAux.susc_bounds_general hgi ĝ hĝ
    (ResponseAux.hcoef_of_funFourierCoeff hcoef) hρ hΛ hβ
  refine ⟨c, 1, hc, fun φ hφ => ?_⟩
  have hex := exists_unique_response_of_kernel hgi ĝ hĝ hcoef ρ hρ Λ hΛ β hβ φ hφ
  have hex' : ∃ h, IsResponse g (withDensityReal ρ) β φ h :=
    let ⟨h, hh, _⟩ := hex; ⟨h, hh⟩
  have hr : IsResponse g (withDensityReal ρ) β φ (responseInverse g (withDensityReal ρ) β φ) := by
    have e : responseInverse g (withDensityReal ρ) β φ = hex'.choose := by
      unfold responseInverse
      simp only [hex', dite_true]
    rw [e]
    exact hex'.choose_spec
  obtain ⟨h1, h2⟩ := H φ _ hφ hr
  refine ⟨h1, ?_⟩
  rw [one_mul]
  exact h2

/-- `K_μ` is a bounded nonnegative self-adjoint operator on `L²_0(μ)` for a bounded density
`μ` and `0 ≤ s < d` (positivity of `ĝ`); hence for every `β ≥ 0` and `ψ ∈ L²(μ)` the
response equation has a unique solution (KERN-02). -/
theorem exists_unique_response (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ)
    (β : ℝ) (hβ : 0 ≤ β) (ψ : Torus d → ℝ) (hψ : MemLp ψ 2 (withDensityReal ρ)) :
    ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h ∧
      ∀ h', IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h' →
        h' =ᵐ[withDensityReal ρ] h := by
  have h0 : ∀ n : Lattice d, 0 ≤ rieszCoeff d s n := fun n => by
    by_cases hn : n = 0
    · simp [rieszCoeff, hn]
    · exact (rieszCoeff_pos hd hs0 hsd n hn).le
  exact exists_unique_response_of_kernel (integral_periodicRiesz hd hs0 hsd).1 _ h0
    (periodicRiesz_fourierCoeff hd hs0 hsd) ρ hρ Λ hΛ β hβ ψ hψ

/-- The susceptibility form is symmetric and nonnegative, bounded above and below by
multiples of `‖P_μ φ‖²_{L²(μ)}` (used in Proposition 2.4; KERN-02). -/
theorem susceptibilityCov_bounds (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ)
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c C : ℝ, 0 < c ∧ ∀ φ : Torus d → ℝ, MemLp φ 2 (withDensityReal ρ) →
      c * l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
          (projMean (withDensityReal ρ) φ) ≤
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ φ ∧
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ φ ≤
        C * l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
          (projMean (withDensityReal ρ) φ) := by
  have h0 : ∀ n : Lattice d, 0 ≤ rieszCoeff d s n := fun n => by
    by_cases hn : n = 0
    · simp [rieszCoeff, hn]
    · exact (rieszCoeff_pos hd hs0 hsd n hn).le
  exact susceptibilityCov_bounds_of_kernel (integral_periodicRiesz hd hs0 hsd).1 _ h0
    (periodicRiesz_fourierCoeff hd hs0 hsd) ρ hρ Λ hΛ β hβ

end Response

end HRS
