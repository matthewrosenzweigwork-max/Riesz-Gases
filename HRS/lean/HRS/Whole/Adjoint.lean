import HRS.Whole.Dynamics
import HRS.PDE.ToolboxRd.Defs

/-!
# Whole-space adjoint estimates (package S-ADJ-01): Sections S4.10-S4.14 and S5.1

Source: HRS whole-space supplement (S).

* S4.10 `W:r2:far-derivatives` (S lines 2961-2975), S4.11 `W:r2:local-decay` (3003-3019),
  S4.12 `W:r2:adjoint-decay` (3066-3084), S4.13 `W:r2:fractional-decay` (3107-3120),
  S4.14 `W:r2:sharp-all-sub` (3153-3166); the decay norm `W:r2:decay-norm` (2951-2953).
* S5.1 `W:r2:ul-adjoint` (3204-3235), with the uniformly local norm (S lines 3192-3198).

## Representation decisions

* Weighted sup norms (`W:r2:decay-norm`, `‖f‖_{k,b} = max_{|α|≤k} sup_x ⟨x⟩^{b+|α|}|∂^α f(x)|`) are
  `ℝ≥0∞`-valued (`decayNormE`; `∂^α f` as the iterated Fréchet derivative applied to coordinate
  vectors), so that "infinite norm" is `⊤`, never a junk `0`; bounds read `‖·‖ ≤ C ‖·‖` in `ℝ≥0∞`.
  Statements apply them to smooth functions, and assert the needed smoothness in the conclusion.
* The uniformly local norm `‖f‖_{H^r_ul} = sup_{z∈ℤ^d} ‖θ(·-z) f‖_{H^r(ℝ^d)}` (S lines 3192-3198) is
  `ulNormE` (`ℝ≥0∞`, `⊤` when some `θ(·-z)f ∉ H^r`), with the Fourier definition of `H^r` of
  `HRS.PDE.ToolboxRd` (`sobolevNormSq`); the cutoff `θ` is a fixed parameter satisfying
  `IsUlCutoff` and the constants may depend on it (the norm changes by equivalent constants
  with `θ`, S line 3197).  The supplement's `H^m_uloc` (S line 9637, sup over `z ∈ ℝ^d`) of
  S4.12/S4.14 is the same space with an equivalent norm.
* "`|D|^α v ∈ L^p`" for a function `v` with only algebraic decay is understood distributionally
  (`IsFracDerivRep`: `∫ v |D|^α φ = ∫ w φ` for all Schwartz `φ`, `|D|^α φ = 𝓕⁻[(2π|ξ|)^α 𝓕φ]`);
  the Fourier transform of `v` itself may not exist (`v ∉ L¹`), so Mathlib's `fracGradPow` (junk
  `0` for non-integrable `v`) would make S4.13 trivially true and is not used.
* "The whole-space uniformly local adjoint theorem applies, uniformly in `0 ≤ ν ≤ ν_*`, through
  derivative order `j` in `C_b`" (S4.12, S lines 3068-3070, and S5 hypotheses) is the predicate
  `UlAdjointInput`: for every smooth terminal test `φ` with finite `H^{j+1+⌈d/2⌉}_ul` norm
  (the index used in the proof, S lines 3098-3101) the classical adjoint solution exists and
  `‖U(r,t)φ‖_{C_b^j} ≤ K ‖φ‖_{H^{j+1+⌈d/2⌉}_ul}`, `K` independent of `ν` and of `r ≤ t ≤ T`.
  This replaces the regime/theorem citations (`B:thm:adjoint-rd`, `B:thm:adjoint-lp`), which are
  not formalized here.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.Whole

variable {d N : ℕ}

/-! ### Weighted norms -/

/-- `⟨x⟩ = (1+|x|²)^{1/2}`. -/
def jbracket (x : Euc d) : ℝ := Real.sqrt (1 + ‖x‖ ^ 2)

/-- The partial derivative `∂_{i_1}⋯∂_{i_j} f(x) = D^j f(x)[e_{i_1},…,e_{i_j}]`. -/
def partialDeriv {j : ℕ} (i : Fin j → Fin d) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  iteratedFDeriv ℝ j f x (fun l => EuclideanSpace.single (i l) 1)

/-- `max_{|α|≤k} sup_x ⟨x⟩^{w(|α|)} |∂^α f(x)|` in `ℝ≥0∞` (derivatives of order `j ≤ k`,
all index tuples; a multi-index `α` with `|α| = j` is a symmetric class of index tuples). -/
def derivSupE (k : ℕ) (w : ℕ → ℝ) (f : Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ j : Fin (k + 1), ⨆ i : Fin (j : ℕ) → Fin d, ⨆ x : Euc d,
    ENNReal.ofReal (jbracket x ^ w j * |partialDeriv i f x|)

/-- The decay norm `‖f‖_{k,b} = max_{|α|≤k} sup_x ⟨x⟩^{b+|α|}|∂^α f(x)|`
(`W:r2:decay-norm`, S lines 2951-2953). -/
def decayNormE (k : ℕ) (b : ℝ) (f : Euc d → ℝ) : ℝ≥0∞ := derivSupE k (fun j => b + j) f

/-- `max_{|α|≤k} sup_x ⟨x⟩^{L}|∂^α f(x)|` (S lines 2962-2964: the weight exponent does not grow with
`|α|`). -/
def weightedSupE (k : ℕ) (L : ℝ) (f : Euc d → ℝ) : ℝ≥0∞ := derivSupE k (fun _ => L) f

/-- `‖v‖_{k,b}` of a vector field, componentwise ("a vector-valued function is treated
componentwise", S line 2955). -/
def decayNormVecE (k : ℕ) (b : ℝ) (v : Euc d → Euc d) : ℝ≥0∞ :=
  ⨆ i : Fin d, decayNormE k b fun x => v x i

/-- `Σ_j ∂_j g * G_j` for a vector field `G` (the contracted convolution `Div g*G`, plain
Bochner integral; absolutely convergent when `s + 1 < d` and `G` is bounded and integrable, which is
the case in S4.10 where `s ≤ d - 2`). -/
def divGConvPlain (d : ℕ) (s : ℝ) (G : Euc d → Euc d) (x : Euc d) : ℝ :=
  ∑ j : Fin d, ∫ y, rieszKernelGrad d s (x - y) j * G y j

/-- `∇g * h (x) = ∫ ∇g(x-y) h(y) dy` for a scalar `h` (plain Bochner integral). -/
def gradGConvPlain (d : ℕ) (s : ℝ) (h : Euc d → ℝ) (x : Euc d) : Euc d :=
  ∫ y, h y • rieszKernelGrad d s (x - y)

/-! ### The uniformly local scale -/

/-- A cutoff `θ ∈ C_c^∞` equal to `1` on `[-2,2]^d` (S lines 3191-3193). -/
def IsUlCutoff (θ : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ ∀ x : Euc d, (∀ i, |x i| ≤ 2) → θ x = 1

open Classical in
/-- `‖u‖_{H^r(ℝ^d)}` in `ℝ≥0∞` (`⊤` if `u ∉ H^r`). -/
def sobolevNormE (r : ℝ) (u : Euc d → ℝ) : ℝ≥0∞ :=
  if HRS.PDE.ToolboxRd.MemSobolev r u then
    ENNReal.ofReal (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r u)) else ⊤

/-- The lattice point `z ∈ ℤ^d ⊂ ℝ^d`. -/
def latticePt (z : Fin d → ℤ) : Euc d := WithLp.toLp 2 fun i => (z i : ℝ)

/-- The cell centres `⌈√d⌉⁻¹ • ℤ^d`: the closed balls of radius `1` about them cover `ℝ^d` (every point is within
`√d / (2⌈√d⌉) ≤ 1/2` of a centre).  Statement repair `MH-REPAIRS-1` / `MS-ULOC-LAT` (docs/ISSUES.md): the closed unit
balls about `ℤ^d` cover `ℝ^d` only for `d ≤ 4`. -/
def cellPt (d : ℕ) (z : Fin d → ℤ) : Euc d := ((⌈Real.sqrt d⌉ : ℝ)⁻¹) • latticePt z

/-- `‖f‖_{H^r_ul} = sup_{z∈ℤ^d} ‖θ(·-z) f‖_{H^r(ℝ^d)}` (S lines 3195-3198), `r` a natural number. -/
def ulNormE (r : ℕ) (θ : Euc d → ℝ) (f : Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ z : Fin d → ℤ, sobolevNormE (r : ℝ) fun x => θ (x - latticePt z) * f x

/-- `C_c^∞` plus a constant. -/
def IsCcInftyPlusConst (g : Euc d → ℝ) : Prop :=
  ∃ (h : Euc d → ℝ) (c : ℝ), ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ g = fun x => h x + c

/-- The closure of `C_c^∞` (constants adjoined) in the `H^k_ul` norm (S lines 3199-3201: "we take
the closure of `C_c^∞` in this norm, and may adjoin the constants"); the representative is taken
`C²` (for `k > d/2 + 2` every element has a `C²` representative). -/
def UlClosure (k : ℕ) (θ : Euc d → ℝ) (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ ε : ℝ, 0 < ε → ∃ g, IsCcInftyPlusConst g ∧
    ulNormE k θ (fun x => f x - g x) ≤ ENNReal.ofReal ε

/-- `u : [0,t] → H^k_ul` is a backward evolution with terminal datum `f` for the generator `C`
in the uniformly local scale: a classical adjoint solution (`IsClassicalAdjointW`) with values in
the closure `UlClosure k θ`, strongly continuous in the `H^k_ul` norm. -/
structure IsUlBackwardEvolution (θ : Euc d → ℝ) (k : ℕ) (C : WholeCoeff d) (t : ℝ)
    (f : Euc d → ℝ) (u : ℝ → Euc d → ℝ) : Prop where
  classicalSol : IsClassicalAdjointW C t f u
  mem : ∀ r ∈ Set.Icc 0 t, UlClosure k θ (u r)
  cont : ∀ r₀ ∈ Set.Icc 0 t, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Set.Icc 0 t,
    |r - r₀| < δ → ulNormE k θ (fun x => u r x - u r₀ x) ≤ ENNReal.ofReal ε

/-- The adjoint input "the whole-space uniformly local adjoint theorem applies through derivative
order `j` in `C_b`" with constant `K` (see the module docstring): for `0 ≤ r ≤ t ≤ T` and every
`φ ∈ C^{j+1+⌈d/2⌉}` with finite `H^{j+1+⌈d/2⌉}_ul` norm the classical adjoint solution
(`IsClassicalAdjointW`, with the repaired growth condition on `∂_r f`, see there) exists and
`‖U(r,t)φ‖_{C_b^j} ≤ K ‖φ‖_{H^{j+1+⌈d/2⌉}_ul}`.  The data class is finitely smooth, not `C^∞`:
S5.5 (S L3914-3919) applies the adjoint estimate to `L_N^t φ_j`, which is only
`C^{k+6+⌈d/2⌉}` (the density `ρ` has finitely many derivatives).  The TeX (S L3199-3202, "every
function to which the evolution is applied belongs to the closure of `C_c^∞` in `H^k_ul`") restricts
the data to that closure for strong continuity; for the *existence/bound* statement here the
`C^{j+1+⌈d/2⌉} ∩ H_ul` class is what is used (this contains the closure's elements of that
smoothness). -/
def UlAdjointInput (θ : Euc d → ℝ) (C : WholeCoeff d) (T : ℝ) (j : ℕ) (K : ℝ) : Prop :=
  ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
    ContDiff ℝ ((j + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
    ulNormE (j + 1 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
    (∃ f, IsClassicalAdjointW C t φ f) ∧ MemCb j (propagatorW C r t φ) ∧
      cbNorm j (propagatorW C r t φ) ≤ K * (ulNormE (j + 1 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal

/-- The standing hypotheses of S4.12 (S lines 3066-3075) for one pair `(ν, ρ)`:
`0 ≤ s ≤ d-2`; `ν ∈ [0, ν_*]`; `Q` symmetric; `ρ_t` (`t ∈ [0,T]`) probability densities, `C^{k+1}`,
with `max_{|α|≤k+1} sup_x ⟨x⟩^L|∂^α ρ_t| ≤ Λ`, common exponent `L > d + k + s + 4`; the adjoint input
through order `k+1` in `C_b` with constant `K`.  The generator is that of the dynamics with
`V(x) = xᵀQx/2 + c·x`, interaction matrix `M`, along `ρ`. -/
structure AdjointDecayHyp (θ : Euc d → ℝ) (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d)
    (T νstar : ℝ) (k : ℕ) (L Λ K : ℝ) (ν : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop where
  s_range : 0 ≤ s ∧ s ≤ (d : ℝ) - 2
  ν_range : 0 ≤ ν ∧ ν ≤ νstar
  Q_symm : Q.IsSymm
  L_range : (d : ℝ) + k + s + 4 < L
  density : ∀ t ∈ Set.Icc 0 T, IsProbDensity (ρ t) ∧ ContDiff ℝ (k + 1) (ρ t) ∧
    weightedSupE (k + 1) L (ρ t) ≤ ENNReal.ofReal Λ
  adjoint : UlAdjointInput θ ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) T (k + 1) K
  /-- Joint continuity of the interaction drift `(t,x) ↦ (∇g * ρ_t)(x)` on `[0,T] × ℝ^d` (needed
  by S4.11; supplement repair P2). -/
  drift_cont : ContinuousOn
    (fun p : ℝ × Euc d => convGradConvW (rieszKernelGrad d s) (ρ p.1) p.2)
    (Set.Icc 0 T ×ˢ Set.univ)

/-- `Comm_N(v; X_N, μ) = ∬_{x≠y} (v(x)-v(y))·∇g(x-y) d(μ_N-μ)^{⊗2}` with the deleted particle
diagonal (M line 2819; S line 6411 `𝖢_N`); equal to `2 𝖥_N^{h_v}` (`S3.2`). -/
def commN (d : ℕ) (s : ℝ) (v : Euc d → Euc d) (X : EucConfig d N) (μ : Measure (Euc d)) : ℝ :=
  centeredPairFunctional (commutatorKernel d s v) X μ

/-! ### S4.10 -/

/-- Lemma S4.10 (S:W:r2:far-derivatives, TeX S L2961-2975).  `d ≥ 2`, `0 ≤ s ≤ d - 2`, `k ≥ 0`,
`L > d + k + s + 3`.  (a) If `h` is `C^k` (supplement repair P2: smoothness is not needed, and S4.12 applies
this to `ρ_t`, which is only `C^{k+1}`) and `A = max_{|α|≤k} sup_x ⟨x⟩^L |∂^α h(x)| < ∞`, then
`∇g * h` is `C^k` and `‖∇g*h‖_{k,s+1} ≤ C A`.  (b) In particular, if `ρ ∈ C^k` has the displayed weighted
derivative bounds (`A_ρ ≤ Λρ`; only `C^k`, as fed by S4.12) and `f ∈ C_b^{k+1}`, then `div g*(ρ Mᵀ∇f)` is `C^k` and
`‖div g*(ρ Mᵀ∇f)‖_{k,s+1} ≤ C ‖f‖_{C_b^{k+1}}`; `C` depends on `d, s, k, L, M, Λρ`, on no
support radius.  Technical hypotheses: none (`k` is a natural number; `∇g*h` is the plain integral,
absolutely convergent as `s + 1 < d`). -/
theorem far_derivatives (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (k : ℕ)
    (L : ℝ) (hL : (d : ℝ) + k + s + 3 < L) :
    (∃ C : ℝ, ∀ h : Euc d → ℝ, ContDiff ℝ k h → weightedSupE k L h < ⊤ →
      ContDiff ℝ k (gradGConvPlain d s h) ∧
        decayNormVecE k (s + 1) (gradGConvPlain d s h) ≤ ENNReal.ofReal C * weightedSupE k L h) ∧
    ∀ (M : Matrix (Fin d) (Fin d) ℝ) (Λρ : ℝ), ∃ C : ℝ, ∀ ρ : Euc d → ℝ, ContDiff ℝ k ρ →
      weightedSupE k L ρ ≤ ENNReal.ofReal Λρ → ∀ f : Euc d → ℝ, MemCb (k + 1) f →
        ContDiff ℝ k (fun x => divGConvPlain d s
          (fun y => ρ y • Torus.matVec M.transpose (gradient f y)) x) ∧
        decayNormE k (s + 1) (fun x => divGConvPlain d s
          (fun y => ρ y • Torus.matVec M.transpose (gradient f y)) x) ≤
          ENNReal.ofReal (C * cbNorm (k + 1) f) := by
  sorry

/-! ### S4.11 -/

/-- A bounded classical backward solution on `[0,t]` of `∂_r u + ν_r Δu + b_r·∇u = 0`,
`u(t) = f` (the backward local evolution `P(r,t)f`, S lines 3004-3006, of the stochastic flow of
`dX = b dt + √(2ν) dW`; bounded classical solutions are unique). -/
structure IsLocalBackwardSolution (ν : ℝ → ℝ) (b : ℝ → Euc d → Euc d) (t : ℝ) (f : Euc d → ℝ)
    (u : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc 0 t, ContDiff ℝ 2 (u r)
  bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ x, |u r x| ≤ B
  cont : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => u p.1 p.2
  terminal : u t = f
  time_deriv : ∀ x : Euc d, ∀ r ∈ Set.Ioo 0 t,
    HasDerivAt (fun r' => u r' x)
      (-(ν r * Laplacian.laplacian (u r) x + inner ℝ (b r x) (gradient (u r) x))) r

/-- Lemma S4.11 (S:W:r2:local-decay, TeX S L3003-3019).  `Q` a fixed real matrix,
`b_t(x) = -Qx - c_t + B_t(x)` on `[0,T]` with `c_t ∈ ℝ^d` independent of `x` (S L3006: `c_t` is a
bounded *vector*; an `x`-dependent `c` would make the lemma false, e.g. `c(x) = min(|x₁|,1)e₁`
admits no `C²` solution), `c` bounded, `sup_t (‖B_t‖_{C_b^{k+1}} + ‖B_t‖_{k+1,s+1}) < ∞` (each
bounded by `ΛB`).  The backward local evolution satisfies `‖P(r,t)f‖_{k,b} ≤ C_{T,k,b}‖f‖_{k,b}`,
`0 ≤ r ≤ t ≤ T`, for every `b > 0`, uniformly in the viscosity `0 ≤ ν ≤ ν_*`; the viscosity may be
a continuous function `ν_r ∈ [0,ν_*]` of time (a constant is a special case).  The constant depends
on `d, s, Q, k, T, ν_*, b, Λc, ΛB` (quantified before `ν, c, B, f`).  Test functions `f` are `C^{max(k,2)}`
(supplement repair P2: the classical solution is `C²` up to `r = t` where `u t = f`; smoothness is not
needed) with finite `‖f‖_{k,b}`; existence of the solution is part of the conclusion, smoothness `C^k` of
`u_r` too.
Technical hypotheses: `0 ≤ s` (the section works with `0 ≤ s`; for `s ≤ -2` the bound fails);
`2 ≤ k` (repair 2026-10-21, approved by the author after independent review: the proof differentiates the stochastic flow twice under the expectation, which needs `D²f` controlled by `‖f‖_{k,b}`; for `k = 1` the statement is not refuted but needs Bismut–Elworthy–Li type regularity, and no consumer uses `k = 1`; `adjoint_decay` has `hk2 : 2 ≤ k`; the classical formulation also needs `u_r ∈ C²` and `B_t ∈ C^{k+1}`); continuity of
`t ↦ c_t` and joint continuity of `(t,x) ↦ B_t(x)` on `[0,T] × ℝ^d` (the drift of the flow is
continuous in `(τ,x)`, S lines 10052-10060). -/
theorem local_decay (hd : 2 ≤ d) (s : ℝ) (hs : 0 ≤ s) (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ)
    (hk : 2 ≤ k) (T νstar bexp Λc ΛB : ℝ) (hb : 0 < bexp) :
    ∃ C : ℝ, ∀ (ν : ℝ → ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d), Continuous ν →
      (∀ r, 0 ≤ ν r ∧ ν r ≤ νstar) →
      ContinuousOn c (Set.Icc 0 T) →
      ContinuousOn (fun p : ℝ × Euc d => B p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) →
      (∀ t ∈ Set.Icc 0 T, ‖c t‖ ≤ Λc) →
      (∀ t ∈ Set.Icc 0 T, ContDiff ℝ (k + 1) (B t) ∧
        (∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j (B t) x‖ ≤ ΛB) ∧
        decayNormVecE (k + 1) (s + 1) (B t) ≤ ENNReal.ofReal ΛB) →
      ∀ t ∈ Set.Icc 0 T, ∀ f : Euc d → ℝ, ContDiff ℝ ((max k 2 : ℕ) : WithTop ℕ∞) f → decayNormE k bexp f < ⊤ →
        (∃ u, IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f u) ∧
        ∀ u, IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f u →
          ∀ r ∈ Set.Icc 0 t, ContDiff ℝ k (u r) ∧
            decayNormE k bexp (u r) ≤ ENNReal.ofReal C * decayNormE k bexp f := by
  sorry

/-! ### S4.12 -/

/-- Proposition S4.12 (S:W:r2:adjoint-decay, TeX S L3066-3084).  Under `AdjointDecayHyp`
(`0 ≤ s ≤ d-2`, the uniformly local adjoint theorem through order `k+1` uniformly in `ν ∈ [0,ν_*]`,
uniform weighted bounds on the derivatives of `ρ_t` through order `k+1` with a common exponent
`L > d + k + s + 4`, `V = xᵀQx/2 + c·x`, `Q` symmetric) the full adjoint evolution satisfies
`‖U(r,t)φ‖_{k,s+1} ≤ C_T(‖φ‖_{k,s+1} + ‖φ‖_{H^{k+2+⌈d/2⌉}_ul})`, `C_T` independent of the support of
`φ`, of `r, t` and of the viscosity in its interval.  The constant is quantified before the family
`(ν, ρ)` and depends only on `d, s, k, L, Λ, K, T, ν_*, M, Q, c` and the cutoff `θ`.  The matrix `M`
is arbitrary (S lines 3081-3083); `U(r,t)φ` is `propagatorW` (existence is part of the adjoint
input); smoothness `C^k` of `U(r,t)φ` is part of the conclusion.  Technical hypotheses: `φ` is
`C^{k+2+⌈d/2⌉}` with finite `H^{k+2+⌈d/2⌉}_ul` norm (so the adjoint solution exists and the `C^k`
conclusion is meaningful; the `H_ul` norm is finite in the bound's right side anyway); `ρ_t ∈ C^{k+1}` (the weighted
derivative bounds on `ρ_t` presuppose these derivatives); `d ≥ 2`; `k ≥ 2` (supplement repair P2: for
`k = 1` the Duhamel source is only `C¹`; the consumers have `k > 2`); joint continuity of the drift
`(t,x) ↦ ∇g*ρ_t(x)` (`AdjointDecayHyp.drift_cont`). -/
theorem adjoint_decay (hd : 2 ≤ d) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (s : ℝ)
    (M Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d) (T νstar : ℝ) (k : ℕ) (hk2 : 2 ≤ k)
    (L Λ K : ℝ) :
    ∃ C : ℝ, ∀ (ν : ℝ) (ρ : ℝ → Euc d → ℝ), AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
        ContDiff ℝ ((k + 2 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
        ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
        ContDiff ℝ k (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) ∧
        decayNormE k (s + 1) (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) ≤
          ENNReal.ofReal C * (decayNormE k (s + 1) φ +
            ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ) := by
  sorry

/-! ### S4.13 -/

/-- `w` represents the fractional derivative `|D|^α v` in the sense of distributions:
`∫ v · 𝓕⁻[(2π|ξ|)^α 𝓕φ] = ∫ w φ` for every Schwartz function `φ` (both integrals absolutely
convergent).  The multiplier `(2π|ξ|)^α` differs from `|ξ|^α` by a constant factor, absorbed in the
constants of the statements. -/
def IsFracDerivRep (α : ℝ) (v w : Euc d → ℝ) : Prop :=
  ∀ φ : SchwartzMap (Euc d) ℂ,
    Integrable (fun x => ((v x : ℝ) : ℂ) *
      (𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) x) ∧
    Integrable (fun x => ((w x : ℝ) : ℂ) * φ x) ∧
    ∫ x, ((v x : ℝ) : ℂ) *
        (𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) x =
      ∫ x, ((w x : ℝ) : ℂ) * φ x

/-- Lemma S4.13 (S:W:r2:fractional-decay, TeX S L3107-3120), first assertion
`W:r2:fractional-decay-bound`: `b > 0`, `α > 0`, `1 < p < ∞`, `k` an integer larger than `α`,
`b + α > d/p`: for every smooth `v` (with finite `‖v‖_{k,b}`) `|D|^α v` (distributional) is in `L^p`
and `‖|D|^α v‖_{L^p} ≤ C‖v‖_{k,b}`.  Technical hypothesis: `v` is `C^k` (the norm `‖v‖_{k,b}` involves
its derivatives); `d ≥ 2` (standing). -/
theorem fractional_decay (hd : 2 ≤ d) (bexp α p : ℝ) (k : ℕ) (hb : 0 < bexp) (hα : 0 < α)
    (hp : 1 < p) (hk : α < k) (hbα : (d : ℝ) / p < bexp + α) :
    ∃ C : ℝ, ∀ v : Euc d → ℝ, ContDiff ℝ k v → decayNormE k bexp v < ⊤ →
      ∃ w : Euc d → ℝ, IsFracDerivRep α v w ∧ MemLp w (ENNReal.ofReal p) volume ∧
        eLpNorm w (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * decayNormE k bexp v := by
  sorry

/-- Lemma S4.13 (S:W:r2:fractional-decay, TeX S L3107-3120), second assertion
`W:r2:sharp-tail-bound` (S L3114-3118): for `a ∈ (d, d+2)`,
`k > a/2 + 1` an integer and `s ≥ 0`,
`‖D²f‖_∞ + ‖|D|^{a/2}∇f‖_{L^{2d/(a-2)}} ≤ C‖f‖_{k,s+1}` (`∇f` componentwise, summed over the
components; `‖D²f‖_∞ = sup_x ‖D²f(x)‖` operator norm), for every smooth `f` with finite
`‖f‖_{k,s+1}`.  Technical hypothesis: `f` is `C^k`; `d ≥ 2` (standing). -/
theorem sharp_tail_bound (hd : 2 ≤ d) (a s : ℝ) (k : ℕ) (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2)
    (hk : a / 2 + 1 < k) (hs : 0 ≤ s) :
    ∃ C : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ k f → decayNormE k (s + 1) f < ⊤ →
      ∃ w : Fin d → Euc d → ℝ, (∀ i, IsFracDerivRep (a / 2) (fun x => gradient f x i) (w i)) ∧
        (∀ i, MemLp (w i) (ENNReal.ofReal (2 * d / (a - 2))) volume) ∧
        (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
          ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (a - 2))) volume ≤
            ENNReal.ofReal C * decayNormE k (s + 1) f := by
  sorry

/-! ### S4.14 -/

/-- Corollary S4.14 (S:W:r2:sharp-all-sub, TeX S L3153-3166).  For the trajectories and adjoints
of Proposition S4.12 (`AdjointDecayHyp`) and `0 ≤ s < d - 2`, with `k > (d+1)/2 + 1` an integer:
`|Comm_N(Mᵀ∇U(r,t)φ; X_N, ρ_r)| ≤ C_T(‖φ‖_{k,s+1} + ‖φ‖_{H^{k+2+⌈d/2⌉}_ul})(F_N(X_N,ρ_r) + o_N)`,
for every `N ≥ 2`, every pairwise distinct configuration `X_N`, `0 ≤ r ≤ t ≤ T` and smooth `φ` with
finite norms.  `o_N` is `oN d s C₀ N` with the heat-kernel completion `C₀` of the main paper
(`H:eq:energy-completion`), chosen once (`∃ C₀`) for the class; `C_T` independent of `φ`, `N`,
`X_N`, `r`, `t` and of the viscosity.  The density-moment, deleted-diagonal and logarithmic
hypotheses of the commutator inequality `B:eq:sharp-decaying-commutator` are implied by the weighted
bounds on `ρ` (bounded density with all moments) and by `X_N` pairwise distinct.  The proof uses the
external sharp commutator estimate (Hess-Childs-Rosenzweig) and S4.12, S4.13.
Technical hypotheses: `N ≥ 2`; `φ ∈ C^{k+2+⌈d/2⌉}` with `‖φ‖_{k,s+1} < ∞` and `‖φ‖_{H^{k+2+⌈d/2⌉}_ul} < ∞`
(the bound is meaningless otherwise; the right side uses the real values of these norms); `X_N`
pairwise distinct (the commutator is defined off the collision set). -/
theorem sharp_all_sub (hd : 2 ≤ d) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (s : ℝ)
    (M Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d) (T νstar : ℝ) (k : ℕ) (L Λ K : ℝ)
    (hs : s < (d : ℝ) - 2) (hk : ((d : ℝ) + 1) / 2 + 1 < k) :
    ∃ C₀ C : ℝ, ∀ (ν : ℝ) (ρ : ℝ → Euc d → ℝ), AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ →
      ∀ (N : ℕ), 2 ≤ N → ∀ X : EucConfig d N, Function.Injective X →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
        ContDiff ℝ ((k + 2 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
        decayNormE k (s + 1) φ < ⊤ → ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
        |commN d s (fun x => Torus.matVec M.transpose
              (gradient (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) x))
            X (withDensityReal (ρ r))| ≤
          C * ((decayNormE k (s + 1) φ).toReal +
              (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal) *
            (rieszModulatedEnergy d s X (withDensityReal (ρ r)) + oN d s C₀ N) := by
  sorry

/-! ### S5.1 -/

/-- The nonnegative Schwartz probability density hypothesis. -/
def IsSchwartzDensity (ρ : Euc d → ℝ) : Prop :=
  IsProbDensity ρ ∧ ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ

/-- "`c` smooth with all derivatives bounded". -/
def IsSmoothBounded (c : Euc d → Euc d) : Prop :=
  ContDiff ℝ ∞ c ∧ ∀ j : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ j c x‖ ≤ B

/-- The coefficients of the operator `L f = νΔf + (-Qx + c(x))·∇f + div g*(ρ∇f)`
(`W:r2:adjoint-operator`, S lines 3213-3215) in the form `νΔ + b·∇ - Div g*(ρ Mᵀ∇ ·)` with
`b = -Qx + c`, `ρ` time independent and `M` a fixed matrix (`M = -1` is the displayed `+div g*(ρ∇f)`;
"signs or fixed matrices in the last term make no difference to this analytic assertion",
S line 3216). -/
def fixedViscosityCoeff (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : Euc d → Euc d)
    (ρ : Euc d → ℝ) : WholeCoeff d :=
  ⟨s, M, ν, fun _ x => -(Torus.matVec Q x) + c x, fun _ => ρ⟩

/-- Lemma S5.1 (S:W:r2:ul-adjoint, TeX S L3204-3235), first part (L3204-3224): `d ≥ 2`, `0 ≤ s < d`, `ν > 0`,
`Q` a fixed matrix, `ρ` a nonnegative Schwartz probability density, `c` smooth with all derivatives
bounded, `M` any fixed matrix (the displayed operator is `M = -1`).  For every sufficiently large
integer `k` (`k ≥ k₀(d)`), every finite `T` the operator has a unique backward evolution on the
closure of `C_c^∞` (constants adjoined) in `H^k_ul`, and
`sup_{0≤t≤T}‖U_t f‖_{H^k_ul} ≤ C_{T,k}‖f‖_{H^k_ul}`.  Uniqueness is stated on `[0,t]` only (nothing
constrains `u r` for `r ∉ [0,t]`).  The solution notion is the repaired `IsClassicalAdjointW`
(growth condition on `∂_r f`, see `Dynamics.lean`: the source's boundedness of `∂_r f` is
incompatible with the confining drift, a latent problem of the TeX), and the data are the
elements of the closure `UlClosure k θ` (S L3199-3202), as the TeX prescribes.  Here the evolution with terminal time `t` and
datum `f` is the family `u(r) = U_{t-r} f`, `IsUlBackwardEvolution` (existence and uniqueness are
asserted for every `t ∈ [0,T]`; the bound for every `r ∈ [0,t]`, in particular `u(0) = U_t f`).
`C_{T,k}` may depend on `ν⁻¹` and all the data.  Technical hypothesis: none. -/
theorem ul_adjoint_fixed_viscosity (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (T ν : ℝ) (Q M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
      (c : Euc d → Euc d), 0 ≤ T → 0 < ν → IsSchwartzDensity ρ → IsSmoothBounded c →
      ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ f : Euc d → ℝ, UlClosure k θ f →
        (∃ u, IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u) ∧
        (∀ u u', IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u →
          IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u' →
          ∀ r ∈ Set.Icc 0 t, u r = u' r) ∧
        ∀ u, IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u →
          ∀ r ∈ Set.Icc 0 t, ulNormE k θ (u r) ≤ ENNReal.ofReal C * ulNormE k θ f := by
  sorry

/-- Lemma S5.1 (S:W:r2:ul-adjoint, TeX S L3204-3235), second part (L3225-3235),
`W:r2:orbit-bounds`:
suppose in addition `c = -∇g*ρ` plus a Schwartz vector field (and `M = -1`, the displayed
operator, for which `c = -∇g*ρ` is the transport matched to the nonlocal term; the hypotheses of
the first part, `ν > 0`, are retained).  For every integer `k` there is an integer `J` (the source
takes `J = 2k+2d+20`) such that, with `𝓗 = 1-Δ+|x|²` (`oscNorm J f = ‖𝓗^{J/2}f‖₂`),
`sup_{t≤T} ∑_{a=0}^3 ‖U_t L^a f‖_{C_b^k} ≤ C_{T,k}‖𝓗^{J/2} f‖₂` for every Schwartz `f`, and
`∂_t^a U_t f = U_t L^a f` (`a = 1,2,3`) in the `C_b^k` norm.  `U_t g` is the evolution of the first
part applied at an index `k₁ ≥ k₀` (`k₀` is an output of the statement, the "sufficiently large" threshold
of S5.1, quantified before the data: supplement repair P5) with `k₁ > k + d/2` (`Sobolev embedding`, "an index greater than
`k + d/2`", S lines 3282-3284); `U_t L^a f` is `u_a(0)` for the backward evolution `u_a` with terminal
time `t` and datum `L^a f`.  The family `F a t = U_t L^a f` is quantified (existence is part of the
conclusion). -/
theorem ul_adjoint_orbit_bounds (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (k : ℕ) :
    ∃ k₀ J : ℕ, ∀ (k₁ : ℕ), k₀ ≤ k₁ → (k : ℝ) + (d : ℝ) / 2 < k₁ →
      ∀ (T ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (c : Euc d → Euc d),
      0 ≤ T → 0 < ν → IsSchwartzDensity ρ →
      (∃ σ : Euc d → Euc d, (∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) ∧
        c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) →
      ∃ C : ℝ, ∀ f : SchwartzMap (Euc d) ℝ,
        let Cf := fixedViscosityCoeff s (-1) Q ν c ρ
        (∃ F : Fin 4 → ℝ → Euc d → ℝ, ∀ a : Fin 4, ∀ t ∈ Set.Icc 0 T, ∃ u,
          IsUlBackwardEvolution θ k₁ Cf t ((fun g x => generatorW Cf 0 g x)^[(a : ℕ)] ⇑f) u ∧
            F a t = u 0) ∧
        ∀ F : Fin 4 → ℝ → Euc d → ℝ, (∀ a : Fin 4, ∀ t ∈ Set.Icc 0 T, ∃ u,
          IsUlBackwardEvolution θ k₁ Cf t ((fun g x => generatorW Cf 0 g x)^[(a : ℕ)] ⇑f) u ∧
            F a t = u 0) →
          (∀ t ∈ Set.Icc 0 T, (∀ a, MemCb k (F a t)) ∧
            ∑ a : Fin 4, cbNorm k (F a t) ≤ C * oscNorm (J : ℝ) f) ∧
          ∀ (a : Fin 4) (ha3 : (a : ℕ) < 3), ∀ t ∈ Set.Icc 0 T, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
            ∀ h : ℝ, h ≠ 0 → |h| < δ → t + h ∈ Set.Icc 0 T →
              ∀ j ≤ k, ∀ x : Euc d, ‖iteratedFDeriv ℝ j
                (fun y => h⁻¹ * (F a (t + h) y - F a t y) - F ⟨(a : ℕ) + 1, by omega⟩ t y) x‖ ≤ ε := by
  sorry

end HRS.Whole
