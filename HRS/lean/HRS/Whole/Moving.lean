import HRS.Whole.HeadlineStatement

/-!
# Whole-space supplement, Section S6.1 (`W:sec:r2mov-relaxation`): nonlinear relaxation near
quadratic equilibrium -- statements S6.1 - S6.5 (rows `S:W:lem:r2mov-operators`,
`S:W:lem:r2mov-linear`, `S:W:thm:r2mov-nonlinear`, `S:W:cor:r2mov-Schwartz`, `S:@remark:L4537`)

Source: HRS whole-space supplement (S), lines 4148-4542.

Standing assumptions of the section (S L4148-4170): `V(x) = q|x|²/2`, `q > 0`, `ν = β⁻¹`
(`β > 0`), `0 ≤ s < d` (the source writes `σ`), and (S L4154 "Throughout `d ≥ 2`", S L218-219) `d ≥ 2`;
`ρ_*` is the thermal equilibrium density (`IsThermalEquilibrium d s q β ρ_*`).  Its "previously
proved properties, used here as inputs" (S L4156-4170: Gaussian comparison, thermal equation,
smoothness, bounded derivatives of `g*ρ_*`, moments, Poincare inequality) are the conclusions of
`HRS.Whole.euc_thermal_*`, `HRS.Whole.logThermal_*` and `HRS.Whole.reflection_gap_poincare`
(S3.4, S4.1, S4.9); they are *not* repeated as hypotheses.

## Representation decisions

* `Σ^r` is the Hermite-coefficient scale of `Oscillator.lean` (`MemOsc`, `oscNorm`, valid for every
  real index, also negative).  The operators `P`, `B` of S6.1 are *unbounded differential
  operators defined on the dense core `𝒮(ℝ^d)`* (Schwartz functions); "maps `Σ^r` to `Σ^{r-a}`"
  is stated as the boundedness estimate on this core (its unique continuous extension is the
  operator of the source).  For `v ∈ 𝒮`, `√ρ_* v` is a smooth Gaussian-decaying function.
* `∇g*h` is the force by the cancellation convention `B:eq:nabla-g-convolution` (`convGradConvW`,
  M L10091-10101, valid on `ℝ^d`), which is the distributional `∇(g*h)` for the `C¹` functions
  with Gaussian decay used here; `Δg*h := div(∇g*h)`.
* The mean-field equation `∂_tρ = νΔρ + div(ρ(qx + ∇g*ρ))` is the gradient case `M = -I` of
  `H:eq:meanfield`; its solutions are the weak solutions `IsWholeMeanFieldSolution` for
  `quadraticGradientDyn d s q β` (W1, `Dynamics.lean`).
* The "small Gaussian weighted mild class" of S6.3 (S L4349) is not defined in the TeX beyond its
  proof (S L4380-4395, norm `sup_{t≥0} e^{c₀t}‖v_t‖_{Σ^m}` on a small ball, `0 < c₀ < c`).  It is
  represented by `MovInSmallClass`: global weak solutions with `v_t = (ρ^t-ρ_*)/√ρ_*` continuous
  into `Σ^m` and `‖v_t‖_{Σ^m} ≤ r e^{-c₀t}`; the radius `r > 0` is existentially quantified in S6.3
  (small-ball uniqueness), `c₀ ≥ 0` is arbitrary in the uniqueness clause
  (decision M7: exponent `0` covers all).  AMBIGUITY: the source says *mild* solutions
  (Duhamel formula with the semigroup of S6.2); in this regularity class mild and weak solutions
  coincide (S L4396-4401 "repeated positive-time smoothing gives the classical equation"), and
  the Duhamel formula needs the semigroup `T(t)` which is itself only stated existentially.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### Notation -/

/-- `⟨x⟩ = (1+|x|²)^{1/2}`. -/
def movBracket (x : Euc d) : ℝ := Real.sqrt (1 + ‖x‖ ^ 2)

/-- The divergence `div F = ∑_i ∂_i F_i` of a vector field. -/
def movDiv (F : Euc d → Euc d) (x : Euc d) : ℝ :=
  ∑ i, fderiv ℝ F x (EuclideanSpace.single i 1) i

/-- The loss `a = max(1, s+2-d)` of S6.1 (S L4195). -/
def movA (d : ℕ) (s : ℝ) : ℝ := max 1 (s + 2 - d)

/-- The force `∇g * h` (`g` the whole-space kernel with exponent `s`), cancellation convention. -/
def movForce (d : ℕ) (s : ℝ) (h : Euc d → ℝ) : Euc d → Euc d :=
  convGradConvW (rieszKernelGrad d s) h

/-- `P v = -ρ_*^{-1/2} div(ρ_* ∇g*(√ρ_* v))` (`W:r2mov:P`, S L4199-4203). -/
def movP (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (v : Euc d → ℝ) (x : Euc d) : ℝ :=
  -(Real.sqrt (ρ x))⁻¹ *
    movDiv (fun y => ρ y • movForce d s (fun z => Real.sqrt (ρ z) * v z) y) x

/-- The bilinear term `B(v,w) = ρ_*^{-1/2} div(√ρ_* v ∇g*(√ρ_* w))` (`W:r2mov:B-bound`, S L4206-4208). -/
def movB (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (v w : Euc d → ℝ) (x : Euc d) : ℝ :=
  (Real.sqrt (ρ x))⁻¹ *
    movDiv (fun y => (Real.sqrt (ρ y) * v y) • movForce d s (fun z => Real.sqrt (ρ z) * w z) y) x

/-- The linearized operator `S v = -ρ_*^{-1/2} div(ρ_* ∇(ν v/√ρ_* + g*(√ρ_* v)))`,
`ν = β⁻¹` (`W:r2mov:S`, S L4278-4281). -/
def movS (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) (v : Euc d → ℝ) (x : Euc d) : ℝ :=
  -(Real.sqrt (ρ x))⁻¹ *
      movDiv (fun y => ρ y • gradient (fun z => β⁻¹ * (v z / Real.sqrt (ρ z))) y) x
    + movP d s ρ v x

/-! ### S6.1 `W:lem:r2mov-operators` (S L4195-4217) -/

section Operators

variable {s : ℝ}

/-- Lemma 6.1 (S:W:lem:r2mov-operators, TeX S L4195-4217), first assertion: with `a = max(1,s+2-d)`,
`P` maps `Σ^r` to `Σ^{r-a}` for every fixed `r ≥ -a` (`W:r2mov:P`).  Represented as the bound
`‖Pv‖_{Σ^{r-a}} ≤ C_r ‖v‖_{Σ^r}` on the dense core `v ∈ 𝒮(ℝ^d)`, `Pv ∈ L²` included in the claim
(so that the Hermite coefficients of `Pv` are genuine integrals).  The constant `C_r` depends on
`d, s, q, β, r` only.  Standing assumptions as in the module docstring. -/
theorem mov_operators_P (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) :
    ∀ r : ℝ, -movA d s ≤ r → ∃ C : ℝ, ∀ v : SchwartzMap (Euc d) ℝ,
      MemOsc (r - movA d s) (movP d s ρ v) ∧
        oscNorm (r - movA d s) (movP d s ρ v) ≤ C * oscNorm r v := by
  sorry

/-- Lemma 6.1, second assertion (`W:r2mov:B-bound`, S L4205-4209): for `m > d/2 + 3`,
`‖ρ_*^{-1/2} div(√ρ_* v ∇g*(√ρ_* w))‖_{Σ^{m-a}} ≤ C_m ‖v‖_{Σ^m} ‖w‖_{Σ^m}` (on the core
`v, w ∈ 𝒮`, as in `mov_operators_P`; `m` real). -/
theorem mov_operators_B (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ)
    (m : ℝ) (hm : (d : ℝ) / 2 + 3 < m) :
    ∃ C : ℝ, ∀ v w : SchwartzMap (Euc d) ℝ,
      MemOsc (m - movA d s) (movB d s ρ v w) ∧
        oscNorm (m - movA d s) (movB d s ρ v w) ≤ C * oscNorm m v * oscNorm m w := by
  sorry

/-- Lemma 6.1, third assertion (`W:r2mov:force-source-bound`, S L4210-4216): for an integer
`j ≥ 0` and `m > d/2 + j + 4`, with `h = √ρ_* v`,
`‖∇g*h‖_{C_b^{j+1}} + ‖Δg*h + ∇log ρ_*·∇g*h‖_{C_b^j} ≤ C_{m,j} ‖v‖_{Σ^m}`, the left side being
finite and the two functions of the stated smoothness (on the core `v ∈ 𝒮`).  The constants are
independent of the support of the inputs (they are chosen before `v`; S L4216-4217). -/
theorem mov_operators_force (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ)
    (j : ℕ) (m : ℝ) (hm : (d : ℝ) / 2 + j + 4 < m) :
    ∃ C : ℝ, ∀ v : SchwartzMap (Euc d) ℝ,
      ContDiff ℝ (j + 1) (movForce d s (fun x => Real.sqrt (ρ x) * v x)) ∧
      MemCb j (fun x => movDiv (movForce d s (fun y => Real.sqrt (ρ y) * v y)) x +
        inner ℝ (gradient (fun y => Real.log (ρ y)) x)
          (movForce d s (fun y => Real.sqrt (ρ y) * v y) x)) ∧
      cbNormVecE (j + 1) (movForce d s (fun x => Real.sqrt (ρ x) * v x)) +
        ENNReal.ofReal (cbNorm j (fun x => movDiv (movForce d s (fun y => Real.sqrt (ρ y) * v y)) x +
          inner ℝ (gradient (fun y => Real.log (ρ y)) x)
            (movForce d s (fun y => Real.sqrt (ρ y) * v y) x))) ≤
        ENNReal.ofReal (C * oscNorm m v) := by
  sorry

end Operators

/-! ### S6.2 `W:lem:r2mov-linear` (S L4278-4293) -/

section Linear

variable {s : ℝ}

open Classical in
/-- `√ρ_*` as an element of `L²(ℝ^d)` (`0` if `√ρ_* ∉ L²`; for a probability density it is in `L²`). -/
def movSqrtLp (ρ : Euc d → ℝ) : Lp ℝ 2 (volume : Measure (Euc d)) :=
  if h : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) then h.toLp _ else 0

/-- The closed subspace `{v ∈ L²(ℝ^d) : ⟨v, √ρ_*⟩ = 0}` on which `S` is considered (S L4278). -/
def MovL2Zero (ρ : Euc d → ℝ) : Submodule ℝ (Lp ℝ 2 (volume : Measure (Euc d))) :=
  (Submodule.span ℝ {movSqrtLp ρ})ᗮ

instance (ρ : Euc d → ℝ) : CompleteSpace (MovL2Zero ρ) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

/-- The function represented by an element of `L²`. -/
abbrev movFun {ρ : Euc d → ℝ} (v : MovL2Zero ρ) : Euc d → ℝ :=
  ⇑(v : Lp ℝ 2 (volume : Measure (Euc d)))

/-- "`(T(t))_{t≥0}` is the strongly continuous semigroup on `L²_0 = {⟨v,√ρ_*⟩=0}` whose generator
is `-S̄`, `S̄` the closure of `S` on the Schwartz core": `T(0) = I`, `T(a+b) = T(a)T(b)`, strong
continuity on `[0,∞)`, and for every Schwartz `φ ∈ L²_0` there is `w ∈ L²_0` with `w = Sφ` a.e.
such that `(d/dt)T(t)φ = -T(t)w` (right derivative) for all `t ≥ 0`.  A strongly continuous
semigroup whose generator extends `-S|_core` has generator `-S̄` as soon as `-S̄` is a generator, so
`MovIsSemigroup` pins `T` down uniquely when it exists. -/
structure MovIsSemigroup (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ)
    (T : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ)) : Prop where
  zero : T 0 = 1
  add : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = T a * T b
  cont : ∀ v : MovL2Zero ρ, ContinuousOn (fun t => T t v) (Set.Ici 0)
  generator : ∀ (φ : SchwartzMap (Euc d) ℝ) (v : MovL2Zero ρ),
    (∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x) →
      ∃ w : MovL2Zero ρ, (∀ᵐ x ∂(volume : Measure (Euc d)), movFun w x = movS d s β ρ φ x) ∧
        ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (fun τ => T τ v) (-(T t w)) (Set.Ici t) t

/-- The two estimates `W:r2mov:linear-smoothing` (S L4286-4291) for a family `U(t)` of operators on
`L²_0`: `‖U(t)‖_{Σ^m→Σ^m} ≤ C e^{-ct}` (`t ≥ 0`) and `‖U(t)‖_{Σ^{m-a}→Σ^m} ≤ C(1+t^{-a/2})e^{-ct}`
(`t > 0`), on `L²_0 ∩ Σ^m` resp. `L²_0 ∩ Σ^{m-a}`, including `U(t)v ∈ Σ^m`. -/
def MovSmoothingBounds (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (m c C : ℝ)
    (U : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ)) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ v : MovL2Zero ρ, MemOsc m (movFun v) →
    MemOsc m (movFun (U t v)) ∧
      oscNorm m (movFun (U t v)) ≤ C * Real.exp (-c * t) * oscNorm m (movFun v)) ∧
  (∀ t : ℝ, 0 < t → ∀ v : MovL2Zero ρ, MemOsc (m - movA d s) (movFun v) →
    MemOsc m (movFun (U t v)) ∧
      oscNorm m (movFun (U t v)) ≤
        C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-c * t) * oscNorm (m - movA d s) (movFun v))

/-- Lemma 6.2 (S:W:lem:r2mov-linear, TeX S L4278-4293).  On `⟨v,√ρ_*⟩ = 0` let `S` be the closure of
`Sv = -ρ_*^{-1/2} div(ρ_* ∇(νv/√ρ_* + g*(√ρ_* v)))`.  Then `-S` generates a semigroup
`T(t) = e^{-tS}` (existence and uniqueness of `T` with `MovIsSemigroup`), and there is `c > 0`
such that for each fixed `m ≥ a = max(1,s+2-d)` there is `C_m` with `MovSmoothingBounds` for
`T` and for the `L²`-adjoint `T(t)^†` on `L²_0` ("the projected adjoint semigroup has the
corresponding estimates").  `c` is chosen before `m` (the source writes `e^{-ct}` with `c` not
indexed by `m`). -/
theorem mov_linear (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) :
    ∃ T : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ), MovIsSemigroup d s β ρ T ∧
      (∀ T' : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ), MovIsSemigroup d s β ρ T' →
        ∀ t : ℝ, 0 ≤ t → T' t = T t) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, movA d s ≤ m → ∃ C : ℝ,
        MovSmoothingBounds d s ρ m c C T ∧
        MovSmoothingBounds d s ρ m c C (fun t => ContinuousLinearMap.adjoint (T t)) := by
  sorry

end Linear

/-! ### S6.3 `W:thm:r2mov-nonlinear` (S L4345-4371), S6.4, S6.5 -/

section Nonlinear

variable {s : ℝ}

/-- The initial class `W:r2mov:initial-class` (S L4350-4354): `ρ^0 = ρ_*(1+f^0)` with
`∫ f^0 ρ_* = 0` and `‖f^0‖_{C_b^{j+1}} + ‖√ρ_* f^0‖_{Σ^m} ≤ ε_*` (the norms are finite, `f^0 ∈ C_b^{j+1}`,
`√ρ_* f^0 ∈ Σ^m`; the `C_b^k` norm is the project's SUM convention `HRS.cbNorm`). -/
structure MovInitialClass (ρ : Euc d → ℝ) (j m : ℕ) (εstar : ℝ) (f0 : Euc d → ℝ) : Prop where
  cb : MemCb (j + 1) f0
  osc : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)
  mean : ∫ x, f0 x * ρ x = 0
  small : cbNorm (j + 1) f0 + oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) ≤ εstar

/-- The actual initial norm `‖f^0‖_{C_b^{j+1}} + ‖√ρ_* f^0‖_{Σ^m}` (S L4352). -/
def movInitialNorm (ρ : Euc d → ℝ) (j m : ℕ) (f0 : Euc d → ℝ) : ℝ :=
  cbNorm (j + 1) f0 + oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)

/-- The weighted perturbation `v_t = (ρ^t - ρ_*)/√ρ_*` (S L4377). -/
def movV (ρ₀ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) (t : ℝ) (x : Euc d) : ℝ :=
  (ρ t x - ρ₀ x) / Real.sqrt (ρ₀ x)

/-- The velocity `u^t = ν∇log ρ^t + qx + ∇g*ρ^t` (`W:r2mov:velocity`, S L4363), `ν = β⁻¹`. -/
def movU (d : ℕ) (s q β : ℝ) (ρ : Euc d → ℝ) (x : Euc d) : Euc d :=
  β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + movForce d s ρ x

/-- The small Gaussian weighted solution class of S6.3 (S L4349; see the module docstring):
a global weak solution of the mean-field equation of the quadratic gradient dynamics with initial
datum `ρ_*(1+f^0)`, whose perturbation `v_t = (ρ^t-ρ_*)/√ρ_*` lies in `Σ^m`, is continuous into
`Σ^m` on `[0,∞)` and satisfies `‖v_t‖_{Σ^m} ≤ r e^{-c₀t}` (ball of radius `r` in the weighted norm
`sup_{t≥0} e^{c₀t}‖v_t‖_{Σ^m}`).
Technical hypothesis `regular` (`ρ^t` continuous in `x`): the other conditions only see `ρ^t` through
integrals / `Σ^m` coefficients, i.e. up to null sets; in the TeX class (`m > d/2`, so `v_t` is
continuous by Sobolev embedding) the continuous representative is canonical, and without `regular`
the uniqueness clause `ρ' t = ρ t` of `MovNonlinearConclusion` would be false pointwise.
Limitation: `IsWholeMeanFieldSolution` forces `ρ^t ≥ 0`, whereas the TeX mild class allows signed `v`
(positivity is proved afterwards, S L4378-4387); so uniqueness here is among nonnegative solutions
only (AMBIGUITY / weaker than the TeX; stating it for signed solutions needs a separate weak
formulation of the equation for signed densities).
Statement change (S6.3 review, decision M7): the exponent `c₀` is allowed to be `0` (`c₀ ≥ 0`); the class with `c₀ = 0`
is the ball `sup_{t≥0}‖v_t‖_{Σ^m} ≤ r`, which contains every class with `c₀ ≥ 0` (`MovInSmallClass.mono_rate`), and the
uniqueness clause of `MovNonlinearConclusion` is stated there. -/
structure MovInSmallClass (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (m : ℕ) (r c₀ : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) : Prop where
  solution : ∀ T : ℝ, IsWholeMeanFieldSolution (quadraticGradientDyn d s q β) T ρ
  init : ∀ x, ρ 0 x = ρ₀ x * (1 + f0 x)
  weighted : ∀ t : ℝ, 0 ≤ t → MemOsc (m : ℝ) (movV ρ₀ ρ t) ∧
    oscNorm (m : ℝ) (movV ρ₀ ρ t) ≤ r * Real.exp (-c₀ * t)
  cont : ContinuousOn (fun t => OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t)) (Set.Ici 0)
  regular : ∀ t : ℝ, 0 ≤ t → Continuous (ρ t)

/-- Monotonicity in the exponent: a solution of the class with exponent `c₀ ≥ 0` is in the class with exponent `0`
(the ball `sup_{t≥0}‖v_t‖_{Σ^m} ≤ r`). -/
theorem MovInSmallClass.mono_rate {d : ℕ} {s q β : ℝ} {ρ₀ : Euc d → ℝ} {m : ℕ} {r c₀ : ℝ}
    {f0 : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} (h : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ)
    (hc : 0 ≤ c₀) : MovInSmallClass d s q β ρ₀ m r 0 f0 ρ := by
  refine ⟨h.solution, h.init, fun t ht => ⟨(h.weighted t ht).1, ?_⟩, h.cont, h.regular⟩
  have h1 := (h.weighted t ht).2
  have hn : 0 ≤ oscNorm (m : ℝ) (movV ρ₀ ρ t) := by unfold oscNorm; exact Real.sqrt_nonneg _
  have hr : 0 ≤ r := by
    by_contra hr
    rw [not_le] at hr
    have := mul_neg_of_neg_of_pos hr (Real.exp_pos (-c₀ * t))
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hr)

/-- Monotonicity in the radius. -/
theorem MovInSmallClass.mono_radius {d : ℕ} {s q β : ℝ} {ρ₀ : Euc d → ℝ} {m : ℕ} {r r' c₀ : ℝ}
    {f0 : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} (h : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ)
    (hr : r ≤ r') : MovInSmallClass d s q β ρ₀ m r' c₀ f0 ρ := by
  refine ⟨h.solution, h.init, fun t ht => ⟨(h.weighted t ht).1, ?_⟩, h.cont, h.regular⟩
  exact (h.weighted t ht).2.trans (mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le)

/-- The decay conclusions of S6.3 with amplitude `K` (`ε_*` in the displayed bounds, or the actual
initial norm, S L4366-4368): `W:r2mov:nonlinear-weighted` and `W:r2mov:velocity`
(`‖∇log(ρ^t/ρ_*)‖_{C_b^j} + ‖u^t‖_{C_b^j} ≤ C K e^{-ct}`, the functions being `C^j`). -/
def MovDecayBounds (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (c C K : ℝ)
    (ρ : ℝ → Euc d → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (MemOsc (m : ℝ) (movV ρ₀ ρ t) ∧
      oscNorm (m : ℝ) (movV ρ₀ ρ t) ≤ C * K * Real.exp (-c * t)) ∧
    (ContDiff ℝ j (fun x => gradient (fun y => Real.log (ρ t y / ρ₀ y)) x) ∧
      ContDiff ℝ j (movU d s q β (ρ t)) ∧
      cbNormVecE j (fun x => gradient (fun y => Real.log (ρ t y / ρ₀ y)) x) +
          cbNormVecE j (movU d s q β (ρ t)) ≤
        ENNReal.ofReal (C * K * Real.exp (-c * t)))

/-- The conclusion of Theorem 6.3 for given constants `(ε_*, r, c₀, c, C)` and regularity indices
`(j, m)`: for every initial datum of the class `W:r2mov:initial-class` there is a global solution
in the small class (`MovInSmallClass r c₀`), which is unique in the small ball of radius `r` at EVERY
exponent `c₁ ≥ 0` (the last clause is stated at exponent `0`, the largest class `sup_t‖v_t‖_{Σ^m} ≤ r`, which
contains `MovInSmallClass r' c₁` for all `r' ≤ r`, `c₁ ≥ 0`: `MovInSmallClass.mono_rate`, `.mono_radius`; the
TeX contraction (S L4380-4395) is uniform down to `c₀ → 0`), is a positive probability
density, satisfies `C⁻¹ρ_* ≤ ρ^t ≤ Cρ_*` (`W:r2mov:ratio`) and the decay bounds with amplitude `ε_*` and
with amplitude the actual initial norm, and `∫_0^∞ ‖u^t‖_{C_b^j} dt < ∞`.  Statement change (decision M7,
S6.3 review): the uniqueness clause was `MovInSmallClass .. r c₀ ..` (one exponent only), which does not cover the
solutions of `IsResultingSolution` with `c₁ < c₀` (supplement repair P3). -/
def MovNonlinearConclusion (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ)
    (εstar r c₀ c C : ℝ) : Prop :=
  ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∃ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ ∧
      (∀ t : ℝ, 0 ≤ t → IsProbDensity (ρ t) ∧ ∀ x, 0 < ρ t x) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x, C⁻¹ * ρ₀ x ≤ ρ t x ∧ ρ t x ≤ C * ρ₀ x) ∧
      MovDecayBounds d s q β ρ₀ j m c C εstar ρ ∧
      MovDecayBounds d s q β ρ₀ j m c C (movInitialNorm ρ₀ j m f0) ρ ∧
      ∫⁻ t in Set.Ioi (0 : ℝ), cbNormVecE j (movU d s q β (ρ t)) < ⊤ ∧
      ∀ ρ' : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r 0 f0 ρ' →
        ∀ t : ℝ, 0 ≤ t → ρ' t = ρ t

/-- Uniqueness of `MovNonlinearConclusion` at every exponent and every smaller radius (consumer form). -/
theorem MovNonlinearConclusion.exists_unique {d : ℕ} {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ}
    {εstar r c₀ c C : ℝ} (h : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C)
    {f0 : Euc d → ℝ} (hf0 : MovInitialClass ρ₀ j m εstar f0) :
    ∃ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ ∧
      ∀ (r' c₁ : ℝ), r' ≤ r → 0 ≤ c₁ → ∀ ρ' : ℝ → Euc d → ℝ,
        MovInSmallClass d s q β ρ₀ m r' c₁ f0 ρ' → ∀ t : ℝ, 0 ≤ t → ρ' t = ρ t := by
  obtain ⟨ρ, hρ, -, -, -, -, -, hu⟩ := h f0 hf0
  exact ⟨ρ, hρ, fun r' c₁ hr hc ρ' hρ' t ht => hu ρ' ((hρ'.mono_rate hc).mono_radius hr) t ht⟩

/-- Theorem 6.3 (S:W:thm:r2mov-nonlinear, TeX S L4345-4371).  Fix `β, q > 0`, `0 ≤ s < d`
(`d ≥ 2`), an integer `j ≥ 1` and an integer `m > d/2 + j + 6`.  There is `ε_* > 0` (with the
constants `r, c₀, c, C > 0`, all depending only on `d, s, q, β, j, m`) such that every initial
datum `ρ^0 = ρ_*(1+f^0)` of the class `W:r2mov:initial-class` has a unique global solution in the
small Gaussian weighted class, a positive probability density with the bounds
`W:r2mov:nonlinear-weighted`, `W:r2mov:ratio`, `W:r2mov:velocity` (`MovNonlinearConclusion`); and
for any nonzero `ψ ∈ C_c^∞` with `∫ψρ_* = 0`, `ρ^0 = ρ_*(1+εψ)` belongs to the class for all
sufficiently small `|ε|`.  AMBIGUITY: "mild class" (see the module docstring); the radius `r` of the uniqueness
class is existentially quantified (S L4349 "small"), the decay exponent is not restricted: uniqueness is stated in the
ball `sup_t ‖v_t‖_{Σ^m} ≤ r` (exponent `0`), which contains the classes of every exponent `c₁ ≥ 0` (decision M7).  The
bounds are stated with amplitude `ε_*` and, as in S L4367-4368 ("each right side is also bounded by
a constant times the actual initial norm"), with the actual initial norm and the same constant. -/
theorem mov_nonlinear (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (j : ℕ) (hj : 1 ≤ j) (m : ℕ) (hm : (d : ℝ) / 2 + j + 6 < m)
    (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ εstar r c₀ c C : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C ∧
      MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C ∧
      ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ψ ≠ 0 →
        ∫ x, ψ x * ρ₀ x = 0 →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| < ε₀ →
          MovInitialClass ρ₀ j m εstar (fun x => ε * ψ x) := by
  sorry

/-- Corollary 6.4 (S:W:cor:r2mov-Schwartz, TeX S L4509-4523).  For a fixed integer `K` take the
regularity index of Theorem 6.3 also larger than `K + d/2 + 4`.  Then, for the solutions of
Theorem 6.3 (constants `ε_*, r, c₀, c, C` with `MovNonlinearConclusion`), for every integer `L ≥ 0`
there is `C_{K,L}` such that for all admissible data, all `t ≥ 0`, all `x` and all derivative orders
`k ≤ K` (`‖D^k‖` the multilinear operator norm, equivalent to the multi-index form
`|γ| ≤ K` up to a constant absorbed in `C_{K,L}`):
`⟨x⟩^L (‖D^k(ρ^t-ρ_*)(x)‖ + ‖D^k ∂_tρ^t(x)‖) ≤ C_{K,L} ε_* e^{-ct}` (`W:r2mov:Schwartz-time`).
The time derivative `∂_tρ^t` (right derivative at `t = 0`) exists (`HasDerivWithinAt`) and `ρ^t`,
`∂_tρ^t` are `C^K` (so no junk value of `deriv`/`iteratedFDeriv` is used).  The decay exponent is
the `c` of Theorem 6.3. -/
theorem mov_schwartz (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (K j m : ℕ) (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m)
    (hmK : (K : ℝ) + d / 2 + 4 < m) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ εstar r c₀ c C : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C ∧
      MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C ∧
      ∀ L : ℕ, ∃ CKL : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
        ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
          ∃ ρ' : ℝ → Euc d → ℝ,
            (∀ t : ℝ, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => ρ τ x) (ρ' t x) (Set.Ici t) t) ∧
            ∀ t : ℝ, 0 ≤ t → ContDiff ℝ K (ρ t) ∧ ContDiff ℝ K (ρ' t) ∧
              ∀ k : ℕ, k ≤ K → ∀ x : Euc d,
                movBracket x ^ L * (‖iteratedFDeriv ℝ k (fun y => ρ t y - ρ₀ y) x‖ +
                    ‖iteratedFDeriv ℝ k (ρ' t) x‖) ≤
                  CKL * εstar * Real.exp (-c * t) := by
  sorry

/-- Remark (S:@remark:L4537, "Scope", TeX S L4537-4542): the only checkable claim is that Theorem 6.3
is a local stability result for an *infinite-dimensional* class of relative perturbations, "for the
logarithm and every fixed positive Riesz exponent, at every fixed positive temperature" (`0 ≤ s < d`,
`β > 0`).  Formalized: for every `ε_* > 0` and every `n`, the initial class
`W:r2mov:initial-class` contains a ball (in the coefficients `c ∈ ℝ^n`) of an `n`-dimensional
subspace spanned by linearly independent `C_c^∞` functions `ψ_i` with `∫ψ_iρ_* = 0`.  The
non-claims ("does not prove global convergence from arbitrary smooth data") and the comment on the
logarithmic proof are prose (`no_formal_content`).  Repair P11 (2026-10-20): `hρsm : ContDiff ℝ ∞ ρ₀` (smoothness of the thermal measure is
S3.4 regularity, not derivable from `IsThermalEquilibrium` here, and not available for `s = 0`; `MovInitialClass` needs `√ρ₀` smooth;
`ρ₀ > 0` is automatic from the Gibbs formula). -/
theorem mov_scope_infinite_dim (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (j m : ℕ) (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m)
    (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (hρsm : ContDiff ℝ ∞ ρ₀)
    (εstar : ℝ) (hε : 0 < εstar) :
    ∀ n : ℕ, ∃ ψ : Fin n → Euc d → ℝ, LinearIndependent ℝ ψ ∧
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧ ∫ x, ψ i x * ρ₀ x = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ δ) →
        MovInitialClass ρ₀ j m εstar (fun x => ∑ i, c i * ψ i x) := by
  sorry

end Nonlinear

end HRS.Whole
