import HRS.Whole.Round2
import HRS.Whole.MovingDyn

/-!
# Whole-space supplement, Sections 10-11.2: the weighted path correction, uniform windows, relaxation of
the correction -- statements S10.1-S10.5, S11.1, S11.2

Source: HRS whole-space supplement (S), lines 7697-8841.

* S10.1 `W:lem:r2-covariance-measure` (L7740-7767) with the weighted dual `F_{r,P}` of `W:eq:r2-weighted-test`;
* S10.2 `W:prop:r2-path-interpolation` (L8049-8062) with the data of `W:sec:r2-dynamic-edgeworth` (L7855-8048);
* S10.3 `W:lem:r2-window-orbits` (L8238-8257), S10.4 `W:lem:r2-window-errors` (L8304-8312),
  S10.5 `W:cor:r2-window-general-initial` (L8403-8455) with the window indices of L8218-8236;
* S11.1 `W:prop:r2-tensor-relaxation` (L8716-8734), S11.2 `W:cor:r2-two-parameter-edgeworth` (L8825-8841), with the
  stationary-covariance setting of L8684-8714.

## Representation decisions (the torus analogues are the Section 7 statements of the periodic main paper)

* Path space `𝒳 = C([0,T];B_m)` is `OscPath d m T`; its projective tensor powers are `projTensor`/`TensorDual`
  (`HRS.Prob.Gaussian`), a bounded multilinear form `M` being evaluated by `K M`.
* The adjoint propagator is `propagatorW C u t φ = U^{u,t}φ` (the classical adjoint solution, `0` if none exists; existence is an input
  of the statements where used, never assumed in a definition); `V^{t,u}`, the transpose on `B_m`, is `r2Vprop`
  (`⟨V^{t,u}z, h_α⟩ = z(U^{u,t}h_α)`), exactly the periodic `Vprop`.
* A field `z^u ∈ F_{r,P} = (E_{r,P})'` is a functional `z u : (ℝ^d → ℝ) → ℝ` on test functions with `‖z^u‖_{F_{r,P}} = dualNormE r P (z u)`
  (`Orbits.lean`), the norm of `E_{r,P}` being `weightedSobolevE` (an equivalent norm to the one of `W:eq:r2-weighted-test`: derivatives are
  indexed by ordered tuples; the source's constants are not tracked).  The empirical field `η_N^u = √N(μ_N^u-μ^u)` is such a functional.
* "`𝒥_z ∈ BV_0(𝒳^{⊗̂π2})`" is represented by the family `Jm z a a'` of its values on the intervals `(a,a']` (elements of
  `projTensor 𝒳 2`, additive, with continuous cumulative path `u ↦ Jm z 0 u`) and the total variation by `eVariationOn` of the
  cumulative path, as for the torus (`Sec7Fields`); the evaluation (`W:eq:r2-J-evaluation`) is `IsR2JValue`.
* Riemann--Stieltjes integrals are the limits of tagged sums (`IsR2RS`), as for the torus.
* The Gaussian future `Γ_u` is represented by its law (`IsR2FutureGaussian`); `u_Φ(u,y) = E Φ(y + Γ_u)` is `r2HeatFn`.
* The window indices `k = 4d+42`, `M = 8d+80`, `J = 18d+180`, `m = 24d+240` (`wholeSpaceIndex d`), `J_* = 4J+4d+40` (S L8222-8227).
* "A small nonlinear trajectory (or the stationary measure)" of S10.3-S11 is `IsR2WindowTrajectory` (the class of S2.1(ii)/(iii),
  `IsResultingSolution` with `ε_*` chosen first, or `ρ^t ≡ ρ_β`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### The weighted dual spaces and the covariance measure (S10.1) -/

section CovarianceMeasure

/-- `f` is a test function of `E_{r,P}`: `C^r` with finite weighted norm. -/
def IsR2WeightedTest (r : ℕ) (Pw : ℝ) (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ r f ∧ weightedSobolevE r Pw f < ⊤

/-- `z ∈ L¹([0,T];F_{r,P})` (S L7744): each `z^u` is a linear functional on the test functions of `E_{r,P}`,
`u ↦ z^u(f)` is measurable (weak measurability, equivalent to strong measurability since `F_{r,P}` is separable) and
`∫_0^T ‖z^u‖_{F_{r,P}} du < ∞`.  Each `z^u` is norm-continuous on the test functions (`∃ M, |z^u f| ≤ M‖f‖_E`; the continuity clause of
`F_{r,P} = E_{r,P}'`, the dual of the completion of `C_c^∞`, TeX S L7698-7700; without it `dualNormE`, a supremum over `C_c^∞` only, does not see
the values of `z^u` on the non-compactly supported `∇U^{u,t_a}φ·∇U^{u,t_b}ψ`, see ISSUES `Supplement repair P1`); `M` depends on `u`. -/
def IsR2L1F (r : ℕ) (Pw T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  (∀ u ∈ Set.Icc (0 : ℝ) T, (∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g →
      z u (f + g) = z u f + z u g) ∧
    (∀ (c : ℝ) f, IsR2WeightedTest r Pw f → z u (c • f) = c * z u f) ∧
    ∃ M : ℝ, ∀ f, IsR2WeightedTest r Pw f → |z u f| ≤ M * (weightedSobolevE r Pw f).toReal) ∧
  (∀ f, IsR2WeightedTest r Pw f → Measurable fun u => z u f) ∧
  ∫⁻ u in Set.Icc (0 : ℝ) T, dualNormE r Pw (z u) < ⊤

/-- The dual tests `φ_α = λ_α^{-m/2}h_α` (finite linear combinations are the observation functionals of S10.1). -/
def IsR2DualCombo (m : ℝ) (φ : Euc d → ℝ) : Prop :=
  ∃ (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ), φ = fun x => ∑ α ∈ S, c α * oscTestFun m α x

/-- The value of `t ↦ w(t)` of a path at a real time (`0` outside `[0,T]`). -/
def r2PathAt {m T : ℝ} (w : OscPath d m T) (t : ℝ) : OscDual d m :=
  open Classical in if h : t ∈ Set.Icc (0 : ℝ) T then OscPath.at' w ⟨t, h⟩ else 0

/-- `V^{t,u}z ∈ B_m` for a functional `z` on test functions: `⟨V^{t,u}z, h_α⟩ = z(U^{u,t}h_α)` (transpose of the adjoint
propagator, S L7880-7881; the periodic `Vprop`). -/
def r2Vprop (C : WholeCoeff d) (m : ℝ) (t u : ℝ) (z : (Euc d → ℝ) → ℝ) : OscDual d m :=
  OscDual.ofSeq m fun α => z (propagatorW C u t (hermiteFunD α))

/-- The orbit assumption `W:eq:r2-orbit-assumption` (S L7729-7734) for the adjoint along `C` with the dual tests `φ_α`:
the orbits `U^{u,t}φ_α` are `C^{r+1}` in `x` and `∂_tU^{u,t}φ_α` exists and is `C^{r+1}` in `x` (for `0 ≤ u ≤ t ≤ T`, the derivative being the one-sided derivative within `[u,T]` -- `propagatorW C u t'` is only meaningful for
`t' ∈ [u,T]` -- so that the endpoints `t = u`, `t = T` are covered; without this the derivative norms below would use Lean's junk value
`0` of non-differentiable functions), and
`∑_α sup_{0≤u≤t≤T} (‖∂^β U^{u,t}φ_α‖²_∞ + ‖∂^β ∂_tU^{u,t}φ_α‖²_∞) < ∞` over `|β| ≤ r+1`
(written with `weightedSupE (r+1) 0`, the maximum over `|β| ≤ r+1`, equivalent up to a dimensional constant). -/
def R2OrbitSummable (C : WholeCoeff d) (m : ℝ) (T : ℝ) (r : ℕ) : Prop :=
  (∀ α : MultiIndex d, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc u T,
    ContDiff ℝ (r + 1) (propagatorW C u t (oscTestFun m α)) ∧
    (∀ x, DifferentiableWithinAt ℝ (fun t' => propagatorW C u t' (oscTestFun m α) x) (Set.Icc u T) t) ∧
    ContDiff ℝ (r + 1) (fun x => derivWithin (fun t' => propagatorW C u t' (oscTestFun m α) x) (Set.Icc u T) t)) ∧
  ∑' α : MultiIndex d, ⨆ u ∈ Set.Icc (0 : ℝ) T, ⨆ t ∈ Set.Icc u T,
    (weightedSupE (r + 1) 0 (propagatorW C u t (oscTestFun m α)) ^ 2 +
      weightedSupE (r + 1) 0
        (fun x => derivWithin (fun t' => propagatorW C u t' (oscTestFun m α) x) (Set.Icc u T) t) ^ 2) < ⊤

/-- The value of the covariance measure on an interval `I`: `J ∈ 𝒳⊗̂𝒳` (`projTensor`) whose values on the products of evaluation
functionals `ℓ_1⊗ℓ_2`, `ℓ_1(w) = w(t_1)(φ)`, `ℓ_2(w) = w(t_2)(ψ)` (`φ,ψ` finite combinations of the `φ_α`) are
`(2/β)∫_{I∩[0,t_1∧t_2]} z^u(∇U^{u,t_1}φ·∇U^{u,t_2}ψ) du` (`W:eq:r2-J-evaluation`, S L7754-7760; `2/β = 2ν`). -/
def IsR2JValue (C : WholeCoeff d) (m T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (I : Set ℝ)
    (J : TensorDual (OscPath d m T) 2) : Prop :=
  J ∈ projTensor (OscPath d m T) 2 ∧
  ∀ (ta tb : ℝ) (φa φb : Euc d → ℝ) (l₁ l₂ : StrongDual ℝ (OscPath d m T)),
    IsR2DualCombo m φa → IsR2DualCombo m φb → ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
    (∀ w, l₁ w = OscDual.eval (r2PathAt w ta) φa) → (∀ w, l₂ w = OscDual.eval (r2PathAt w tb) φb) →
    J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
      2 * C.ν * ∫ u in I ∩ Set.Icc (0 : ℝ) (min ta tb), z u (fun x =>
        inner ℝ (gradient (propagatorW C u ta φa) x) (gradient (propagatorW C u tb φb) x))

/-- Measurability of the integrand of `IsR2JValue`: for `t_a,t_b ∈ [0,T]` and finite combinations `φ_a,φ_b` of the dual tests,
`u ↦ z^u(∇U^{u,t_a}φ_a·∇U^{u,t_b}φ_b)` is a.e.-measurable on `[0,t_a∧t_b]` (otherwise the integral in `IsR2JValue` is Lean's junk `0`). -/
def R2JIntegrandMeas (C : WholeCoeff d) (m T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  ∀ (ta tb : ℝ) (φa φb : Euc d → ℝ), IsR2DualCombo m φa → IsR2DualCombo m φb →
    ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
    AEMeasurable (fun u => z u (fun x =>
      inner ℝ (gradient (propagatorW C u ta φa) x) (gradient (propagatorW C u tb φb) x)))
      (volume.restrict (Set.Icc (0 : ℝ) (min ta tb)))

/-- Lemma 10.1 (S:W:lem:r2-covariance-measure, TeX S L7740-7767): whole-space signed covariance measure.  `r ≥ 0` an integer,
`P > d/2`, `E_{r,P}` the weighted test space and `F_{r,P} = E_{r,P}'` (`IsR2L1F`, `dualNormE`), a backward propagator `U^{u,t}`
(the adjoint along `C`, `propagatorW C u t`) and the dual tests `φ_α` of `B_m` satisfying the orbit assumption
`W:eq:r2-orbit-assumption` (`R2OrbitSummable`).  Then there is a constant `K` and a *linear* assignment
`z ∈ L¹([0,T];F_{r,P}) ↦ 𝒥_z ∈ BV_0(𝒳^{⊗̂π2})` (`Jm z a a'` is `𝒥_z((a,a'])`: additive in the interval, with continuous cumulative
path `u ↦ 𝒥_z([0,u])`) with `‖𝒥_z‖_{TV} ≤ K∫_0^T‖z^u‖_{F_{r,P}}du` (`W:eq:r2-J-bound`, the total variation is
`eVariationOn` of the cumulative path) whose values on intervals are given by `W:eq:r2-J-evaluation` (`IsR2JValue`).  The
constant `K` depends on `C` through the orbit sum; it is chosen after `C, m, T, r, P` and before `z`.
SPECIALISATION (AMBIGUITY): the abstract "separable Hilbert space `B` of distributions with orthonormal basis `ε_j` and dual tests `φ_j`"
is the oscillator dual `B_m` with `φ_α = λ_α^{-m/2}h_α` (S L7735-7736: "`B` a sufficiently weak harmonic-oscillator dual");
the identity is stated for finite linear combinations of the `φ_α` (S L7762-7763).  The "intrinsic" (representation-independent)
character of the map is the uniqueness of the tensor determined by these evaluations (not restated).
Technical hypotheses: `T > 0`; `Jm` is only constrained on admissible `z`.
Repairs (2026-10-20, ISSUES `Supplement repair P1`): `IsR2L1F` carries the norm-continuity of each `z^u` (the TeX `F_{r,P} = E_{r,P}'`);
`hlin` is the linearity of the adjoint propagator on finite combinations of the `φ_α` (uniqueness of the classical adjoint solution; without it
`∇U^{u,t}φ` for a combination `φ` is unrelated to the orbits constrained by `horb`); admissible `z` also satisfy `R2JIntegrandMeas` (reviewer
amendment: the `u`-integral in `IsR2JValue` is not junk).  Additivity and homogeneity are required only for admissible arguments. -/
theorem r2_covariance_measure (hd : 2 ≤ d) (C : WholeCoeff d) (m T : ℝ) (hT : 0 < T) (r : ℕ) (Pw : ℝ)
    (hP : (d : ℝ) / 2 < Pw) (horb : R2OrbitSummable C m T r)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ, IsR2DualCombo m φ → IsR2DualCombo m ψ →
      propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ) :
    ∃ (K : ℝ) (Jm : (ℝ → (Euc d → ℝ) → ℝ) → ℝ → ℝ → projTensor (OscPath d m T) 2),
      (∀ z z', IsR2L1F r Pw T z → IsR2L1F r Pw T z' → R2JIntegrandMeas C m T z → R2JIntegrandMeas C m T z' →
        ∀ a a', Jm (z + z') a a' = Jm z a a' + Jm z' a a') ∧
      (∀ (c : ℝ) z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z → ∀ a a', Jm (c • z) a a' = c • Jm z a a') ∧
      ∀ z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z →
        (∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ T → Jm z a c = Jm z a b + Jm z b c) ∧
        (∀ a, Jm z a a = 0) ∧ ContinuousOn (fun u => Jm z 0 u) (Set.Icc 0 T) ∧
        eVariationOn (fun u => Jm z 0 u) (Set.Icc 0 T) ≤
          ENNReal.ofReal K * ∫⁻ u in Set.Icc (0 : ℝ) T, dualNormE r Pw (z u) ∧
        ∀ a a', 0 ≤ a → a ≤ a' → a' ≤ T →
          IsR2JValue C m T z (Set.Ioc a a') (Jm z a a') := by
  sorry

end CovarianceMeasure

/-! ### The data of the dynamic Edgeworth proof (S10.2) -/

section PathInterpolation

/-- `S` has Riemann--Stieltjes integral `I` over `[0,T]`: for every `ε > 0` there is `δ > 0` such that every tagged partition
`0 = u_0 < ⋯ < u_n = T`, tags `τ_i ∈ [u_i,u_{i+1}]`, mesh `< δ`, satisfies `|∑_i S(τ_i,u_i,u_{i+1}) - I| < ε`
(`S(τ,a,b)` = integrand at the tag applied to the measure of `(a,b]`; as for the torus, `Sec7Fields.IsRS`). -/
def IsR2RS (T : ℝ) (S : ℝ → ℝ → ℝ → ℝ) (I : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ), StrictMono u →
    u 0 = 0 → u (Fin.last n) = T → (∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ) →
    (∀ i : Fin n, u i.succ - u i.castSucc < δ) →
    |∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ) - I| < ε

/-- The initial propagation `(𝖨z)(t) = V^{t,0}z` (S L8026) of a field `z` given as a functional on test functions (for `z = ζ_N^0 =
√N(μ_N^0 - Eμ_N^0)`; `V^{t,0}z` is built from the values `z(U^{0,t}h_α)`, not by pairing an element of `B_m` with `U^{0,t}h_α ∉ Σ^m`,
S L7737). -/
def r2InitProp (C : WholeCoeff d) (m T : ℝ) (z : (Euc d → ℝ) → ℝ) : OscPath d m T :=
  windowPathOf m T 0 fun t => r2Vprop C m t 0 z

/-- The predicted continuation `(𝖳_uw)(t) = w(t)` for `t ≤ u`, `V^{t,u}w(u)` for `t > u` (S L8014-8015), for the path `w = ζ_N` and its
field `z^u = ζ_N^u` as a functional on test functions (`z = fun u f => √N(μ_N^u - Eμ_N^u)(f)`). -/
def r2Predicted (C : WholeCoeff d) {m T : ℝ} (w : OscPath d m T) (z : ℝ → (Euc d → ℝ) → ℝ) (u : ℝ) :
    OscPath d m T :=
  windowPathOf m T 0 fun t => if t ≤ u then r2PathAt w t else r2Vprop C m t u (z u)

/-- The increment `𝒟_b((a,a'])` of the drift measure (`W:eq:r2-D-measure`, S L7991): `t ↦ ∫_{(a,a']∩[0,t]} V^{t,u}b(u) du`. -/
def r2DriftInc (C : WholeCoeff d) (m T : ℝ) (b : ℝ → (Euc d → ℝ) → ℝ) (a a' : ℝ) : OscPath d m T :=
  windowPathOf m T 0 fun t => ∫ u in Set.Ioc a (min a' t), r2Vprop C m t u (b u)

/-- `γ` is (the law of) the Gaussian future path `Γ_u` (S L8037-8041): a centered Gaussian measure on `𝒳` with
`E[Γ_u(t_a)(φ_a)Γ_u(t_b)(φ_b)] = 2β⁻¹∫_u^{t_a∧t_b}μ^v(∇U^{v,t_a}φ_a·∇U^{v,t_b}φ_b)dv` (`= 0` if `t_a∧t_b ≤ u`), the forcing being
restricted to `(u,T]`. -/
def IsR2FutureGaussian (C : WholeCoeff d) (m T u : ℝ) (γ : Measure (OscPath d m T)) : Prop :=
  IsCenteredGaussian γ ∧ ∀ (ta tb : ℝ) (φa φb : Euc d → ℝ), IsOscTest m φa → IsOscTest m φb →
    ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
    ∫ z, OscDual.eval (r2PathAt z ta) φa * OscDual.eval (r2PathAt z tb) φb ∂γ =
      2 * C.ν * ∫ v in Set.Icc u (min ta tb), ∫ x,
        inner ℝ (gradient (propagatorW C v ta φa) x) (gradient (propagatorW C v tb φb) x) * C.ρ v x

/-- `u_Φ(u,y) = E[Φ(y + Γ_u)]` (S L8039). -/
def r2HeatFn {m T : ℝ} (γ : ℝ → Measure (OscPath d m T)) (Φ : OscPath d m T → ℝ) (u : ℝ)
    (y : OscPath d m T) : ℝ :=
  ∫ z, Φ (y + z) ∂(γ u)

open Classical in
/-- The pairing `⟨M, 𝒥_z(I)⟩` of a bounded bilinear form with the tensor `𝒥_z(I)` (`0` if the tensor does not exist, which the
source excludes; cf. `r2_covariance_measure`). -/
def r2JPair (C : WholeCoeff d) (m T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (I : Set ℝ)
    (M : OscPath d m T [×2]→L[ℝ] ℝ) : ℝ :=
  if h : ∃ J, IsR2JValue C m T z I J then h.choose M else 0

/-- The quadratic field `B_N^u(φ) = N{F_N^{h_{∇φ}}(X_N^u,μ) - E F_N^{h_{∇φ}}(X_N^u,μ)}`, `h_v(x,y) = (v(x)-v(y))·∇g(x-y)`
(`W:eq:r2-dynamic-B`, S L7935-7938; the factor is `N F_N`, not `2 N F_N`), as a functional on test functions. -/
def r2QuadField {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (s : ℝ) (μ : Measure (Euc d)) (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N) (u : ℝ) (ζ : Ω) (φ : Euc d → ℝ) : ℝ :=
  N * (pairEnergy (commutatorKernel d s (fun x => gradient φ x)) (X u.toNNReal ζ) μ -
    ∫ ζ', pairEnergy (commutatorKernel d s (fun x => gradient φ x)) (X u.toNNReal ζ') μ ∂P)

/-- A realization of the whole-space gradient particle dynamics (quadratic confinement `a|x|²/2`, `ν = β⁻¹`): independent vector
Brownian motion, initial configuration independent of it, strong solution on every horizon.
Repair (2026-10-24, approved): field `filtered` (as Supplement repair P7 for `IsCanonicalRealization`). -/
structure IsR2Realization (d : ℕ) (s a β : ℝ) {N : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N) : Prop where
  brownian : IsVectorBrownian P W
  indep : IndepFun X₀ (fun ζ t => W t ζ) P
  solution : ∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X
  filtered : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
    IsWholeFilteredSolution P ℱ W' W X

/-- Proposition 10.2 (S:W:prop:r2-path-interpolation, TeX S L8049-8062): exact interpolation on the path space, for the
fixed observation horizon with constant mean-field measure (S L7890-7897).  `d ≥ 2`, `a, β > 0`, `0 ≤ σ < d/2`, `V = a|x|²/2`,
`μ = ρ dx` the thermal equilibrium, particles prepared from `Q_{N,γ}(μ)` (`γ > 0` for `σ > 0`, `γ ≥ 0` for `σ = 0`) and
`ζ_N^t = √N(μ_N^t - Eμ_N^t)`; the spaces `𝒳 = C([0,T];B_m)`, `m = J + 4d + 10 = 14d + 114` (`k = 4d+42`, `J = 2k+2d+20`; S L7864-7867),
weights `r = 2d+8`, `P = d+2` (S L7865), the orbit assumption for these indices (S L8006-8008) and the Gaussian future `Γ_u`
(its existence being the construction of S L7882-7888, taken as `hγG`).  For `Φ ∈ C_b^5(𝒳)` there are random variables `A_N`, `J_N`
(the Riemann--Stieltjes integrals `∫_0^T Du_Φ(u,Y_N^u) d𝒟_{B_N}(u)` and `∫_0^T D²u_Φ(u,Y_N^u)[d𝒥_{η_N}(u)]`, limits of the tagged sums)
with
`E Φ(ζ_N) = E u_Φ(0,𝖨ζ_N^0) - N^{-1/2}E A_N + (2√N)⁻¹E J_N`,
`Y_N^u = 𝖳_uζ_N`, `𝒟_b` the drift measure of `b = B_N`, `𝒥_z` the covariance measure of `z = η_N = √N(μ_N-μ)` (the `z` of
`r2_covariance_measure`, characterised by `IsR2JValue`).
Statement change M1b (2026-10-22): `hinv` (invariance of the canonical Gibbs law for the particle dynamics, `GibbsInvariant d s a β N`) is a hypothesis, used for the `L^p` density bound S L7901-7911.
Technical hypotheses: `N ≥ 2`; `T > 0`; the realization (`IsR2Realization`),
law of `X₀` is `Q_{N,γ}(μ)`; `horb` (the orbit assumption); `Φ ∈ C_b^5` (`MemCb 5`). -/
theorem r2_path_interpolation (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ)
    (horb : R2OrbitSummable ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
      (2 * d + 8))
    (γu : ℝ → Measure (OscPath d ((14 * d + 114 : ℕ) : ℝ) T))
    (hγG : ∀ u ∈ Set.Icc (0 : ℝ) T,
      IsR2FutureGaussian ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T u (γu u))
    (N : ℕ) (hN : 2 ≤ N) (hinv : GibbsInvariant d s a β N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hreal : IsR2Realization d s a β P X₀ W X)
    (hlaw : law P X₀ = modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ))
    (Φ : OscPath d ((14 * d + 114 : ℕ) : ℝ) T → ℝ) (hΦ : MemCb 5 Φ) :
    ∃ A J : Ω → ℝ, Integrable A P ∧ Integrable J P ∧
      (∀ᵐ ζ ∂P, IsR2RS T (fun τ a' b' =>
        fderiv ℝ (r2HeatFn γu Φ τ)
          (r2Predicted ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
            (zetaPathW ((14 * d + 114 : ℕ) : ℝ) T 0 P X ζ)
            (fun u f => Real.sqrt N * (pair (empirical (X u.toNNReal ζ)) f - pair (meanEmpirical (P.map (X u.toNNReal))) f)) τ)
          (r2DriftInc ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
            (fun u => r2QuadField s (withDensityReal ρ) P X u ζ) a' b')) (A ζ)) ∧
      (∀ᵐ ζ ∂P, IsR2RS T (fun τ a' b' =>
        r2JPair ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
          (fun u f => Real.sqrt N * (pair (empirical (X u.toNNReal ζ)) f - pair (withDensityReal ρ) f))
          (Set.Ioc a' b')
          (iteratedFDeriv ℝ 2 (r2HeatFn γu Φ τ)
            (r2Predicted ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
              (zetaPathW ((14 * d + 114 : ℕ) : ℝ) T 0 P X ζ)
              (fun u f => Real.sqrt N * (pair (empirical (X u.toNNReal ζ)) f - pair (meanEmpirical (P.map (X u.toNNReal))) f)) τ))) (J ζ)) ∧
      ∫ ζ, Φ (zetaPathW ((14 * d + 114 : ℕ) : ℝ) T 0 P X ζ) ∂P =
        ∫ ζ, r2HeatFn γu Φ 0 (r2InitProp ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
            ((14 * d + 114 : ℕ) : ℝ) T
            (fun f => Real.sqrt N * (pair (empirical (X 0 ζ)) f - pair (meanEmpirical (P.map (X 0))) f))) ∂P -
          (Real.sqrt N)⁻¹ * ∫ ζ, A ζ ∂P + (1 / (2 * Real.sqrt N)) * ∫ ζ, J ζ ∂P := by
  sorry

end PathInterpolation

/-! ### Uniform windows (S10.3 - S10.5) -/

section Windows

/-- The class of mean-field trajectories of S10.3-S11 (S L8218-8220, L8493-8500): either the stationary quadratic mean-field measure
(`ρ^t ≡ ρ_β`) or one of the small nonlinear trajectories of S2.1(ii) (`IsAdmissiblePerturbation` with smallness `ε_*`, and
`IsResultingSolution` with the constants `c₁, C₁` of S6.3). -/
def IsR2WindowTrajectory (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (εstar c₁ C₁ : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop :=
  ρ = (fun _ => ρβ) ∨ ∃ (ε : ℝ) (ψ : Euc d → ℝ), IsAdmissiblePerturbation ρβ εstar ε ψ ∧
    IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ

/-- The S6.3 conclusion for the class of S2.1(ii)/(iii) with the constants `(ε_*, c₁, C₁)`: every admissible initial perturbation
(`IsAdmissiblePerturbation` with smallness `ε_*`) has a resulting nonlinear solution in the class `IsResultingSolution` with these constants
(Theorem S6.3, S L4345-4371).  Used by the S11 statement in `Round2Moving`, where `ε_*, c₁, C₁` are existentially quantified together; the S10.3-S10.5
window theorems instead take `c₁, C₁` first and then `ε_*` (D2/ED14), and nonemptiness of the class comes from S6.3. -/
def R2ClassExists (d : ℕ) (s a β εstar c₁ C₁ : ℝ) : Prop :=
  ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ (ε : ℝ) (ψ : Euc d → ℝ),
    IsAdmissiblePerturbation ρβ εstar ε ψ → ∃ ρ : ℝ → Euc d → ℝ,
      IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ

/-- `‖f‖_{C_b^k}` in `ℝ≥0∞` for a scalar function (`∑_{j≤k}sup_x‖D^jf(x)‖`). -/
def r2CbNormE (k : ℕ) (f : Euc d → ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (k + 1), ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j f x‖

/-- The window initial tests `f_{b,n,α}(x) = (1+n²)^{3/8}∫_0^T e_n(u)U(0,b+u)φ_α(x)du` (`W:r2:window-initial-tests`, S L8252-8253). -/
def r2WindowTest (C : WholeCoeff d) (m T b : ℝ) (n : ℕ) (α : MultiIndex d) (x : Euc d) : ℝ :=
  (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) *
    ∫ u in Set.Icc (0 : ℝ) T, r2CosBasis T n u * propagatorW C 0 (b + u) (oscTestFun m α) x

/-- The zeroth-order orbit bound `sup_{0≤r≤t}‖U(r,t)φ‖_{C_b^k} ≤ A` for every classical adjoint solution with terminal datum `φ`
(first bound of `W:r2:window-orbit-global`). -/
def R2OrbitSup (C : WholeCoeff d) (k : ℕ) (t : ℝ) (φ : Euc d → ℝ) (A : ℝ) : Prop :=
  ∀ f : ℝ → Euc d → ℝ, IsClassicalAdjointW C t φ f → ∀ r ∈ Set.Icc (0 : ℝ) t,
    ContDiff ℝ k (f r) ∧ r2CbNormE k (f r) ≤ ENNReal.ofReal A

/-- The decaying gradient bound `‖∇U(r,t)φ‖_{C_b^k} ≤ A e^{-c(t-r)}` (second bound of `W:r2:window-orbit-global`). -/
def R2OrbitGrad (C : WholeCoeff d) (k : ℕ) (t : ℝ) (φ : Euc d → ℝ) (A c : ℝ) : Prop :=
  ∀ f : ℝ → Euc d → ℝ, IsClassicalAdjointW C t φ f → ∀ r ∈ Set.Icc (0 : ℝ) t,
    ContDiff ℝ k (fun x => gradient (f r) x) ∧
    cbNormVecE k (fun x => gradient (f r) x) ≤ ENNReal.ofReal (A * Real.exp (-c * (t - r)))

/-- Lemma 10.3 (S:W:lem:r2-window-orbits, TeX S L8238-8257): uniform adjoint orbits for a fixed window.  Quadratic model
(`d ≥ 2`, `a, β > 0`, `0 ≤ σ < d`), window length `T > 0`, the stationary measure or a small nonlinear trajectory
(`IsR2WindowTrajectory`; `c₁, C₁` given first, then `ε_*`, as in S2.1(ii)), the indices
`k = 4d+42`, `J = 18d+180`, `m = 24d+240` (S L8222-8225).  With `φ_α = λ_α^{-m/2}h_α` and `b_α = λ_α^{(J-m)/2}` (summable): there
are `C` and `c > 0` (depending on the fixed orders, model and preparation parameters and `T`, not on `α, r, t, b, n`) such that,
for every `0 ≤ r ≤ t` and every classical adjoint solution `U(·,t)φ`,
`‖U(r,t)φ_α‖_{C_b^k} ≤ C b_α` and `‖∇U(r,t)φ_α‖_{C_b^k} ≤ C b_α e^{-c(t-r)}`; the same two bounds hold for the terminal test `L_tφ_α`;
the first holds for `(L_t²+∂_tL_t)φ_α` as well; and uniformly in `b ≥ 0` the initial window tests satisfy
`‖f_{b,n,α}‖_{C_b^k} ≤ C (1+n)^{-5/4} b_α`.  Technical hypotheses: `0 ≤ σ < d` (the source does not state the range; this is the range of
S6 and S2.1(i)); existence of the adjoint solutions with terminal data `φ_α` (needed to give meaning to `U(0,b+u)φ_α` in the window
tests; the orbit bounds themselves are stated for every classical adjoint solution). Repair ED13 (2026-10-25, approved): the time derivative of the generator in the fifth orbit claim is the right derivative (at t = 0 a two-sided derivative would read the coefficient at negative times). Repair D2/ED14 (2026-10-25, approved): the class constants (c₁, C₁) are universally quantified before εstar (as in S2.1(ii)); R2ClassExists is no longer required. -/
theorem r2_window_orbits (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ) (hT : 0 < T) :
    ∀ c₁ C₁ : ℝ, ∃ εstar : ℝ, 0 < εstar ∧
      ∃ C c : ℝ, 0 < c ∧
      (Summable fun α : MultiIndex d =>
        oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2)) ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
        IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ → ∀ α : MultiIndex d,
        let Cf := (quadraticGradientDyn d s a β).coeff ρ
        let bα := oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2)
        let φ := oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α
        (∀ t : ℝ, 0 ≤ t →
          R2OrbitSup Cf (4 * d + 42) t φ (C * bα) ∧ R2OrbitGrad Cf (4 * d + 42) t φ (C * bα) c ∧
          R2OrbitSup Cf (4 * d + 42) t (generatorW Cf t φ) (C * bα) ∧
          R2OrbitGrad Cf (4 * d + 42) t (generatorW Cf t φ) (C * bα) c ∧
          R2OrbitSup Cf (4 * d + 42) t (fun x => generatorW Cf t (generatorW Cf t φ) x +
            derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t) (C * bα)) ∧
        ((∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW Cf t φ f) →
          ∀ (b : ℝ), 0 ≤ b → ∀ n : ℕ,
            MemCb (4 * d + 42) (r2WindowTest Cf (((24 * d + 240 : ℕ)) : ℝ) T b n α) ∧
            cbNorm (4 * d + 42) (r2WindowTest Cf (((24 * d + 240 : ℕ)) : ℝ) T b n α) ≤
              C * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα) := by
  sorry

/-- The window feature `Γ_{b,r,a}(x) ∈ 𝒦_T = H¹([0,T];ℓ²) ⊕ ℓ²` (S L8314-8322): for `r < b` the first component is
`(u ↦ ∂_aU(r,b+u)φ_j(x))_j` and the second is zero; for `r ≥ b` they are `(u ↦ ∂_aU(r,max{b+u,r})φ_j(x))_j` and `(∂_aφ_j(x))_j`.
In the representation `(A₀, A', B)` of `KSpace`: `A₀ = (∂_aU(r,max{b,r})φ_j(x))_j`, `A'(u) = 1_{r<b+u}(∂_aU(r,b+u)L_{b+u}φ_j(x))_j`,
`B = 1_{b≤r}(∂_aφ_j(x))_j` (for `r ≥ b` the point `max{b,r} = r` and `U(r,r) = id`). -/
def r2WindowFeature (C : WholeCoeff d) (m T : ℝ) (Dop : (Euc d → ℝ) → Euc d → ℝ) (b r : ℝ) (x : Euc d) :
    KSpace d m T :=
  open Classical in
  let base : OscDual d m := ellVec m fun α => Dop (propagatorW C r (max b r) (oscTestFun m α)) x
  let f : ℝ → OscDual d m := fun u => if r < b + u then
    ellVec m fun α => Dop (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x else 0
  KSpace.mk base (if h : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp f else 0)
    (if b ≤ r then ellVec m fun α => Dop (oscTestFun m α) x else 0)

/-- The `α`-th Hermite coordinate of the instantaneous nonlinear forcing for the terminal time `t`, centered at the moving
reference: `D_{μ^r}(h_{U(r,t)φ_α})(X_N^r)`, `h_f = (∇f(x)-∇f(y))·∇g(x-y)` (cf. `commForcing`, which centers at a fixed measure). -/
def r2CommForcingMov {Ω : Type*} {N : ℕ} (C : WholeCoeff d) (s m : ℝ) (ρ : ℝ → Euc d → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (α : MultiIndex d) (t r : ℝ) (ζ : Ω) : ℝ :=
  centeredPairFunctional
    (commutatorKernel d s (fun x => gradient (propagatorW C r t (oscTestFun m α)) x))
    (X (Real.toNNReal r) ζ) (withDensityReal (ρ r))

/-- Lemma 10.4 (S:W:lem:r2-window-errors, TeX S L8304-8312): the past contribution to window noise and forcing.  Quadratic
model (as S10.3, `0 ≤ σ < d`, `T > 0`, `m = 24d+240`), the stationary measure or a small nonlinear trajectory, `w_N = localizationRate`
(`(N^{-1/d} + √o_N)^{4/(d+4)}`, S L343), a canonical particle solution whose time marginals satisfy the uniform actual-law pressure,
energy and moment bounds of Theorem S6.6 (`MovParticleBounds` with constant `CB` for `t ≥ 0` and the window second-moment bound
`E sup_{[b,b+T]}N⁻¹∑|x_i|² ≤ CB`).  Then for every window `[b,b+T]`, `b ≥ 0`: (a) the noise covariance error is at most `C_T w_N` in trace
integral: `E∫_0^{b+T}‖C_r - C̄_r‖_1dr ≤ C_Tw_N`, with `C_r = featureForm (empirical μ_N^r)` and `C̄_r = featureForm (μ^r)` of the window
features `r2WindowFeature` for the gradient components (`‖·‖_1` is `traceNormForm`; the existence of the bounded bilinear forms is
part of the conclusion), and (b) the nonlinear fluctuation remainder `D_b(u)_α = -(√N/2)∫_0^{b+u}D_{μ^r}(h_{U(r,b+u)φ_α})(X_N^r)dr`
has `E sup_{0≤u≤T}‖D_b(u)‖_{ℓ²} ≤ C_T√Nδ_N`.  Constants uniform in `b ≥ 0`; `C_T` is chosen after `CB`; `c₁, C₁`, then `ε_*, C₀` first, `C₀` being the completion constant of the class (`F_N(X_N,μ^t) + o_N ≥ 0` off collisions, as in `whole_space_prepared`: without this property the hypothesis `MovParticleBounds` could be vacuous).
AMBIGUITY: (a) the trace error carries the factor `q = β⁻¹` of S L3441 (absorbed in `C_T`); the "trace integral" of S L8308 is
the displayed `E∫‖C_r-C̄_r‖_1dr` of S L3441, over the whole history `[0,b+T]`.  Technical: `N ≥ 2`.  Repair ED12 (2026-10-25, approved): the identification of `Bt` is required only for r ∈ [0, b+T] (for r < 0 the adjoint propagator is an unconstrained choice). Repair D2/ED14 (2026-10-25, approved): the class constants (c₁, C₁) are universally quantified before εstar (as in S2.1(ii)); R2ClassExists is no longer required. -/
theorem r2_window_errors (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ) (hT : 0 < T) :
    ∀ c₁ C₁ : ℝ, ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀ : ℝ,
      (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
        IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (withDensityReal (ρ t)) + oN d s C₀ N) ∧
      ∀ CB : ℝ, ∃ CT : ℝ,
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
        IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
          IsR2Realization d s a β P X₀ W X →
          MovParticleBounds d s a β C₀ CB ρ N P X →
          (∀ b : ℝ, 0 ≤ b → ∫⁻ ζ, ⨆ t ∈ Set.Icc b (b + T),
            ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal CB) →
          ∀ b : ℝ, 0 ≤ b →
            (∃ Bt : ℝ → Ω → (KSpace d (wholeSpaceIndex d) T →L[ℝ] KSpace d (wholeSpaceIndex d) T →L[ℝ] ℝ),
              (∀ r ∈ Set.Icc (0:ℝ) (b + T), ∀ ζ u v, Bt r ζ u v =
                featureForm (wholeSpaceIndex d) T β⁻¹
                  (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ)
                    (wholeSpaceIndex d) T (gradComp i) b r x) (empirical (X r.toNNReal ζ)) u v -
                featureForm (wholeSpaceIndex d) T β⁻¹
                  (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ)
                    (wholeSpaceIndex d) T (gradComp i) b r x) (withDensityReal (ρ r)) u v) ∧
              ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (traceNormForm (Bt r ζ))) ∂P ≤
                ENNReal.ofReal (CT * localizationRate d s C₀ N)) ∧
            ∫⁻ ζ, ⨆ u ∈ Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
                -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u),
                  r2CommForcingMov ((quadraticGradientDyn d s a β).coeff ρ) s (wholeSpaceIndex d) ρ X α
                    (b + u) r ζ) ∂P ≤
              ENNReal.ofReal (CT * Real.sqrt N * deltaN d s N) := by
  sorry

/-- The initial coupling field `u ↦ (((√N(μ_N^0-μ^0) - η_N)(U(0,b+u)φ_α)))_α ∈ ℓ² = B_m` of
`W:r2:window-general-initial-cost` (S L8419-8422), as a function of `u`. -/
def r2InitCouplingFun {Ω : Type*} {N : ℕ} (C : WholeCoeff d) (m : ℝ) (μ0 : Measure (Euc d)) (b : ℝ)
    (X₀ : Ω → EucConfig d N) (η₀ : Ω → (Euc d → ℝ) → ℝ) (ζ : Ω) (u : ℝ) : OscDual d m :=
  ellVec m fun α =>
    Real.sqrt N * (pair (empirical (X₀ ζ)) (propagatorW C 0 (b + u) (oscTestFun m α)) -
      pair μ0 (propagatorW C 0 (b + u) (oscTestFun m α))) - η₀ ζ (propagatorW C 0 (b + u) (oscTestFun m α))

/-- The initial coupling path in `C([0,T];ℓ²)` (`0` if the field is not continuous in `u`; continuity is the hypothesis "the transported
initial paths are well-defined" of S10.5). -/
def r2InitCouplingPath {Ω : Type*} {N : ℕ} (C : WholeCoeff d) (m T : ℝ) (μ0 : Measure (Euc d)) (b : ℝ)
    (X₀ : Ω → EucConfig d N) (η₀ : Ω → (Euc d → ℝ) → ℝ) (ζ : Ω) : OscPath d m T :=
  windowPathOf m T 0 (r2InitCouplingFun C m μ0 b X₀ η₀ ζ)

/-- Corollary 10.5 (S:W:cor:r2-window-general-initial, TeX S L8403-8455): a prescribed, possibly non-Gaussian initial field.  A small
nonlinear quadratic trajectory (or the stationary measure), `0 ≤ σ < 2d/3`, `T > 0`, `m = 24d+240`; an arbitrary initial particle law `f_N^0` with
`H_{N,0} = H(f_N^0|Q_{N,β}(μ^0)) < ∞`, `B_N = 1 + H_{N,0} + Nδ_N`, `E_N = C_E(o_N + B_N/N)`; a prescribed random initial field `η_N` (a random
functional, coupled to the particle initial data on the same probability space) with coupling cost
`ε_N = sup_{b≥0}E‖(((√N(μ_N^0-μ^0) - η_N)(U(0,b+u)φ_j))_j‖_{C([0,T];ℓ²)}` (`ℝ≥0∞`-valued; finiteness is not assumed, an infinite right side
is trivial); `Y_N` the original linearized equation with initial field `η_N` and independent Gaussian noise
(`IsLinearFluctuationSolutionW`); `w_N^{ent} = inf_{R≥1}{R^{d/2}(N^{-1/d}+√E_N) + (1+B_N/N)R^{-2}}` (`generalLocalizationRate d E_N (B_N/N) N`).
Then for the windows `Ξ_{N,b}` (`flucPathW`, `η_N^{b+·}`) and `Y_{N,b}` (`processWindow`), uniformly in `b ≥ 0`:
`d_{C_b²}(Law Ξ_{N,b},Law Y_{N,b}) ≤ C_T(ε_N + B_N/√N + w_N^{ent})` and `W_1(Law Ξ_{N,b},Law Y_{N,b}) ≤ C_T(ε_N + B_N/√N + √w_N^{ent})`,
the constants being independent of `N, b, H_{N,0}`.  Quantifier order: `c₁, C₁`, then `ε_*`, the completion constant `C₀` (with its defining property `F_N(X_N,μ^t) + o_N ≥ 0` off collisions), the constant `C_E` in `E_N`
(source: "`E_N = C(o_N + B_N/N)`", the entropy-theorem constant; a larger `C_E` only weakens the conclusion) and `C_T` are chosen before `ρ, N, P, η_N`.
(The "sufficient fixed initial-field hypothesis" (convergence in the dual of `H^k(⟨x⟩^{-d-3}dx)`) and the remark that the exact empirical field is an
admissible `η_N` are not separate claims.)  Hypothesis from the source (S L8416-8417): "the transported initial paths are well-defined", i.e. the coupling field is a.s. continuous in `u` for every `b ≥ 0` (otherwise the junk `0` of `windowPathOf` makes `ε_N` spuriously `0`).
Statement change M1b (2026-10-22): conditional on `GibbsEntropyContraction d s a β N` (the arbitrary initial law `f_N^0` with `H_{N,0} < ∞` is propagated by entropy contraction against the invariant canonical Gibbs law, S L4640-4650).
Technical: `N ≥ 2`; measurability of both window maps is part of the conclusion. Repair D2/ED14 (2026-10-25, approved): the class constants (c₁, C₁) are universally quantified before εstar (as in S2.1(ii)); R2ClassExists is no longer required. -/
theorem r2_window_general_initial (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T) :
    ∀ c₁ C₁ : ℝ, ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀ : ℝ,
      (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
        IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (withDensityReal (ρ t)) + oN d s C₀ N) ∧
      ∃ CE CT : ℝ,
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
        IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N →
        GibbsEntropyContraction d s a β N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
          IsR2Realization d s a β P X₀ W X →
          relEntropy (law P X₀) (modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ 0))) < ⊤ →
          ∀ η₀ : Ω → (Euc d → ℝ) → ℝ, IndepFun (fun ζ => (X₀ ζ, η₀ ζ)) (fun ζ t => W t ζ) P →
          ∀ Y : ℝ → Ω → OscDual d (wholeSpaceIndex d),
          (∀ T' : ℝ, IsLinearFluctuationSolutionW P ((quadraticGradientDyn d s a β).coeff ρ)
            (wholeSpaceIndex d) β⁻¹ T' η₀ Y) →
          (∀ b : ℝ, 0 ≤ b → ∀ᵐ ζ ∂P, Continuous fun u : Set.Icc (0 : ℝ) T =>
            r2InitCouplingFun ((quadraticGradientDyn d s a β).coeff ρ) (wholeSpaceIndex d)
              (withDensityReal (ρ 0)) b X₀ η₀ ζ u) →
          let BN : ℝ := 1 + (relEntropy (law P X₀)
            (modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ 0)))).toReal + N * deltaN d s N
          let EN : ℝ := CE * (oN d s C₀ N + BN / N)
          let wEnt : ℝ := generalLocalizationRate d EN (BN / N) N
          let εN : ℝ≥0∞ := ⨆ b : {b : ℝ // 0 ≤ b}, ∫⁻ ζ, ENNReal.ofReal
            ‖r2InitCouplingPath ((quadraticGradientDyn d s a β).coeff ρ) (wholeSpaceIndex d) T
              (withDensityReal (ρ 0)) b X₀ η₀ ζ‖ ∂P
          ∀ b : ℝ, 0 ≤ b →
            AEMeasurable (flucPathW (wholeSpaceIndex d) T b (Real.sqrt N) X ρ) P ∧
            AEMeasurable (processWindow (wholeSpaceIndex d) T b Y) P ∧
            ENNReal.ofReal (smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T b (Real.sqrt N) X ρ))
                (law P (processWindow (wholeSpaceIndex d) T b Y))) ≤
              ENNReal.ofReal CT * (εN + ENNReal.ofReal (BN / Real.sqrt N + wEnt)) ∧
            wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T b (Real.sqrt N) X ρ))
                (law P (processWindow (wholeSpaceIndex d) T b Y)) ≤
              ENNReal.ofReal CT * (εN + ENNReal.ofReal (BN / Real.sqrt N + Real.sqrt wEnt)) := by
  sorry

end Windows


/-! ### Relaxation of the correction (S11.1, S11.2) -/

section Relaxation

/-- The path space `𝒳 = C([0,T];B_m)` with the fixed index `m = 24d+240` of S11 (S L8502). -/
abbrev R2X (d : ℕ) (T : ℝ) : Type := OscPath d (wholeSpaceIndex d : ℝ) T

/-- `λ` is a Poincaré constant of `μ` for `L = -ρ⁻¹div(ρ∇)` (S L8687): `λ Var_μ(f) ≤ ∫|∇f|²dμ` for `C¹` functions with bounded
gradient in `L²(μ)` (the form `Var ≤ λ⁻¹ E(f)`; same convention as `reflection_gap_poincare`). -/
def IsR2Poincare (μ : Measure (Euc d)) (lam : ℝ) : Prop :=
  ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → (∃ Cf : ℝ, ∀ x, ‖gradient f x‖ ≤ Cf) → MemLp f 2 μ →
    lam * ProbabilityTheory.variance f μ ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂μ

/-- The cross-covariance densities `χ_i^r` of the window `[u,u+T]` for the observation family `(τ,φ)` (S L8185-8187, M
`H:eq:cross-covariance-density`): for every `r ∈ [0,u+T]`, `χ_i^r` is a signed density with `χ_i^r/ρ_β ∈ L²(μ)`, `μ = ρ_β dx` (the
`L²(μ)`-relative density supplied by the Hilbert--Schmidt bound on the covariance; NOT a smooth density, which the source does not
assert), the pairings `∫ψ'χ_i^r` are integrable for the oscillator tests `ψ'`, and `∫ψ'χ_i^r = Cov(Z^r(ψ'),Z^{u+τ_i}(φ_i))`
(`linearGaussianCov`; the stationary reference `ρ_β`, preparation parameter `γ`). -/
def IsR2CrossDensities (d : ℕ) (s a β γ : ℝ) (ρβ : Euc d → ℝ) (T u : ℝ) (τ : Fin 3 → Set.Icc (0 : ℝ) T)
    (φ : Fin 3 → Euc d → ℝ) (χ : Fin 3 → ℝ → Euc d → ℝ) : Prop :=
  ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (u + T),
    MemLp (fun x => χ i r x / ρβ x) 2 (withDensityReal ρβ) ∧
    ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
      Integrable (fun x => ψ' x * χ i r x) ∧
      ∫ x, ψ' x * χ i r x = linearGaussianCov
        ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) β⁻¹
        (susceptibilityCov (rieszKernel d s) (withDensityReal ρβ) γ) r (u + τ i) ψ' (φ i)

/-- The cross-covariance densities `χ_i^r` (S L8185-8187) exist for every observation family on the window `[u,u+T]`.  (Without this
the `∀ χ` clause of `IsR2PathCubic` would be vacuous and `κ` unconstrained.) -/
def R2CrossDensitiesExist (d : ℕ) (s a β γ : ℝ) (ρβ : Euc d → ℝ) (T u : ℝ) : Prop :=
  ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ), (∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
    ∃ χ : Fin 3 → ℝ → Euc d → ℝ, IsR2CrossDensities d s a β γ ρβ T u τ φ χ

/-- `κ` is the cubic tensor `𝒦_{γ,u,T}` of the window `[u,u+T]` for the quadratic model with constant thermal reference `ρ_β`
and preparation parameter `γ` (S L8497-8499, the tensor `W:eq:r2-path-cubic` evaluated on this window): a symmetric element of
`𝒳^{⊗̂π3}` (`projTensor`) whose values on the trilinear forms `M(w_1,w_2,w_3) = ∏_iw_i(τ_i)(φ_i)` are the three terms of
`W:eq:r2-coordinate-cubic` (`cubicFormula`, with the whole-space adjoint, the Gaussian cross-covariance densities `χ_i^r` of `Z^{u+·}`
whose initial covariance is `R_γ`, and the integrals starting at physical time `0`), exactly the (repaired) clause of `whole_space_edgeworth` (S2.1(iii)): the densities `χ_i^r` (`IsR2CrossDensities`: `L²(μ)`-relative densities, no smoothness) are imposed for all `r ∈ [0,u+T]` (the formula uses `χ_{i+1}^r, χ_{i+2}^r` for `r ≤ t_i`), the pairings `∫ψ'χ_i^r` are integrable, and all integrals of `cubicFormula` are absolutely defined (`CubicFormulaIntegrable`).  Their existence (`R2CrossDensitiesExist`) is part of the predicate (repair P4: otherwise the formula clause is vacuous when no density family exists). -/
def IsR2PathCubic (d : ℕ) (s a β γ : ℝ) (ρβ : Euc d → ℝ) (T u : ℝ) (κ : projTensor (R2X d T) 3) : Prop :=
  (∀ (σ : Equiv.Perm (Fin 3)) (M : (R2X d T) [×3]→L[ℝ] ℝ),
    (κ : TensorDual (R2X d T) 3) (M.domDomCongr σ) = (κ : TensorDual (R2X d T) 3) M) ∧
  R2CrossDensitiesExist d s a β γ ρβ T u ∧
  ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ),
    (∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
    ∀ χ : Fin 3 → ℝ → Euc d → ℝ,
    IsR2CrossDensities d s a β γ ρβ T u τ φ χ →
    ∀ M : (R2X d T) [×3]→L[ℝ] ℝ,
      (∀ w : Fin 3 → R2X d T, M w = ∏ i, OscDual.eval (OscPath.at' (w i) (τ i)) (φ i)) →
      (κ : TensorDual (R2X d T) 3) M =
        cubicFormula (quadraticGradientDyn d s a β) (fun _ => ρβ) β γ (withDensityReal ρβ)
          (fun i => u + τ i) φ χ ∧
      CubicFormulaIntegrable (quadraticGradientDyn d s a β) (fun _ => ρβ) γ (withDensityReal ρβ)
        (fun i => u + τ i) φ χ

/-- The cross-covariance densities exist (the row repairing S11.1(b); TeX S L8185-8187: `χ_i^r/ρ_β ∈ L²(μ)` is the Hilbert--Schmidt/Riesz
representation of the covariance functional `ψ' ↦ Cov(Z^r(ψ'),Z^{u+τ_i}(φ_i))`). -/
theorem r2_cross_density_exists (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ) (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) :
    ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ u : ℝ, 0 ≤ u → R2CrossDensitiesExist d s a β γ ρβ T u := by
  sorry

/-- Proposition 11.1 (S:W:prop:r2-tensor-relaxation, TeX S L8716-8734): covariance and cubic-tensor relaxation.  Quadratic
model (`d ≥ 2`, `a, β > 0`, `0 ≤ σ < d/2`), constant thermal mean-field measure `μ = ρ_β dx`, preparation parameter `γ`
(`γ > 0` for `σ > 0`, `γ ≥ 0` for `σ = 0`; the stationary preparation is `γ = β`), window length `T > 0`, `𝒳 = C([0,T];B_m)`,
`m = 24d+240`, and `λ_μ > 0` a Poincaré constant of `L = -ρ⁻¹div(ρ∇)` (`IsR2Poincare`), `κ = λ_μ/β`.  There are `c > 0` and `C`
(depending only on the fixed model and preparation parameters, `T` and `λ_μ`) such that for all `u ≥ 0`:
(a) `‖Cov(Z_{γ,u}) - Cov(Z_{β,T})‖_π ≤ Ce^{-2κu}`, with `Z_{γ,u}(t) = Z^{u+t}` the linear Gaussian evolution with initial covariance `R_γ` and
`Z_{β,T}` the stationary window (initial covariance `R_β`), the projective norm of the covariance tensor `E[Z⊗Z] ∈ 𝒳⊗̂𝒳` being its dual
norm on bounded bilinear forms: `sup_{‖M‖≤1}|E M(Z_{γ,u},Z_{γ,u}) - E M(Z_{β,T},Z_{β,T})| ≤ Ce^{-2κu}` (law-only statement, any realization);
(b) `‖𝒦_{γ,u,T} - 𝒦_{β,T}‖_π ≤ Ce^{-cu}` for the cubic tensors (`IsR2PathCubic`; the norm of `projTensor` is the projective norm).
The last sentences of the proposition (the stationary cubic tensor at one time is `∫ℓ_x^{⊗3}dμ`, `ℓ_x(φ) = R_βP_μφ(x)`, and the compatibility of the
formulas under restriction to windows) are the case `γ = β` of `r2_static_edgeworth` / `IsR2PathCubic`; not restated. -/
theorem r2_tensor_relaxation (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hlam : 0 < lam) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      IsR2Poincare (withDensityReal ρβ) lam →
      (∀ {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
        [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] (Z₁ : ℝ → Ω₁ → OscDual d (wholeSpaceIndex d : ℝ))
        (Z₂ : ℝ → Ω₂ → OscDual d (wholeSpaceIndex d : ℝ)),
        (∀ T' : ℝ, IsLinearGaussianEvolutionW P₁ ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
          (wholeSpaceIndex d) β⁻¹ T' (susceptibilityCov (rieszKernel d s) (withDensityReal ρβ) γ) Z₁) →
        (∀ T' : ℝ, IsLinearGaussianEvolutionW P₂ ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
          (wholeSpaceIndex d) β⁻¹ T' (susceptibilityCov (rieszKernel d s) (withDensityReal ρβ) β) Z₂) →
        ∀ u : ℝ, 0 ≤ u → ∀ M : (R2X d T) [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
          |∫ ζ, M ![processWindow (wholeSpaceIndex d) T u Z₁ ζ, processWindow (wholeSpaceIndex d) T u Z₁ ζ] ∂P₁ -
            ∫ ζ, M ![processWindow (wholeSpaceIndex d) T 0 Z₂ ζ, processWindow (wholeSpaceIndex d) T 0 Z₂ ζ] ∂P₂| ≤
            C * Real.exp (-2 * (lam / β) * u)) ∧
      ∀ u : ℝ, 0 ≤ u → ∀ κu κβ : projTensor (R2X d T) 3,
        IsR2PathCubic d s a β γ ρβ T u κu → IsR2PathCubic d s a β β ρβ T 0 κβ →
        ‖κu - κβ‖ ≤ C * Real.exp (-c * u) := by
  sorry

/-- The pairing `E⟨D³Φ(w),κ⟩ = E[κ(D³Φ(w))]` of the third derivative along a random path with a projective tensor. -/
def r2CubicExpect {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') {T : ℝ} (w : Ω' → R2X d T)
    (κ : projTensor (R2X d T) 3) (Φ : R2X d T → ℝ) : ℝ :=
  ∫ ζ, (κ : TensorDual (R2X d T) 3) (iteratedFDeriv ℝ 3 Φ (w ζ)) ∂P'

/-- Corollary 11.2 (S:W:cor:r2-two-parameter-edgeworth, TeX S L8825-8841): joint particle-number and time limits.  Setting of
`r2_tensor_relaxation` (quadratic model, `0 ≤ σ < d/2`, constant thermal reference, particles prepared from `Q_{N,γ}(μ)` and run
with the gradient dynamics, `ζ_{N,u} = ζ_N^{u+·}`, `Z_{γ,u}`, `Z_{β,T}`, the tensors `𝒦_{γ,u,T}`, `𝒦_{β,T}`, `κ = λ_μ/β`).  Let `ε_N` bound the uniform window
expansion remainder `W:eq:r2-uniform-window-edgeworth`: `sup_{u≥0}sup_{‖Φ‖_{C_b^5}≤1}|√N{EΦ(ζ_{N,u}) - EΦ(Z_{γ,u})} - (1/6)E D³Φ(Z_{γ,u})[𝒦_{γ,u,T}]| ≤ ε_N`
(the quantity `ε_N` of the source, `ε_N → 0` by S2.1(iii)/`whole_space_edgeworth`).  Then, with `c, C` of `r2_tensor_relaxation`:
(a) `sup_{‖Φ‖_{C_b^5}≤1}|EΦ(ζ_{N,u}) - EΦ(Z_{β,T}) - (6√N)⁻¹E D³Φ(Z_{β,T})[𝒦_{β,T}]| ≤ ε_N/√N + Ce^{-2κu} + (C/√N)e^{-cu}`, for all `u ≥ 0, N ≥ 2`;
(b) consequently, if `ε_N → 0` and `u_N ≥ 0` satisfies `√N e^{-2κu_N} → 0`, then the expansion
`√N{EΦ(ζ_{N,u_N}) - EΦ(Z_{β,T})} - (1/6)E D³Φ(Z_{β,T})[𝒦_{β,T}] → 0` holds uniformly over the unit ball of `C_b^5(𝒳)`, i.e. `o(N^{-1/2})` on `[u_N,u_N+T]`;
(c) the same conclusion holds for every `u_N ≥ (1/(4κ)+δ)log N` (fixed `δ > 0`).
Representation: the realization is any `IsR2Realization` of the particle system with initial law `Q_{N,γ}(μ)` and the Gaussian windows are those
of `IsLinearGaussianEvolutionW` with initial covariances `susceptibilityCov` at `γ`, `β`; (b), (c) are stated for a sequence of such realizations.  `ε_N` enters as the
hypothesis `hε` (it dominates the expansion error of the uniform window theorem); `C` depends on `λ_μ`. -/
theorem r2_two_parameter_edgeworth (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hlam : 0 < lam) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      IsR2Poincare (withDensityReal ρβ) lam →
      ∀ (κγ : ℝ → projTensor (R2X d T) 3) (κβ : projTensor (R2X d T) 3),
        (∀ u : ℝ, 0 ≤ u → IsR2PathCubic d s a β γ ρβ T u (κγ u)) → IsR2PathCubic d s a β β ρβ T 0 κβ →
        ∀ {Ω' Ω'' : Type} [MeasurableSpace Ω'] [MeasurableSpace Ω''] (P' : Measure Ω') (P'' : Measure Ω'')
          [IsProbabilityMeasure P'] [IsProbabilityMeasure P''] (Zγ : ℝ → Ω' → OscDual d (wholeSpaceIndex d : ℝ))
          (Zβ : ℝ → Ω'' → OscDual d (wholeSpaceIndex d : ℝ)),
        (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
          (wholeSpaceIndex d) β⁻¹ T' (susceptibilityCov (rieszKernel d s) (withDensityReal ρβ) γ) Zγ) →
        (∀ T' : ℝ, IsLinearGaussianEvolutionW P'' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
          (wholeSpaceIndex d) β⁻¹ T' (susceptibilityCov (rieszKernel d s) (withDensityReal ρβ) β) Zβ) →
        (∀ {N : ℕ}, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
          (εN : ℝ),
          IsR2Realization d s a β P X₀ W X →
          law P X₀ = modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρβ) →
          (∀ u : ℝ, 0 ≤ u → ∀ Φ ∈ CbUnitBall (R2X d T) 5,
            |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T u P X ζ) ∂P -
                ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T u Zγ ζ) ∂P') -
              (1 / 6) * r2CubicExpect P' (processWindow (wholeSpaceIndex d) T u Zγ) (κγ u) Φ| ≤ εN) →
          ∀ u : ℝ, 0 ≤ u → ∀ Φ ∈ CbUnitBall (R2X d T) 5,
            |∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T u P X ζ) ∂P -
                ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T 0 Zβ ζ) ∂P'' -
              (1 / (6 * Real.sqrt N)) * r2CubicExpect P'' (processWindow (wholeSpaceIndex d) T 0 Zβ) κβ Φ| ≤
              εN / Real.sqrt N + C * Real.exp (-2 * (lam / β) * u) +
                C / Real.sqrt N * Real.exp (-c * u)) ∧
        ∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
          [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → EucConfig d N)
          (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N)
          (εN : ℕ → ℝ), Tendsto εN atTop (𝓝 0) →
          (∀ N, 2 ≤ N → IsR2Realization d s a β (P N) (X₀ N) (W N) (X N) ∧
            law (P N) (X₀ N) = modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρβ) ∧
            ∀ u : ℝ, 0 ≤ u → ∀ Φ ∈ CbUnitBall (R2X d T) 5,
              |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T u (P N) (X N) ζ) ∂(P N) -
                  ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T u Zγ ζ) ∂P') -
                (1 / 6) * r2CubicExpect P' (processWindow (wholeSpaceIndex d) T u Zγ) (κγ u) Φ| ≤ εN N) →
          ∀ uN : ℕ → ℝ, (∀ N, 0 ≤ uN N) →
            ((Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * (lam / β) * uN N)) atTop (𝓝 0)) ∨
              ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 2 ≤ N →
                (1 / (4 * (lam / β)) + δ) * Real.log N ≤ uN N) →
            ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 2 ≤ N → ∀ Φ ∈ CbUnitBall (R2X d T) 5,
              |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T (uN N) (P N) (X N) ζ) ∂(P N) -
                  ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T 0 Zβ ζ) ∂P'') -
                (1 / 6) * r2CubicExpect P'' (processWindow (wholeSpaceIndex d) T 0 Zβ) κβ Φ| ≤ ε := by
  sorry

end Relaxation

end HRS.Whole
