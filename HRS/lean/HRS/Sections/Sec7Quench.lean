import HRS.Sections.Sec7Setting

/-!
# Section 7: change of preparation temperature (Propositions 7.13, 7.14) (SPEC-7)

Specification file (statements with `sorry` proofs).  Sources (`HRS_periodic_main_20261008T010000Z.tex`):
* Proposition 7.13 `M:E:prop:quench` (TeX L9352-9393): exact mode and window covariances;
* Corollary 7.14 `M:E:cor:critical-Edgeworth` (TeX L9453-9485): sharp waiting time.

## Representation decisions
* The homogeneous torus (`V = 0`, `ρ ≡ 1`, `μ = dx`), gradient dynamics `D` (`M = -I`), `D.invβ = β⁻¹`.
  `ĝ(k)` is `HRS.rieszCoeff d s k`; `λ_{β,k} = (2π|k|)²(β⁻¹ + ĝ(k))`, `v_{β,k} = (1 + βĝ(k))⁻¹`
  (TeX L877, L1236).  `ℤ^d_+` is the lexicographically positive half-lattice `Lattice.IsPosHalf`, and
  `ψ_k = √2 cos(2πk·x)`, `χ_k = √2 sin(2πk·x)`.
* `Z` is `IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z` (the solution of `E:eq:homogeneous-linear` with
  `Z^0` the homogeneous Gibbs susceptibility at `β₀`); the stationary window `Z_{∞,T}` is the same with `β₀ = β`.
* The SDE `dZ^t(e) = -λ Z^t(e) dt + σ dB^t` is stated in integrated form (the project's convention for additive
  noise), with an existentially quantified Brownian motion `B` independent of `Z^0(e)`.
* Projective covariance tensors `C_a = E[Z^{a+·}⊗Z^{a+·}] ∈ 𝒳_T ⊗̂_π 𝒳_T` are represented as functionals on
  bounded bilinear forms `M` on `𝒳_T`: `M ↦ E[M(Z^{a+·},Z^{a+·})]`; the projective norm of a (difference of)
  tensor(s) is the supremum over `‖M‖ ≤ 1` (the tensor lives in the dual of the bilinear forms,
  `HRS.TensorDual`).  Convergence "in projective tensor norm" is therefore uniform convergence over the unit
  ball of bilinear forms.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Sec7

variable {d : ℕ}

/-- `λ_{β,k} = (2π|k|)²(β⁻¹ + ĝ(k))` (TeX L877). -/
def lamMode (d : ℕ) (s β : ℝ) (k : Lattice d) : ℝ :=
  (2 * Real.pi * Lattice.enorm k) ^ 2 * (β⁻¹ + rieszCoeff d s k)

/-- `v_{β,k} = (1 + βĝ(k))⁻¹` (TeX L1236). -/
def varMode (d : ℕ) (s β : ℝ) (k : Lattice d) : ℝ := (1 + β * rieszCoeff d s k)⁻¹

/-- `δv_k = v_{β₀,k} - v_{β,k}` (TeX L9363). -/
def deltaVar (d : ℕ) (s β β₀ : ℝ) (k : Lattice d) : ℝ := varMode d s β₀ k - varMode d s β k

/-- The positive half-lattice `ℤ^d_+`. -/
abbrev PosHalf (d : ℕ) : Type := {k : Lattice d // Lattice.IsPosHalf k}

/-- The real modes `ψ_k = √2 cos(2πk·x)` (`b = true`) and `χ_k = √2 sin(2πk·x)` (`b = false`). -/
def modeFn (k : Lattice d) (b : Bool) (x : Torus d) : ℝ :=
  if b then Real.sqrt 2 * Torus.cosMode k x else Real.sqrt 2 * Torus.sinMode k x

/-- `λ_* = min_{k ≠ 0} λ_{β,k}` over `ℤ^d_+` (as an infimum; the theorem asserts it is attained). -/
def lamStar (d : ℕ) (s β : ℝ) : ℝ := ⨅ k : PosHalf d, lamMode d s β k.1

/-- The elementary path `f_{k,e}(t) = e^{-λ t} e ∈ 𝒳_{m,T}` (`E:eq:slowest`, TeX L9374). -/
def modePath (m T lam : ℝ) (e : Torus d → ℝ) : PathSpace d m T :=
  show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from
    ⟨fun t => Real.exp (-lam * (t : ℝ)) • NegSobolev.ofFun m e, by fun_prop⟩

/-- The tensor `D_* = ∑_{k∈ℐ_*} δv_k (f_{k,ψ_k}^{⊗2} + f_{k,χ_k}^{⊗2})` (`E:eq:Dstar`, TeX L9383-9385),
as a functional on bounded bilinear forms `M` on `𝒳_T`. -/
def slowTensor (d : ℕ) (s β β₀ m T : ℝ) (M : PathSpace d m T [×2]→L[ℝ] ℝ) : ℝ :=
  ∑' k : {k : PosHalf d // lamMode d s β k.1 = lamStar d s β},
    deltaVar d s β β₀ k.1.1 *
      (M ![modePath m T (lamMode d s β k.1.1) (modeFn k.1.1 true),
           modePath m T (lamMode d s β k.1.1) (modeFn k.1.1 true)] +
        M ![modePath m T (lamMode d s β k.1.1) (modeFn k.1.1 false),
           modePath m T (lamMode d s β k.1.1) (modeFn k.1.1 false)])

/-- Proposition 7.13 `M:E:prop:quench` (TeX L9352-9393), first part: the Fourier coordinates of `Z`
(`E:eq:mode-OU`, `E:eq:quench-covariance`).  Setting (TeX L9334-9351): homogeneous torus `V = 0`, `ρ ≡ 1`,
`0 ≤ s < d`, `β > 0`, `β₀ > 0`, `β₀ ≠ β`, `Z` the solution of `E:eq:homogeneous-linear` with `Z^0` having the
homogeneous Gibbs susceptibility at `β₀` independent of the noise.  For each real mode `e ∈ {ψ_k, χ_k}`,
`k ∈ ℤ^d_+`:
* `Z^t(e)` solves `dZ^t(e) = -λ_{β,k}Z^t(e)dt + √(2/β)(2π|k|) dB^t_{k,e}` (integrated form) with a Brownian
  motion `B` independent of `Z^0(e)`, and `Var(Z^0(e)) = v_{β₀,k}`;
* all these real coordinate processes (over `(k,e)`) are independent;
* `E[Z^{a+t}(e)Z^{a+r}(e)] = v_{β,k}e^{-λ|t-r|} + δv_k e^{-2λa}e^{-λ(t+r)}` for `a,t,r ≥ 0`.
Standing: `d ≥ 2` (M L419); "all Gaussian assertions hold for every `0 ≤ s < d`" (TeX L9351), which is
`D.hsd`. -/
theorem quench_modes (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) (hne : β₀ ≠ β)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z) :
    (∀ (k : PosHalf d) (b : Bool), ∃ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P ∧
        IndepFun (fun ω => NegSobolev.eval (Z 0 ω) (modeFn k.1 b)) (fun ω => fun t => B t ω) P ∧
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, NegSobolev.eval (Z t ω) (modeFn k.1 b) =
          NegSobolev.eval (Z 0 ω) (modeFn k.1 b) -
            lamMode d s β k.1 * (∫ u in Set.Icc (0 : ℝ) t, NegSobolev.eval (Z u ω) (modeFn k.1 b)) +
            Real.sqrt (2 / β) * (2 * Real.pi * Lattice.enorm k.1) * B t ω) ∧
    (∀ (k : PosHalf d) (b : Bool),
      ∫ ω, NegSobolev.eval (Z 0 ω) (modeFn k.1 b) ^ 2 ∂P = varMode d s β₀ k.1) ∧
    iIndepFun (fun (kb : PosHalf d × Bool) ω => fun t : ℝ≥0 =>
      NegSobolev.eval (Z t ω) (modeFn kb.1.1 kb.2)) P ∧
    (∀ (k : PosHalf d) (b : Bool) (a t r : ℝ), 0 ≤ a → 0 ≤ t → 0 ≤ r →
      ∫ ω, NegSobolev.eval (Z (a + t) ω) (modeFn k.1 b) * NegSobolev.eval (Z (a + r) ω) (modeFn k.1 b) ∂P =
        varMode d s β k.1 * Real.exp (-lamMode d s β k.1 * |t - r|) +
          deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
            Real.exp (-lamMode d s β k.1 * (t + r))) := by
  sorry

/-- Proposition 7.13 `M:E:prop:quench` (TeX L9352-9393), second part: window covariance tensors
(`E:eq:slowest`-`E:eq:sharp-covnorm`).  For `m > d/2 + 1`, `T > 0`, `𝒳_T = C([0,T];H^{-m}_0)`, `Z` as above
(initial temperature `β₀ ≠ β`) and `Z_∞` the stationary solution (initial temperature `β`); `C_a - C_∞` is the
difference of the covariance tensors of the windows `Z^{a+·}` and `Z_∞^{0+·}`, written `Δ_a(M) =
E[M(Z^{a+·},Z^{a+·})] - E[M(Z_∞^{·},Z_∞^{·})]` on bilinear forms `M`.  Conclusions:
(i) `λ_* > 0`, `ℐ_*` finite and nonempty;
(ii) for `a ≥ 0`, the series `∑_k δv_k e^{-2λ_k a}(f_{kψ}^{⊗2} + f_{kχ}^{⊗2})` converges absolutely in projective
norm (`‖f⊗f‖_π = ‖f‖²`) and equals `Δ_a` on every bilinear form (`E:eq:window-spectral`);
(iii) `e^{2λ_*a}Δ_a → D_*` in projective norm, i.e. uniformly on the unit ball of bilinear forms, and `D_* ≠ 0`
(`E:eq:Dstar`);
(iv) there are `0 < c_T ≤ C_T` with `c_T e^{-2λ_*a} ≤ ‖Δ_a‖_π ≤ C_T e^{-2λ_*a}` for `a ≥ 0`
(`E:eq:sharp-covnorm`; the projective norm is the supremum over the unit ball, written as a supremum for the lower
bound and as a pointwise bound for the upper bound, avoiding the real `iSup` junk value).
Technical hypotheses: as in `quench_modes`. -/
theorem quench_window_tensors (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) (hne : β₀ ≠ β)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ) (hm : (d : ℝ) / 2 + 1 < m)
    (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Zs : ℝ → Ω' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m P' Zs) :
    let Δ : ℝ → (PathSpace d m T [×2]→L[ℝ] ℝ) → ℝ := fun a M =>
      ∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P -
        ∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂P'
    (0 < lamStar d s β ∧ {k : PosHalf d | lamMode d s β k.1 = lamStar d s β}.Finite ∧
      {k : PosHalf d | lamMode d s β k.1 = lamStar d s β}.Nonempty) ∧
    (∀ a : ℝ, 0 ≤ a →
      Summable (fun k : PosHalf d => |deltaVar d s β β₀ k.1| * Real.exp (-2 * lamMode d s β k.1 * a) *
        (‖modePath m T (lamMode d s β k.1) (modeFn k.1 true)‖ ^ 2 +
          ‖modePath m T (lamMode d s β k.1) (modeFn k.1 false)‖ ^ 2)) ∧
      ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ a M =
        ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)])) ∧
    (∀ ε : ℝ, 0 < ε → ∃ a₀ : ℝ, ∀ a ≥ a₀, ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |Real.exp (2 * lamStar d s β * a) * Δ a M - slowTensor d s β β₀ m T M| ≤ ε) ∧
    (∃ M : PathSpace d m T [×2]→L[ℝ] ℝ, slowTensor d s β β₀ m T M ≠ 0) ∧
    ∃ cT CT : ℝ, 0 < cT ∧ cT ≤ CT ∧ ∀ a : ℝ, 0 ≤ a →
      (∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |Δ a M| ≤ CT * Real.exp (-2 * lamStar d s β * a)) ∧
      cT * Real.exp (-2 * lamStar d s β * a) ≤
        ⨆ M : {M : PathSpace d m T [×2]→L[ℝ] ℝ // ‖M‖ ≤ 1}, |Δ a M.1| := by
  sorry

/-- Proposition 7.13, equal-temperature remark (TeX L9484-9485, last sentence of Corollary 7.14: "When
`β₀ = β`, the covariance transient vanishes exactly"): for `β₀ = β` the window covariance tensors of `Z^{a+·}`
and of the stationary window coincide for every `a ≥ 0` (formula `E:eq:window-spectral` with `δv = 0`).
Only this Gaussian part of that sentence is formalised (see the docstring of `critical_edgeworth`). -/
theorem quench_equal_temperature (hd : 2 ≤ d) {s β : ℝ} (hβ : 0 < β)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ) (hm : (d : ℝ) / 2 + 1 < m)
    (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β m P Z)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Zs : ℝ → Ω' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m P' Zs) :
    ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ,
      ∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P =
        ∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂P' := by
  sorry

/-- Corollary 7.14 `M:E:cor:critical-Edgeworth` (TeX L9453-9485).  Assume `0 ≤ s < d/2`, `m > 3d + 8`, the
particles start from `Q_{N,β₀}(dx)` with fixed `β₀ > 0`, `β₀ ≠ β` (homogeneous torus, `V = 0`, gradient
dynamics), `T > 0`.
1. `m_N^t = dx` for all `N ≥ 1`, `t ≥ 0` (the mean empirical measure is Haar measure), hence
   `η_N^t = ζ_N^t = √N(μ_N^t - dx)`.
2. If `a_N = log N/(4λ_*) + τ + o(1)`, `τ ∈ ℝ`, then uniformly over `‖Φ‖_{C_b^5(𝒳_T)} ≤ 1`,
   `√N(E Φ(ζ_N^{a_N+·}) - E Φ(Z_{∞,T})) = (e^{-2λ_*τ}/2) E⟨D²Φ(Z_{∞,T}),D_*⟩ + (1/6) E⟨D³Φ(Z_{∞,T}),𝔎_{∞,T}⟩ + o(1)`
   (`E:eq:critical-expansion`; `⟨D²Φ,D_*⟩ = slowTensor` applied to `D²Φ`).
3. For an arbitrary `a_N → ∞`, the purely stationary Edgeworth formula (quadratic term omitted, uniform
   `o(N^{-1/2})` remainder) holds iff `√N e^{-2λ_*a_N} → 0`, equivalently `a_N - log N/(4λ_*) → +∞`
   (`E:eq:necessary-wait`).
The last sentence of the corollary ("When `β₀ = β` ... no waiting-time condition") is formalised by
`quench_equal_temperature` (the covariance transient vanishes exactly) and `critical_edgeworth_equal_temperature`
(under the same import `hK`, the purely stationary formula holds for every `a_N → ∞`, because `Z^{a+·}` and the
stationary window have the same law).
INTERIM IMPORT (hypothesis `hK`): `hK` is the conclusion of Corollary 2.14 `H:cor:stationary-correction`
(`H:eq:hybrid-correction`, TeX L1342-1348), imported as a hypothesis; it is to be replaced by Theorem 2.13/Corollary 2.14
once those are stated in Lean (a Section 2 packet is drafting them).  `𝔎_{∞,T}` is "the stationary cubic path tensor of
`H:thm:edgeworth`".  It is represented as a bounded functional `Kinf` on trilinear forms
(an element of `TensorDual 𝒳_T 3`, `Kinf ∈ projTensor`) satisfying the hybrid expansion
`E:eq:hybrid-correction` (imported in the TeX proof as `E:eq:hybrid-import`, L9487-9492) for every
`a_N → ∞`, uniformly on the `C_b^5` unit ball; this is the only property of `𝔎_{∞,T}` used.
Technical hypotheses: `d ≥ 2`; realisations exist for every `N ≥ 1`; `Z`, `Z_∞` Gaussian windows on arbitrary
probability spaces; `hK` as just described. -/
theorem critical_edgeworth (hd : 2 ≤ d) {s β β₀ : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hne : β₀ ≠ β) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0))
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization D (P N)
      (modulatedGibbs (periodicRiesz d s) N β₀ volume) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P' Z)
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Zs : ℝ → Ω'' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m P'' Zs)
    (Kinf : TensorDual (PathSpace d m T) 3) (hKmem : Kinf ∈ projTensor (PathSpace d m T) 3)
    (hK : ∀ a : ℕ → ℝ, Tendsto a atTop atTop → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
      ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
            ∫ ω, Φ (procWin m T (a N) Z ω) ∂P') -
          (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P''| ≤ ε) :
    (∀ N, 1 ≤ N → ∀ t : ℝ, 0 ≤ t → meanEmpirical ((P N).map (X N t.toNNReal)) = volume ∧
        ∀ ω, zetaAt m (P N) (X N) t ω = etaE m (X N t.toNNReal ω) volume) ∧
    (∀ (a : ℕ → ℝ) (τ : ℝ),
      Tendsto (fun N : ℕ => a N - Real.log N / (4 * lamStar d s β) - τ) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
              ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') -
            (Real.exp (-2 * lamStar d s β * τ) / 2 *
                ∫ ω, slowTensor d s β β₀ m T (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂P'' +
              (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P'')| ≤ ε) ∧
    (∀ a : ℕ → ℝ, Tendsto a atTop atTop →
      ((∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
          |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
                ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') -
            (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P''| ≤ ε) ↔
        Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * lamStar d s β * a N)) atTop (𝓝 0)) ∧
      (Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * lamStar d s β * a N)) atTop (𝓝 0) ↔
        Tendsto (fun N : ℕ => a N - Real.log N / (4 * lamStar d s β)) atTop atTop)) := by
  sorry

/-- Corollary 7.14 `M:E:cor:critical-Edgeworth`, last sentence (TeX L9484-9485): for `β₀ = β` (particles started from
`Q_{N,β}(dx)`, `V = 0`), the covariance transient vanishes (`quench_equal_temperature`) and there is no waiting-time
condition: under the import `hK` (Corollary 2.14, `H:eq:hybrid-correction`, with `Z` of initial temperature `β`; see
`critical_edgeworth` for its status), the purely stationary Edgeworth formula (quadratic term omitted, uniform
`o(N^{-1/2})` remainder) holds for *every* sequence `a_N → ∞`, because the Gaussian windows `Z^{a+·}` and `Z_{∞,T}`
have the same law.  Same setting and technical hypotheses as `critical_edgeworth` (with `β₀ = β`, no `hne`). -/
theorem critical_edgeworth_equal_temperature (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hβ : 0 < β) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0))
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization D (P N)
      (modulatedGibbs (periodicRiesz d s) N β volume) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β m P' Z)
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Zs : ℝ → Ω'' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m P'' Zs)
    (Kinf : TensorDual (PathSpace d m T) 3) (hKmem : Kinf ∈ projTensor (PathSpace d m T) 3)
    (hK : ∀ a : ℕ → ℝ, Tendsto a atTop atTop → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
      ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
            ∫ ω, Φ (procWin m T (a N) Z ω) ∂P') -
          (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P''| ≤ ε) :
    ∀ a : ℕ → ℝ, Tendsto a atTop atTop →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
              ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') -
            (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P''| ≤ ε := by
  sorry

end Sec7

end HRS

end
