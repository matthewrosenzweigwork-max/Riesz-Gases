import HRS.Sections.Sec7Setting

/-!
# Section 7: field-valued rows (Propositions 7.6, 7.8, 7.9) (SPEC-7)

Specification file (statements with `sorry` proofs).  Sources (`HRS_periodic_main_20261008T010000Z.tex`):
* Proposition 7.6 `M:F:prop:field-chaos` (TeX L8199-8214);
* Lemma 7.8 `M:U:lem:alltime-Lp` (TeX L8399-8407);
* Proposition 7.9 `M:U:prop:uniform-chaos` (TeX L8476-8492).

## Representation decisions
* Standing regime: `HRS.Sec7.Regime` (see `Sec7Setting.lean`).  The order of `E_r` is fixed to `r = 2d + 6`
  (hypothesis `hr`), the value used in the proofs (TeX L8504, L9171, L8663); the TeX statements leave `r`
  implicit.  SUSPECTED ISSUE: the subsection `sec:quadratic-fields` (TeX L8079) begins in the middle of a
  sentence ("gives the following uniform bounds on our fixed time interval", L8080), so its standing
  assumptions (the value of `r`, the horizon `T`, the preparation) are not stated in the source text.
* The quadratic field of the particle system `ℬ_N^t(φ) = N F_N^{h_{∇φ}}(X_N^t, μ^t) - E[·]` is `quadFieldAt`,
  with `φ` ranging over the real trigonometric basis (`ℬ̃_N^t(e_k) = N F_N^{h_{∇e_k}}`, `F:eq:Bdef`, TeX L8137-8140).
* Convergence in law is stated twice: against bounded continuous functions (weak convergence) and in
  `wassersteinE q` (`q ∈ [1,∞)`, values in `ℝ≥0∞`), on the product `C([0,T];E_r) × L²([0,T];E_r)` with the
  product (max) norm; the TeX does not specify the product metric.
* The limit objects: for *every* Gaussian solution `η` (`IsGaussianLimitField`) there is a field `ℬ` on the same
  probability space with `ℬ^t(e_k) = ½ I_2^{𝒞_t}(h_{∇e_k})` (`IsWickQuadraticField`, centred under `μ^t`) for a.e.
  `t`, and the stated convergence holds.  Uniqueness of `ℬ` (a.s.) is part of the Wick construction.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Sec7

variable {d : ℕ}

/-- `ℬ̃_N^t = N F_N^{h_{∇·}}(X, μ) ∈ E_r`, i.e. `ℬ̃_N^t(e_k) = N F_N^{h_{∇e_k}}(X,μ)` (`F:eq:Bdef`). -/
def quadFieldTilde {N : ℕ} (r : ℝ) (s : ℝ) (μ : Measure (Torus d)) (X : Config d N) : NegSobolev d r :=
  NegSobolev.ofSeq r fun k => (N : ℝ) * modulatedEnergy (hTransport d s (Torus.realMode k)) X μ

/-- `ℬ_N^t = ℬ̃_N^t - E[ℬ̃_N^t]` for the particle path `X` under `P` with background `μ^t`
(`F:eq:Bdef`, `U:eq:quadratic-fields`). -/
def quadFieldAt {N : ℕ} (r s : ℝ) (μ : ℝ → Measure (Torus d)) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (t : ℝ) (ω : Ω) : NegSobolev d r :=
  quadFieldTilde r s (μ t) (X t.toNNReal ω) - ∫ ω', quadFieldTilde r s (μ t) (X t.toNNReal ω') ∂P

section Fields

variable (R : Regime d)

/-- The commutator envelope `w = g + c_*` (TeX L6113, `N:sec:pressure`): the constant `c` with
`1 ≤ g + c` off zero, as in `HRS.perturbed_pressure`. -/
def EnvelopeConst (s c : ℝ) : Prop := ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + c

/-- Lemma 7.8 `M:U:lem:alltime-Lp` (TeX L8399-8407).  In the regime of Section 7 (fixed `β > 0`, `s < d/2`,
preparation `Q_{N,β₀}(μ°)`), with `Q_N^t = Q_{N,β}(μ^t)` and `h_N^t = df_N^t/dQ_N^t` (`f_N^t` the law of `X_N^t`):
1. there is `p_∞ > 1` with `sup_{N ≥ 2} sup_{t ≥ 0} ‖h_N^t‖_{L^{p_∞}(Q_N^t)} < ∞` (with `f_N^t ≪ Q_N^t`
   part of the conclusion, so that `h_N^t` is the genuine density);
2. for every fixed `q < ∞`, `sup_{N≥2, t≥0} ‖dQ_N^t/d(μ^t)^{⊗N}‖_{L^q((μ^t)^{⊗N})} < ∞` (`F:eq:input-product`
   on the half-line);
3. the exponential pair estimate (`N:eq:pair-exp`, `F:eq:input-pair`) is uniform on the whole trajectory: for every
   `B` there are `c_B > 0`, `C_B` with `E_{Q_N^t}[e^{c_B N|F_N^h(X_N,μ^t)|}] ≤ C_B` for all `N ≥ 2`, `t ≥ 0` and all
   symmetric measurable `h` with `|h(x,y)| ≤ B w(x-y)`.
The constants do not depend on the realisation (the laws `f_N^t` are determined by pathwise uniqueness); items 2-3
do not involve the particle system.  Technical hypotheses: `c` with `w = g + c ≥ 1` off zero (the TeX's `c_*`,
fixed once); `q`, `p_∞` are real exponents (`eLpNorm` at `ENNReal.ofReal`).

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): in item 3 the bound `|h| ≤ B w` is required only off the diagonal (`x ≠ y`), as in `moving_pair_moments`: the TeX states `|h| ≤ Bw` without a diagonal convention, `w = g + c_*` (TeX L6113) is singular at `0`, `periodicRiesz d s 0` is a junk value, and the diagonal is null for every measure involved (`modulatedEnergy` sums over `j ≠ i`).  -/
theorem alltime_Lp (c : ℝ) (hc : EnvelopeConst (d := d) R.D.s c) :
    (∃ p : ℝ, 1 < p ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → Config d N)
        (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ t : ℝ, 0 ≤ t →
          (P.map (X t.toNNReal)) ≪ modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)) ∧
          eLpNorm ((P.map (X t.toNNReal)).rnDeriv
              (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))))
            (ENNReal.ofReal p)
            (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤ ENNReal.ofReal C) ∧
    (∀ q : ℝ, 1 ≤ q → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)) ≪
          Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t)) ∧
        eLpNorm ((modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))).rnDeriv
            (Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t)))) (ENNReal.ofReal q)
          (Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t))) ≤ ENNReal.ofReal C) ∧
    (∀ B : ℝ, ∃ cB CB : ℝ, 0 < cB ∧ ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d R.D.s (x - y) + c)) →
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (cB * N *
            |modulatedEnergy h X (withDensityReal (R.ρ t))|))
          ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤
          ENNReal.ofReal CB) := by
  sorry

/-- The pair `(ζ_N^{a+·}, ℬ_N^{a+·}) ∈ C([0,T];E_r) × L²([0,T];E_r)` of the particle system. -/
def pairN (r T a : ℝ) {N : ℕ} (s : ℝ) (ρ : ℝ → Torus d → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (ω : Ω) : PathSpace d r T × L2Path d r T :=
  (zetaWin r T a P X ω,
    toL2 r T (fun t => quadFieldAt r s (fun t => withDensityReal (ρ t)) P X (a + t) ω))

/-- The pair `(η^{a+·}, ℬ^{a+·})` of the Gaussian limit. -/
def pairLim (r T a : ℝ) {Ω : Type} (η B : ℝ → Ω → NegSobolev d r) (ω : Ω) :
    PathSpace d r T × L2Path d r T :=
  (procWin r T a η ω, toL2 r T (fun t => B (a + t) ω))

/-- Proposition 7.6 `M:F:prop:field-chaos` (TeX L8199-8214).  Regime `R` (TeX L1255-1265, L7893), `r = 2d+6`,
horizon `T > 0`, particle laws `ζ_N = √N(μ_N - E μ_N)` from `Q_{N,β₀}(μ°)`, `η` the Gaussian limit
(`H:eq:linear-equation` with `q = β⁻¹` and initial covariance `H:eq:prepared-susceptibility`).  There is
`ℬ ∈ L²([0,T];E_r)` (a random element on the probability space of `η`), a.s. in `L²_tE_r`, with
`ℬ^t(φ) = ½ I_2^{𝒞_t}(h_{∇φ})` for a.e. `t` (`F:eq:Blimit`: Wick centring with the actual covariance `𝒞_t` of
`η^t`, pair kernel centred under `μ^t`), hence in the centred second Gaussian chaos of the Gaussian family generated
by `η`, such that `(ζ_N, ℬ_N) ⟹ (η, ℬ)` in `C([0,T];E_r) × L²([0,T];E_r)` (`F:eq:field-chaos`), and the convergence
holds in every Wasserstein order `1 ≤ q < ∞`.  The pair kernel `h_{∇φ}` is `hTransport`; `φ` runs over the
trigonometric basis, which determines the `E_r`-element `ℬ^t`.
Technical hypotheses: `hreal` (a realisation of the particle system for every `N ≥ 1`); the probability space
of `η` is arbitrary; `B` jointly measurable so that `ℬ ∈ L²_t` is a random element. -/
theorem field_chaos (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    ∃ B : ℝ → Ω' → NegSobolev d r, Measurable (Function.uncurry B) ∧
      (∀ᵐ ω ∂P', MemLp (fun t => B t ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) ∧
      (∀ G : PathSpace d r T × L2Path d r T → ℝ, Continuous G → (∃ M, ∀ z, |G z| ≤ M) →
        Tendsto (fun N : ℕ => ∫ ω, G (pairN r T 0 R.D.s R.ρ (P N) (X N) ω) ∂(P N)) atTop
          (𝓝 (∫ ω, G (pairLim r T 0 η B ω) ∂P'))) ∧
      (∀ q : ℝ, 1 ≤ q →
        Tendsto (fun N : ℕ => wassersteinE q (law (P N) (pairN r T 0 R.D.s R.ρ (P N) (X N)))
            (law P' (pairLim r T 0 η B))) atTop (𝓝 0)) := by
  sorry

/-- Proposition 7.9 `M:U:prop:uniform-chaos` (TeX L8476-8492).  Same regime and objects as `field_chaos`, on the
half-line.  For every Gaussian limit `η` (on any probability space) and every `R < ∞` (`Rw > 0` here) and
`1 ≤ p < ∞`:
1. `sup_{a ≥ 0} W_p(Law(ζ_N^{a+·}), Law(η^{a+·})) → 0` on `C([0,R];E_r)` (`U:eq:uniform-Wp`);
2. there is the Wick-centred quadratic Gaussian field `ℬ^t` with `ℬ^t(φ) = ½ I_2^{𝒞_t}(h_{∇φ})` (`U:eq:B-limit`,
   for a.e. `t ≥ 0`) such that the joint convergence of `(ζ_N^{a+·}, ℬ_N^{a+·})` to `(η^{a+·}, ℬ^{a+·})` holds
   uniformly in `a ≥ 0`, in `W_p` on `C([0,R];E_r) × L²([0,R];E_r)`.
The supremum over `a` is taken in `ℝ≥0∞` (no junk value).  The field `ℬ` does not depend on `R, p`.
Same technical hypotheses and `r = 2d + 6` convention as `field_chaos`. -/
theorem uniform_chaos (r : ℝ) (hr : r = 2 * (d : ℝ) + 6)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    (∀ Rw : ℝ, 0 < Rw → ∀ p : ℝ, 1 ≤ p →
      Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
          wassersteinE p (law (P N) (zetaWin r Rw a.1 (P N) (X N))) (law P' (procWin r Rw a.1 η)))
        atTop (𝓝 0)) ∧
    ∃ B : ℝ → Ω' → NegSobolev d r, Measurable (Function.uncurry B) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
        IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) ∧
      ∀ Rw : ℝ, 0 < Rw → ∀ p : ℝ, 1 ≤ p →
        (∀ a : ℝ, 0 ≤ a → ∀ᵐ ω ∂P', MemLp (fun t => B (a + t) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) Rw))) ∧
        Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
            wassersteinE p (law (P N) (pairN r Rw a.1 R.D.s R.ρ (P N) (X N)))
              (law P' (pairLim r Rw a.1 η B))) atTop (𝓝 0) := by
  sorry

/-! ### Lemma 7.12: exponential relaxation of the quadratic Gaussian field -/

/-- The noise part `G^t(φ) = Y^t(φ) - Y^0(U^{0,t}φ)` of a solution of the linear equation. -/
def noisePart (D : DynData d) (ρ : ℝ → Torus d → ℝ) {r : ℝ} {Ω : Type}
    (Y₀ : Ω → NegSobolev d r) (Y : ℝ → Ω → NegSobolev d r) (t : ℝ) (φ : Torus d → ℝ) (ω : Ω) : ℝ :=
  NegSobolev.eval (Y t ω) φ - NegSobolev.eval (Y₀ ω) (propagator D ρ 0 t φ)

/-- The covariance `2q ∫_0^{t_a∧t_b} ∫ √(ρ^v ρ'^v) ∇U^{v,t_a}φ·∇Ū^{v,t_b}ψ dx dv` of the noise parts of two linear
evolutions (mean-field densities `ρ`, `ρ'`) driven by the *same* cylindrical white noise
(`H:eq:linear-mild`, TeX L497-500; for `ρ = ρ'` this is `HRS.noiseCovariance`'s cross-covariance). -/
def crossNoiseCov (D : DynData d) (q : ℝ) (ρ ρ' : ℝ → Torus d → ℝ) (ta tb : ℝ) (φ ψ : Torus d → ℝ) : ℝ :=
  2 * q * ∫ v in Set.Icc (0 : ℝ) (min ta tb), ∫ x,
    inner ℝ (Torus.grad (propagator D ρ v ta φ) x) (Torus.grad (propagator D ρ' v tb ψ) x) *
      Real.sqrt (ρ v x * ρ' v x)

/-- `(Y, Ys)` (initial fields `Y₀`, `Ys₀`, with mean-field densities `ρ`, `ρ'`) are coupled by the same noise on
`[0,∞)`, the initial fields being independent of the noise: for finitely many smooth tests at nonnegative times the
joint vector of noise parts is centred Gaussian with the cross-covariance `crossNoiseCov` and independent of
`(Y₀,Ys₀)`.  (TeX L9124-9128: "Couple `η` and `ηs` by the same noise on `[0,∞)`".) -/
def IsSameNoise (D : DynData d) (ρ ρ' : ℝ → Torus d → ℝ) (r : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (Y₀ Ys₀ : Ω → NegSobolev d r) (Y Ys : ℝ → Ω → NegSobolev d r) : Prop :=
  ∀ (p p' : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (ts' : Fin p' → ℝ) (ψ : Fin p' → Torus d → ℝ),
    (∀ a, 0 ≤ ts a) → (∀ b, 0 ≤ ts' b) → (∀ a, Torus.IsSmooth (φ a)) → (∀ b, Torus.IsSmooth (ψ b)) →
    let G : Ω → EuclideanSpace ℝ (Fin p ⊕ Fin p') := fun ω => WithLp.toLp 2 (Sum.elim
      (fun a => noisePart D ρ Y₀ Y (ts a) (φ a) ω) (fun b => noisePart D ρ' Ys₀ Ys (ts' b) (ψ b) ω))
    IndepFun (fun ω => (Y₀ ω, Ys₀ ω)) G P ∧
    law P G = multivariateGaussian 0 (Matrix.of fun i j => match i, j with
      | Sum.inl a, Sum.inl b => crossNoiseCov D D.invβ ρ ρ (ts a) (ts b) (φ a) (φ b)
      | Sum.inl a, Sum.inr b => crossNoiseCov D D.invβ ρ ρ' (ts a) (ts' b) (φ a) (ψ b)
      | Sum.inr a, Sum.inl b => crossNoiseCov D D.invβ ρ' ρ (ts' a) (ts b) (ψ a) (φ b)
      | Sum.inr a, Sum.inr b => crossNoiseCov D D.invβ ρ' ρ' (ts' a) (ts' b) (ψ a) (ψ b))

/-- Lemma 7.12 `M:U:lem:quadratic-relaxation` (TeX L9142-9150).  Regime `R`, `r = 2d+6`.  (Notation: `ηs`, `Ys`, `Bs`, `ℬs` stand for the TeX bars `η̄`, `Ȳ`, `B̄`, `ℬ̄`.)  Let `ηs` be the
stationary Gaussian field (equilibrium evolution, mean-field density `ρ_β`, centred Gaussian initial field of
covariance `C_β`, `U:eq:stationary-covariance`), `η` the Gaussian limit of the prepared system
(`ρ`, initial covariance `H:eq:prepared-susceptibility`), coupled by the same noise on `[0,∞)` with independent
initial fields (TeX L9124-9128), and `ℬ^t`, `ℬs^t` the Wick-centred quadratic fields constructed from `η^t`
(centred under `μ^t = ρ^t dx`) and from `ηs^t` (centred under `μ_β`) with the same commutator kernel `h_{∇φ}`.
Then for every finite `p ≥ 1` there are `C_p`, `c > 0` (independent of `t` and of the coupling) with
`‖ℬ^t - ℬs^t‖_{L^p(E_r)} ≤ C_p e^{-ct}`, `t ≥ 0`.
AMBIGUITY (TeX L9142-9145): the lemma does not say under which measure the stationary pair kernel is centred;
`μ_β` (the law of the stationary background) is used, in analogy with `μ^t` for `ℬ^t`.  The coupling is the one
of the preceding paragraph (L9124-9128), the lemma statement itself does not repeat it.
The initial fields are independent (`IndepFun Y₀ Ys₀`, TeX L9119: "their initial fields may be coupled independently").
Technical hypotheses: `ℬ^t`, `ℬs^t` are measurable `E_r`-valued random variables for each `t`. -/
theorem quadratic_relaxation (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∀ p : ℝ, 1 ≤ p → ∃ C c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r),
        IsCenteredGaussianWithCov r (P.map Y₀)
          (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) →
        IsCenteredGaussianWithCov r (P.map Ys₀)
          (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) →
        IndepFun Y₀ Ys₀ P →
        (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ r R.D.invβ T Y₀ η) →
        (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) r R.D.invβ T Ys₀ ηs) →
        IsSameNoise R.D R.ρ (fun _ => R.ρβ) r P Y₀ Ys₀ η ηs →
        ∀ B Bs : ℝ → Ω → NegSobolev d r,
          (∀ t, Measurable (B t)) → (∀ t, Measurable (Bs t)) →
          (∀ t : ℝ, 0 ≤ t → IsWickQuadraticField R.D.s P (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) →
          (∀ t : ℝ, 0 ≤ t → IsWickQuadraticField R.D.s P (fun ω => ηs t ω) (withDensityReal R.ρβ) (Bs t)) →
          ∀ t : ℝ, 0 ≤ t →
            eLpNorm (fun ω => B t ω - Bs t ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C * Real.exp (-c * t)) := by
  sorry

/-! ### Remark 7.10 and Proposition 7.11: Riemann--Stieltjes integrals against vector measures -/

/-- `S` has Riemann--Stieltjes integral `I` over `[0,T]`: for every `ε > 0` there is `δ > 0` such that every tagged
partition `0 = u_0 < ⋯ < u_n = T` with tags `τ_i ∈ [u_i,u_{i+1}]` and mesh `< δ` satisfies
`|∑_i S(τ_i, u_i, u_{i+1}) - I| < ε`.  Here `S(τ, a, b)` stands for "integrand at the tag `τ` applied to the
measure of the interval `(a,b]`" (`F:sec:measures`, TeX L8699-8705: "integration ... is defined by
Riemann--Stieltjes sums"). -/
def IsRS (T : ℝ) (S : ℝ → ℝ → ℝ → ℝ) (I : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ), StrictMono u →
    u 0 = 0 → u (Fin.last n) = T → (∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ) →
    (∀ i : Fin n, u i.succ - u i.castSucc < δ) →
    |∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ) - I| < ε

/-- The spatial Fourier projection `Π_L` on `E_m` (frequencies `|k_i| ≤ L` for all `i`). -/
def fourierProj (m : ℝ) (L : ℕ) (F : NegSobolev d m) : NegSobolev d m :=
  NegSobolev.ofSeq m fun k => if ∀ i, |k.1 i| ≤ (L : ℤ) then NegSobolev.fourierCoeff F k else 0

/-- The projection `P_L` of Remark 7.10 (TeX L8682-8685): spatial Fourier projection followed by polygonal
interpolation at the dyadic time grid `t_i = iT/2^L` (a refining grid): `(P_L w)(t) = ∑_i hat_i(t) Π_L w(t_i)`. -/
def projPoly (m T : ℝ) (hT : 0 ≤ T) (L : ℕ) (w : PathSpace d m T) : PathSpace d m T :=
  show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from
    ⟨fun t => ∑ i ∈ Finset.range (2 ^ L + 1),
      max 0 (1 - |(t : ℝ) * 2 ^ L / T - i|) •
        fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT (i * T / 2 ^ L))), by fun_prop⟩

/-- The action `P^{⊗j}` of a bounded operator `P` on the dual `TensorDual B j` of the bounded `j`-linear forms
(which carries the projective tensor power `B^{⊗̂π j}`, `HRS.projTensor`): `(P^{⊗j}u)(M) = u(M∘(P,…,P))`. -/
def tensorPow {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] (j : ℕ) (P : B →L[ℝ] B) :
    TensorDual B j →L[ℝ] TensorDual B j :=
  (ContinuousLinearMap.precomp ℝ (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := ℝ) (fun _ : Fin j => P)))

/-- Remark 7.10 `M:F:rem:projection` (TeX L8682-8698), the assertions with mathematical content.  (The sentence
"these facts do *not* imply `‖P_Lν-ν‖_var → 0`" is a non-implication and is not formalised.)
For `T > 0`, `m ∈ ℝ`: the maps `P_L` (`projPoly`) are bounded linear contractions of `𝒳 = C([0,T];E_m)`, i.e. there
are continuous linear `Pj L` with `Pj L w = projPoly .. w` and `‖Pj L‖ ≤ 1`; `P_L w → w` for every continuous
path `w`; and `P_L^{⊗j} v → v` in `TensorDual 𝒳 j` for every `v` in the projective tensor power `projTensor 𝒳 j`
and every fixed `j`.  Technical hypotheses: none beyond `T > 0`. -/
theorem projection_strong (m T : ℝ) (hT : 0 < T) :
    ∃ Pj : ℕ → (PathSpace d m T →L[ℝ] PathSpace d m T),
      (∀ L w, Pj L w = projPoly m T hT.le L w) ∧ (∀ L, ‖Pj L‖ ≤ 1) ∧
      (∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w)) ∧
      ∀ (j : ℕ) (v : TensorDual (PathSpace d m T) j), v ∈ projTensor (PathSpace d m T) j →
        Tendsto (fun L => tensorPow j (Pj L) v) atTop (𝓝 v) := by
  sorry

/-- Remark 7.10 `M:F:rem:projection` (TeX L8686-8698), equation `F:eq:measure-projection`, in the abstract form of
its proof.  `E` is a Banach space (in the TeX `E = 𝒳^{⊗̂j}`, projective tensor power, with `Pj L = P_L^{⊗j}`;
`‖P_L^{⊗j}‖ ≤ 1` and `P_L^{⊗j}v → v` by `projection_strong`); `Pj L` are uniformly bounded operators converging
strongly to the identity; `ν` is a vector measure of bounded variation given by its cumulative path `F : [0,T] → E`
(`F 0 = 0`, `BoundedVariationOn`); `A_L(u)`, `A(u)` are continuous (in operator norm) families of bounded linear
functionals ("operators `A(u)`" acting on the tensor; `A_L → A` uniformly, `A_L = A` for the first assertion).
Then `∫ A(u) d(P_L ν)(u)` (the Riemann--Stieltjes integral of `A_L` against the cumulative path `P_L F`) converges to
`∫ A(u) dν(u)`.  Existence of the Riemann--Stieltjes integrals is part of the conclusion. -/
theorem measure_projection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Pj : ℕ → (E →L[ℝ] E)) (K : ℝ) (hK : ∀ L, ‖Pj L‖ ≤ K)
    (hconv : ∀ e, Tendsto (fun L => Pj L e) atTop (𝓝 e))
    (T : ℝ) (hT : 0 < T) (F : ℝ → E) (hF : BoundedVariationOn F (Set.Icc 0 T)) (hF0 : F 0 = 0)
    (A : ℝ → (E →L[ℝ] ℝ)) (AL : ℕ → ℝ → (E →L[ℝ] ℝ))
    (hA : ContinuousOn A (Set.Icc 0 T)) (hAL : ∀ L, ContinuousOn (AL L) (Set.Icc 0 T))
    (hAu : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ u ∈ Set.Icc (0 : ℝ) T, ‖AL L u - A u‖ ≤ ε) :
    ∃ I : ℝ, IsRS T (fun τ a b => A τ (F b - F a)) I ∧
      ∃ IL : ℕ → ℝ, (∀ L, IsRS T (fun τ a b => AL L τ (Pj L (F b - F a))) (IL L)) ∧
        Tendsto IL atTop (𝓝 I) := by
  sorry

/-- `V^{t,u}` acting on `E_m`: `⟨e_k, V^{t,u}F⟩ = F(U^{u,t}e_k)` on the real trigonometric basis (zero mode
dropped: the adjoint is projected modulo constants, TeX L8362-8363), with `U` the project's `propagator`. -/
def Vprop (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m : ℝ) (t u : ℝ) (F : NegSobolev d m) :
    NegSobolev d m :=
  NegSobolev.ofSeq m fun k => NegSobolev.eval F (propagator D ρ u t (Torus.realMode k))

open Classical in
/-- The element of `𝒳_{m,T}` given by a path `g : ℝ → E_m` (`0` if `g` is not continuous on `[0,T]`). -/
def pathOf (m T : ℝ) (g : ℝ → NegSobolev d m) : PathSpace d m T :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T => g t then
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from ⟨_, h⟩)
  else 0

/-- The value `w(t)` of a path at a real time `t` (`0` outside `[0,T]`). -/
def pathAt {m T : ℝ} (w : PathSpace d m T) (t : ℝ) : NegSobolev d m :=
  if h : t ∈ Set.Icc (0 : ℝ) T then PathSpace.at' w ⟨t, h⟩ else 0

/-- The initial propagation `(𝖨z)(t) = V^{t,0}z` (`F:sec:path-identity`, TeX L8702). -/
def initProp (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (z : NegSobolev d m) : PathSpace d m T :=
  pathOf m T fun t => Vprop D ρ m t 0 z

/-- The predicted continuation `(𝖳_u w)(t) = w(t)` for `t ≤ u`, `V^{t,u}w(u)` for `t > u`
(`F:eq:predicted`, TeX L8705-8710). -/
def predicted (D : DynData d) (ρ : ℝ → Torus d → ℝ) {m T : ℝ} (w : PathSpace d m T) (u : ℝ) :
    PathSpace d m T :=
  pathOf m T fun t => if t ≤ u then pathAt w t else Vprop D ρ m t u (pathAt w u)

/-- The increment `𝒟_b((a,a'])` of the drift measure (`F:eq:Dmeasure`, TeX L8725):
`t ↦ ∫_{(a,a'] ∩ [0,t]} V^{t,u} b(u) du`. -/
def driftInc (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (b : ℝ → NegSobolev d m) (a a' : ℝ) :
    PathSpace d m T :=
  pathOf m T fun t => ∫ u in Set.Ioc a (min a' t), Vprop D ρ m t u (b u)

/-- `γ` is (the law of) the Gaussian future path `Γ_u` (`F:eq:future`, TeX L8737-8741): a centred Gaussian measure
on `𝒳_{m,T}` with
`E[Γ_u(t_a)(φ_a)Γ_u(t_b)(φ_b)] = 2β⁻¹ ∫_u^{t_a∧t_b} μ^v(∇U^{v,t_a}φ_a·∇U^{v,t_b}φ_b) dv` for smooth tests
(`= 0` if `t_a∧t_b ≤ u`). -/
def IsFutureGaussian (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T u : ℝ) (γ : Measure (PathSpace d m T)) :
    Prop :=
  IsCenteredGaussian γ ∧ ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ), Torus.IsSmooth φa → Torus.IsSmooth φb →
    ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
    ∫ z, NegSobolev.eval (pathAt z ta) φa * NegSobolev.eval (pathAt z tb) φb ∂γ =
      2 * D.invβ * ∫ v in Set.Icc u (min ta tb), ∫ x,
        inner ℝ (Torus.grad (propagator D ρ v ta φa) x) (Torus.grad (propagator D ρ v tb φb) x) * ρ v x

/-- `u_Φ(u,y) = E[Φ(y + Γ_u)]` (`F:eq:heat-u`, TeX L8751). -/
def heatFn {m T : ℝ} (γ : ℝ → Measure (PathSpace d m T)) (Φ : PathSpace d m T → ℝ) (u : ℝ)
    (y : PathSpace d m T) : ℝ :=
  ∫ z, Φ (y + z) ∂(γ u)

/-- The value `𝒥_z(I)` of the covariance measure on the interval `I` (`F:eq:Jmeasure`, `F:eq:Jevaluation`, TeX
L8660-8680): an element `J` of the projective tensor square `𝒳 ⊗̂ 𝒳` (`projTensor`, in `TensorDual 𝒳 2`) whose
values on the products of evaluation functionals `ℓ_1 ⊗ ℓ_2`, `ℓ_i(w) = w(t_i)(φ_i)`, are
`2β⁻¹ ∫_{I∩[0,t_a∧t_b]} z^u(∇U^{u,t_a}φ_a·∇U^{u,t_b}φ_b) du` (`z^u` paired with the smooth function).
"These evaluations determine the tensor" (TeX L8680). -/
def IsJValue (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (z : ℝ → NegSobolev d m) (I : Set ℝ)
    (J : TensorDual (PathSpace d m T) 2) : Prop :=
  J ∈ projTensor (PathSpace d m T) 2 ∧
  ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
    Torus.IsSmooth φa → Torus.IsSmooth φb → ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
    (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
    J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
      2 * D.invβ * ∫ u in I ∩ Set.Icc (0 : ℝ) (min ta tb), NegSobolev.eval (z u)
        (fun x => inner ℝ (Torus.grad (propagator D ρ u ta φa) x) (Torus.grad (propagator D ρ u tb φb) x))

open Classical in
/-- The pairing `⟨M, 𝒥_z(I)⟩` of a bounded bilinear form `M` with the tensor `𝒥_z(I)` (`0` if the tensor does not
exist, which the TeX excludes). -/
def jPair (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (z : ℝ → NegSobolev d m) (I : Set ℝ)
    (M : PathSpace d m T [×2]→L[ℝ] ℝ) : ℝ :=
  if h : ∃ J, IsJValue D ρ m T z I J then h.choose M else 0

/-- Proposition 7.11 `M:F:prop:path-Ito` (TeX L8753-8764).  Regime `R`, `m > 3d + 8`, `T > 0`, `𝒳 = 𝒳_{m,T}`,
`N ≥ 1`, a realisation of the particle system from `Q_{N,β₀}(μ°)`, `γ_u` the law of the Gaussian future path
`Γ_u`, `Φ ∈ C_b^5(𝒳)`.  Then there are random variables `A_N`, `J_N` (the Riemann--Stieltjes integrals), integrable,
with a.s.
`A_N = ∫_0^T Du_Φ(u,Y_N^u) d𝒟_{ℬ_N}(u)`, `J_N = ∫_0^T ⟨D²u_Φ(u,Y_N^u), d𝒥_{η_N}(u)⟩` (limits of the sums
`∑_i Du_Φ(τ_i,Y_N^{τ_i})[𝒟_{ℬ_N}((u_i,u_{i+1}])]` and
`∑_i ⟨D²u_Φ(τ_i,Y_N^{τ_i}), 𝒥_{η_N}((u_i,u_{i+1}])⟩`), and
`E[Φ(ζ_N)] = E[u_Φ(0,𝖨ζ_N^0)] - N^{-1/2} E[A_N] + (1/2) N^{-1/2} E[J_N]` (`F:eq:path-Ito`), where
`Y_N^u = 𝖳_u ζ_N`, `ℬ_N`, `η_N = √N(μ_N - μ)` are the particle fields.
The Riemann--Stieltjes integrals are those of TeX L8764 ("not applications of derivatives to discontinuous
impulse paths"), defined by the sums above.
REPRESENTATION: `ζ_N ∈ C([0,T];E_m)` is taken directly in `E_m` (`ζ_N ∈ C([0,T];E_r) ↪ 𝒳`, same Fourier
coefficients); `𝒟_b(I)` is the explicit path `driftInc`, `𝒥_z(I)` the tensor characterised by its evaluations on
products of evaluation functionals (`IsJValue`), `Γ_u` through its law (`IsFutureGaussian`, hypothesis `hγ`, whose
existence is the TeX's construction L8737-8741).  Technical hypotheses: `hreal`; `hγ`. -/
theorem path_Ito (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T))
    (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    (N : ℕ) (hN : 1 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) :
    ∃ A J : Ω → ℝ, Integrable A P ∧ Integrable J P ∧
      (∀ᵐ ω ∂P, IsRS T (fun τ a b =>
        fderiv ℝ (heatFn γ Φ τ) (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ)
          (driftInc R.D R.ρ m T
            (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω) a b)) (A ω)) ∧
      (∀ᵐ ω ∂P, IsRS T (fun τ a b =>
        jPair R.D R.ρ m T (fun u => etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u))) (Set.Ioc a b)
          (iteratedFDeriv ℝ 2 (heatFn γ Φ τ) (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ))) (J ω)) ∧
      ∫ ω, Φ (zetaWin m T 0 P X ω) ∂P =
        ∫ ω, heatFn γ Φ 0 (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) ∂P -
          (Real.sqrt N)⁻¹ * ∫ ω, A ω ∂P + (1 / (2 * Real.sqrt N)) * ∫ ω, J ω ∂P := by
  sorry

end Fields

end Sec7

end HRS

end
