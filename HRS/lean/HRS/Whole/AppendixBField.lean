import HRS.Whole.Adjoint
import HRS.Whole.SobolevDual
import HRS.Dynamics.Setup
import HRS.Prob.Metrics

/-!
# Appendix S.B (whole-space supplement): the transported initial field for i.i.d. data and the
whole-space limit field (SPEC-WB)

Source: HRS whole-space supplement (S), Appendix S.B:

* S.B.2 `B:lem:iid-init-field-rd` (S L11169-11192): `iid_init_field_rd`, `iid_init_field_rd_multitime`;
* S.B.3 `B:rem:iid-init-field-rd` (S L11303-11305): **no_formal_content** (a remark that says what the
  lemma does *not* provide: no quantitative coupling in `W^{-m,p'}` nor of the whole path in
  `C([0,T];H^{-Γ})`, "not pursued here"; it asserts nothing mathematical);
* S.B.7 `B:prop:limit-field` (S L11465-11496): `limit_field_rd_gaussian` (item (ii)),
  `limit_field_rd_duality` (item (iii), first part), `limit_field_rd_weak_form` (item (iii), the weak
  equation `B:eq:spde-weak`).  Item (i) (the torus) is Proposition A.33 of the main paper and is the
  existing statement `HRS.Main.periodic_limit_field` (SPEC-A, branch `wk/specA`), which is not re-stated
  (S.B.7(i) *is* that torus statement).  Uniqueness in S.B.7 (iii) is uniqueness *in law*: the pathwise
  uniqueness of S L11500 needs the cylindrical Wiener process `W^ξ`, which is not represented.

## Representation decisions

* `H = H^{-Γ}(ℝ^d)` is `HRS.Whole.HNeg d Γ` (`HRS/Whole/SobolevDual.lean`), the duality pairing
  `⟨φ, F⟩_{H^Γ,H^{-Γ}}` is `HNeg.pairing`; terminal tests are the smooth functions of `H^Γ`
  (`IsSobolevTest`), because the classical adjoint solution has terminal datum a function.
* The *selected adjoint density* `(𝒳, Γ)` (S.A.6) is represented by its index `Γ` and the uniform
  adjoint input `AdjointFieldInput` (the estimate `H^Γ → C_b^1` of `U_N^{0,t}`, S L11213-11217): the
  constants of the selected density are the constant `K` of that estimate.  The S.A theorem bundles are
  not defined here.
* The transported fields `𝓘_{N,emp}^t, 𝓘_N^t` (`B:eq:transported-initial-rd`) are *random elements of
  `H` representing the functionals* `φ ↦ A_N⟨U_N^{0,t}φ, κ_N Fluc_N^0⟩`, `φ ↦ A_N⟨U_N^{0,t}φ, η°⟩`
  on the test class (the TeX says "these functionals extend to `H^{-Γ}`-valued random variables"):
  the statements are for *every* such representative, and existence is part of the conclusion
  (`W_1` and the moment bound depend only on the laws, which are determined by the representation).
* `η°` (the Gaussian bridge of `B:ex:iid`) is a random linear functional on `C_b^1` test functions with
  Gaussian finite-dimensional laws of covariance `μ°(ψφ) - μ°(ψ)μ°(φ)` (`IsGaussianBridgeW`), as the
  random functional `η₀` of `HRS/Whole/Dynamics.lean`.
* `A_N = σ_N/κ_N` with `κ_N = √N` and `β_N⁻¹ = invβ N ≥ 0` is `HRS.Ascale` (`≤ 1`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### Definitions -/

/-- The covariance `μ(ψφ) - μ(ψ)μ(φ)` of the Gaussian bridge (`B:ex:iid`, M L10469-10475). -/
def iidCovW (μ : Measure (Euc d)) (ψ φ : Euc d → ℝ) : ℝ :=
  pair μ (fun x => ψ x * φ x) - pair μ ψ * pair μ φ

/-- `η°` is a centered Gaussian field on `C_b^1` test functions with covariance `iidCovW μ°`
(`B:ex:iid`): every `η°(ψ)` is a random variable and every finite family is jointly centered Gaussian
with covariance matrix `(μ°(ψ_aψ_b) - μ°(ψ_a)μ°(ψ_b))_{ab}`. -/
def IsGaussianBridgeW {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Measure (Euc d))
    (η : Ω → (Euc d → ℝ) → ℝ) : Prop :=
  (∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ) ∧
  ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
    law P (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b))

/-- The amplitude `A_N = σ_N/κ_N` for `κ_N = √N`, `β_N⁻¹ = invβ` (`H:eq:intro-scales`). -/
def fieldAmp (N : ℕ) (invβ : ℝ) : ℝ := Ascale N (Real.sqrt N) invβ

/-- The adjoint input of the selected field density `(𝒳, Γ)` for one coefficient `C` (S L11213-11217,
the estimates "`H^Γ → C_b^0`" and "`H^Γ → C_b^1`" for `U^{0,t}`) on `[0,T]`: for every `t ∈ [0,T]` and
every smooth `φ ∈ H^Γ` the classical adjoint solution with terminal datum `φ` exists, `φ ↦ U^{r,t}φ`
is linear on the test class (`propagatorW` is a `choose`; the classical adjoint solution is unique, and
this linearity is that uniqueness), and `‖U^{0,t}φ‖_{C_b^1} ≤ K ‖φ‖_{H^Γ}` (the project's SUM convention
of `C_b^1`, `HRS.cbNorm`). -/
def AdjointInputOne (Γ : ℝ) (C : WholeCoeff d) (T K : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T,
    (∀ φ : Euc d → ℝ, IsSobolevTest Γ φ → ∃ f, IsClassicalAdjointW C t φ f) ∧
    (∀ φ₁ φ₂ : Euc d → ℝ, IsSobolevTest Γ φ₁ → IsSobolevTest Γ φ₂ → ∀ c : ℝ,
      ∀ r ∈ Set.Icc (0 : ℝ) t,
        propagatorW C r t (φ₁ + c • φ₂) = propagatorW C r t φ₁ + c • propagatorW C r t φ₂) ∧
    ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ →
      MemCb 1 (propagatorW C 0 t φ) ∧ cbNorm 1 (propagatorW C 0 t φ) ≤ K * sobolevNorm Γ φ

/-- The uniform adjoint input of the selected field density for the family `(Cf N)_{N ≥ 1}`:
`AdjointInputOne` for every `N ≥ 1`, with `K` independent of `N` and `t`. -/
def AdjointFieldInput (Γ : ℝ) (Cf : ℕ → WholeCoeff d) (T K : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → AdjointInputOne Γ (Cf N) T K

/-! ### S.B.2 -/

/-- Lemma S.B.2 (`B:lem:iid-init-field-rd`, TeX S L11169-11192).  Let `𝔻 = ℝ^d`,
`x_1°,…,x_N°` i.i.d. with law `μ°` (`law X = (μ°)^{⊗N}`), `m_2° = ∫|x|²dμ° < ∞`, `κ_N = √N`, `η°` the
centered Gaussian bridge of `B:ex:iid`, `(𝒳, Γ)` a selected whole-space field density (index `Γ` and
adjoint input `AdjointFieldInput`), `H = H^{-Γ}(ℝ^d)`, and `𝓘_{N,emp}^t, 𝓘_N^t` the `H`-valued
representatives of `φ ↦ A_N⟨U_N^{0,t}φ, κ_N Fluc_N^0⟩ = A_N √N (μ_N^0(U_N^{0,t}φ) - μ°(U_N^{0,t}φ))`
and `φ ↦ A_N⟨U_N^{0,t}φ, η°⟩` (`B:eq:transported-initial-rd`).  Then
* (existence) the functionals extend to `H`-valued random variables (a measurable map of the
  configuration, resp. of `η°`);
* for `N ≥ 3` and `0 ≤ t ≤ T` (`B:eq:iid-init-field-rd`):
  `W_1(Law 𝓘_{N,emp}^t, Law 𝓘_N^t) ≤ C A_N N^{-1/(4d+10)} (log N)^{1/(2d+5)}`, and, as `d_{C²} ≤ W_1`
  (the TeX's "consequently `B:ass:init-field`(F-rd) holds with `ε_N^f = C A_N N^{-1/(4d+10)}
  (log N)^{1/(2d+5)}`"), the same bound for `d_{C²}`;
* for all `N ≥ 1` (`B:eq:iid-init-field-rd-moment`): `E‖𝓘_{N,emp}^t‖²_H + E‖𝓘_N^t‖²_H ≤ C`
  (in `ℝ≥0∞`, so finiteness is part of the claim).
`C` depends only on the constants of the selected adjoint density (`d`, `Γ`, `K`), `T` and `m_2°`
(`m₂ ≥ ∫|x|²dμ°`), as in the TeX; it is quantified before `(Cf, invβ, μ°, N, t, …)`.  The statement
holds for all bridges `η°` and all representatives (any probability spaces).
Technical hypotheses: `Measurable` of the configuration and of the representatives (so that `law` is
the true law); `IsProbabilityMeasure μ°`, `Integrable |x|²` (so that `∫|x|² ≤ m₂` is not a junk-value
statement); `1 ≤ d`; `0 ≤ invβ N` (`β_N ∈ (0,∞]`). -/
theorem iid_init_field_rd (hd : 1 ≤ d) (Γ : ℕ) (T K m₂ : ℝ) :
    ∃ C : ℝ, ∀ (Cf : ℕ → WholeCoeff d) (invβ : ℕ → ℝ), (∀ N, 0 ≤ invβ N) →
      AdjointFieldInput (Γ : ℝ) Cf T K →
      ∀ μ : Measure (Euc d), IsProbabilityMeasure μ → Integrable (fun x => ‖x‖ ^ 2) μ →
        ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂ →
      ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
        (∃ Iemp : EucConfig d N → HNeg d (Γ : ℝ), Measurable Iemp ∧
          ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ X : EucConfig d N,
            HNeg.pairing φ (Iemp X) = fieldAmp N (invβ N) * Real.sqrt N *
              (pair (empirical X) (propagatorW (Cf N) 0 t φ) -
                pair μ (propagatorW (Cf N) 0 t φ))) ∧
        (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (η : Ω' → (Euc d → ℝ) → ℝ), IsGaussianBridgeW P' μ η →
          ∃ I : Ω' → HNeg d (Γ : ℝ), Measurable I ∧
            ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
              ∀ᵐ ζ ∂P', HNeg.pairing φ (I ζ) =
                fieldAmp N (invβ N) * η ζ (propagatorW (Cf N) 0 t φ)) ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X : Ω → EucConfig d N), Measurable X → law P X = Measure.pi (fun _ => μ) →
        ∀ (Iemp : Ω → HNeg d (Γ : ℝ)), Measurable Iemp →
          (∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂P,
            HNeg.pairing φ (Iemp ζ) = fieldAmp N (invβ N) * Real.sqrt N *
              (pair (empirical (X ζ)) (propagatorW (Cf N) 0 t φ) -
                pair μ (propagatorW (Cf N) 0 t φ))) →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (η : Ω' → (Euc d → ℝ) → ℝ), IsGaussianBridgeW P' μ η →
        ∀ (I : Ω' → HNeg d (Γ : ℝ)), Measurable I →
          (∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂P',
            HNeg.pairing φ (I ζ) = fieldAmp N (invβ N) * η ζ (propagatorW (Cf N) 0 t φ)) →
          (3 ≤ N →
            wassersteinE 1 (law P Iemp) (law P' I) ≤
              ENNReal.ofReal (C * fieldAmp N (invβ N) *
                (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
                  Real.log N ^ (1 / (2 * (d : ℝ) + 5))) ∧
            smoothDist 2 (law P Iemp) (law P' I) ≤
              C * fieldAmp N (invβ N) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
                Real.log N ^ (1 / (2 * (d : ℝ) + 5))) ∧
          ∫⁻ ζ, ‖Iemp ζ‖ₑ ^ 2 ∂P + ∫⁻ ζ, ‖I ζ‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal C := by
  sorry

/-- Lemma S.B.2 (`B:lem:iid-init-field-rd`, TeX S L11190-11191): "the same conclusion holds for any
fixed finite collection of times, with values in the corresponding finite Hilbert direct sum": for
`p` times `t_1,…,t_p ∈ [0,T]` and the `ℓ²`-direct sum `H^p = PiLp 2 (fun _ => H)`, the `W_1` and
`d_{C²}` bounds (for `N ≥ 3`) and the moment bound (for `N ≥ 1`) hold with a constant `C` depending in
addition on `p`.  Representatives of the vector of transported fields are `H^p`-valued maps whose
`a`-th component represents the functional at time `t_a`. -/
theorem iid_init_field_rd_multitime (hd : 1 ≤ d) (Γ : ℕ) (T K m₂ : ℝ) (p : ℕ) :
    ∃ C : ℝ, ∀ (Cf : ℕ → WholeCoeff d) (invβ : ℕ → ℝ), (∀ N, 0 ≤ invβ N) →
      AdjointFieldInput (Γ : ℝ) Cf T K →
      ∀ μ : Measure (Euc d), IsProbabilityMeasure μ → Integrable (fun x => ‖x‖ ^ 2) μ →
        ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂ →
      ∀ N : ℕ, 1 ≤ N → ∀ ts : Fin p → ℝ, (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X : Ω → EucConfig d N), Measurable X → law P X = Measure.pi (fun _ => μ) →
        ∀ (Iemp : Ω → PiLp 2 (fun _ : Fin p => HNeg d (Γ : ℝ))), Measurable Iemp →
          (∀ a : Fin p, ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂P,
            HNeg.pairing φ (Iemp ζ a) = fieldAmp N (invβ N) * Real.sqrt N *
              (pair (empirical (X ζ)) (propagatorW (Cf N) 0 (ts a) φ) -
                pair μ (propagatorW (Cf N) 0 (ts a) φ))) →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (η : Ω' → (Euc d → ℝ) → ℝ), IsGaussianBridgeW P' μ η →
        ∀ (I : Ω' → PiLp 2 (fun _ : Fin p => HNeg d (Γ : ℝ))), Measurable I →
          (∀ a : Fin p, ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂P',
            HNeg.pairing φ (I ζ a) =
              fieldAmp N (invβ N) * η ζ (propagatorW (Cf N) 0 (ts a) φ)) →
          (3 ≤ N →
            wassersteinE 1 (law P Iemp) (law P' I) ≤
              ENNReal.ofReal (C * fieldAmp N (invβ N) *
                (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
                  Real.log N ^ (1 / (2 * (d : ℝ) + 5))) ∧
            smoothDist 2 (law P Iemp) (law P' I) ≤
              C * fieldAmp N (invβ N) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
                Real.log N ^ (1 / (2 * (d : ℝ) + 5))) ∧
          ∫⁻ ζ, ‖Iemp ζ‖ₑ ^ 2 ∂P + ∫⁻ ζ, ‖I ζ‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal C := by
  sorry

/-! ### S.B.7: the whole-space limit field -/

/-- The intrinsic kernels `K_{N,j}^{r,t}(x) ∈ H^{-Γ}` of Lemma S.A.20 `B:lem:adjoint-field-kernel`
(S L10562-10581), for the coefficients `C` on `[0,T]`: `⟨φ, K_j^{r,t}(x)⟩_{H^Γ,H^{-Γ}} = ∂_j U^{r,t}φ(x)`
for `φ ∈ H^Γ` (here: smooth tests), strong measurability in `(r,t,x)` and the uniform bound
`‖K_j^{r,t}(x)‖_{H^{-Γ}} ≤ B` (the case `α = 0` of `B:eq:intrinsic-kernel-bound`).  The existence and
uniqueness of `K` is S.A.20 (not stated here): this predicate is its conclusion. -/
structure IsIntrinsicKernel (Γ : ℝ) (C : WholeCoeff d) (T B : ℝ)
    (Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ) : Prop where
  represent : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ (x : Euc d) (j : Fin d) (φ : Euc d → ℝ),
    IsSobolevTest Γ φ → HNeg.pairing φ (Kern r t x j) = gradient (propagatorW C r t φ) x j
  measurable : ∀ j : Fin d, Measurable fun p : ℝ × ℝ × Euc d => Kern p.1 p.2.1 p.2.2 j
  bound : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ (x : Euc d) (j : Fin d), ‖Kern r t x j‖ ≤ B

/-- Proposition S.B.7(ii) (`B:prop:limit-field`, TeX S L11474-11485): on `ℝ^d`, for the selected field
density (index `Γ`), coefficients `C` (the density `μ^r = C.ρ r dx`, probability densities) and noise
level `q = σ_N²/(Nβ_N) ≥ 0`, the intrinsic kernels define the positive trace-class covariance
`Q_N^t = 2q ∫_0^t ∫ ∑_j K_j^{r,t}(x) ⊗ K_j^{r,t}(x) dμ^r(x) dr` and the centered Gaussian
`G_N^t ~ N(0, Q_N^t)` is an `H^{-Γ}`-valued random variable with covariance `B:eq:surrogate-cov` on
`H^Γ`, realized on an extension independent of the initial `σ`-field `𝓕_0^{in}`.  Formally: there is a
centered Gaussian probability measure `ν` on `H` with (a) `E‖G‖² = Tr Q_N^t = 2q ∫_0^t ∫ ∑_j ‖K_j‖² dμ^r dr`
`≤ 2 q d t B²` (positive trace class with uniformly bounded trace), (b) `E⟨φ,G⟩⟨ψ,G⟩` equals both the
kernel form of `Q_N^t` and `noiseCovW C q t t φ ψ = 2q ∫_0^t ⟨∇U^{r,t}φ·∇U^{r,t}ψ, μ^r⟩ dr` for
smooth `φ, ψ ∈ H^Γ`, (c) for every probability space carrying any random element `Y` (the generator of
`𝓕_0^{in}`) there is an extension on which a random element `G` of law `ν` is independent of `Y`.
The hypotheses are the whole-space field theorem's (`B:thm:main-rd-field`, represented by the intrinsic
kernel input) and `0 ≤ t ≤ T`. -/
theorem limit_field_rd_gaussian (Γ : ℝ) (C : WholeCoeff d) (q T B : ℝ) (hq : 0 ≤ q)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (C.ρ r)) (hρm : Measurable (Function.uncurry C.ρ))
    (Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ) (hK : IsIntrinsicKernel Γ C T B Kern)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ ν : Measure (HNeg d Γ), IsProbabilityMeasure ν ∧ IsCenteredGaussian ν ∧
      ∫⁻ x, ‖x‖ₑ ^ 2 ∂ν =
        ENNReal.ofReal (2 * q * ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ∑ j, ‖Kern r t x j‖ ^ 2 * C.ρ r x) ∧
      ∫⁻ x, ‖x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (2 * q * d * t * B ^ 2) ∧
      (∀ φ ψ : Euc d → ℝ, IsSobolevTest Γ φ → IsSobolevTest Γ ψ →
        ∫ x, HNeg.pairing φ x * HNeg.pairing ψ x ∂ν =
          2 * q * ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ∑ j,
            HNeg.pairing φ (Kern r t x j) * HNeg.pairing ψ (Kern r t x j) * C.ρ r x ∧
        ∫ x, HNeg.pairing φ x * HNeg.pairing ψ x ∂ν = noiseCovW C q t t φ ψ) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {β : Type} [MeasurableSpace β] (Y : Ω → β), Measurable Y →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (π : Ω' → Ω) (G : Ω' → HNeg d Γ),
          MeasurePreserving π P' P ∧ Measurable G ∧ law P' G = ν ∧ IndepFun (Y ∘ π) G P' := by
  sorry

/-- The transported initial field `A η°(U^{0,t}·)` is `H^{-Γ}`-valued (the transported initial-field
hypothesis `B:ass:init-field`(F-rd) for the limit coefficients): for every `t ∈ [0,T]` there is a
measurable `I^t : Ω → H` representing `φ ↦ A η°(U^{0,t}φ)` on the smooth tests, a.s. -/
def HasTransportedField {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : WholeCoeff d)
    (Γ A T : ℝ) (η₀ : Ω → (Euc d → ℝ) → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ I : Ω → HNeg d Γ, Measurable I ∧
    ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ →
      ∀ᵐ ζ ∂P, HNeg.pairing φ (I ζ) = A * η₀ ζ (propagatorW C 0 t φ)

/-- The adjoint-duality solution `η` of `B:eq:adjoint-duality-limit-rd` (S L11487-11490), for terminal
tests `φ ∈ H^Γ` (smooth): `⟨φ, η^t⟩ = A ⟨U^{0,t}φ, η°⟩ + √(2q) ∫_0^t ⟨√μ^r ∇U^{r,t}φ, dW_r^ξ⟩`, `q = 1/β_*`
(`2/β_*`), `W^ξ` a cylindrical Wiener process independent of `η°`.  As in the project's
`IsLinearFluctuationSolutionW`, the Wiener integral is characterised by its law: for every finite
family of times and tests the vector `(⟨φ_a, η^{t_a}⟩ - A η°(U^{0,t_a}φ_a))_a` is centered Gaussian,
independent of `η°`, with covariance `noiseCovW C q t_a t_b φ_a φ_b = 2q ∫_0^{t_a∧t_b}⟨∇U^{r,t_a}φ_a ·
∇U^{r,t_b}φ_b, μ^r⟩ dr` (the Wiener-integral covariance). -/
structure IsAdjointDualityLimitW {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : WholeCoeff d)
    (Γ A q T : ℝ) (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → HNeg d Γ) : Prop where
  rho_meas : Measurable (Function.uncurry C.ρ)
  meas : ∀ t, Measurable (Y t)
  gaussian_part : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ),
    (∀ a, ts a ∈ Set.Icc 0 T) → (∀ a, IsSobolevTest Γ (φ a)) →
    let G : Ω → EuclideanSpace ℝ (Fin p) := fun ζ => WithLp.toLp 2 fun a =>
      HNeg.pairing (φ a) (Y (ts a) ζ) - A * η₀ ζ (propagatorW C 0 (ts a) (φ a))
    IndepFun G η₀ P ∧
    law P G = multivariateGaussian 0 (Matrix.of fun a b =>
      noiseCovW C q (ts a) (ts b) (φ a) (φ b))

/-- Proposition S.B.7(iii) (`B:prop:limit-field`, TeX S L11486-11491, and the uniqueness proof L11500):
the `N`-independent field (the same construction with the limiting coefficients `C = (β_∞, μ_{β_∞})`,
`A`, `q = β_*⁻¹`) exists and is the unique adjoint-duality solution.  Formally, for every initial
random functional `η°` on `(Ω, P)` whose transported fields are `H`-valued (`HasTransportedField`, i.e.
(F-rd) for the limit), and the intrinsic kernels of the limit coefficients
(`IsIntrinsicKernel`; with `μ^r` probability densities and `q ≥ 0`):
(a) existence: on an extension `(Ω', P', π)` of `(Ω, P)` there is an `H`-valued process `Y` (the
limit field `η^t`) with `IsAdjointDualityLimitW P' C Γ A q T (η° ∘ π) Y`;
(b) uniqueness: any two solutions started from initial functionals of the same law have the same
finite-dimensional laws on smooth tests (`Law (⟨φ_a, Y^{t_a}⟩)_a`).  Repair S.B.7 (2026-10-22, approved):
the initial functionals are assumed a.e.-measurable (`AEMeasurable η₁ P₁`, `AEMeasurable η₂ P₂`), as in the
S5.7 statement in `Orbits.lean` (`η⁰` measurable): `law P η = Measure.map η P` is a fixed junk Dirac mass for
a map that is not a.e.-measurable, so without this the statement is false.
The agreement with the `H^Γ`-`H^{-Γ}` pairing for `φ ∈ H^Γ` is built into the definition (the pairing is
`HNeg.pairing`).  Representation decision: the "extended" pairing `⟨φ,η^t⟩_ext` for tests `φ ∈ 𝒳`
outside `H^Γ` (S L11487) is not represented (it needs the extension of `η°` to `𝒳`); the identity is
asserted for the smooth tests of `H^Γ` (S L11492 "for `φ ∈ H^Γ`, this agrees ..."). -/
theorem limit_field_rd_duality (Γ : ℝ) (C : WholeCoeff d) (A q T B : ℝ) (hq : 0 ≤ q)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (C.ρ r)) (hρm : Measurable (Function.uncurry C.ρ))
    (Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ) (hK : IsIntrinsicKernel Γ C T B Kern) :
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (η₀ : Ω → (Euc d → ℝ) → ℝ), HasTransportedField P C Γ A T η₀ →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
        (π : Ω' → Ω) (Y : ℝ → Ω' → HNeg d Γ),
        MeasurePreserving π P' P ∧ IsAdjointDualityLimitW P' C Γ A q T (fun ζ' => η₀ (π ζ')) Y) ∧
    ∀ {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁)
      (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
      (η₁ : Ω₁ → (Euc d → ℝ) → ℝ) (η₂ : Ω₂ → (Euc d → ℝ) → ℝ)
      (Y₁ : ℝ → Ω₁ → HNeg d Γ) (Y₂ : ℝ → Ω₂ → HNeg d Γ),
      AEMeasurable η₁ P₁ → AEMeasurable η₂ P₂ →
      law P₁ η₁ = law P₂ η₂ →
      IsAdjointDualityLimitW P₁ C Γ A q T η₁ Y₁ → IsAdjointDualityLimitW P₂ C Γ A q T η₂ Y₂ →
      ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ),
        (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) → (∀ a, IsSobolevTest Γ (φ a)) →
        law P₁ (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y₁ (ts a) ζ) :
            EuclideanSpace ℝ (Fin p))) =
          law P₂ (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y₂ (ts a) ζ) :
            EuclideanSpace ℝ (Fin p))) := by
  sorry

/-- A smooth decaying test `ϑ` of the weak form `B:eq:spde-weak` (S L11492-11494): a Schwartz function
such that `𝓛_{β,μ^r}ϑ`, `r ∈ [0,T]`, is again a smooth test of `H^Γ` (so that
`⟨𝓛ϑ, η^r⟩` is the `H^Γ`-`H^{-Γ}` pairing; technical, see `limit_field_rd_weak_form`). -/
def IsWeakTestFn (Γ : ℝ) (C : WholeCoeff d) (T : ℝ) (ϑ : Euc d → ℝ) : Prop :=
  (∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ϑ) ∧ IsSobolevTest Γ ϑ ∧
    ∀ r ∈ Set.Icc (0 : ℝ) T, IsSobolevTest Γ (generatorW C r ϑ)

/-- The weak equation `B:eq:spde-weak` (S L11493-11496) for `Y = η`: for every smooth decaying test `ϑ`,
`⟨ϑ,η^t⟩ = A⟨ϑ,η°⟩ + ∫_0^t ⟨𝓛_{β_∞,μ^r}ϑ, η^r⟩ dr + √(2q) ∫_0^t ⟨√μ^r ∇ϑ, dW^ξ_r⟩`; as in
`IsAdjointDualityLimitW` the Wiener integral is characterised by its law: the vector of
`⟨ϑ_a,η^{t_a}⟩ - A⟨ϑ_a,η°⟩ - ∫_0^{t_a}⟨𝓛_rϑ_a, η^r⟩ dr` is centered Gaussian, independent of `η°`,
with covariance `2q ∫_0^{t_a∧t_b}⟨∇ϑ_a·∇ϑ_b, μ^r⟩ dr`.  `η^0 = A η°` (`init`). -/
structure IsWeakLimitSPDEW {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : WholeCoeff d)
    (Γ A q T : ℝ) (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → HNeg d Γ) : Prop where
  rho_meas : Measurable (Function.uncurry C.ρ)
  meas : ∀ t, Measurable (Y t)
  init : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ →
    ∀ᵐ ζ ∂P, HNeg.pairing ϑ (Y 0 ζ) = A * η₀ ζ ϑ
  gaussian_part : ∀ (p : ℕ) (ts : Fin p → ℝ) (ϑ : Fin p → Euc d → ℝ),
    (∀ a, ts a ∈ Set.Icc 0 T) → (∀ a, IsWeakTestFn Γ C T (ϑ a)) →
    let M : Ω → EuclideanSpace ℝ (Fin p) := fun ζ => WithLp.toLp 2 fun a =>
      HNeg.pairing (ϑ a) (Y (ts a) ζ) - A * η₀ ζ (ϑ a) -
        ∫ r in Set.Icc (0 : ℝ) (ts a), HNeg.pairing (generatorW C r (ϑ a)) (Y r ζ)
    IndepFun M η₀ P ∧
    law P M = multivariateGaussian 0 (Matrix.of fun a b =>
      2 * q * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
        inner ℝ (gradient (ϑ a) x) (gradient (ϑ b) x) * C.ρ r x)

/-- A random functional `η°` is linear on `C_b^1` test functions (almost surely). -/
def IsLinearOnCb1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (η₀ : Ω → (Euc d → ℝ) → ℝ) :
    Prop :=
  ∀ᵐ ζ ∂P, ∀ (f g : Euc d → ℝ) (c : ℝ), MemCb 1 f → MemCb 1 g → η₀ ζ (f + c • g) = η₀ ζ f + c * η₀ ζ g

/-- Proposition S.B.7(iii), last sentence (`B:eq:spde-weak`, TeX S L11492-11494, proof L11500:
"differentiating the adjoint representation in the terminal time and applying stochastic Fubini yields
the weak equation"): an adjoint-duality solution `Y` solves the weak equation for every smooth decaying
test `ϑ`.  Only this direction is stated.
SUSPECTED ISSUE (S L11492): the TeX says the duality identity is "equivalent" to the weak equation for
smooth decaying `ϑ`, but the proof (L11500) gives only duality `⇒` weak; the converse is false in this
formalization (with `IsWeakTestFn = {0}` the weak equation is empty) and is not needed (uniqueness is
proved in the duality class).
Extra hypotheses (technical, used implicitly by the proof): the adjoint input `AdjointInputOne` (so that
`U^{0,t}` exists and is linear on tests), joint measurability of `(t,ζ) ↦ Y^t(ζ)` (so that
`r ↦ ⟨𝓛_rϑ, η^r⟩` is measurable), `η°` linear on `C_b^1` and *continuous along the orbits*
`U^{0,r}𝓛_rϑ` (the TeX's `⟨·, η°⟩_ext`): `η°` commutes with the time integral
`∫_0^t U^{0,r}𝓛_rϑ dr = U^{0,t}ϑ - ϑ` (Duhamel), and the `r`-integrand `r ↦ η°(U^{0,r}𝓛_rϑ)` is integrable (so that the right side is not
the junk `0`).  Coefficients as in (ii)/(iii).
Repair P12 (2026-10-20): the Duhamel identity is the hypothesis `hduh` (shape of `IsWeightedExtension.terminal_identity`, TeX S L10763-10768):
for `0 ≤ s ≤ t ≤ T`, `U^{s,t}ϑ - ϑ = ∫_s^t U^{s,r}𝓛_rϑ dr` together with its gradient version (the uniform bound of `∇U^{s,r}𝓛_rϑ` is the separate hypothesis `hbd`)
(needed for the stochastic Fubini); `horbit` alone only says that `η°` commutes with the `r`-integral, and `AdjointInputOne` gives
bounds only at `r = 0`, so none of this is derivable from the other hypotheses.
Repair S.B.7 (2026-10-22, approved): technical hypotheses `0 ≤ T`, `Measurable η₀`, the joint
measurability `hΛm`, `hgm` of the Duhamel gradient integrand `(r,w,x) ↦ ∇U^{w,r}(𝓛_rϑ)(x)` (cut off to
`0 ≤ w ≤ r ≤ T`) and of the noise integrand `(r,ζ) ↦ ⟨𝓛_rϑ, Y^r⟩ - A η°(U^{0,r}𝓛_rϑ)` (cut off to `r ∈ [0,T]`),
and the bound of `∇U^{s,r}𝓛_rϑ` is uniform in `s` (`hbd`, from `sup_{N,r,t,x}‖K^{r,t}‖ ≤ C`, S L10751-10752, and `B:eq:path-generator-C1`, S L10771-10772;
formerly the `∃ B` inside `hduh` depended on `s`). -/
theorem limit_field_rd_weak_form (Γ : ℝ) (C : WholeCoeff d) (A q T K : ℝ) (hq : 0 ≤ q)
    (hT : 0 ≤ T) (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (C.ρ r)) (hρm : Measurable (Function.uncurry C.ρ))
    (hU : AdjointInputOne Γ C T K)
    (hduh : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      ∀ x, propagatorW C s t ϑ x - ϑ x = ∫ r in Set.Icc s t, propagatorW C s r (generatorW C r ϑ) x ∧
        gradient (propagatorW C s t ϑ) x - gradient ϑ x =
          ∫ r in Set.Icc s t, gradient (propagatorW C s r (generatorW C r ϑ)) x)
    (hbd : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∃ B : ℝ, ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ T →
      ∀ x, ‖gradient (propagatorW C s r (generatorW C r ϑ)) x‖ ≤ B)
    (hΛm : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ →
      Measurable (fun q : ℝ × (ℝ × Euc d) =>
        if 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.1 ≤ T then
          gradient (propagatorW C q.2.1 q.1 (generatorW C q.1 ϑ)) q.2.2 else 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (hη : HasTransportedField P C Γ A T η₀)
    (hη₀m : Measurable η₀) (hlin : IsLinearOnCb1 P η₀)
    (horbit : ∀ᵐ ζ ∂P, ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun r => η₀ ζ (propagatorW C 0 r (generatorW C r ϑ))) (Set.Icc (0 : ℝ) t) ∧
      η₀ ζ (fun x => ∫ r in Set.Icc (0 : ℝ) t, propagatorW C 0 r (generatorW C r ϑ) x) =
        ∫ r in Set.Icc (0 : ℝ) t, η₀ ζ (propagatorW C 0 r (generatorW C r ϑ)))
    (Y : ℝ → Ω → HNeg d Γ) (hYm : Measurable (fun p : ℝ × Ω => Y p.1 p.2))
    (hgm : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ →
      Measurable (fun q : ℝ × Ω =>
        if q.1 ∈ Set.Icc (0 : ℝ) T then
          HNeg.pairing (generatorW C q.1 ϑ) (Y q.1 q.2) -
            A * η₀ q.2 (propagatorW C 0 q.1 (generatorW C q.1 ϑ)) else 0)) :
    IsAdjointDualityLimitW P C Γ A q T η₀ Y → IsWeakLimitSPDEW P C Γ A q T η₀ Y := by
  sorry

end HRS.Whole
