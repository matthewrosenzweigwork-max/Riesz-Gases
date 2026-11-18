import HRS.Whole.Adjoint
import HRS.Whole.Static
import HRS.Energy.Coercivity
import HRS.Whole.Q09AAux1

/-!
# Appendix S.B (whole-space supplement): modulated free energy under confinement and the
whole-space commutator estimates (SPEC-WB)

Source: HRS whole-space supplement (S), Appendix S.B ("Further whole-space comparison estimates"):

* S.B.1 `B:prop:mfe-confined-rd-gradient` (S L11079-11117): `mfe_confined_rd_gradient_super`,
  `mfe_confined_rd_gradient_sub` (the two alternatives (i), (ii) of the proposition);
* S.B.5 `S:prop:whole-commutators` (S L11371-11403): `whole_commutator_super`,
  `whole_commutator_sub_sharp`, `whole_commutator_sub_lower` (items (i), (ii), (iii)); the
  items are external results (Rosenzweig-Serfaty, Hess-Childs-Rosenzweig, Nguyen-Rosenzweig-Serfaty)
  stated as written in S;
* S.B.6 `B:rem:comm-sub-nondecay` (S L11405-11415): `planeWave_not_fracLp` (the one checkable
  claim of the remark: a plane wave has no `L^p` fractional derivative).

## Representation decisions (consequential; all mirror the torus statements `HRS.mfe_uniform`,
`HRS.commutator_estimate` of `HRS/Energy/Coercivity.lean`)

* `𝖤_N(f, μ) = β⁻¹ 𝖧_N(f | μ^{⊗N}) + ∫ 𝖥_N(X_N, μ) f(dX_N)` with `𝖧_N = N⁻¹ H` (`modulatedFreeEnergyW`):
  the same reading as the torus (the manuscripts use `𝖤_N` without a definition, ISSUES §C).
  Finiteness is the separate predicate `MFEFiniteW` and part of the conclusion.
* `o_N` of S.B.1 and S.B.5 is `HRS.oNΛ d s C₀ Λ N` with the constant `C₀` chosen before everything
  (`o_N = o_N(Λ)` of `H:eq:energy-completion`, as in the torus statements); `Λ` is the bound of the
  "stated bounded reference densities" (S.B.5) / of the regularity `S:eq:mf-regularity-whole`.
* Norms of the transport are represented by *upper bounds* `K` (any `K ≥` the norm): `‖∇v‖_{L^∞}` by a
  Lipschitz constant (`LipschitzWith`), `‖|∇|^{α}v‖_{L^p}` by a distributional representative
  (`IsFracDerivRep`, `HRS/Whole/Adjoint.lean`, never Mathlib's junk-valued `fracGradPow`) with
  `eLpNorm ≤ F`.  The time integrals `L_T = ∫_0^T ‖·‖ dt` are `∫_0^T K` for an integrable `K`
  dominating the norm (as the torus `mfe_uniform`).
* Commutators are `HRS.Whole.commN` (deleted particle diagonal, `Comm_N = 𝖢_N`); the integrals defining
  them converge absolutely and this is part of the conclusion (`CommIntegrableW`), as on the torus.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### Modulated free energy -/

/-- The modulated free energy `𝖤_N(f, μ) = β⁻¹ 𝖧_N(f | μ^{⊗N}) + ∫ 𝖥_N(X_N, μ) f(dX_N)` on `ℝ^d`,
`β⁻¹ = invβ`, `𝖧_N = N⁻¹ H` (the torus `HRS.modulatedFreeEnergy`); a real number meaningful under
`MFEFiniteW`. -/
def modulatedFreeEnergyW (d : ℕ) (s invβ : ℝ) {N : ℕ} (f : Measure (EucConfig d N))
    (μ : Measure (Euc d)) : ℝ :=
  invβ * (relEntropy f (Measure.pi fun _ : Fin N => μ) / (N : ℝ≥0∞)).toReal +
    ∫ X, rieszModulatedEnergy d s X μ ∂f

/-- `𝖤_N(f, μ) < ∞`: finite relative entropy and integrable interaction energy. -/
def MFEFiniteW (d : ℕ) (s : ℝ) {N : ℕ} (f : Measure (EucConfig d N)) (μ : Measure (Euc d)) :
    Prop :=
  relEntropy f (Measure.pi fun _ : Fin N => μ) ≠ ⊤ ∧
    Integrable (fun X => rieszModulatedEnergy d s X μ) f

/-- `u_0 = β⁻¹ ∇ log μ + ∇g * μ` (`B:prop:mfe-confined-rd-gradient` L11098-11100), with `∇g*μ` by the
cancellation convention (`convGradConvW`). -/
def mfeTransport0W (D : WholeDyn d) (ρ : Euc d → ℝ) (x : Euc d) : Euc d :=
  D.invβ • gradient (fun y => Real.log (ρ y)) x + convGradConvW (rieszKernelGrad d D.s) ρ x

/-- `u_V = β⁻¹ ∇ log μ + ∇g * μ + ∇V` (S L11083-11085, `B:eq:uV-periodic` of M). -/
def mfeTransportW (D : WholeDyn d) (ρ : Euc d → ℝ) (x : Euc d) : Euc d :=
  mfeTransport0W D ρ x + gradient D.V x

/-- The weighted regularity `‖ρ‖_{C_b^r} + max_{j≤r} ‖⟨x⟩^{d+3} ∇^{⊗j}ρ‖_∞ ≤ Λ` of one density
(`S:eq:mf-regularity-whole`, S L9662-9665); the weighted sup is `ℝ≥0∞`-valued (`weightedSupE`). -/
def IsRegularDensityW (r : ℕ) (Λ : ℝ) (ρ : Euc d → ℝ) : Prop :=
  ContDiff ℝ r ρ ∧ MemCb r ρ ∧
    ENNReal.ofReal (cbNorm r ρ) + weightedSupE r ((d : ℝ) + 3) ρ ≤ ENNReal.ofReal Λ

/-- `(r,Λ)`-regularity of a whole-space mean-field trajectory on `[0,T]`
(`S:eq:mf-regularity-whole`, S L9662-9665, for one value of `N`):
`sup_{t≤T} (‖ρ^t‖_{C_b^r} + max_{j≤r} ‖⟨x⟩^{d+3} ∇^{⊗j}ρ^t‖_∞) ≤ Λ`. -/
def IsRegularMFW (r : ℕ) (Λ T : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, IsRegularDensityW r Λ (ρ t)

/-- `‖v‖_{Lip} ≤ K`, i.e. `‖∇v‖_{L^∞} ≤ K` for a Lipschitz field (the Lipschitz constant). -/
def HasLipBoundW (v : Euc d → Euc d) (K : ℝ) : Prop :=
  ∃ L : ℝ≥0, LipschitzWith L v ∧ (L : ℝ) ≤ K

/-- `‖∇v‖_{L^∞} + ‖|∇|^α v‖_{L^p} ≤ K` (the transport seminorms of S.B.1(ii), S.B.5(ii),(iii)):
`v` is Lipschitz with constant `L` and the distributional fractional derivative `|∇|^α v`
(`IsFracDerivRep`, componentwise) has a representative `w` with `‖ |w| ‖_{L^p} ≤ F`, `L + F ≤ K`. -/
def HasFracTransportBound (α p : ℝ) (v : Euc d → Euc d) (K : ℝ) : Prop :=
  ∃ (L : ℝ≥0) (F : ℝ), 0 ≤ F ∧ LipschitzWith L v ∧
    (∃ w : Euc d → Euc d, (∀ i, IsFracDerivRep α (fun x => v x i) (fun x => w x i)) ∧
      eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F) ∧
    (L : ℝ) + F ≤ K

/-- Absolute convergence of the integrals defining `Comm_N(v; X_N, μ)`:
`∫ h_v(x_i, y) dμ(y)` and `∬ h_v dμ dμ`, `h_v(x,y) = (v(x)-v(y))·∇g(x-y)`. -/
def CommIntegrableW (d : ℕ) (s : ℝ) {N : ℕ} (v : Euc d → Euc d) (X : EucConfig d N)
    (μ : Measure (Euc d)) : Prop :=
  (∀ i, Integrable (fun y => commutatorKernel d s v (X i) y) μ) ∧
    Integrable (fun p : Euc d × Euc d => commutatorKernel d s v p.1 p.2) (μ.prod μ)

/-! ### S.B.1: modulated free energy under confinement -/

/-- The standing hypotheses of Proposition S.B.1 `B:prop:mfe-confined-rd-gradient` (S L11080-11082),
common to both alternatives: `𝔻 = ℝ^d`, `M = -I`, `β_N < ∞` (`invβ > 0`); the initial particle law has
finite Gibbs entropy `B:eq:selected-initial-gibbs-entropy` (relative entropy with respect to the
canonical Gibbs law `G_{N,β_N,V}`) and `𝖤_N(f_N^0, μ°) < ∞`; `μ = μ_{β_N}` (`ρ`) is a *regular
solution* of `H:eq:meanfield` on `[0,T]` (`IsWholeMeanFieldSolution` plus the `(r,Λ)`-regularity
`S:eq:mf-regularity-whole`, `Λ ≥ 1`, and `ρ^t > 0` so that `∇ log μ` is defined; AMBIGUITY: the
supplement does not define "regular"); `X` is the selected particle process (the collision-free
strong solution of the whole-space particle system, `IsWholeStrongSolution`, S L9698-9724, with `X_0`
independent of the noise). -/
structure WholeMFEHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : WholeDyn d) (N : ℕ)
    (T Λ : ℝ) (r : ℕ) (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → EucConfig d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N) : Prop where
  gradient : D.M = -1
  pos_temp : 0 < D.invβ
  mf : IsWholeMeanFieldSolution D T ρ
  mf_reg : IsRegularMFW r Λ T ρ
  r_ge : 3 ≤ r
  Λ_ge : 1 ≤ Λ
  pos_density : ∀ t ∈ Set.Icc 0 T, ∀ x, 0 < ρ t x
  gibbs_entropy :
    relEntropy (P.map X₀) (canonicalGibbs (rieszKernel d D.s) D.V N (1 / D.invβ)) ≠ ⊤
  mfe_init : MFEFiniteW d D.s (P.map X₀) (withDensityReal (ρ 0))
  brownian : IsVectorBrownian P W
  indep : IndepFun X₀ (fun ζ t => W t ζ) P
  sol : IsWholeStrongSolution P D T X₀ W X
  /-- Strong-solution adaptedness (`Supplement repair S.B.1`, docs/ISSUES.md; as `HRS.MFEHyp.filtered` on the torus and
  `RdStanding.filtered`): `IsWholeStrongSolution.adapted` is only measurability of each `X t`, whereas the Itô/entropy calculus
  needs `X` adapted and `W` Brownian for a common filtration. -/
  filtered : ∃ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
    IsWholeFilteredSolution P ℱ W' W X

/-- Proposition S.B.1 (`B:prop:mfe-confined-rd-gradient`, TeX S L11079-11117), alternative (i)
(L11086-11099): `s ≥ max{0, d-2}` (and `s < d`), `V ∈ C³`, `‖∇²V‖_{L^∞} < ∞`,
`V(x) ≥ c_V|x|² - C_V` (`c_V > 0`), and `L_T^{nd} = ∫_0^T ‖∇u_V^t‖_{L^∞} dt < ∞` with
`u_V^t = β_N⁻¹ ∇ log μ^t + ∇g*μ^t + ∇V` (represented by an integrable `K ≥ ‖∇u_V^t‖_∞`,
`HasLipBoundW`).  Conclusion (L11108-11114): for `0 ≤ t ≤ T`, `P_N^t = f_N^t dX_N`
(`law ≪ volume`), `𝖤_N(f_N^t, μ^t) < ∞` (`MFEFiniteW`; implicit in the TeX bound) and
`𝖤_N(f_N^t, μ^t) + o_N ≤ exp(C L_T^{nd}) (𝖤_N(f_N^0, μ°) + o_N)`, `C = C(d,s)`, `C₀ = C₀(d,s)` of
`o_N = oNΛ d s C₀ Λ N` (`H:eq:energy-completion`).
Technical hypotheses: `1 ≤ d` and `2 ≤ N` (as `HRS.mfe_uniform`); `3 ≤ r` and `ρ^t > 0`
(`WholeMFEHyp`: `∇ log μ`, `∇u_V` must exist); `c_V > 0` (`V(x) ≥ c_V|x|² - C_V` with `c_V ≤ 0`
is vacuous and the TeX means a confining potential); `K` integrable (as in the torus).
Constants: `C₀, C` are quantified before every other object, as in the TeX ("`C` depends only on
`d, s`"); `c_V, C_V, ‖∇²V‖_∞, Λ` enter only through the hypotheses. -/
theorem mfe_confined_rd_gradient_super (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hsc : (d : ℝ) - 2 ≤ s) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : WholeDyn d), D.s = s → ContDiff ℝ 3 D.V →
      (∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 D.V x‖ ≤ B) →
      (∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → EucConfig d N),
        WholeMFEHyp P D N T Λ r ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, HasLipBoundW (mfeTransportW D (ρ t)) (K t)) →
      ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        MFEFiniteW d s (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) ∧
        modulatedFreeEnergyW d s D.invβ (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) +
            oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (modulatedFreeEnergyW d s D.invβ (P.map X₀) (withDensityReal (ρ 0)) +
              oNΛ d s C₀ Λ N) := by
  sorry

/-- Proposition S.B.1 (`B:prop:mfe-confined-rd-gradient`, TeX S L11079-11117), alternative (ii)
(L11100-11107): `0 ≤ s < d-2` and `V(x) = ½ xᵀQx + b·x + c`, `Q = Qᵀ ≥ qI`, `q > 0`; for some
`a ∈ (d, d+2)` and `u_0^t = β_N⁻¹ ∇ log μ^t + ∇g*μ^t`,
`L_{T,a}^{quad} = ∫_0^T (‖∇u_0^t‖_{L^∞} + ‖|∇|^{a/2} u_0^t‖_{L^{2d/(a-2)}} + ‖Q‖) dt < ∞` (an
integrable `K` dominating the integrand: `HasFracTransportBound (a/2) (2d/(a-2)) (u_0^t) (K t - ‖Q‖)`,
`‖Q‖` the operator norm).  The conclusion is as in (i), with `C` depending on `d, s` and `a` (the
exponent `a` is quantified before `∃ C₀ C`; `C₀` too, as `o_N`'s constant).
Same technical hypotheses as `mfe_confined_rd_gradient_super` (`1 ≤ d` is automatic from `s < d-2`,
`0 ≤ s`; we state `3 ≤ d` implicitly through `hsd`). -/
theorem mfe_confined_rd_gradient_sub {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : WholeDyn d), D.s = s →
      ∀ (Q : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) (c q : ℝ), 0 < q → Q.IsSymm →
        (Q - q • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef →
        (∀ x, D.V x = (1 / 2) * inner ℝ x (Torus.matVec Q x) + inner ℝ b x + c) →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → EucConfig d N),
        WholeMFEHyp P D N T Λ r ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, HasFracTransportBound (a / 2) (2 * d / (a - 2))
          (mfeTransport0W D (ρ t))
          (K t - ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖)) →
      ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        MFEFiniteW d s (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) ∧
        modulatedFreeEnergyW d s D.invβ (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) +
            oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (modulatedFreeEnergyW d s D.invβ (P.map X₀) (withDensityReal (ρ 0)) +
              oNΛ d s C₀ Λ N) := by
  sorry

/-! ### S.B.5: whole-space commutator estimates -/

/-- Proposition S.B.5(i) (`S:prop:whole-commutators`, `B:item:comm-rd-super`, TeX S L11371-11381;
external: Rosenzweig-Serfaty, *Sharp commutator estimates*, Thm 1.1): on `ℝ^d`, for
`s ≥ max{0, d-2}` (and `s < d`), for every probability density `ρ` with `‖ρ‖_∞ ≤ Λ` (the "stated
bounded reference densities"; `Λ ≥ 1`), every `N ≥ 2`, every pairwise distinct `X_N` and every
Lipschitz `v` (`‖∇v‖_∞ ≤ K`; no decay of `v`):
`|Comm_N(v; X_N, μ)| ≤ C ‖∇v‖_∞ (𝖥_N(X_N, μ) + o_N)`, `o_N = oNΛ d s C₀ Λ N`; the integrals defining
`Comm_N` converge absolutely.  For `s = 0` ("the usual logarithmic integrability assumption")
`∫ log(2+|x|) dμ ≤ L` (`HasLogMoment`), `L` quantified before the constants (as the log-moment
parameter `L` of `HRS.Whole.euclidean_pressure`; AMBIGUITY: the TeX does not say how the constants
depend on this assumption).
Technical hypotheses: `1 ≤ d`, `2 ≤ N`, `1 ≤ Λ` (as `HRS.commutator_estimate`).  PLAN: external
results, cited in the TeX, not proved in the repository. -/
theorem whole_commutator_super (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hsc : (d : ℝ) - 2 ≤ s) (L : ℝ) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) →
      ∀ X : EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), HasLipBoundW v K →
        CommIntegrableW d s v X (withDensityReal ρ) ∧
        |commN d s v X (withDensityReal ρ)| ≤
          C * K * (rieszModulatedEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  sorry

/-- Proposition S.B.5(ii) (`S:prop:whole-commutators`, `B:item:comm-rd-sub-sharp`, TeX S L11382-11389;
external: Hess-Childs-Rosenzweig, *Sharp commutator estimates*, Thm 1.1): on `ℝ^d`, `0 ≤ s < d-2` and
every `a ∈ (d, d+2)` (quantified first: `C_a`):
`|Comm_N(v;X_N,μ)| ≤ C_a (‖∇v‖_∞ + ‖|∇|^{a/2} v‖_{L^{2d/(a-2)}}) (𝖥_N(X_N,μ) + o_N)`; the decay
hypothesis `|∇|^{a/2} v ∈ L^{2d/(a-2)}` is part of the assertion (`HasFracTransportBound`).
Same standing assumptions and technical hypotheses as `whole_commutator_super`. -/
theorem whole_commutator_sub_sharp {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) (L : ℝ) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) →
      ∀ X : EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), HasFracTransportBound (a / 2) (2 * d / (a - 2)) v K →
        CommIntegrableW d s v X (withDensityReal ρ) ∧
        |commN d s v X (withDensityReal ρ)| ≤
          C * K * (rieszModulatedEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  sorry

/-- The long-range error `e_N^{lr} = (1 + 1_{s=0} log N) N^{-2/((s+1)(s+2))}`
(`B:eq:old-comm-error`, S L11396-11398). -/
def commLowRateError (s : ℝ) (N : ℕ) : ℝ :=
  (1 + (if s = 0 then Real.log N else 0)) * (N : ℝ) ^ (-(2 / ((s + 1) * (s + 2))))

/-- Proposition S.B.5(iii) (`S:prop:whole-commutators`, `B:item:comm-rd-sub-lower`, TeX S L11390-11403;
the strict sub-Coulomb specialization of Nguyen-Rosenzweig-Serfaty, Prop. 4.1): on `ℝ^d`,
`0 ≤ s < d-2`:
`|Comm_N(v;X_N,μ)| ≤ C (‖∇v‖_∞ + ‖|∇|^{(d-s)/2} v‖_{L^{2d/(d-s-2)}}) (𝖥_N(X_N,μ) + o_N + C e_N^{lr})`.
The same `C` is used in front and inside (the literal reading; the statement with two constants is
equivalent after taking the maximum).  Same standing assumptions and technical hypotheses as
`whole_commutator_super`. -/
theorem whole_commutator_sub_lower {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (L : ℝ) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) →
      ∀ X : EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ),
        HasFracTransportBound (((d : ℝ) - s) / 2) (2 * d / ((d : ℝ) - s - 2)) v K →
        CommIntegrableW d s v X (withDensityReal ρ) ∧
        |commN d s v X (withDensityReal ρ)| ≤
          C * K * (rieszModulatedEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N +
            C * commLowRateError s N) := by
  sorry

/-! ### S.B.6: decay of the sub-Coulomb transport -/

/-- Remark S.B.6 (`B:rem:comm-sub-nondecay`, TeX S L11405-11415), its checkable claim: "a general plane
wave ... does not satisfy this requirement", i.e. for `v(x) = cos(2π k·x) e` (`k ≠ 0`, `e ≠ 0`) and
every `α > 0`, `1 ≤ p < ∞` there is no representative `w ∈ L^p` of the distributional fractional
derivative `|∇|^α v` (`IsFracDerivRep`): the hypothesis `‖|∇|^{α}v‖_{L^p} < ∞` of S.B.5(ii),(iii)
excludes plane waves.  (The rest of the remark -- combining with the decaying `W^{m,p}` adjoint theory,
the far-field condition `p(s+1) > d` giving the ranges of Definition S.A.1 -- is prose; the identity
`p_𝔠(s+1) > d` is `HRS.Whole.DecayingDensity.integrability_mul_gt`.  The phrase "or uniformly local
transport" is not formalized: the plane wave is the example.) -/
theorem planeWave_not_fracLp (k e : Euc d) (hk : k ≠ 0) (he : e ≠ 0) (α p : ℝ) (hα : 0 < α)
    (hp : 1 ≤ p) :
    ¬ ∃ w : Euc d → Euc d,
      (∀ i, IsFracDerivRep α (fun x => Real.cos (2 * Real.pi * inner ℝ k x) * e i)
        (fun x => w x i)) ∧
      MemLp (fun x => ‖w x‖) (ENNReal.ofReal p) volume := by
  exact HRS.Whole.Q09A.q09a_planeWave k e hk he α p hα hp

/-! ### S.A.1, claim 2 (stated here because `HasFracTransportBound` is defined here) -/

namespace DecayingDensity

variable {s : ℝ}

/-- Claim 2 of Definition S.A.1: `‖𝖬^*∇f‖_𝔠 ≤ C ‖f‖_{W^{m_𝔠,p_𝔠}}` for every fixed matrix `𝖬`, with `‖v‖_𝔠 = ‖∇v‖_{L^∞} +
‖|∇|^{r_𝔠}v‖_{L^{p_𝔠}}` (TeX S L9829-9833) expressed by the distributional transport bound `HasFracTransportBound` (Lipschitz
constant of `v`, distributional fractional derivative in `L^{p_𝔠}`) with the bound `C‖f‖_{W^{m_𝔠,p_𝔠}}`.  Repair P10 (2026-10-20): the
earlier form used the Bochner-integral `commutatorNorm`, which is `0` in its `L^p` term for `v ∉ L¹`, so the inequality was true but
empty.  (Moved from `HRS/Whole/Basic.lean`, where `HasFracTransportBound` is not yet available; same name.) -/
theorem commutatorNorm_le (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ C : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ c.sobolevIndex, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ c.integrability)) →
      HasFracTransportBound c.regularity c.integrability
        (fun x => Matrix.toEuclideanLin M.transpose (gradient f x))
        (C * sobolevWNorm c.sobolevIndex c.integrability f) := by
  sorry

end DecayingDensity

end HRS.Whole
