import HRS.Whole.AppendixA

/-!
# Appendix S.A of the whole-space supplement: the adjoint linearized flow on `ℝ^d` (SPEC-WA, part 2)

Specification file (statements with `sorry` proofs).  Sources (`HRS_whole_space_supplement_20261008T010000Z.tex`, "S"):

* S.A.12 `B:thm:adjoint-rd` (S L10089-10109): `adjoint_rd` (existence, uniqueness, bound), `adjoint_rd_classical` (a),
  `adjoint_rd_planewave` (b), `adjoint_rd_sobolev` (c), `adjoint_rd_stability` (d), `adjoint_rd_weighted` (e);
* S.A.13 `B:rem:def-adjoint-rd` (S L10111-10113): the notion is `HRS.Whole.IsClassicalAdjointW` (SUSPECTED ISSUE, see
  below); its checkable claim "sufficient for `B:prop:duality-identity`" is `duality_identity_rd`;
* S.A.14 `B:prop:low-frequency-obstruction` (S L10115-10121): `multipole_tail`, `multipole_not_lp`;
* S.A.15 `B:lem:lp-coefficient-commutator` (S L10141-10204): `lp_screened_negative_order`, `lp_positive_order_product`,
  `lp_Lambda_commutator_low`, `lp_Lambda_commutator_expansion`, `lp_tensor_absorption`;
* S.A.16 `B:thm:adjoint-lp` (S L10265-10297): `adjoint_lp`, `adjoint_lp_classical`, `adjoint_lp_stability`;
* S.A.17 `B:rem:lp-anisotropic` (S L10375-10383): `no_formal_content`.

## Representation decisions

* The standing coefficient hypothesis `B:eq:coeff-hypothesis-rd` is `AdjointRdData` (+ the regime `RdRegimeHolds`
  for `B:thm:adjoint-rd`, `AdjointLpRegime` for `B:thm:adjoint-lp`); the constants are chosen before the data
  (`∃ C, 0 < C ∧ ∀ D ν₀ μ …`), depending on `(d, s, m, |M|, Λ, Λ_V, |∇V(0)|, ν̄, T)` and the regime, with `ν₀` (regime R3)
  quantified after `C` as on the torus (`HRS.PDE.adjoint_torus`), `Λ_m = PDE.Regime.lambdaM Rg C ν₀ (s+2-d)`.
* "`F` solves `B:eq:adjoint-forward` in the distributional sense with `F(0) = φ`" is `IsForwardSolutionRd`: the weak
  (integrated in time) form against `C_c^∞` tests `ψ`, `d/dτ∫Fψ = ν∫FΔψ - ∫F div(b^τψ) - ∫𝒢^τ[F]ψ`, with
  `𝒢^τ[F] = ∑_{ij} M^*_{ij} ∂_i g*(μ^{t-τ} ∂_jF)` and the nonlocal term moved onto the test function
  (`∫ 𝒢[F]ψ = +∑ M^*_{ij} ∫ F ∂_j(μ ∂_i(g*ψ))`, `g*ψ ∈ C^∞`; no derivative of `F` is needed).  Integrability of every
  term is part of the solution concept.
* `F(τ)` are functions defined a.e.; "unique" is a.e. equality for every `τ`.  `L^∞([0,t]; H^m_uloc)` is the bound for
  every `τ`; `C([0,t]; H^{m'}_loc)` is continuity of `τ ↦ χ(·-z)F(τ)` in `H^{m'}` for each `z` (real `m' < m`);
  `C_w([0,t]; H^m)` is continuity of `τ ↦ ⟨F(τ), h⟩_{H^m}` for every `h ∈ H^m`.
* `W^{m,p}(ℝ^d)` is `WmpSpace` of `HRS/Whole/AppendixA.lean` (closure of the jets of `C_c^∞` in `L^p`); "`u ∈ W^{m,p}`
  with norm `‖u‖`" is `wNormE` (`⊤` if `u` is not the zeroth component of an element of `WmpSpace`).
  `C([0,t]; W^{m',p}_loc)` is for integers `0 ≤ m' < m`.
* SUSPECTED ISSUE (S.A.12(a), S.A.13, S L10098-10100, L10111-10113): a classical adjoint solution on `ℝ^d` is required to have
  *bounded* `∂_r f` (`f, ∇f, ∇²f, ∂_rf` bounded and continuous).  For a confining drift `-Qx` (`Q ≠ 0`; `V = |x|²/2`) this
  fails already at `r = t` for a bounded smooth datum such as `φ = sin x_i`, since `∂_rf = -𝓛φ` contains `Qx·∇φ`, which grows
  linearly.  The repository's notion `HRS.Whole.IsClassicalAdjointW` asks `|∂_rf| ≤ B(1+|x|)` instead (`bdd_time_deriv`);
  the statements here (a), `adjoint_lp_classical`, `duality_identity_rd` and `WeightedPathInput` use it.  See
  `docs/ISSUES.md` §I.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### The distributional solution concept -/

/-- The nonlocal part of the weak form: `∑_{i,j} M^*_{ij} ∂_j(μ^{τ'} ∂_i(g*ψ))` (`M^*_{ij} = M_{ji}`), the function
by which `F` is integrated in `∫ 𝒢[F]ψ = +∫ F · nonlocalTestRd` (`∫ ∂_ig*(μ∂_jF) ψ = -∫ μ ∂_jF ∂_i(g*ψ)` since `∂_ig` is
odd, then integrate by parts in `∂_j`); so `forwardWeakTerm` carries `-∫ F · nonlocalTestRd`. -/
def nonlocalTestRd (C : WholeCoeff d) (τ' : ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, C.M j i *
    partialDeriv (fun _ : Fin 1 => j)
      (fun y => C.ρ τ' y * gradient (convFun (rieszKernel d C.s) ψ) y i) x

/-- The time-`σ` integrand of the weak form of `∂_σF = νΔF + b^σ·∇F - 𝒢^σ[F]` against `ψ`, coefficients at time `t - σ`:
`ν∫FΔψ - ∫F div(b ψ) - ∫F·nonlocalTestRd`, `b = C.drift (t-σ)`. -/
def forwardWeakTerm (C : WholeCoeff d) (t : ℝ) (F : ℝ → Euc d → ℝ) (ψ : Euc d → ℝ) (σ : ℝ) : ℝ :=
  C.ν * (∫ x, F σ x * Laplacian.laplacian ψ x) -
    (∫ x, F σ x * movDiv (fun y => ψ y • C.drift (t - σ) y) x) -
    ∫ x, F σ x * nonlocalTestRd C (t - σ) ψ x

/-- `F` solves the forward adjoint equation `B:eq:adjoint-forward` (`∂_τF = νΔF + b^τ·∇F - 𝒢^τ[F]`,
`b^τ = M∇g*μ^{t-τ} - ∇V`, `𝒢^τ[F] = Div g*(μ^{t-τ}M^*∇F)`) on `[0,t]` in the distributional sense with `F(0) = φ`, in the
integrated weak form against `ψ ∈ C_c^∞(ℝ^d)` (see the module docstring); every pairing is absolutely convergent and the
time integrand is integrable. -/
structure IsForwardSolutionRd (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) (F : ℝ → Euc d → ℝ) : Prop where
  integrable_x : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Set.Icc (0 : ℝ) t,
    Integrable (fun x => F σ x * ψ x) ∧ Integrable (fun x => F σ x * Laplacian.laplacian ψ x) ∧
    Integrable (fun x => F σ x * movDiv (fun y => ψ y • C.drift (t - σ) y) x) ∧
    Integrable (fun x => F σ x * nonlocalTestRd C (t - σ) ψ x)
  integrable_σ : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
    IntegrableOn (fun σ => forwardWeakTerm C t F ψ σ) (Set.Icc (0 : ℝ) t)
  eq : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ τ ∈ Set.Icc (0 : ℝ) t,
    ∫ x, F τ x * ψ x = (∫ x, φ x * ψ x) + ∫ σ in Set.Icc (0 : ℝ) τ, forwardWeakTerm C t F ψ σ

/-- The solution class of `B:thm:adjoint-rd`: `F ∈ L^∞([0,t]; H^m_uloc) ∩ C([0,t]; H^{m'}_loc)`, `m' < m`, solving
`B:eq:adjoint-forward` (`IsForwardSolutionRd`).  `L^∞H^m_uloc`: `‖F(τ)‖_{H^m_uloc} ≤ B` for all `τ ∈ [0,t]`;
`C([0,t];H^{m'}_loc)`: for every `z` the map `τ ↦ χ(·-z)F(τ)` is continuous into `H^{m'}(ℝ^d)`. -/
structure IsUlocSolutionRd (χ : Euc d → ℝ) (m : ℕ) (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ)
    (F : ℝ → Euc d → ℝ) : Prop where
  sol : IsForwardSolutionRd C t φ F
  bounded : ∃ B : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) t, ulocNormE m χ (F τ) ≤ ENNReal.ofReal B
  cont : ∀ m' : ℝ, m' < m → ∀ z : Euc d, ∀ τ₀ ∈ Set.Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) t, |τ - τ₀| < δ →
      sobolevNormE m' (fun x => χ (x - z) * (F τ x - F τ₀ x)) ≤ ENNReal.ofReal ε

/-- The `H^m(ℝ^d)` inner product `⟨u,v⟩_{H^m} = Re ∫ (1+4π²|ξ|²)^m û \bar{v̂} dξ`. -/
def sobolevInnerRd (m : ℕ) (u v : Euc d → ℝ) : ℝ :=
  HRS.PDE.ToolboxRd.symbolForm (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ)) u v

/-! ### Proposition S.A.12 -/

/-- Proposition S.A.12 `B:thm:adjoint-rd` (S L10089-10109), existence, uniqueness and bound.  Let `0 ≤ s < d`, `m ≥ 1`,
assume `B:eq:coeff-hypothesis-rd` (`AdjointRdData`, level `m`: `μ` is `(m+3,Λ)`-regular with the decay of
`S:eq:mf-regularity-whole`, `V` with `m_V = m+3`, `ν = β⁻¹ ∈ [0,ν̄]`), and one of the regimes R1, R2a, R2c, R3
(`RdRegimeHolds`).  There is `C` (depending on `d, s, m, |M|, Λ, Λ_V, |∇V(0)|, ν̄, T`, the regime, the cutoff `χ`) such that for
every `t ∈ (0,T]` and `φ ∈ H^m_uloc` there is a unique `F ∈ L^∞([0,t];H^m_uloc) ∩ C([0,t];H^{m'}_loc)`, `m' < m`,
solving `B:eq:adjoint-forward`, and `‖F(τ)‖_{H^m_uloc} ≤ C e^{Λ_mτ}‖φ‖_{H^m_uloc}`, `Λ_m = lambdaM Rg C ν₀ θ`.
Technical hypotheses: none beyond the TeX (the uniqueness clause is within the solution class `IsUlocSolutionRd`). -/
theorem adjoint_rd (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → RdRegimeHolds Rg d s D.M D.invβ ν₀ →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, ulocNormE m χ φ < ⊤ →
        (∃ F : ℝ → Euc d → ℝ, IsUlocSolutionRd χ m (D.coeff μ) t φ F ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) t, ulocNormE m χ (F τ) ≤
            ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) *
              ulocNormE m χ φ) ∧
        ∀ F₁ F₂ : ℝ → Euc d → ℝ, IsUlocSolutionRd χ m (D.coeff μ) t φ F₁ →
          IsUlocSolutionRd χ m (D.coeff μ) t φ F₂ →
          ∀ τ ∈ Set.Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  sorry

/-- Proposition S.A.12(a) (S L10097-10100): if `m ≥ m_*`, `f^r = F(t-r)` is a classical adjoint solution in the sense of
`B:rem:def-adjoint-rd` (`IsClassicalAdjointW`, with the repaired growth condition on `∂_rf`, see the module docstring)
and `‖U^{r,t}φ‖_{C_b²} ≤ C e^{Λ_{m_*}(t-r)}‖φ‖_{H^{m_*}_uloc}`.  The constant `C` is chosen before `m` (it is that of level
`m_*`, so `Λ_{m_*}`; the `C_b²` norm is the project's sum convention `cbNorm`, equivalent to the max norm up to a factor).
Technical hypotheses: the terminal datum `φ` is a `C²` function (a representative; `H^{m_*}_uloc ⊂ C_b²`); the solution
`F` is the one of `adjoint_rd`.
SUSPECTED ISSUE: the literal TeX notion (bounded `∂_rf`) is false for confining drift, see the module docstring. -/
theorem adjoint_rd_classical (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, mStar d ≤ m → ∀ (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → RdRegimeHolds Rg d s D.M D.invβ ν₀ →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, ContDiff ℝ 2 φ → ulocNormE m χ φ < ⊤ →
        ∀ F : ℝ → Euc d → ℝ, IsUlocSolutionRd χ m (D.coeff μ) t φ F →
          (∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW (D.coeff μ) t φ f ∧
            ∀ r ∈ Set.Icc (0 : ℝ) t, f r =ᵐ[volume] F (t - r)) ∧
          ∀ r ∈ Set.Icc (0 : ℝ) t, MemCb 2 (propagatorW (D.coeff μ) r t φ) ∧
            cbNorm 2 (propagatorW (D.coeff μ) r t φ) ≤
              C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * (t - r)) *
                (ulocNormE (mStar d) χ φ).toReal := by
  sorry

/-- Proposition S.A.12(b) (S L10101): for plane waves (real and imaginary parts of `e_k = e^{2πik·x}`),
`‖U^{r,t}e_k‖_{H^m_uloc} ≤ C e^{Λ_m(t-r)}(1+|k|)^m`; the solution `F` with datum `cos(2πk·x)` resp. `sin(2πk·x)` satisfies
`‖F(τ)‖_{H^m_uloc} ≤ C e^{Λ_mτ}(1+|k|)^m`, `τ = t - r` (`C` independent of `k`).  The "corresponding bounded-derivative
estimates supplied by `B:lem:uloc-embedding`" are S.A.31 (not stated here). -/
theorem adjoint_rd_planewave (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → RdRegimeHolds Rg d s D.M D.invβ ν₀ →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ k : Euc d,
        ∀ φ : Euc d → ℝ, (φ = (fun x => Real.cos (2 * Real.pi * inner ℝ k x)) ∨
          φ = (fun x => Real.sin (2 * Real.pi * inner ℝ k x))) →
        ∀ F : ℝ → Euc d → ℝ, IsUlocSolutionRd χ m (D.coeff μ) t φ F →
          ∀ τ ∈ Set.Icc (0 : ℝ) t, ulocNormE m χ (F τ) ≤
            ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) *
              (1 + ‖k‖) ^ m) := by
  sorry

/-- Proposition S.A.12(c) (S L10102-10103): if `2(s+1) > d` and `φ ∈ H^m(ℝ^d)`, then `F ∈ C_w([0,t];H^m(ℝ^d))` and
`‖F(τ)‖_{H^m} ≤ e^{Λ_mτ}‖φ‖_{H^m}` (constant `1`, `Λ_m = lambdaM Rg C ν₀ θ`).  The sentence "without a moment cancellation
this conclusion is in general false when `2(s+1) ≤ d`" is `multipole_not_lp`. -/
theorem adjoint_rd_sobolev (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs : (d : ℝ) < 2 * (s + 1))
    (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → RdRegimeHolds Rg d s D.M D.invβ ν₀ →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) φ →
        ulocNormE m χ φ < ⊤ →
        ∀ F : ℝ → Euc d → ℝ, IsUlocSolutionRd χ m (D.coeff μ) t φ F →
          (∀ τ ∈ Set.Icc (0 : ℝ) t, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (F τ)) ∧
          (∀ h : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) h →
            ContinuousOn (fun τ => sobolevInnerRd m (F τ) h) (Set.Icc (0 : ℝ) t)) ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) t, Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (F τ)) ≤
            Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) *
              Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) φ) := by
  sorry

/-- Proposition S.A.12(d) (S L10103): the stability estimate `B:eq:propagator-stability` holds both in `H^m_uloc` and in
`H^m(ϖ)`, with the coefficient distance augmented by the weighted `C^{m+2}` distance of `S:eq:mf-regularity-whole`.
For `a ∈ {1,2}` let `(ν_a, μ_a)` satisfy `B:eq:coeff-hypothesis-rd` at level `m+2` with a common regime and common
constants and the same confinement `(M, V)`; for `F_a` the solutions with datum `φ ∈ H^{m+2}_uloc` and `δ ≥ 0` bounding
`sup_{r ≤ T}‖μ_1^r - μ_2^r‖` in the coefficient norm `coeffNormE` (`C_b^{m+2}` + weighted `C^{m+2}` (+ the fractional
force bound when `s ≥ d-1`)),
`‖F_1(τ) - F_2(τ)‖_{H^m_uloc} ≤ C τ e^{Λ_{m+2}τ}(|ν_1-ν_2| + δ)‖φ‖_{H^{m+2}_uloc}` and the same in `H^m(ϖ)` with
`‖φ‖_{H^{m+2}(ϖ)}`, `0 ≤ τ ≤ t`, `Λ_{m+2} = lambdaM Rg C' ν₀ θ`.
AMBIGUITY: the exact form of the coefficient norm "augmented by the weighted distance" (S L10103) and of the weighted
norm `H^m(ϖ)` (`varpiNormE`, an equivalent norm). -/
theorem adjoint_rd_stability (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ (D₁ D₂ : WholeDyn d) (ν₀ : ℝ) (μ₁ μ₂ : ℝ → Euc d → ℝ),
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₁ T μ₁ →
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₂ T μ₂ →
      RdRegimeHolds Rg d s D₁.M D₁.invβ ν₀ → RdRegimeHolds Rg d s D₂.M D₂.invβ ν₀ →
      D₁.M = D₂.M → D₁.V = D₂.V →
      ∀ δ : ℝ, 0 ≤ δ → (∀ r ∈ Set.Icc (0 : ℝ) T, coeffNormE d s m (μ₁ r - μ₂ r) ≤ ENNReal.ofReal δ) →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, ulocNormE (m + 2) χ φ < ⊤ →
      ∀ F₁ F₂ : ℝ → Euc d → ℝ,
        IsUlocSolutionRd χ (m + 2) (D₁.coeff μ₁) t φ F₁ →
        IsUlocSolutionRd χ (m + 2) (D₂.coeff μ₂) t φ F₂ →
        ∀ τ ∈ Set.Icc (0 : ℝ) t,
          ulocNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤
            ENNReal.ofReal (C * τ * Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) * τ) *
              (|D₁.invβ - D₂.invβ| + δ)) * ulocNormE (m + 2) χ φ ∧
          varpiNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤
            ENNReal.ofReal (C * τ * Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) * τ) *
              (|D₁.invβ - D₂.invβ| + δ)) * varpiNormE (m + 2) χ φ := by
  sorry

/-- Proposition S.A.12(e) (S L10104-10106): for `ϖ(x) = ⟨x⟩^{-(d+3)}`,
`‖F(τ)‖_{H^m(ϖ)} ≤ C e^{Λ_mτ}‖φ‖_{H^m(ϖ)}` (for the solution of `adjoint_rd`, `φ ∈ H^m_uloc`). -/
theorem adjoint_rd_weighted (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → RdRegimeHolds Rg d s D.M D.invβ ν₀ →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, ulocNormE m χ φ < ⊤ →
        ∀ F : ℝ → Euc d → ℝ, IsUlocSolutionRd χ m (D.coeff μ) t φ F →
          ∀ τ ∈ Set.Icc (0 : ℝ) t, varpiNormE m χ (F τ) ≤
            ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) *
              varpiNormE m χ φ := by
  sorry


/-! ### Remark S.A.13 -/

/-- Remark S.A.13 `B:rem:def-adjoint-rd` (S L10111-10113): "a classical adjoint solution on `ℝ^d` means that `f, ∇f, ∇²f` and `∂_rf`
are bounded and continuous, with local `C²` continuity in time.  This is sufficient for `B:prop:duality-identity`".  The notion
is `HRS.Whole.IsClassicalAdjointW` (SUSPECTED ISSUE: the literal "bounded `∂_rf`" is false for confining drift; the repository
notion asks linear growth, see the module docstring).  The checkable claim is that this notion suffices for the whole-space
duality identity `B:eq:duality-identity` (`DualityIdentityRd`): for a selected flow (A.1) and a mean-field solution that is
`(3,Λ)`-regular (with the proviso for `s ≥ d-1`) with `V` having bounded second derivatives, and every classical adjoint
solution `f` on `[0,t]`, the identity holds for every Brownian-filtration data `(ℱ, W')` of the flow.  (The sentence "the
second-moment bound gives uniform tightness of `μ^r`" is prose.) -/
theorem duality_identity_rd {N : ℕ} (s Λ T ΛV G₀ : ℝ) (D : WholeDyn d) (hs : D.s = s) (hs0 : 0 ≤ s) (hsd : s < d) (hinv : 0 ≤ D.invβ)
    (hV : VHypRd 2 ΛV G₀ D.V) (ρ : ℝ → Euc d → ℝ) (hρ : IsWholeMeanFieldSolution D T ρ)
    (hreg : IsRegularMFRd s 3 Λ T ρ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hflow : SelectedFlowRd P D T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ)
    (hf : IsClassicalAdjointW (D.coeff ρ) t φ f) :
    DualityIdentityRd P ℱ W' D ρ X t f := by
  sorry

/-! ### Proposition S.A.14 -/

/-! ### Helpers for Proposition S.A.14 (`q09_` prefix): derivatives of the Riesz kernel -/

section Q09Helpers

open scoped RealInnerProductSpace

theorem q09_norm_rpow_hasFDerivAt {z : Euc d} (hz : z ≠ 0) (p : ℝ) :
    HasFDerivAt (fun x : Euc d => ‖x‖ ^ p) ((p * ‖z‖ ^ (p - 2)) • innerSL ℝ z) z := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert! (hasStrictFDerivAt_norm_sq z).rpow_const (p := p / 2) (by simp [hz]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

theorem q09_gradient_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (f : EuclideanSpace ℝ ι → ℝ)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    gradient f x i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  unfold gradient
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ ι)
    (x := EuclideanSpace.single i 1) (y := fderiv ℝ f x)
  rw [← h, EuclideanSpace.inner_single_right]
  simp

def q09_c (s : ℝ) : ℝ := if s = 0 then -1 else -s

theorem q09_rk_hasFDerivAt (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    HasFDerivAt (rieszKernel d s) ((q09_c s * ‖z‖ ^ (-s - 2)) • innerSL ℝ z) z := by
  by_cases h0 : s = 0
  · subst h0
    have hk : rieszKernel d 0 = fun x : Euc d => -Real.log ‖x‖ := by
      funext x; simp [rieszKernel]
    have h1 := q09_norm_rpow_hasFDerivAt hz 1
    simp only [Real.rpow_one] at h1
    have hn : HasFDerivAt (fun x : Euc d => ‖x‖) ((‖z‖⁻¹) • innerSL ℝ z) z := by
      convert h1 using 2
      rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one, one_mul]
    have hl : HasFDerivAt (fun x : Euc d => -Real.log ‖x‖) (-(‖z‖⁻¹ • ‖z‖⁻¹ • innerSL ℝ z)) z :=
      (hn.log (norm_ne_zero_iff.2 hz)).neg
    rw [hk]
    refine hl.congr_fderiv ?_
    have hc : q09_c 0 = -1 := by simp [q09_c]
    rw [hc, show (-(0:ℝ) - 2) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (norm_nonneg _),
      Real.rpow_natCast, smul_smul, ← neg_smul]
    congr 1
    ring
  · have hk : rieszKernel d s = fun x : Euc d => ‖x‖ ^ (-s) := by
      funext x; simp [rieszKernel, h0]
    rw [hk]
    refine (q09_norm_rpow_hasFDerivAt hz (-s)).congr_fderiv ?_
    simp [q09_c, h0]

/-- The scalar `H_i(z) = c_s ‖z‖^{-s-2} z_i`, the `i`-th coordinate of the force `∇g`. -/
def q09_H (s : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  q09_c s * (‖z‖ ^ (-s - 2) * z i)

theorem q09_H_eq_fderiv (s : ℝ) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single i 1) = q09_H s i z := by
  rw [(q09_rk_hasFDerivAt s hz).fderiv]
  simp [q09_H, EuclideanSpace.inner_single_right, innerSL_apply_apply]
  ring

/-- The derivative of `H_i` at `z ≠ 0`. -/
def q09_DH (s : ℝ) (i : Fin d) (z : Euc d) : Euc d →L[ℝ] ℝ :=
  q09_c s • (‖z‖ ^ (-s - 2) • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) +
    (z i * ((-s - 2) * ‖z‖ ^ (-s - 2 - 2))) • innerSL ℝ z)

theorem q09_H_hasFDerivAt (s : ℝ) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    HasFDerivAt (q09_H s i) (q09_DH s i z) z := by
  have h1 := q09_norm_rpow_hasFDerivAt hz (-s - 2)
  have h2 : HasFDerivAt (fun x : Euc d => x i) (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) z :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt
  have h3 := (h1.mul h2).const_mul (q09_c s)
  unfold q09_DH q09_H
  convert h3 using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul,
    innerSL_apply_apply]
  ring

theorem q09_DH_norm_le (s : ℝ) (i : Fin d) {ξ : Euc d} (hξ : ξ ≠ 0) :
    ‖q09_DH s i ξ‖ ≤ |q09_c s| * (1 + |-s - 2|) * ‖ξ‖ ^ (-s - 2) := by
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have key : ‖ξ‖ ^ (-s - 2 - 2) * ‖ξ‖ ^ 2 = ‖ξ‖ ^ (-s - 2) := by
    rw [Real.rpow_sub hpos, Real.rpow_two]
    field_simp
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv1 : |v i| ≤ ‖v‖ := by
    have := PiLp.norm_apply_le v i
    simpa [Real.norm_eq_abs] using this
  have hξ1 : |ξ i| ≤ ‖ξ‖ := by
    have := PiLp.norm_apply_le ξ i
    simpa [Real.norm_eq_abs] using this
  have hip : |inner ℝ ξ v| ≤ ‖ξ‖ * ‖v‖ := abs_real_inner_le_norm ξ v
  have hA : 0 < ‖ξ‖ ^ (-s - 2) := Real.rpow_pos_of_pos hpos _
  have hB : 0 < ‖ξ‖ ^ (-s - 2 - 2) := Real.rpow_pos_of_pos hpos _
  set A := ‖ξ‖ ^ (-s - 2) with hAdef
  set B := ‖ξ‖ ^ (-s - 2 - 2) with hBdef
  set p := -s - 2 with hp
  have expand : q09_DH s i ξ v = q09_c s * (A * v i + (ξ i * (p * B)) * inner ℝ ξ v) := by
    simp [q09_DH, innerSL_apply_apply, hAdef, hBdef, hp]
    ring
  rw [expand, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hterm : |A * v i + (ξ i * (p * B)) * inner ℝ ξ v| ≤ A * ‖v‖ + |p| * A * ‖v‖ := by
    have h1 : |A * v i| ≤ A * ‖v‖ := by
      rw [abs_mul, abs_of_pos hA]; exact mul_le_mul_of_nonneg_left hv1 hA.le
    have h2 : |(ξ i * (p * B)) * inner ℝ ξ v| ≤ |p| * A * ‖v‖ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hB]
      have hpB : |p| * B = |p| * B := rfl
      calc |ξ i| * (|p| * B) * |inner ℝ ξ v| ≤ ‖ξ‖ * (|p| * B) * (‖ξ‖ * ‖v‖) := by
            gcongr
        _ = |p| * (B * ‖ξ‖ ^ 2) * ‖v‖ := by ring
        _ = |p| * A * ‖v‖ := by rw [key]
    calc |A * v i + (ξ i * (p * B)) * inner ℝ ξ v|
        ≤ |A * v i| + |(ξ i * (p * B)) * inner ℝ ξ v| := abs_add_le _ _
      _ ≤ A * ‖v‖ + |p| * A * ‖v‖ := add_le_add h1 h2
  have hfin : |q09_c s| * |A * v i + (ξ i * (p * B)) * inner ℝ ξ v| ≤
      |q09_c s| * (1 + |p|) * A * ‖v‖ := by
    have := mul_le_mul_of_nonneg_left hterm (abs_nonneg (q09_c s))
    nlinarith [this]
  calc |q09_c s| * |A * v i + (ξ i * (p * B)) * inner ℝ ξ v|
      ≤ |q09_c s| * (1 + |p|) * A * ‖v‖ := hfin
    _ = (|q09_c s| * (1 + |p|) * A) * ‖v‖ := by ring


theorem q09_H_diff_le (s : ℝ) (hs0 : 0 ≤ s) (i : Fin d) {x y : Euc d} (hx : x ≠ 0)
    (hy : ‖y‖ ≤ ‖x‖ / 2) :
    |q09_H s i (x - y) - q09_H s i x| ≤
      |q09_c s| * (1 + |-s - 2|) * (‖x‖ / 2) ^ (-s - 2) * ‖y‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hp : -s - 2 ≤ 0 := by linarith
  set S : Set (Euc d) := Metric.closedBall x (‖x‖ / 2) with hSdef
  have hS : Convex ℝ S := convex_closedBall _ _
  have hmem : ∀ ξ ∈ S, ‖x‖ / 2 ≤ ‖ξ‖ := by
    intro ξ hξ
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm] at hξ
    have h1 : ‖x‖ ≤ ‖x - ξ‖ + ‖ξ‖ := by
      have := norm_add_le (x - ξ) ξ
      simpa using this
    have h2 : ‖x - ξ‖ = ‖ξ - x‖ := norm_sub_rev _ _
    linarith
  have hne : ∀ ξ ∈ S, ξ ≠ 0 := by
    intro ξ hξ h0
    have := hmem ξ hξ
    rw [h0, norm_zero] at this
    linarith
  have hd : ∀ ξ ∈ S, HasFDerivWithinAt (q09_H s i) (q09_DH s i ξ) S ξ :=
    fun ξ hξ => (q09_H_hasFDerivAt s i (hne ξ hξ)).hasFDerivWithinAt
  have hb : ∀ ξ ∈ S, ‖q09_DH s i ξ‖ ≤
      |q09_c s| * (1 + |-s - 2|) * (‖x‖ / 2) ^ (-s - 2) := by
    intro ξ hξ
    have h1 := q09_DH_norm_le s i (hne ξ hξ)
    have h2 : ‖ξ‖ ^ (-s - 2) ≤ (‖x‖ / 2) ^ (-s - 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hmem ξ hξ) hp
    have h3 : 0 ≤ |q09_c s| * (1 + |-s - 2|) := by positivity
    calc ‖q09_DH s i ξ‖ ≤ |q09_c s| * (1 + |-s - 2|) * ‖ξ‖ ^ (-s - 2) := h1
      _ ≤ |q09_c s| * (1 + |-s - 2|) * (‖x‖ / 2) ^ (-s - 2) := mul_le_mul_of_nonneg_left h2 h3
  have hxS : x ∈ S := Metric.mem_closedBall_self (by positivity)
  have hyS : x - y ∈ S := by
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    have : x - y - x = -y := by abel
    rw [this, norm_neg]; exact hy
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb hS hxS hyS
  have e : x - y - x = -y := by abel
  rw [e, norm_neg, Real.norm_eq_abs] at key
  exact key


theorem q09_conv_grad (K F : Euc d → ℝ) (hK : LocallyIntegrable K volume)
    (hF : HasCompactSupport F) (hFc : ContDiff ℝ 1 F) (x : Euc d) (i : Fin d) :
    gradient (convFun K F) x i = ∫ t, fderiv ℝ F t (EuclideanSpace.single i 1) * K (x - t) := by
  have hconv : convFun K F = convolution F K (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext y
    simp only [convFun, convolution_def, ContinuousLinearMap.mul_apply']
    congr 1
    funext t
    ring
  have hd := hF.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hFc hK x
  have hint := ((hF.fderiv ℝ).convolutionExists_left
    (ContinuousLinearMap.precompL (Euc d) (ContinuousLinearMap.mul ℝ ℝ))
    (hFc.continuous_fderiv one_ne_zero) hK) x
  rw [hconv, q09_gradient_apply, hd.fderiv, convolution_def,
    ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.mul_apply']


theorem q09_integrable_of_zero_outside {φ : Euc d → ℝ} {S : Set (Euc d)} (hS : IsCompact S)
    (hc : ContinuousOn φ S) (h0 : ∀ t, t ∉ S → φ t = 0) : Integrable φ volume := by
  have hEq : φ = S.indicator φ := by
    funext t
    by_cases ht : t ∈ S
    · simp [ht]
    · simp [ht, h0 t ht]
  rw [hEq]
  exact (integrable_indicator_iff hS.measurableSet).2 (hc.integrableOn_compact hS)

theorem q09_ibp (s : ℝ) (i : Fin d) (F : Euc d → ℝ) (hF : HasCompactSupport F)
    (hFc : ContDiff ℝ 1 F) (R0 : ℝ) (hR0 : 1 ≤ R0)
    (hsupp : tsupport F ⊆ Metric.closedBall 0 R0) (x : Euc d) (hx : 2 * R0 ≤ ‖x‖) :
    ∫ t, fderiv ℝ F t (EuclideanSpace.single i 1) * rieszKernel d s (x - t) =
      ∫ t, q09_H s i (x - t) * F t := by
  have hbd : ∀ t ∈ tsupport F, R0 ≤ ‖x - t‖ := by
    intro t ht
    have h1 : ‖t‖ ≤ R0 := by
      have := hsupp ht
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have h2 := norm_sub_norm_le x t
    linarith
  have hne : ∀ t ∈ tsupport F, x - t ≠ 0 := by
    intro t ht h0
    have := hbd t ht
    rw [h0, norm_zero] at this
    linarith
  have hK' : ∀ z : Euc d, z ≠ 0 → HasFDerivAt (rieszKernel d s) (fderiv ℝ (rieszKernel d s) z) z :=
    fun z hz => (q09_rk_hasFDerivAt s hz).differentiableAt.hasFDerivAt
  have hdiff : ∀ t ∈ tsupport F, DifferentiableAt ℝ (fun t => rieszKernel d s (x - t)) t := by
    intro t ht
    have h := (hK' _ (hne t ht)).comp t ((hasFDerivAt_const x t).sub (hasFDerivAt_id t))
    exact h.differentiableAt
  have hdu : ∀ t ∈ tsupport F,
      fderiv ℝ (fun t => rieszKernel d s (x - t)) t (EuclideanSpace.single i 1) =
        -(q09_H s i (x - t)) := by
    intro t ht
    have h : HasFDerivAt (fun t => rieszKernel d s (x - t))
        ((fderiv ℝ (rieszKernel d s) (x - t)).comp (0 - ContinuousLinearMap.id ℝ (Euc d))) t :=
      (hK' _ (hne t ht)).comp t ((hasFDerivAt_const x t).sub (hasFDerivAt_id t))
    rw [h.fderiv]
    simp [q09_H_eq_fderiv s i (hne t ht)]
  have hKc : ContinuousOn (fun t => rieszKernel d s (x - t)) (tsupport F) := by
    intro t ht
    exact ((hK' _ (hne t ht)).continuousAt.comp (f := fun t : Euc d => x - t)
      (by fun_prop)).continuousWithinAt
  have hHc : ContinuousOn (fun t => q09_H s i (x - t)) (tsupport F) := by
    intro t ht
    exact ((q09_H_hasFDerivAt s i (hne t ht)).continuousAt.comp (f := fun t : Euc d => x - t)
      (by fun_prop)).continuousWithinAt
  have hFcont : Continuous (fun t => fderiv ℝ F t (EuclideanSpace.single i 1)) :=
    (hFc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfd0 : ∀ t, t ∉ tsupport F → fderiv ℝ F t = 0 := by
    intro t ht
    by_contra h
    exact ht ((support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 h))
  have hF0 : ∀ t, t ∉ tsupport F → F t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport ht
  have hi2 : Integrable (fun t => rieszKernel d s (x - t) *
      fderiv ℝ F t (EuclideanSpace.single i 1)) volume := by
    apply q09_integrable_of_zero_outside hF.isCompact
    · exact hKc.mul hFcont.continuousOn
    · intro t ht; simp [hfd0 t ht]
  have hi3 : Integrable (fun t => rieszKernel d s (x - t) * F t) volume := by
    apply q09_integrable_of_zero_outside hF.isCompact
    · exact hKc.mul hFc.continuous.continuousOn
    · intro t ht; simp [hF0 t ht]
  have hpt : ∀ t, fderiv ℝ (fun t => rieszKernel d s (x - t)) t (EuclideanSpace.single i 1) * F t
      = -(q09_H s i (x - t) * F t) := by
    intro t
    by_cases ht : t ∈ tsupport F
    · rw [hdu t ht]; ring
    · rw [hF0 t ht]; simp
  have hi1 : Integrable (fun t => fderiv ℝ (fun t => rieszKernel d s (x - t)) t
      (EuclideanSpace.single i 1) * F t) volume := by
    have : (fun t => fderiv ℝ (fun t => rieszKernel d s (x - t)) t
        (EuclideanSpace.single i 1) * F t) = fun t => -(q09_H s i (x - t) * F t) :=
      funext hpt
    rw [this]
    apply Integrable.neg
    apply q09_integrable_of_zero_outside hF.isCompact
    · exact hHc.mul hFc.continuous.continuousOn
    · intro t ht; simp [hF0 t ht]
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun t => rieszKernel d s (x - t)) (g := F) (v := EuclideanSpace.single i 1)
    hi1 hi2 hi3 (fun t ht => hdiff t ht) (fun t _ => (hFc.differentiable (by norm_num)) t)
  calc ∫ t, fderiv ℝ F t (EuclideanSpace.single i 1) * rieszKernel d s (x - t)
      = ∫ t, rieszKernel d s (x - t) * fderiv ℝ F t (EuclideanSpace.single i 1) := by
        congr 1; funext t; ring
    _ = -∫ t, fderiv ℝ (fun t => rieszKernel d s (x - t)) t (EuclideanSpace.single i 1) * F t :=
        hIBP
    _ = -∫ t, -(q09_H s i (x - t) * F t) := by
        congr 1; exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ t, q09_H s i (x - t) * F t := by
        rw [integral_neg, neg_neg]


theorem q09_int_H (s : ℝ) (i : Fin d) (F : Euc d → ℝ) (hF : HasCompactSupport F)
    (hFc : ContDiff ℝ 1 F) (R0 : ℝ) (hR0 : 1 ≤ R0)
    (hsupp : tsupport F ⊆ Metric.closedBall 0 R0) (x : Euc d) (hx : 2 * R0 ≤ ‖x‖) :
    Integrable (fun t => q09_H s i (x - t) * F t) volume := by
  have hbd : ∀ t ∈ tsupport F, R0 ≤ ‖x - t‖ := by
    intro t ht
    have h1 : ‖t‖ ≤ R0 := by
      have := hsupp ht
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have h2 := norm_sub_norm_le x t
    linarith
  have hne : ∀ t ∈ tsupport F, x - t ≠ 0 := by
    intro t ht h0
    have := hbd t ht
    rw [h0, norm_zero] at this
    linarith
  have hHc : ContinuousOn (fun t => q09_H s i (x - t)) (tsupport F) := by
    intro t ht
    exact ((q09_H_hasFDerivAt s i (hne t ht)).continuousAt.comp (f := fun t : Euc d => x - t)
      (by fun_prop)).continuousWithinAt
  apply q09_integrable_of_zero_outside hF.isCompact
  · exact hHc.mul hFc.continuous.continuousOn
  · intro t ht; simp [image_eq_zero_of_notMem_tsupport ht]

theorem q09_multipole (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) (F : Euc d → ℝ)
    (hF : HasCompactSupport F) (hFc : ContDiff ℝ 1 F) (x : Euc d) (hx0 : x ≠ 0) (R1 : ℝ)
    (hR1 : 1 ≤ R1) (hsupp : tsupport F ⊆ Metric.closedBall 0 R1) (hx : 2 * R1 ≤ ‖x‖) :
    |gradient (convFun (rieszKernel d s) F) x i - (∫ y, F y) * rieszKernelGrad d s x i| ≤
      |q09_c s| * (1 + |-s - 2|) * R1 * (∫ t, |F t|) / 2 ^ (-s - 2) * ‖x‖ ^ (-s - 2) := by
  have hloc := rieszKernel_locallyIntegrable hs0 hsd
  have hFint : Integrable F volume := hFc.continuous.integrable_of_hasCompactSupport hF
  have hIH := q09_int_H s i F hF hFc R1 hR1 hsupp x hx
  have hIC : Integrable (fun t => q09_H s i x * F t) volume := hFint.const_mul _
  have hCb : 0 ≤ |q09_c s| * (1 + |-s - 2|) * (‖x‖ / 2) ^ (-s - 2) := by positivity
  rw [q09_conv_grad (rieszKernel d s) F hloc hF hFc x i, rieszKernelGrad, q09_gradient_apply,
    q09_H_eq_fderiv s i hx0, q09_ibp s i F hF hFc R1 hR1 hsupp x hx]
  have e1 : (∫ y, F y) * q09_H s i x = ∫ t, q09_H s i x * F t := by
    rw [integral_const_mul, mul_comm]
  rw [e1, ← integral_sub hIH hIC, ← Real.norm_eq_abs]
  have hbound : ∀ t, ‖q09_H s i (x - t) * F t - q09_H s i x * F t‖ ≤
      (|q09_c s| * (1 + |-s - 2|) * (‖x‖ / 2) ^ (-s - 2) * R1) * |F t| := by
    intro t
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    by_cases ht : t ∈ tsupport F
    · have ht1 : ‖t‖ ≤ R1 := by
        have := hsupp ht
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      have hy : ‖t‖ ≤ ‖x‖ / 2 := by linarith
      have hd := q09_H_diff_le s hs0 i hx0 hy
      have hmul : |q09_c s| * (1 + |-s - 2|) * (‖x‖ / 2) ^ (-s - 2) * ‖t‖ ≤
          |q09_c s| * (1 + |-s - 2|) * (‖x‖ / 2) ^ (-s - 2) * R1 :=
        mul_le_mul_of_nonneg_left ht1 hCb
      exact mul_le_mul_of_nonneg_right (le_trans hd hmul) (abs_nonneg _)
    · have h0 : F t = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [h0]
  refine (norm_integral_le_of_norm_le (g := fun t => (|q09_c s| * (1 + |-s - 2|) *
    (‖x‖ / 2) ^ (-s - 2) * R1) * |F t|) (hFint.abs.const_mul _)
    (Filter.Eventually.of_forall hbound)).trans ?_
  rw [integral_const_mul, Real.div_rpow (norm_nonneg x) (by norm_num : (0:ℝ) ≤ 2)]
  apply le_of_eq
  ring

end Q09Helpers

/-- Proposition S.A.14 `B:prop:low-frequency-obstruction` (S L10115-10121), the multipole expansion: for `a, ψ ∈ C_c^∞(ℝ^d)`
with `m_0 = ∫aψ ≠ 0`, `∂_i g*(aψ)(x) = m_0 ∂_ig(x) + O(|x|^{-s-2})` as `|x| → ∞` (`g = rieszKernel d s`, `∂_ig =
rieszKernelGrad d s · i`; the convolution is the plain integral, absolutely convergent as `∂_ig` is locally integrable
for `s < d - 1`; for `d-1 ≤ s < d` it is the integral of the compactly supported `aψ` against `∂_ig`, which is read
as the convention-free integral when it converges; the `O` is stated for `|x| ≥ R`).  (Technical: `0 ≤ s < d`, `d ≥ 1`.) -/
theorem multipole_tail (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d)
    (a ψ : Euc d → ℝ) (ha : IsCcInfty a) (hψ : IsCcInfty ψ) (hm0 : ∫ x, a x * ψ x ≠ 0) :
    ∃ C R : ℝ, 0 < R ∧ ∀ x : Euc d, R ≤ ‖x‖ →
      |gradient (convFun (rieszKernel d s) (fun y => a y * ψ y)) x i -
          (∫ y, a y * ψ y) * rieszKernelGrad d s x i| ≤ C * ‖x‖ ^ (-s - 2) := by
  have hFs : HasCompactSupport (fun y => a y * ψ y) := ha.2.mul_right
  have hFc : ContDiff ℝ 1 (fun y => a y * ψ y) :=
    (ha.1.mul hψ.1).of_le (by exact_mod_cast le_top)
  obtain ⟨R0, hR0⟩ := hFs.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hsupp : tsupport (fun y => a y * ψ y) ⊆ Metric.closedBall 0 (max R0 1) :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR1 : 1 ≤ max R0 1 := le_max_right _ _
  refine ⟨|q09_c s| * (1 + |-s - 2|) * max R0 1 * (∫ t, |a t * ψ t|) / 2 ^ (-s - 2),
    2 * max R0 1, by linarith, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    linarith
  exact q09_multipole s hs0 hsd i _ hFs hFc x hx0 (max R0 1) hR1 hsupp hx

/-- The coordinate formula of `rieszKernelGrad` away from `0`. -/
theorem q09_rkg_eq (s : ℝ) (i : Fin d) {x : Euc d} (hx : x ≠ 0) :
    rieszKernelGrad d s x i = q09_H s i x := by
  unfold rieszKernelGrad
  rw [q09_gradient_apply, q09_H_eq_fderiv s i hx]

theorem q09_c_ne (s : ℝ) (hs0 : 0 ≤ s) : q09_c s ≠ 0 := by
  unfold q09_c
  split_ifs with h
  · norm_num
  · exact neg_ne_zero.2 h

/-- Far out on the cone `x_i ≥ ‖x‖/2`, the leading term forces `|G x| ≥ κ ‖x‖^{-s-1}`. -/
theorem q09_cone_lower (s : ℝ) (hs0 : 0 ≤ s) (i : Fin d) (m0 C R0 : ℝ) (G : Euc d → ℝ)
    (hm0 : m0 ≠ 0)
    (hG : ∀ x : Euc d, R0 ≤ ‖x‖ → |G x - m0 * rieszKernelGrad d s x i| ≤ C * ‖x‖ ^ (-s - 2))
    (x : Euc d) (hx : x ≠ 0)
    (hxR : max R0 (C / (|m0| * |q09_c s| / 4)) ≤ ‖x‖) (hcone : ‖x‖ / 2 ≤ x i) :
    (|m0| * |q09_c s| / 4) * ‖x‖ ^ (-s - 1) ≤ |G x| := by
  have hc : q09_c s ≠ 0 := q09_c_ne s hs0
  have hm0' : 0 < |m0| := abs_pos.2 hm0
  have hc' : 0 < |q09_c s| := abs_pos.2 hc
  set κ := |m0| * |q09_c s| / 4 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hu : 0 < ‖x‖ ^ (-s - 2) := Real.rpow_pos_of_pos hxpos _
  have hbd := hG x (le_trans (le_max_left _ _) hxR)
  have hCκ : C ≤ κ * ‖x‖ := by
    have h1 : C / κ ≤ ‖x‖ := le_trans (le_max_right _ _) hxR
    have := (div_le_iff₀ hκ).1 h1
    linarith [mul_comm κ ‖x‖]
  have hH : |m0 * rieszKernelGrad d s x i| =
      |m0| * |q09_c s| * ‖x‖ ^ (-s - 2) * |x i| := by
    rw [q09_rkg_eq s i hx]
    unfold q09_H
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hu]
    ring
  have hxi : ‖x‖ / 2 ≤ |x i| := le_trans hcone (le_abs_self _)
  have hlow : 2 * κ * ‖x‖ ^ (-s - 2) * ‖x‖ ≤ |m0 * rieszKernelGrad d s x i| := by
    rw [hH]
    have hpos : 0 ≤ |m0| * |q09_c s| * ‖x‖ ^ (-s - 2) := by positivity
    have := mul_le_mul_of_nonneg_left hxi hpos
    rw [hκdef]
    nlinarith [this]
  have htri : |m0 * rieszKernelGrad d s x i| - |G x - m0 * rieszKernelGrad d s x i| ≤ |G x| := by
    have := abs_sub_abs_le_abs_sub (m0 * rieszKernelGrad d s x i) (G x)
    rw [abs_sub_comm] at this
    linarith
  have hCu : C * ‖x‖ ^ (-s - 2) ≤ κ * ‖x‖ * ‖x‖ ^ (-s - 2) :=
    mul_le_mul_of_nonneg_right hCκ hu.le
  have hfin : κ * ‖x‖ ^ (-s - 2) * ‖x‖ ≤ |G x| := by nlinarith [hbd, hlow, hCu, htri]
  have e : ‖x‖ ^ (-s - 1) = ‖x‖ ^ (-s - 2) * ‖x‖ := by
    rw [show (-s - 1) = (-s - 2) + 1 by ring, Real.rpow_add_one hxpos.ne']
  rw [e]
  linarith [hfin]

/-- The ball `B(λ) = B(λ e_i, λ/4)`. -/
def q09_ball (i : Fin d) (lam : ℝ) : Set (Euc d) :=
  Metric.ball (EuclideanSpace.single i lam) (lam / 4)

theorem q09_ball_mem (i : Fin d) {lam : ℝ} (hlam : 0 < lam) {x : Euc d}
    (hx : x ∈ q09_ball i lam) :
    ‖x‖ ≤ 5 * lam / 4 ∧ 3 * lam / 4 ≤ ‖x‖ ∧ ‖x‖ / 2 ≤ x i := by
  unfold q09_ball at hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hc : ‖(EuclideanSpace.single i lam : Euc d)‖ = lam := by
    rw [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos hlam]
  have hci : (EuclideanSpace.single i lam : Euc d) i = lam := by
    simp
  have h1 : ‖x‖ ≤ ‖x - EuclideanSpace.single i lam‖ + ‖(EuclideanSpace.single i lam : Euc d)‖ := by
    have := norm_add_le (x - EuclideanSpace.single i lam) (EuclideanSpace.single i lam)
    rwa [sub_add_cancel] at this
  have h2 : ‖(EuclideanSpace.single i lam : Euc d)‖ - ‖x‖ ≤
      ‖(EuclideanSpace.single i lam : Euc d) - x‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev] at h2
  have h3 : |x i - lam| ≤ ‖x - EuclideanSpace.single i lam‖ := by
    have := PiLp.norm_apply_le (x - EuclideanSpace.single i lam) i
    rw [PiLp.sub_apply, hci, Real.norm_eq_abs] at this
    exact this
  have h4 := (abs_le.1 h3).1
  refine ⟨by linarith, by linarith, by linarith⟩

theorem q09_ball_disj (i : Fin d) {l1 l2 : ℝ} (hl1 : 0 < l1) (h12 : 2 * l1 ≤ l2) :
    Disjoint (q09_ball i l1) (q09_ball i l2) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have a1 := q09_ball_mem i hl1 hx1
  have a2 := q09_ball_mem i (lt_of_lt_of_le (by linarith) h12) hx2
  linarith [a1.1, a1.2.1, a2.2.1, a2.1]

/-- Proposition S.A.14, consequence (S L10118-10119): `∂_ig*(aψ) ∉ L^p(ℝ^d)` whenever `p(s+1) ≤ d` (`1 ≤ p < ∞`), for
`a, ψ ∈ C_c^∞` with `∫aψ ≠ 0` and some coordinate `i`.  ("In particular an unweighted `H^m` theory cannot hold for
arbitrary compactly supported data when `2(s+1) ≤ d`" is the case `p = 2`, a prose consequence for the adjoint theory.)
Statement: there is an `i` for which `∂_ig*(aψ) ∉ L^p` (the TeX asserts it for the cone `|x_i| ≥ |x|/2`, i.e. for every
`i`; we assert it for every `i`). -/
theorem multipole_not_lp (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d)
    (a ψ : Euc d → ℝ) (ha : IsCcInfty a) (hψ : IsCcInfty ψ) (hm0 : ∫ x, a x * ψ x ≠ 0)
    (p : ℝ) (hp : 1 ≤ p) (hps : p * (s + 1) ≤ d) :
    ¬ MemLp (fun x : Euc d => gradient (convFun (rieszKernel d s) (fun y => a y * ψ y)) x i) (ENNReal.ofReal p)
      volume := by
  intro hG
  obtain ⟨C, R, hR, hbd⟩ := multipole_tail hd s hs0 hsd i a ψ ha hψ hm0
  haveI : Nontrivial (Euc d) := by
    rw [← Module.finrank_pos_iff (R := ℝ), finrank_euclideanSpace_fin]
    exact hd
  set m0 := ∫ y, a y * ψ y with hm0def
  set G : Euc d → ℝ := fun x => gradient (convFun (rieszKernel d s) (fun y => a y * ψ y)) x i
    with hGdef
  have hc : q09_c s ≠ 0 := q09_c_ne s hs0
  have hm0' : 0 < |m0| := abs_pos.2 hm0
  have hc' : 0 < |q09_c s| := abs_pos.2 hc
  set κ := |m0| * |q09_c s| / 4 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; positivity
  set Rb := max R (C / κ) with hRbdef
  set L := max 1 (2 * |Rb|) with hLdef
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLRb : 4 * Rb / 3 ≤ L := by
    have h1 := le_abs_self Rb
    have h2 := abs_nonneg Rb
    have h3 : 2 * |Rb| ≤ L := le_max_right _ _
    linarith
  set p' := p with hp'def
  set V : ℝ := (volume (Metric.ball (0 : Euc d) 1)).toReal with hVdef
  have hVpos : 0 < V := by
    rw [hVdef]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne'
      measure_ball_lt_top.ne
  -- integrability of the power
  have hint : Integrable (fun x => ‖G x‖ ^ p) volume := by
    have h := hG.integrable_norm_rpow (ENNReal.ofReal_pos.2 (by linarith)).ne'
      ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal (by linarith)] at h
  -- the constant
  set e : ℝ := (-s - 1) * p with hedef
  set c0 : ℝ := κ ^ p * (5 / 4 : ℝ) ^ e * (1 / 4 : ℝ) ^ d * V with hc0def
  have hc0 : 0 < c0 := by
    rw [hc0def]
    have : 0 < (5 / 4 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) _
    have : 0 < (1 / 4 : ℝ) ^ d := pow_pos (by norm_num) _
    have : 0 < κ ^ p := Real.rpow_pos_of_pos hκ _
    positivity
  -- pointwise lower bound on the cone far out
  have hpt : ∀ (lam : ℝ), L ≤ lam → ∀ x ∈ q09_ball i lam,
      (κ * (5 * lam / 4) ^ ((-s - 1))) ^ p ≤ ‖G x‖ ^ p := by
    intro lam hlamL x hx
    have hlam : 0 < lam := lt_of_lt_of_le (by linarith) hlamL
    obtain ⟨h1, h2, h3⟩ := q09_ball_mem i hlam hx
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by linarith) h2
    have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
    have hxR : max R (C / κ) ≤ ‖x‖ := by
      have : Rb ≤ ‖x‖ := by
        have : Rb ≤ 3 * L / 4 := by linarith
        linarith
      exact this
    have hlow := q09_cone_lower s hs0 i m0 C R G hm0 hbd x hx0 hxR h3
    have hpow : (5 * lam / 4) ^ ((-s - 1)) ≤ ‖x‖ ^ ((-s - 1)) :=
      Real.rpow_le_rpow_of_nonpos hxpos h1 (by linarith)
    have ha0 : 0 ≤ κ * (5 * lam / 4) ^ ((-s - 1)) := by positivity
    have hle : κ * (5 * lam / 4) ^ ((-s - 1)) ≤ ‖G x‖ := by
      rw [Real.norm_eq_abs]
      have : κ * (5 * lam / 4) ^ ((-s - 1)) ≤ κ * ‖x‖ ^ ((-s - 1)) :=
        mul_le_mul_of_nonneg_left hpow hκ.le
      have hh : κ * ‖x‖ ^ ((-s - 1)) ≤ |G x| := hlow
      linarith
    exact Real.rpow_le_rpow ha0 hle (by linarith)
  -- lower bound on each ball
  have hball : ∀ k : ℕ, c0 ≤ ∫ x in q09_ball i (2 ^ k * L), ‖G x‖ ^ p := by
    intro k
    set lam : ℝ := 2 ^ k * L with hlamdef
    have hL0 : 0 < L := by linarith
    have hlamL : L ≤ lam := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      rw [hlamdef]; nlinarith
    have hlam1 : 1 ≤ lam := le_trans hL1 hlamL
    have hlam : 0 < lam := by linarith
    have hvol : volume.real (q09_ball i lam) = (lam / 4) ^ d * V := by
      unfold q09_ball
      rw [measureReal_def, Measure.addHaar_ball volume _ (by positivity),
        finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have hset := setIntegral_ge_of_const_le_real (μ := volume) (f := fun x => ‖G x‖ ^ p)
      (c := (κ * (5 * lam / 4) ^ ((-s - 1))) ^ p) (s := q09_ball i lam)
      measurableSet_ball (by unfold q09_ball; exact measure_ball_lt_top.ne)
      (fun x hx => hpt lam hlamL x hx)
      hint.integrableOn
    have heq : (κ * (5 * lam / 4) ^ ((-s - 1))) ^ p * volume.real (q09_ball i lam)
        = c0 * (lam ^ e * lam ^ (d : ℕ)) := by
      rw [hvol, hc0def, Real.mul_rpow hκ.le (by positivity), ← Real.rpow_mul (by positivity)]
      rw [show 5 * lam / 4 = (5 / 4 : ℝ) * lam by ring, Real.mul_rpow (by norm_num) hlam.le,
        show (lam / 4) = lam * (1 / 4 : ℝ) by ring, mul_pow, ← hedef]
      ring
    have hone : 1 ≤ lam ^ e * lam ^ (d : ℕ) := by
      rw [← Real.rpow_natCast lam d, ← Real.rpow_add (by linarith)]
      apply Real.one_le_rpow hlam1
      rw [hedef]
      nlinarith [hps]
    have : c0 ≤ c0 * (lam ^ e * lam ^ (d : ℕ)) := le_mul_of_one_le_right hc0.le hone
    linarith [hset, heq]
  -- the disjoint union
  have hsum : ∀ N : ℕ, (N : ℝ) * c0 ≤ ∫ x, ‖G x‖ ^ p := by
    intro N
    have hdisj : (↑(Finset.range N) : Set ℕ).Pairwise
        (Function.onFun Disjoint fun k : ℕ => q09_ball i (2 ^ k * L)) := by
      intro k _ j _ hkj
      rcases lt_or_gt_of_ne hkj with h | h
      · have hk0 : 0 < 2 ^ k * L := by positivity
        have hpow : (2 : ℝ) ^ (k + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) h
        have h12 : 2 * (2 ^ k * L) ≤ 2 ^ j * L := by
          have : 2 * (2 ^ k * L) = 2 ^ (k + 1) * L := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right hpow (by linarith)
        exact q09_ball_disj i hk0 h12
      · have hk0 : 0 < 2 ^ j * L := by positivity
        have hpow : (2 : ℝ) ^ (j + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) h
        have h12 : 2 * (2 ^ j * L) ≤ 2 ^ k * L := by
          have : 2 * (2 ^ j * L) = 2 ^ (j + 1) * L := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right hpow (by linarith)
        exact (q09_ball_disj i hk0 h12).symm
    have hU := integral_biUnion_finset (μ := volume) (f := fun x => ‖G x‖ ^ p)
      (Finset.range N) (s := fun k : ℕ => q09_ball i (2 ^ k * L))
      (fun k _ => measurableSet_ball) hdisj (fun k _ => hint.integrableOn)
    have hle : ∫ x in ⋃ k ∈ Finset.range N, q09_ball i (2 ^ k * L), ‖G x‖ ^ p
        ≤ ∫ x, ‖G x‖ ^ p :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => by positivity)
    have hge : ∑ k ∈ Finset.range N, c0 ≤ ∑ k ∈ Finset.range N,
        ∫ x in q09_ball i (2 ^ k * L), ‖G x‖ ^ p :=
      Finset.sum_le_sum (fun k _ => hball k)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hge
    rw [hU] at hle
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ x, ‖G x‖ ^ p) / c0)
  have hlt := (div_lt_iff₀ hc0).1 hN
  linarith [hsum N]

/-! ### Lemma S.A.15 -/

/-- The odd homogeneous multiplier `𝒯_θ` of order `θ - 1` (S L10143-10148): on a function `u`,
`𝒯_θ u(x) = p.v.∫ Ω(z/|z|)|z|^{-(d+θ-1)}u(x-z) dz = lim_{ε→0}∫_{|z|>ε} …` (the limit exists for Schwartz `u`, and a.e. for
`u ∈ L^q` in the cases below; for `θ < 1` it is the absolutely convergent integral, i.e. the fractional integral
multiplier).  The `finitely many` multipliers are indexed by the smooth odd `Ω`. -/
def pvOdd (d : ℕ) (θ : ℝ) (Ω : Euc d → ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ =>
    ∫ z in {z : Euc d | ε < ‖z‖}, Ω (‖z‖⁻¹ • z) / ‖z‖ ^ ((d : ℝ) + θ - 1) * u (x - z)

/-- `Ω` is smooth and odd on the sphere. -/
def IsOddSmooth (Ω : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ Ω ∧ ∀ u : Euc d, ‖u‖ = 1 → Ω (-u) = -Ω u

/-- The fractional Laplacian `Λ^θ = (-Δ)^{θ/2}` as the singular integral `p.v.∫(W(x)-W(x-z))|z|^{-(d+θ)}dz` (the positive
normalizing constant `c_{d,θ}` of S L10188 is omitted: it is absorbed in the constants of the estimates and in `c_θ`
of `lp_Lambda_commutator_expansion`). -/
def fracLap (d : ℕ) (θ : ℝ) (W : Euc d → ℝ) (x : Euc d) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ =>
    ∫ z in {z : Euc d | ε < ‖z‖}, (W x - W (x - z)) / ‖z‖ ^ ((d : ℝ) + θ)

/-- The commutator `[Λ^θ, μ]W = Λ^θ(μW) - μΛ^θW`. -/
def lamComm (d : ℕ) (θ : ℝ) (μ W : Euc d → ℝ) (x : Euc d) : ℝ :=
  fracLap d θ (fun y => μ y * W y) x - μ x * fracLap d θ W x

/-- The Euclidean norm `|v|` of a finite-dimensional tensor `v ∈ ℝ^ι`. -/
def vnorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- The dissipation density `𝔡_p[W](x) = ∫(|W(x)|+|W(x-z)|)^{p-2}|W(x)-W(x-z)|²|z|^{-(d+θ)}dz`
(`B:eq:lp-dissipation-density`, S L10133-10138) of a finite-dimensional tensor field `W : ℝ^d → ℝ^ι` (`|·|` the Euclidean
norm), valued in `ℝ≥0∞`. -/
def dissipationDensity {ι : Type*} [Fintype ι] (d : ℕ) (θ p : ℝ) (W : Euc d → ι → ℝ) (x : Euc d) :
    ℝ≥0∞ :=
  ∫⁻ z : Euc d, ENNReal.ofReal ((vnorm (W x) + vnorm (W (x - z))) ^ (p - 2) *
    vnorm (fun i => W x i - W (x - z) i) ^ 2 / ‖z‖ ^ ((d : ℝ) + θ))

/-- The Bessel-potential norm `‖Z‖_{W^{r,p}} = ‖𝓕⁻[(1+4π²|ξ|²)^{r/2}𝓕Z]‖_{L^p}` of a Schwartz function. -/
def besselNormE (d : ℕ) (r p : ℝ) (Z : SchwartzMap (Euc d) ℝ) : ℝ≥0∞ :=
  eLpNorm (𝓕⁻ (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) *
    𝓕 (fun y : Euc d => ((Z y : ℝ) : ℂ)) ξ)) (ENNReal.ofReal p) volume

/-- Lemma S.A.15(i) `B:item:screened-negative-order` (S L10150-10155): `0 < θ < 1`, `2 ≤ p < ∞`, `1/p + (1-θ)/d < 1`,
`a ∈ L^{d/(1-θ)}`: `‖𝒯_θ(aW)‖_{L^p} ≤ C‖a‖_{L^{d/(1-θ)}}‖W‖_{L^p}`, `C = C(d,θ,p)` (here `Ω(u) = u_i`, the coordinate kernel); and at `θ = 1`
(Calderón-Zygmund) `‖𝒯_1(aW)‖_p ≤ C‖a‖_{L^∞}‖W‖_p`.  Scalar `W`; for finite-dimensional tensor fields and tensor
contractions the proof is componentwise (S L10256).  The estimates are for `W ∈ L^p` (`MemLp`).

Statement change 2026-10-22 (owner approved): `Ω` restricted to the coordinate kernel `u_i` (linear `Ω`); all S.A.16 uses are of this form. -/
theorem lp_screened_negative_order (hd : 1 ≤ d) (θ p : ℝ) (hp : 2 ≤ p) (i : Fin d) :
    (0 < θ → θ < 1 → 1 / p + (1 - θ) / d < 1 →
      ∃ C : ℝ, ∀ a W : Euc d → ℝ, MemLp a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume →
        MemLp W (ENNReal.ofReal p) volume →
        eLpNorm (pvOdd d θ (fun u : Euc d => u i) fun x => a x * W x) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal C * eLpNorm a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume *
            eLpNorm W (ENNReal.ofReal p) volume) ∧
    (∃ C : ℝ, ∀ a W : Euc d → ℝ, MemLp a ⊤ volume → MemLp W (ENNReal.ofReal p) volume →
      eLpNorm (pvOdd d 1 (fun u : Euc d => u i) fun x => a x * W x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm a ⊤ volume * eLpNorm W (ENNReal.ofReal p) volume) := by
  sorry

/-- Lemma S.A.15(ii) `B:item:positive-order-product` (S L10157-10165): `1 < θ < 2`, `a ∈ C_b^1`, `W` Schwartz:
`𝒯_θ(aW) = a𝒯_θW + [𝒯_θ,a]W` (definition of the commutator) with
`‖[𝒯_θ,a]W‖_{L^p} ≤ C‖a‖_{C_b^1}‖W‖_{L^p}` (`B:eq:positive-order-product`), and for Schwartz `Z` (a dense class of
`W^{θ-1,p}`) `‖𝒯_θ(aZ)‖_{L^p} ≤ C‖a‖_{C_b^1}‖Z‖_{W^{θ-1,p}}` (`B:eq:positive-order-lower`).

Statement change 2026-10-22 (owner approved): `Ω` restricted to the coordinate kernel `u_i` (linear `Ω`); all S.A.16 uses are of this form. -/
theorem lp_positive_order_product (hd : 1 ≤ d) (θ p : ℝ) (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p)
    (i : Fin d) :
    ∃ C : ℝ, ∀ a : Euc d → ℝ, MemCb 1 a →
      (∀ W : SchwartzMap (Euc d) ℝ,
        eLpNorm (fun x => pvOdd d θ (fun u : Euc d => u i) (fun y => a y * W y) x -
            a x * pvOdd d θ (fun u : Euc d => u i) W x)
            (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * cbNorm 1 a) * eLpNorm W (ENNReal.ofReal p) volume) ∧
      ∀ Z : SchwartzMap (Euc d) ℝ,
        eLpNorm (pvOdd d θ (fun u : Euc d => u i) fun y => a y * Z y) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * cbNorm 1 a) * besselNormE d (θ - 1) p Z := by
  sorry

/-- Lemma S.A.15(iii), first part `B:item:Lambda-commutator` (S L10167-10178): for `μ ∈ C_b²` and `0 < θ ≤ 1` (`θ < 1`:
`B:eq:Lambda-commutator-low`; `θ = 1`: the first Calderón commutator estimate), `‖[Λ^θ,μ]W‖_{L^p} ≤ C‖μ‖_{C_b^2}‖W‖_{L^p}`
for Schwartz `W`.

Statement change 2026-10-22 (project owner approved): the norm is `‖μ‖_{C_b^2}` (was `C_b^1`), i.e. weaker than the TeX at `θ = 1`
(the first Calderón commutator is skipped); the proof is `lp_Lambda_commutator_low_cb2` in `CzElemAux4`. -/
theorem lp_Lambda_commutator_low (hd : 1 ≤ d) (θ p : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hp : 2 ≤ p) :
    ∃ C : ℝ, ∀ μ : Euc d → ℝ, MemCb 2 μ → ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (lamComm d θ μ W) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * cbNorm 2 μ) * eLpNorm W (ENNReal.ofReal p) volume := by
  sorry

/-- Lemma S.A.15(iii), second part (S L10179-10187, `B:eq:Lambda-commutator-expansion`): for `1 < θ < 2`,
`[Λ^θ,μ]W = c_θ∇μ·∇Λ^{θ-2}W + 𝓡_μW` with `‖𝓡_μW‖_{L^p} ≤ C‖μ‖_{C_b²}‖W‖_{L^p}`; `∇Λ^{θ-2}` is the finite vector of
operators `𝒯^{(i)}_θ` of the form above with `Ω(u) = u_i` (symbol `iξ_i|ξ|^{θ-2}`), so the statement is: there are
`c_θ` and `C` such that `‖[Λ^θ,μ]W - c_θ∑_i∂_iμ·𝒯^{(i)}_θW‖_{L^p} ≤ C‖μ‖_{C_b²}‖W‖_{L^p}` for `μ ∈ C_b²`, `W` Schwartz
(`c_θ` depends on the normalization omitted in `fracLap`). -/
theorem lp_Lambda_commutator_expansion (hd : 1 ≤ d) (θ p : ℝ) (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p) :
    ∃ cθ C : ℝ, ∀ μ : Euc d → ℝ, MemCb 2 μ → ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (fun x => lamComm d θ μ W x - cθ * ∑ i : Fin d,
          gradient μ x i * pvOdd d θ (fun u : Euc d => u i) W x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * cbNorm 2 μ) * eLpNorm W (ENNReal.ofReal p) volume := by
  sorry

/-- Lemma S.A.15(iv) `B:item:tensor-absorption` (S L10189-10196): `1 < θ < 2`, `μ ≥ 0`, `a = √μ b` with `b ∈ L^∞`: for every
`ε > 0`,
`|∫|W|^{p-2}W : a𝒯_θW dx| ≤ ε∫μ𝔡_p[W]dx + C_{ε,θ,p,Λ}(1+‖b‖_∞²)‖W‖_p^p` (`B:eq:tensor-absorption`).  The inequality is
nonlinear in `W`, so it is stated for a finite-dimensional tensor field `W = (W_i)_{i ∈ ι}`, `W_i` Schwartz (used for
`W = ∇^{⊗m}F`), `𝒯_θ` acting componentwise, `a = √μ B` with a matrix field `B(x) ∈ ℝ^{ι×ι}` (the tensor contraction; `|B_{ij}| ≤ Bb`
plays the role of `‖b‖_∞`), and `|W|` the Euclidean norm; `ι` is `Unit` for the scalar case.  `Λ` bounds `‖μ‖_∞` (the
dependence `C_{ε,θ,p,Λ}` of the TeX; S L10250: "far part bounded by `C‖a‖_∞‖W‖_p^p`").  `C` may depend on `ι`.  Valued in `ℝ≥0∞` (the dissipation integral may be `∞`). -/
theorem lp_tensor_absorption (hd : 1 ≤ d) (θ p : ℝ) (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p)
    (Ω : Euc d → ℝ) (hΩ : IsOddSmooth Ω) (Λ : ℝ) (ε : ℝ) (hε : 0 < ε) (ι : Type*) [Fintype ι] :
    ∃ C : ℝ, ∀ (μ : Euc d → ℝ) (B : Euc d → Matrix ι ι ℝ) (Bb : ℝ), (∀ x, 0 ≤ μ x ∧ μ x ≤ Λ) →
      (∀ x i j, |B x i j| ≤ Bb) → ∀ W : ι → SchwartzMap (Euc d) ℝ,
        ENNReal.ofReal |∫ x, vnorm (fun i => W i x) ^ (p - 2) *
            ∑ i, W i x * (Real.sqrt (μ x) * ∑ j, B x i j * pvOdd d θ Ω (fun y => W j y) x)| ≤
          ENNReal.ofReal ε * (∫⁻ x, ENNReal.ofReal (μ x) *
              dissipationDensity d θ p (fun y i => W i y) x) +
            ENNReal.ofReal (C * (1 + Bb ^ 2)) *
              ∫⁻ x, ENNReal.ofReal (vnorm (fun i => W i x) ^ p) := by
  sorry

/-! ### Proposition S.A.16 -/

/-- `F ∈ C_w([0,t]; W^{m,p}(ℝ^d))`: `F(τ) ∈ W^{m,p}` for every `τ ∈ [0,t]` and for every choice `G(τ)` of the
corresponding element of `W^{m,p}`, `τ ↦ ℓ(G(τ))` is continuous for every `ℓ ∈ (W^{m,p})^*`. -/
def IsWmpWeaklyContinuous (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (t : ℝ) (F : ℝ → Euc d → ℝ) : Prop :=
  (∀ τ ∈ Set.Icc (0 : ℝ) t, wNormE m p (F τ) < ⊤) ∧
    ∀ G : ℝ → WmpSpace d m p,
      (∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ᵐ x ∂(volume : Measure (Euc d)),
        ((G τ : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = F τ x) →
      ∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G τ)) (Set.Icc (0 : ℝ) t)

/-- The solution class of `B:thm:adjoint-lp`: `F ∈ C_w([0,t];W^{m,p}) ∩ C([0,t];W^{m',p}_loc)`, `0 ≤ m' < m` (integers),
a distributional solution of `B:eq:adjoint-forward` with `F(0) = φ`, bounded in `W^{m,p}` (a consequence of weak
continuity, stated for definiteness). -/
structure IsLpSolutionRd (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (χ : Euc d → ℝ) (C : WholeCoeff d) (t : ℝ)
    (φ : Euc d → ℝ) (F : ℝ → Euc d → ℝ) : Prop where
  sol : IsForwardSolutionRd C t φ F
  wcont : IsWmpWeaklyContinuous m p t F
  bounded : ∃ B : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) t, wNormE m p (F τ) ≤ ENNReal.ofReal B
  cont : ∀ m' : ℕ, m' < m → ∀ z : Euc d, ∀ τ₀ ∈ Set.Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) t, |τ - τ₀| < δ →
      wNormE m' p (fun x => χ (x - z) * (F τ x - F τ₀ x)) ≤ ENNReal.ofReal ε

/-- Proposition S.A.16 `B:thm:adjoint-lp` (S L10265-10297), existence, uniqueness and bound.  Let `m ≥ 1`, `p ∈ [2,∞)`,
assume `B:eq:coeff-hypothesis-rd` (`AdjointRdData`, level `m`).  In each case (i), (ii), (iii) (`LpCase.Holds`), for every
`t ∈ (0,T]` and `φ ∈ W^{m,p}(ℝ^d)` there is a unique distributional solution
`F ∈ C_w([0,t];W^{m,p}) ∩ C([0,t];W^{m',p}_loc)` (`0 ≤ m' < m`) of `B:eq:adjoint-forward` with `F(0) = φ`, and
`‖F(τ)‖_{W^{m,p}} ≤ Ce^{Cτ}‖φ‖_{W^{m,p}}` (`B:eq:adjoint-lp-bound`; the exponent constant is also `C`: "`C e^{Cτ}`").
`C` depends on `d, s, m, p`, the case, `|M|, Λ, Λ_V, |∇V(0)|, ν̄, T`.  The prose "in case (ii) the solution is constructed
directly ... in the overlap uniqueness identifies the solutions" is the compatibility with `adjoint_rd`.
Technical hypotheses: `m' ` ranges over integers `< m` (see the module docstring); the norm `‖·‖_{W^{m,p}}` is the
equivalent sup-on-jets norm `wNormE`. -/
theorem adjoint_lp (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (κc : LpCase) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → κc.Holds d s p D.M →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, wNormE m p φ < ⊤ →
        (∃ F : ℝ → Euc d → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) t, wNormE m p (F τ) ≤
            ENNReal.ofReal (C * Real.exp (C * τ)) * wNormE m p φ) ∧
        ∀ F₁ F₂ : ℝ → Euc d → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F₁ →
          IsLpSolutionRd m p χ (D.coeff μ) t φ F₂ →
          ∀ τ ∈ Set.Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  sorry

/-- Proposition S.A.16, last sentence of the first paragraph (S L10286-10287): if `m > 2 + d/p`, then `f^r := F(t-r)` is a
classical adjoint solution in the sense of `B:rem:def-adjoint-rd` (`IsClassicalAdjointW`, see SUSPECTED ISSUE in the module
docstring).  Technical: the terminal datum `φ` is a `C²` representative. -/
theorem adjoint_lp_classical (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (p : ℝ)
    [Fact (2 ≤ p)] (hmp : 2 + (d : ℝ) / p < m) (κc : LpCase) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ)
    (D : WholeDyn d) (μ : ℝ → Euc d → ℝ) (hA : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (hκ : κc.Holds d s p D.M) (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (hφ : ContDiff ℝ 2 φ)
    (F : ℝ → Euc d → ℝ) (hF : IsLpSolutionRd m p χ (D.coeff μ) t φ F) :
    ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW (D.coeff μ) t φ f ∧
      ∀ r ∈ Set.Icc (0 : ℝ) t, f r =ᵐ[volume] F (t - r) := by
  sorry

/-- Proposition S.A.16, stability (S L10289-10297, `B:eq:adjoint-lp-stability`): for `a ∈ {1,2}` let `(ν_a, μ_a)` satisfy the
hypotheses at level `m+2` with a common regime (`κc`), common constants and the same confinement `(M,V)`, `F_a` the solutions
with datum `φ ∈ W^{m+2,p}`, and `δ` bound `sup_{τ ≤ T}‖μ_1^τ - μ_2^τ‖` in the coefficient norm `coeffNormE` (`𝒞^{m+2}` plus the
weighted `𝒞_w^{m+2}` and, for `s ≥ d-1`, the fractional force bound).  Then
`‖F_1(τ) - F_2(τ)‖_{W^{m,p}} ≤ C τ e^{Cτ}(|ν_1-ν_2| + δ)‖φ‖_{W^{m+2,p}}`, `τ = t - r`. -/
theorem adjoint_lp_stability (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (κc : LpCase) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D₁ D₂ : WholeDyn d) (μ₁ μ₂ : ℝ → Euc d → ℝ),
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₁ T μ₁ →
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₂ T μ₂ →
      κc.Holds d s p D₁.M → κc.Holds d s p D₂.M → D₁.M = D₂.M → D₁.V = D₂.V →
      ∀ δ : ℝ, 0 ≤ δ → (∀ r ∈ Set.Icc (0 : ℝ) T, coeffNormE d s m (μ₁ r - μ₂ r) ≤ ENNReal.ofReal δ) →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, wNormE (m + 2) p φ < ⊤ →
      ∀ F₁ F₂ : ℝ → Euc d → ℝ,
        IsLpSolutionRd (m + 2) p χ (D₁.coeff μ₁) t φ F₁ →
        IsLpSolutionRd (m + 2) p χ (D₂.coeff μ₂) t φ F₂ →
        ∀ τ ∈ Set.Icc (0 : ℝ) t,
          wNormE m p (fun x => F₁ τ x - F₂ τ x) ≤
            ENNReal.ofReal (C * τ * Real.exp (C * τ) * (|D₁.invβ - D₂.invβ| + δ)) * wNormE (m + 2) p φ := by
  sorry

/-! ### Remark S.A.17 -/

-- Remark S.A.17 `B:rem:lp-anisotropic` (S L10375-10383): no_formal_content.  It explains why `B:thm:adjoint-lp` separates the
-- isotropic `L^p` case from the Hilbert-space case ("for `p ≠ 2` the test `|W|^{p-2}W` changes the quadratic-form
-- calculation; the argument above does not provide the corresponding estimate for a general anisotropic matrix").  It
-- asserts only that a certain proof does not supply an estimate, not a mathematical claim; the scope of the theorem is the
-- hypotheses of `adjoint_lp` (cases (ii), (iii)).

end HRS.Whole.AppendixA
