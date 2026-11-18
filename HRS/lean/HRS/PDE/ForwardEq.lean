import HRS.PDE.Convention

/-!
# Torus PDE layer III: the forward adjoint equation in Fourier form, its solution concept,
the coefficient hypothesis, and the adjoint regimes

Sources (HRS periodic main paper, Section 3.2 `B:sec:adjoint-torus`, lines 1711–1738):
* backward problem `B:eq:adjoint-backward` (1715–1717), forward problem after `F(τ) := f(t-τ)`
  `B:eq:adjoint-forward` (1719–1721): `∂_τ F = νΔF + b^τ·∇F - 𝒢^τ[F]`, `F(0) = φ`, with
  `ν = β⁻¹ ∈ [0,∞)`, `b^τ = M∇g*μ^{t-τ} - ∇V`, and `𝒢^τ[F] = Div g*(μ^{t-τ} M^*∇F)
  = ∑_{i,j} M^*_{ij} ∂_i g*(μ^{t-τ} ∂_j F)` (`B:eq:G-def`, 1723–1725);
* standing coefficient hypothesis `B:eq:coeff-hypothesis` (1727–1729):
  `μ ∈ C([0,T]; 𝒫(𝕋^d))`, `sup_{[0,T]} ‖μ^r‖_{C^{m+3}} ≤ Λ`, `V ∈ C^{m+3}`;
* constants depend only on `(d, s, m, |M|, Λ, ‖V‖_{C^{m+3}})` and, where indicated, on `lam0`
  or `ν₀`; never on `t ∈ [0,T]`, `β`, or `φ` (1730);
* `θ = s + 2 - d` (1732); Assumption A.2 `B:ass:regime` (10168–10180): regimes R1, R2a, R2b,
  R2c, R3; `Λ_m` of `B:eq:LambdaM` (1745–1750).

## Representation decisions (SPEC_NOTES §1–2)

* All operators act on coefficient sequences through the multipliers of `HRS/PDE/Fourier.lean`
  (`forwardGen`).  For `F ∈ H^1` and `μ ∈ C^{m+3}` every term is an absolutely convergent
  coefficient (`summable_mulCoeff`).
* "`F` solves `B:eq:adjoint-forward` in the distributional sense with `F(0) = φ`" is represented
  coefficientwise by the integrated equation `F̂(τ,k) = φc(k) + ∫_0^τ (𝓛^σ F(σ))^(k) dσ` for every
  `k` and `τ ∈ [0,t]`, with the integrand integrable in `σ` (`IsForwardSolution`).  On the torus this
  is equivalent to the distributional formulation (test with `η(τ) e_{-k}(x)`; trigonometric
  polynomials are dense), see SPEC_NOTES §1.  `C_w([0,t];H^m)` and `C([0,t];H^{m'})` are the
  predicates `WeakContinuousInHs`, `ContinuousInHs` of `Fourier.lean`.
* The dependence on `|M|` and `‖V‖_{C^{m+3}}` is expressed through bounds (`MB`, `VB`), the regime
  (including `lam0` in R2b) is a parameter placed before the constant, and `ν₀` (R3) is quantified
  after it since its dependence is displayed in `Λ_m` (`Regime.lambdaM`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- The order `θ = s + 2 - d` of the nonlocal term (line 1732). -/
def thetaOrder (d : ℕ) (s : ℝ) : ℝ := s + 2 - d

/-! ### The forward generator in Fourier form -/

/-- Coefficients of the `j`-th component of the drift `b = M∇g*ρ - ∇V` (line 1722):
`b̂_j(k) = ∑_i M_{ji} 2πi k_i ĝ(k) ρ̂(k) - 2πi k_j V̂(k)`. -/
def driftCoeff (D : DynData d) (ρ : Torus d → ℝ) (j : Fin d) : Coeff d :=
  fun k => (∑ i : Fin d, ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (coeffOf ρ) k) -
    derivCoeff j (coeffOf D.V) k

/-- Coefficients of the transport term `b·∇F = ∑_j b_j ∂_j F`. -/
def transportCoeff (D : DynData d) (ρ : Torus d → ℝ) (F : Coeff d) : Coeff d :=
  fun k => ∑ j : Fin d, mulCoeff (driftCoeff D ρ j) (derivCoeff j F) k

/-- Coefficients of the nonlocal term `𝒢[F] = ∑_{i,j} M^*_{ij} ∂_i g*(ρ ∂_j F)`, `M^* = Mᵀ`
(`B:eq:G-def`, lines 1723–1725): `∑_{i,j} M_{ji} · 2πi k_i ĝ(k) · (ρ ∂_jF)^(k)`. -/
def nonlocalCoeff (D : DynData d) (ρ : Torus d → ℝ) (F : Coeff d) : Coeff d :=
  fun k => ∑ i : Fin d, ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
    gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F)) k

/-- The forward generator `𝓛 F = νΔF + b·∇F - 𝒢[F]` of `B:eq:adjoint-forward` (line 1720) at a
frozen density `ρ` (`= μ^{t-τ}`), in Fourier form, `ν = D.invβ`. -/
def forwardGen (D : DynData d) (ρ : Torus d → ℝ) (F : Coeff d) : Coeff d :=
  fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff F k + transportCoeff D ρ F k - nonlocalCoeff D ρ F k

/-! ### The solution concept -/

/-- `F` solves `B:eq:adjoint-forward` on `[0,t]` with datum `φc` and coefficient path
`σ ↦ μ^{t-σ}`, in the integrated coefficient form (distributional sense; SPEC_NOTES §1):
`F(τ) ∈ H^1` for `τ ∈ [0,t]`, and for every `k`,
`F̂(τ,k) = φc(k) + ∫_0^τ (𝓛^σ F(σ))^(k) dσ` with an integrable integrand. -/
structure IsForwardSolution (D : DynData d) (μ : ℝ → Torus d → ℝ) (t : ℝ) (φc : Coeff d)
    (F : ℝ → Coeff d) : Prop where
  h1 : ∀ τ ∈ Set.Icc 0 t, MemHs 1 (F τ)
  integrable : ∀ k, IntegrableOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k) (Set.Icc 0 t)
  eq : ∀ k, ∀ τ ∈ Set.Icc 0 t,
    F τ k = φc k + ∫ σ in (0 : ℝ)..τ, forwardGen D (μ (t - σ)) (F σ) k

open Classical in
/-- The forward solution operator at level `m`: the unique `F ∈ C_w([0,t];H^m)` solving the forward
equation with datum `φc` (Proposition 3.9), `0` if there is none.  `U^{r,t} φ` corresponds to
`propagatorCoeff D μ m t φc (t - r)`. -/
def propagatorCoeff (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℝ) (t : ℝ) (φc : Coeff d) :
    ℝ → Coeff d :=
  if h : ∃ F, IsForwardSolution D μ t φc F ∧ WeakContinuousInHs m F t then h.choose
  else fun _ => 0

/-! ### The coefficient hypothesis `B:eq:coeff-hypothesis` -/

/-- `B:eq:coeff-hypothesis` (lines 1727–1729) for the density path: `μ^r` is a probability density
of class `C^{m+3}` with `‖μ^r‖_{C^{m+3}} ≤ Λ` for `r ∈ [0,T]`, and `r ↦ μ^r` is continuous into
`𝒫(𝕋^d)` (weakly, i.e. against continuous tests).  (The source's `C^{m+3}` norm is the max over
orders, `cbNorm` is the sum: equivalent up to the factor `m+4`, ISSUES §M3.)  The hypothesis on `V`
(`V ∈ C^{m+3}`) is carried separately by the theorems. -/
structure CoeffHyp (m : ℕ) (Λ T : ℝ) (μ : ℝ → Torus d → ℝ) : Prop where
  prob : ∀ r ∈ Set.Icc 0 T, IsProbDensity (μ r)
  smooth : ∀ r ∈ Set.Icc 0 T, Torus.IsCk (m + 3) (μ r)
  bound : ∀ r ∈ Set.Icc 0 T, Torus.cbNorm (m + 3) (μ r) ≤ Λ
  cont : ∀ ψ : Torus d → ℝ, Continuous ψ →
    ContinuousOn (fun r => ∫ x, ψ x * μ r x) (Set.Icc 0 T)

/-- The hypotheses on `V` of `B:eq:coeff-hypothesis`: `V ∈ C^{m+3}` with `‖V‖_{C^{m+3}} ≤ VB`. -/
def VHyp (m : ℕ) (VB : ℝ) (V : Torus d → ℝ) : Prop :=
  Torus.IsCk (m + 3) V ∧ Torus.cbNorm (m + 3) V ≤ VB

/-- Entrywise bound `|M_{ij}| ≤ MB` (the dependence on `|M|`). -/
def MatBound (MB : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : Prop := ∀ i j, |M i j| ≤ MB

/-! ### Assumption A.2 `B:ass:regime` (lines 10168–10180) and `Λ_m` -/

/-- The adjoint regimes of Assumption A.2.  `R2b` carries its lower bound `lam0` (constants may
depend on it, line 1730); the `ν₀` of `R3` is a separate argument of `Regime.Holds`. -/
inductive Regime
  | R1
  | R2a
  | R2b (lam0 : ℝ)
  | R2c
  | R3

/-- The conditions of each regime (Assumption A.2, lines 10171–10178), for a single trajectory
`μ` on `[0,T]`, with `θ = s+2-d`:
* R1: `0 ≤ s ≤ d-2`, `M` arbitrary, `β ∈ (0,∞]` arbitrary;
* R2 (`d-2 < s < d`, `S = ½(M+Mᵀ) ≤ 0`, `β` arbitrary) and one of
  R2a: `M` antisymmetric (`S = 0`); R2b: `inf_{[0,T]×𝕋^d} μ ≥ lam0 > 0`; R2c: `s ≤ d-1` (`θ ≤ 1`),
  no positivity condition;
* R3: `d-2 < s < d`, `M` arbitrary, `ν = β⁻¹ ≥ ν₀ > 0`.
(`0 ≤ s < d` is a standing hypothesis of the theorems.) -/
def Regime.Holds (R : Regime) (d : ℕ) (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (invβ ν₀ T : ℝ)
    (μ : ℝ → Torus d → ℝ) : Prop :=
  match R with
  | .R1 => s ≤ (d : ℝ) - 2
  | .R2a => (d : ℝ) - 2 < s ∧ Torus.symPart M = 0
  | .R2b lam0 => (d : ℝ) - 2 < s ∧ Torus.SymNonpos M ∧ 0 < lam0 ∧
      ∀ r ∈ Set.Icc 0 T, ∀ x, lam0 ≤ μ r x
  | .R2c => (d : ℝ) - 2 < s ∧ s ≤ (d : ℝ) - 1 ∧ Torus.SymNonpos M
  | .R3 => (d : ℝ) - 2 < s ∧ 0 < ν₀ ∧ ν₀ ≤ invβ

/-- Whether the regime is one of the R2 cases (where the weighted dissipation of
`B:eq:energy-torus` is retained). -/
def Regime.IsR2 : Regime → Prop
  | .R1 => False
  | .R2a => True
  | .R2b _ => True
  | .R2c => True
  | .R3 => False

instance (R : Regime) : Decidable R.IsR2 := by cases R <;> simp only [Regime.IsR2] <;> infer_instance

/-- `Λ_m` of `B:eq:LambdaM` (lines 1745–1750): `C` in regimes R1 and R2 (uniformly in
`β ∈ (0,∞]`), `C(1 + ν₀^{-θ/(2-θ)})` in regime R3. -/
def Regime.lambdaM (R : Regime) (C ν₀ θ : ℝ) : ℝ :=
  match R with
  | .R3 => C * (1 + ν₀ ^ (-(θ / (2 - θ))))
  | _ => C

/-- The full hypothesis package of Proposition 3.9 for the data `(D, μ)` at level `m` on `[0,T]`
(everything after the constant quantifier): `D.s = s`, the entrywise bound on `M`, `V ∈ C^{m+3}`
with norm bound, the coefficient hypothesis, and the regime. -/
structure AdjointData (s : ℝ) (m : ℕ) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ)
    (μ : ℝ → Torus d → ℝ) : Prop where
  hs : D.s = s
  hM : MatBound MB D.M
  hV : VHyp m VB D.V
  hμ : CoeffHyp m Λ T μ
  hT : 0 < T
  regime : R.Holds d s D.M D.invβ ν₀ T μ

end HRS.PDE
