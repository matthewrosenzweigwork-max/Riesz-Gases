import HRS.MC.S7PIDDefs

/-!
# Packets PI-B, PI-F, PI-G: sorry-free vocabulary for the split of `path_Ito` (`HRS/MC/S7PIPlan.lean`)

Everything is about the CYLINDRICAL functionals `Φ ∘ Pj L` of `X = C([0,T];E_m)`.  Since `Pj L = Λ_L ∘ obs_L` with
`obs_L : X → ℝ^q` the finite vector of grid observations `w ↦ (w(t_i)(φ_i))_i` and `Λ_L : ℝ^q → X` a continuous linear
map, the heat function and the Itô formula of PI-F live in finite dimension:

* `obsVec m T t φ w = (w(t_i)(φ_i))_i ∈ ℝ^q` (a continuous linear map `X → ℝ^q` for smooth `φ_i`);
* `obsTest D ρ t φ i u = 1_{u ≤ t_i} U^{u,t_i} φ_i`: the (frozen after `t_i`) test function seen by the `i`-th coordinate of
  `u ↦ obsVec(𝖳_u ζ)` (the coordinate is `ζ_u(obsTest i u)` for `u ≤ t_i`, constant `ζ_{t_i}(φ_i)` afterwards);
* `obsRate D ρ t φ u = (2β⁻¹ ∫ ∇obsTest_i · ∇obsTest_j ρ_u dx)_{ij}`: the covariance RATE, PSD, piecewise continuous;
* `obsCov D ρ t φ u = (2β⁻¹ ∫_u^{t_i∧t_j} ∫ ∇U^{v,t_i}φ_i · ∇U^{v,t_j}φ_j ρ_v dx dv)_{ij}`: the Gram matrix of the
  `IsFutureGaussian` law of `Γ_u` on the observations; `obsCov u = ∫_u^T obsRate`;
* `gaussHeat S G u c = ∫ G(c + x) dN(0, S u)(x)`: the finite-dimensional heat function.

Nothing here is a statement about the dynamics.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PI

open HRS HRS.Sec7

variable {d : ℕ}

/-- The observation vector `w ↦ (w(t_i)(φ_i))_i ∈ ℝ^q`. -/
def obsVec {q : ℕ} (m T : ℝ) (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (w : PathSpace d m T) :
    EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 fun i => NegSobolev.eval (pathAt w (t i)) (φ i)

/-- The test function seen by the `i`-th observation at time `u`: `1_{u ≤ t_i} U^{u,t_i} φ_i`. -/
def obsTest (D : DynData d) (ρ : ℝ → Torus d → ℝ) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (i : Fin q) (u : ℝ) : Torus d → ℝ :=
  if u ≤ t i then propagator D ρ u (t i) (φ i) else 0

/-- The same with the cut-off `c < t_i` instead of `u ≤ t_i` (equal to `obsTest` for `u ∈ (c, c']` as long as
no `t_i` lies in `(c, c')`; it is the continuous piece of `obsTest` on the closed interval `[c,c']`). -/
def obsTestR (D : DynData d) (ρ : ℝ → Torus d → ℝ) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (c : ℝ) (i : Fin q) (u : ℝ) : Torus d → ℝ :=
  if c < t i then propagator D ρ u (t i) (φ i) else 0

/-- The covariance rate `A(u)_{ij} = 2β⁻¹ ∫ ∇obsTest_i(u) · ∇obsTest_j(u) ρ_u dx`. -/
def obsRate (D : DynData d) (ρ : ℝ → Torus d → ℝ) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (u : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun i j => 2 * D.invβ * ∫ x, inner ℝ (Torus.grad (obsTest D ρ t φ i u) x)
    (Torus.grad (obsTest D ρ t φ j u) x) * ρ u x

/-- The continuous piece `A^{(c)}(u)_{ij} = 2β⁻¹ ∫ ∇obsTestR_i(u) · ∇obsTestR_j(u) ρ_u dx` of the rate. -/
def obsRateR (D : DynData d) (ρ : ℝ → Torus d → ℝ) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (c u : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun i j => 2 * D.invβ * ∫ x, inner ℝ (Torus.grad (obsTestR D ρ t φ c i u) x)
    (Torus.grad (obsTestR D ρ t φ c j u) x) * ρ u x

/-- The covariance matrix of the observations of `Γ_u` (the Gram matrix in `IsFutureGaussian`). -/
def obsCov (D : DynData d) (ρ : ℝ → Torus d → ℝ) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (u : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun i j => 2 * D.invβ * ∫ v in Set.Icc u (min (t i) (t j)), ∫ x,
    inner ℝ (Torus.grad (propagator D ρ v (t i) (φ i)) x) (Torus.grad (propagator D ρ v (t j) (φ j)) x) * ρ v x

/-- The finite-dimensional heat function `u, c ↦ E G(c + N(0, S u))`
(`= dirac` at `c` if `S u` is not positive semidefinite, which never happens below). -/
def gaussHeat {q : ℕ} (S : ℝ → Matrix (Fin q) (Fin q) ℝ) (G : EuclideanSpace ℝ (Fin q) → ℝ) (u : ℝ)
    (c : EuclideanSpace ℝ (Fin q)) : ℝ :=
  ∫ x, G (c + x) ∂(ProbabilityTheory.multivariateGaussian 0 (S u))

/-- `(Pj, Λ, obs)` are the grid data of the projection `P_L = projPoly .. L` (Remark 7.10): `q` observations
`(t_i, φ_i = realMode k_i)` at grid times `t_i ∈ [0,T]`, a continuous linear `Λ : ℝ^q → X`, and
`P_L w = Λ (obsVec w)` for every path `w`.  Existence: `s7_PIS_obs_proj`. -/
def IsGridData (m T : ℝ) (hT : 0 ≤ T) (L q : ℕ) (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (Λ : EuclideanSpace ℝ (Fin q) →L[ℝ] PathSpace d m T) : Prop :=
  (∀ i, t i ∈ Set.Icc (0 : ℝ) T) ∧ (∀ i, ∃ k : NonzeroLattice d, φ i = Torus.realMode k) ∧
    ∀ w, projPoly m T hT L w = Λ (obsVec m T t φ w)

/-- The projected derivative of the heat function without the projection on the arguments:
`(u,y) ↦ ∫ D^jΦ(P(y+z)) dγ_u(z)`, a `j`-linear form on `X` (`0` if not integrable, which does not happen for
`Φ ∈ C_b^j`).  Then `D^j (heatFn γ (Φ ∘ P) u) y = (projHeatD ..).compContinuousLinearMap (fun _ => P)`
(`s7_PIG_proj_deriv`). -/
def projHeatD {m T : ℝ} (γ : ℝ → Measure (PathSpace d m T)) (Φ : PathSpace d m T → ℝ)
    (P : PathSpace d m T →L[ℝ] PathSpace d m T) (j : ℕ) (u : ℝ) (y : PathSpace d m T) :
    PathSpace d m T [×j]→L[ℝ] ℝ :=
  ∫ z, iteratedFDeriv ℝ j Φ (P (y + z)) ∂(γ u)

/-- The CONCLUSION of `path_Ito` for the functional `Φ ∘ Pj` (`Pj = id` gives `path_Ito`, `Pj = Pj L` gives
`s7_PI_F_projected_identity`; the statement is copied verbatim from `HRS.Sec7.path_Ito` / Sec7Spec.lean:792). -/
def PathItoConcl (R : Regime d) (m T : ℝ) (γ : ℝ → Measure (PathSpace d m T)) (N : ℕ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (Φ : PathSpace d m T → ℝ)
    (Pj : PathSpace d m T →L[ℝ] PathSpace d m T) : Prop :=
  ∃ A J : Ω → ℝ, Integrable A P ∧ Integrable J P ∧
    (∀ᵐ ω ∂P, IsRS T (fun τ a b =>
      fderiv ℝ (heatFn γ (fun w => Φ (Pj w)) τ) (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ)
        (driftInc R.D R.ρ m T
          (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω) a b)) (A ω)) ∧
    (∀ᵐ ω ∂P, IsRS T (fun τ a b =>
      jPair R.D R.ρ m T (fun u => etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u))) (Set.Ioc a b)
        (iteratedFDeriv ℝ 2 (heatFn γ (fun w => Φ (Pj w)) τ)
          (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ))) (J ω)) ∧
    ∫ ω, Φ (Pj (zetaWin m T 0 P X ω)) ∂P =
      ∫ ω, heatFn γ (fun w => Φ (Pj w)) 0 (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) ∂P -
        (Real.sqrt N)⁻¹ * ∫ ω, A ω ∂P + (1 / (2 * Real.sqrt N)) * ∫ ω, J ω ∂P

/-- The drift density of the cylindrical Itô identity:
`∑_i ∂_iF(r, z(r)) · ℬ_N^r(obsTest_i r)` with `F = gaussHeat obsCov G`, `z(r) = obsVec(𝖳_r ζ_N)`. -/
def cylA (R : Regime d) (m T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    (X : ℝ≥0 → Ω → Config d N) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (ω : Ω) (r : ℝ) : ℝ :=
  ∑ i, fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G r)
      (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) r)) (EuclideanSpace.single i 1) *
    NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r)

/-- The covariance density of the cylindrical Itô identity:
`∑_{ij} ∂_{ij}F(r, z(r)) · 2β⁻¹ η_N^r(∇obsTest_i r · ∇obsTest_j r)`. -/
def cylJ (R : Regime d) (m T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    (X : ℝ≥0 → Ω → Config d N) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (ω : Ω) (r : ℝ) : ℝ :=
  ∑ i, ∑ j, iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G r)
      (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) r))
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
    (2 * R.D.invβ * NegSobolev.eval (etaE m (X r.toNNReal ω) (withDensityReal (R.ρ r)))
      (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i r) y) (Torus.grad (obsTest R.D R.ρ t φ j r) y)))

end HRS.MC.Sec7.PI

end
