import HRS.Appendix.CepaFlow
import HRS.Stochastic.ParticleLog

/-!
# Packet CEPA-DEFS: the vocabulary (definitions only) of `HRS/MC/CepaSpec.lean`

All non-theorem declarations of the Cépa–Lépingle specification file live here, with identical names, bodies and
namespace, so that proof modules can import the vocabulary without importing the `sorry` theorems of
`HRS.MC.CepaSpec`.  No theorem, no `sorry`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Cepa

open HRS

/-! ### Vocabulary (new; no redefinition of existing objects) -/

/-- `V` is `C¹` with Lipschitz gradient on the covering line: exactly the hypothesis pair
`hV₁ : Torus.IsCk 1 D.V`, `hV₂ : LipschitzWith L (gradient (Torus.lift D.V))` of `cepa_log_flow` and
`cepa_noncollision_iff_threshold`.  (The existing barrier chain of `Particle.lean` assumes the stronger
`Torus.IsCk 2 D.V`; see packet `S1`.) -/
def cep_IsC11 {d : ℕ} (V : Torus d → ℝ) : Prop :=
  Torus.IsCk 1 V ∧ ∃ L : ℝ≥0, LipschitzWith L (gradient (Torus.lift V))

/-- `X` has no contact on `[0, σ)` along the path `ω`. -/
def cep_NoContactBefore {Ω : Type*} {d N : ℕ} (X : ℝ≥0 → Ω → Config d N) (ω : Ω) (σ : WithTop ℝ) : Prop :=
  ∀ t : ℝ≥0, (((t : ℝ)) : WithTop ℝ) < σ → X t ω ∉ collisionSet d N

/-- Rank coordinates: the lift `y` read in the order `π` (`z k = y (π k)`). -/
def cep_rank {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Fin N → ℝ :=
  fun k => y (π k) 0

/-- Strict cyclic order of a lift: `y (π 0) < ... < y (π (N-1)) < y (π 0) + 1`. -/
def cep_StrictlyOrdered {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Prop :=
  (∀ k k' : Fin N, k < k' → y (π k) 0 < y (π k') 0) ∧
    ∀ k k' : Fin N, y (π k') 0 < y (π k) 0 + 1

section Necessity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- The scale function `S(z) = ∫_0^z u^{-θ} e^{-λ u} du` of the localised Bessel-type gap equation
(`θ = 2κ/σ² < 1` is the exponent; `λ = 2C/σ²` absorbs the bounded drift perturbation).  Finite at `0`
exactly when `θ < 1`, i.e. `κ < σ²/2`, i.e. Bessel dimension `< 2`, i.e. `a < N invβ`. -/
def cep_scale (θ lam z : ℝ) : ℝ := ∫ u in (0 : ℝ)..z, u ^ (-θ) * Real.exp (-(lam * u))

/-- The first two ranks `0, 1` of `Fin N` (`N ≥ 2`); the pair of consecutive particles `(π i0, π i1)`. -/
def cep_i0 (hN : 2 ≤ N) : Fin N := ⟨0, by omega⟩

/-- See `cep_i0`. -/
def cep_i1 (hN : 2 ≤ N) : Fin N := ⟨1, by omega⟩

/-- The pair `(π i0, π i1)` is isolated at scale `r` in the lift `y`: every other particle is at circle distance
`≥ r` from both (`|y k - y (π j) - m| ≥ r` for all `m ∈ ℤ`). -/
def cep_PairIsolated (hN : 2 ≤ N) (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) (r : ℝ) : Prop :=
  ∀ k : Fin N, k ≠ π (cep_i0 hN) → k ≠ π (cep_i1 hN) → ∀ m : ℤ,
    r ≤ |y k 0 - y (π (cep_i0 hN)) 0 - m| ∧ r ≤ |y k 0 - y (π (cep_i1 hN)) 0 - m|

end Necessity

section Existence

/-- Chamber coordinates: `ℝ^N` with the Euclidean structure. -/
abbrev Ch (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- The open cyclic alcove `{z_0 < ... < z_{N-1} < z_0 + 1}` (strict cyclic order, one winding). -/
def cep_Alcove (N : ℕ) : Set (Ch N) :=
  {z | (∀ k l : Fin N, k < l → z k < z l) ∧ ∀ k l : Fin N, z l < z k + 1}

/-- The convex ordered potential `Φ(z) = (a/N) ∑_{k<l} -log(2 sin(π(z_l - z_k)))` on the alcove (junk off it). -/
def cep_chamberPot (a : ℝ) (N : ℕ) (z : Ch N) : ℝ :=
  (a / N) * ∑ k : Fin N, ∑ l : Fin N,
    if k < l then -Real.log (2 * Real.sin (Real.pi * (z l - z k))) else 0

/-- Rank-coordinate vector as a point of `Ch N`. -/
def cep_toCh {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Ch N :=
  WithLp.toLp 2 (cep_rank π y)

/-- The Yosida family: for each `n > 0` a resolvent `J n` with values in the alcove, `G n z = n (z - J n z) =
∇Φ(J n z)`, Lipschitz with constant `n`, and the Yosida inequality
`⟨G m x - G n y, x - y⟩ ≥ -(1/m + 1/n) ⟨G m x, G n y⟩`. -/
structure cep_Yosida (a : ℝ) (N : ℕ) (J : ℝ → Ch N → Ch N) : Prop where
  mem : ∀ n z, 0 < n → J n z ∈ cep_Alcove N
  force : ∀ n z, 0 < n → n • (z - J n z) = gradient (cep_chamberPot a N) (J n z)
  lip : ∀ n, 0 < n → LipschitzWith (Real.toNNReal n) (fun z => n • (z - J n z))
  yosida : ∀ m n x y, 0 < m → 0 < n →
    -((1 / m + 1 / n) * inner ℝ (m • (x - J m x)) (n • (y - J n y)))
      ≤ inner ℝ (m • (x - J m x) - n • (y - J n y)) (x - y)

/-- Rank-coordinates back to a lift: `y (π k) = z k`. -/
def cep_unrank {N : ℕ} (π : Equiv.Perm (Fin N)) (z : Ch N) : Fin N → Euc 1 :=
  fun i => WithLp.toLp 2 (fun _ : Fin 1 => z (π.symm i))

/-- The chamber-coordinate noise `k ↦ W'_{π k, 0}`. -/
def cep_noise {Ω : Type*} {N : ℕ} (π : Ω → Equiv.Perm (Fin N)) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ)
    (t : ℝ) (ω : Ω) : Ch N :=
  WithLp.toLp 2 fun k => W' (Real.toNNReal t) ω (π ω k, 0)

/-- `Z` solves the chamber-coordinate SDE with drift `B` and noise intensity `σ'`. -/
def cep_IsChamberSolution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (π : Ω → Equiv.Perm (Fin N)) (σ' : ℝ) (B : Ch N → Ch N)
    (z₀ : Ω → Ch N) (Z : ℝ → Ω → Ch N) : Prop :=
  (∀ ω, Continuous fun t => Z t ω) ∧ (∀ t, 0 ≤ t → Measurable[ℱ t] (Z t)) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Z t ω = z₀ ω + (∫ s in (0 : ℝ)..t, B (Z s ω)) + σ' • cep_noise π W' t ω

end Existence

section Entropy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- The entropy conjunct of B.14 (first conjunct of the conclusion of `cepa_entropy_confined`). -/
def cep_EntropyConcl (P : Measure Ω) (D : DynData 1) (T : ℝ) (X : ℝ≥0 → Ω → Config 1 N) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, HasSelectedDensity P X t ∧
    gibbsEntropy D (selectedLaw P X t)
      + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
      ≤ gibbsEntropy D (selectedLaw P X 0)

/-! ### Cylinder objects for the regularised chamber flow -/

/-- The diagonal translation vector `(1,…,1)` of chamber coordinates. -/
def cep_diag (N : ℕ) : Ch N := WithLp.toLp 2 fun _ : Fin N => (1 : ℝ)

/-- The fundamental cell `{0 ≤ z_0 < 1}` of the diagonal `ℤ`-action. -/
def cep_cell (N : ℕ) [NeZero N] : Set (Ch N) := {z | 0 ≤ z 0 ∧ z 0 < 1}

/-- Reduction modulo the diagonal translation into the cell. -/
def cep_reduce {N : ℕ} [NeZero N] (z : Ch N) : Ch N := z - (⌊z 0⌋ : ℝ) • cep_diag N

/-- Gibbs weight `exp(-U/invβ)` as an extended real. -/
def cep_cylWeight {N : ℕ} (invβ : ℝ) (U : Ch N → ℝ) (z : Ch N) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(U z) / invβ))

/-- Partition function over the cell. -/
def cep_cylPartition {N : ℕ} [NeZero N] (invβ : ℝ) (U : Ch N → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in cep_cell N, cep_cylWeight invβ U z

/-- The normalised Gibbs reference measure on the cell. -/
def cep_cylRef {N : ℕ} [NeZero N] (invβ : ℝ) (U : Ch N → ℝ) : Measure (Ch N) :=
  (cep_cylPartition invβ U)⁻¹ • ((volume : Measure (Ch N)).restrict (cep_cell N)).withDensity (cep_cylWeight invβ U)

/-- `𝓗_U(μ) = H(μ | Z⁻¹ e^{-U/invβ} 1_cell) - log Z`, the cylinder analogue of `gibbsEntropy`. -/
def cep_cylEntropy {N : ℕ} [NeZero N] (invβ : ℝ) (U : Ch N → ℝ) (μ : Measure (Ch N)) : EReal :=
  ((relEntropy μ (cep_cylRef invβ U) : ℝ≥0∞) : EReal) - ((Real.log (cep_cylPartition invβ U).toReal : ℝ) : EReal)

/-- The cylinder Fisher information: variational formula with diagonally periodic smooth test fields that vanish
outside a tube around the alcove (the cylinder analogue of `fisherInfo`). -/
def cep_cylFisher {N : ℕ} [NeZero N] (invβ : ℝ) (U : Ch N → ℝ) (μ : Measure (Ch N)) : ℝ≥0∞ :=
  ⨆ (ζ : Ch N → Ch N) (_ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ ∧ (∀ z, ζ (z + cep_diag N) = ζ z) ∧
      ∃ R : ℝ, ∀ z, R ≤ Metric.infDist z (cep_Alcove N) → ζ z = 0),
    ENNReal.ofReal (∫ z, (-2 * ∑ k : Fin N, fderiv ℝ (fun w => ζ w k) z (EuclideanSpace.single k 1)
        + 2 * invβ⁻¹ * inner ℝ (gradient U z) (ζ z) - ‖ζ z‖ ^ 2) ∂μ)

end Entropy

end HRS.MC.Cepa
