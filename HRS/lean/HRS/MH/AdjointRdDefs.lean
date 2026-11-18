import HRS.Whole.AppendixAAdjoint
import HRS.Whole.AppendixALemmas
import HRS.MH.ScreenedDefs

/-!
# Definitions for Proposition S.A.12 on `R^d` (shared by the packet statements and proofs)

Extracted unchanged from `HRS/MH/AdjointRdSpec.lean`; no `sorry`.  See `HRS/MH/AdjointRdPlan.md`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.AdjointRd

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- `L`-periodic convolution `(γ ⊛_L h)(x) = ∫_{[0,L)^d} γ(x-y) h(y) dy` for `L`-periodic `γ, h` (the integrand is
`L`-periodic in `y`, so any period cell gives the same value).  No principal value is needed: `s < d` makes `γ_L`
locally integrable (`IsPeriodicRieszKernel.locInt`). -/
def perConv (L : ℝ) (γ h : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y in HRS.Whole.AppendixALemmas.periodBox d L, γ (x - y) * h y

/-- The pointwise periodic nonlocal operator `𝒢_L[F] = ∑_{ij} M_{ji} ∂_i (γ_L ⊛_L (μ ∂_jF))`
(`M^*_{ij} = M_{ji}`, as in `forwardPairing` / `nonlocalTestRd`). -/
def perNonlocal (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ F : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, M j i *
    fderiv ℝ (perConv L γ (fun y => μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) x
      (EuclideanSpace.single i (1 : ℝ))

/-- `u` is `C^∞` with all partial derivatives of order `≤ m` bounded. -/
def BddJets (m : ℕ) (u : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ u ∧ ∀ j ≤ m, ∀ idx : Fin j → Fin d, ∃ B : ℝ, ∀ x, |partialDeriv idx u x| ≤ B

/-- `∑_{j ≤ m} C(m,j) ∑_{idx ∈ [d]^j} ∫ (w ∂^{idx}F)²` (ordered index tuples).  With `w = 1` and `F ∈ C_c^∞` this is
EXACTLY the squared Fourier norm `‖F‖²_{H^m}` of `sobolevNormE m`: `(1+4π²|ξ|²)^m = ∑_j C(m,j) (4π²)^j (∑_i ξ_i²)^j` and
`(∑_iξ_i²)^j = ∑_{idx} ∏_lξ_{idx_l}²`, Plancherel for `∂^{idx}F` (packet N2); this is why the sharp constant `1` of
`adjoint_rd_sobolev` is visible in the energy. -/
def jetSq (m : ℕ) (w F : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∫ x, (w x * partialDeriv idx F x) ^ 2

/-- The mixed jet pairing `∑_{j ≤ m} C(m,j) ∑_{idx} ∫ w² ∂^{idx}F ∂^{idx}G`. -/
def jetPair (m : ℕ) (w F G : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) *
    ∑ idx : Fin j → Fin d, ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)

/-- The dissipation `∑_{j ≤ m} C(m,j) ∑_{idx} ∑_i ∫ w² |∂_i∂^{idx}F|²`. -/
def dissipSq (m : ℕ) (w F : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∑ i : Fin d,
    ∫ x, (w x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2

/-- The local cell energy `𝓕_z(τ) = ∑_{|α| ≤ m} ‖χ_z^τ ∂^αF‖²` with the advected cutoff `χ_z^τ = χ(Ψ_τ^{-1}· - z)`,
`z ∈ ℝ^d` a real centre. -/
def cellEnergy (m : ℕ) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z : Euc d) (F : Euc d → ℝ) : ℝ :=
  jetSq m (advCutoff χ Ψ τ z) F

/-- The cell dissipation with the advected cutoff. -/
def cellDissip (m : ℕ) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z : Euc d) (F : Euc d → ℝ) : ℝ :=
  dissipSq m (advCutoff χ Ψ τ z) F

/-- `F` is a classical solution on `[0,t]` of `∂_τF = νΔF + b^τ·∇F + G` of the regularity needed to differentiate the
local energies: `F(τ), G(τ)` are `C^∞`, every partial derivative of `F, G` is jointly continuous on `[0,t] × ℝ^d`, and
for jets of order `≤ m` the time derivative exists (one-sided at the ends) and commutes with `∂^{idx}`. -/
structure IsClassicalSol (m : ℕ) (ν : ℝ) (b : ℝ → Euc d → Euc d) (G : ℝ → Euc d → ℝ) (t : ℝ)
    (F : ℝ → Euc d → ℝ) : Prop where
  smooth : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (F τ) ∧ ContDiff ℝ ∞ (G τ)
  contF : ∀ j : ℕ, ∀ idx : Fin j → Fin d,
    ContinuousOn (fun p : ℝ × Euc d => partialDeriv idx (F p.1) p.2) (Icc 0 t ×ˢ univ)
  contG : ∀ j : ℕ, ∀ idx : Fin j → Fin d,
    ContinuousOn (fun p : ℝ × Euc d => partialDeriv idx (G p.1) p.2) (Icc 0 t ×ˢ univ)
  deriv_t : ∀ j ≤ m, ∀ idx : Fin j → Fin d, ∀ x : Euc d, ∀ τ ∈ Icc (0 : ℝ) t,
    HasDerivWithinAt (fun τ' => partialDeriv idx (F τ') x)
      (partialDeriv idx (fun y => ν * Laplacian.laplacian (F τ) y +
        inner ℝ (b τ y) (gradient (F τ) y) + G τ y) x) (Icc 0 t) τ

/-- The qualitative data of a periodic approximant (Step 3 of `B:sec:adjoint-rd-proof`, S L10436-10441): `L ≥ 1`, the periodic
Riesz kernel `γ_L`, `M`, `0 ≤ ν`, an `L`-periodic smooth probability density path `μ`, `V` periodic smooth, and the periodic
drift `b = M ∇γ_L ⊛_L μ - ∇V` (`torusDriftL`).  Nothing quantitative: every smooth periodic function has bounded
derivatives of all orders, which is all that existence (packet T1) needs. -/
structure PerSmooth (s : ℝ) (T : ℝ) (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
    (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d) : Prop where
  hL : 1 ≤ L
  hγ : HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ
  hν : 0 ≤ ν
  μ_periodic : ∀ τ ∈ Icc (0 : ℝ) T, ∀ (x : Euc d) (k : Fin d → ℤ), μ τ (x + L • latticePt k) = μ τ x
  μ_smooth : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (μ τ)
  μ_prob : ∀ τ ∈ Icc (0 : ℝ) T, (∀ x, 0 ≤ μ τ x) ∧
    ∫ x in HRS.Whole.AppendixALemmas.periodBox d L, μ τ x = 1
  V_periodic : ∀ (x : Euc d) (k : Fin d → ℤ), V (x + L • latticePt k) = V x
  V_smooth : ContDiff ℝ ∞ V
  b_eq : ∀ τ ∈ Icc (0 : ℝ) T, b τ = HRS.Whole.AppendixALemmas.torusDriftL M L γ (μ τ) V

/-- The quantitative data of a periodic approximant, uniform in `L` (the output of packet T2): `PerSmooth` plus
`|M| ≤ MB`, `ν ≤ ν̄`, `‖∇^jμ‖_∞ ≤ Λ` (`j ≤ m+3`), the periodic decay (every point has a nearest lattice point `Lk` with
`⟨x-Lk⟩^{d+3}|∇^jμ(x)| ≤ Λ`: the periodic form of `S:eq:mf-regularity-whole`), `‖∇^jV‖_∞ ≤ Λ_V` (`2 ≤ j ≤ m+3`), and
the advecting-drift bounds with a constant `Cb` independent of `L`. -/
structure PerData (s : ℝ) (m : ℕ) (MB Λ ΛV νbar Cb T : ℝ) (L : ℝ) (γ : Euc d → ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ)
    (b : ℝ → Euc d → Euc d) : Prop extends PerSmooth s T L γ M ν μ V b where
  hM : PDE.MatBound MB M
  hν' : ν ≤ νbar
  μ_bdd : ∀ τ ∈ Icc (0 : ℝ) T, ∀ j ≤ m + 3, ∀ x, ‖iteratedFDeriv ℝ j (μ τ) x‖ ≤ Λ
  μ_decay : ∀ τ ∈ Icc (0 : ℝ) T, ∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
    jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (μ τ) x‖ ≤ Λ
  V_bdd : ∀ j : ℕ, 2 ≤ j → j ≤ m + 3 → ∀ x, ‖iteratedFDeriv ℝ j V x‖ ≤ ΛV
  b_drift : IsAdvectingDrift m Cb T b

/-- A smooth `L`-periodic classical solution of `∂_τF = νΔF + b·∇F - 𝒢_L[F] + S` on `[0,t]` (`S` a smooth periodic
source, `S = 0` for existence and the uniform bound). -/
structure IsPerSol (m : ℕ) (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
    (μ : ℝ → Euc d → ℝ) (b : ℝ → Euc d → Euc d) (S : ℝ → Euc d → ℝ) (t : ℝ) (F : ℝ → Euc d → ℝ) : Prop where
  sol : IsClassicalSol m ν b (fun τ y => -perNonlocal L γ M (μ τ) (F τ) y + S τ y) t F
  periodic : ∀ τ ∈ Icc (0 : ℝ) t, ∀ (x : Euc d) (k : Fin d → ℤ), F τ (x + L • latticePt k) = F τ x
  bdd : ∀ τ ∈ Icc (0 : ℝ) t, BddJets m (F τ)

/-- The supremum of the local cell energies over the fine-lattice centres `cellPt d z` (`ℝ≥0∞`-valued: the energies of
`BddJets` functions are bounded uniformly in the centre).  Fine-lattice centres: the closed unit balls about
`⌈√d⌉⁻¹ℤ^d` cover `ℝ^d` (`ulNormLat`, `MS-ULOC-LAT`); a real-centre supremum is equivalent
(`uloc_embedding_cutoffs`, third conjunct). -/
def cellSup (m : ℕ) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (F : Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ z : Fin d → ℤ, ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d z) F)

/-- The weighted cell energy `∑_{z ∈ ℤ^d} ⟨cellPt z⟩^{-(d+3)} 𝓕_{cellPt z}(τ)` on the fine lattice (the covering
family of `varpiNormE`). -/
def cellWeighted (m : ℕ) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (F : Euc d → ℝ) : ℝ≥0∞ :=
  ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
    ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d z) F)

/-- The abstract weak form: `A σ ψ` is the (already integrated by parts) operator applied to the test function, so
that `d/dσ ∫F ψ = ∫ F · A σ ψ`.  `IsForwardSolutionRd C t φ F` is this with `A = weakOp C t` and each of the four
pairings separately integrable. -/
structure IsWeakSol (A : ℝ → (Euc d → ℝ) → (Euc d → ℝ)) (t : ℝ) (φ : Euc d → ℝ) (F : ℝ → Euc d → ℝ) : Prop where
  integrable_x : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
    Integrable (fun x => F σ x * ψ x) ∧ Integrable (fun x => F σ x * A σ ψ x)
  integrable_σ : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → IntegrableOn (fun σ => ∫ x, F σ x * A σ ψ x) (Icc (0 : ℝ) t)
  eq : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ τ ∈ Icc (0 : ℝ) t,
    ∫ x, F τ x * ψ x = (∫ x, φ x * ψ x) + ∫ σ in Icc (0 : ℝ) τ, ∫ x, F σ x * A σ ψ x

/-- The test-function operator of `forwardWeakTerm`: `ν Δψ - div(b ψ) - nonlocalTestRd`, coefficients at `t - σ`. -/
def weakOp (C : WholeCoeff d) (t : ℝ) (σ : ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  C.ν * Laplacian.laplacian ψ x - movDiv (fun y => ψ y • C.drift (t - σ) y) x - nonlocalTestRd C (t - σ) ψ x

/-- The conclusion of `per_coefficients` as a predicate: the uniform `PerData` bounds for `L ≥ max 1 L₀`, `ε ∈ (0,1]` and the
locally uniform convergence of the reversed periodic drifts and densities to `drift(max (t-τ) 0)`, `μ(max (t-τ) 0)`. -/
def PerApprox (s : ℝ) (m : ℕ) (MB Λ' ΛV' νbar Cb T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (γ : ℝ → Euc d → ℝ) (t L₀ : ℝ) (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ) : Prop :=
  (∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 →
    PerData s m MB Λ' ΛV' νbar Cb T L (γ L) D.M D.invβ (μL L ε) (VL L ε)
      (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε))) ∧
  (∀ (K : Set (Euc d)), IsCompact K → ∀ j ≤ m + 1, ∀ δ : ℝ, 0 < δ →
    ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) x -
        iteratedFDeriv ℝ j ((D.coeff μ).drift (max (t - τ) 0)) x‖ ≤ δ ∧
      ‖iteratedFDeriv ℝ j (μL L ε τ) x - iteratedFDeriv ℝ j (μ (max (t - τ) 0)) x‖ ≤ δ)

/-- The cell `Ψ_τ(c + [0,1]^d)` with a real corner `c` (`flowCell Ψ τ z = flowCellAt Ψ τ (latticePt z)`). -/
def flowCellAt (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (c : Euc d) : Set (Euc d) :=
  Ψ τ '' {y | ∀ i, 0 ≤ (y - c) i ∧ (y - c) i ≤ 1}

/-- The centred period cell `[-L/2, L/2)^d`. -/
def centeredBox (d : ℕ) (L : ℝ) : Set (Euc d) := {y | ∀ i, -(L / 2) ≤ y i ∧ y i < L / 2}

/-- The Euclidean near operator `∑_{ij}M_{ji}∂_i(g * (a ∂_jF))`, `g = rieszKernel d s` (a compactly supported smooth
density `a`, a smooth function `F`; the convolution is a smooth function, `s < d`). -/
def eucNonlocal (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (a F : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, M j i *
    fderiv ℝ (fun x' => ∫ y, rieszKernel d s (x' - y) * (a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) x
      (EuclideanSpace.single i (1 : ℝ))

/-- The cell mass `∑_{j≤m}C(m,j)∑_{idx}∫_{Q_{z'}^τ}(∂^{idx}F)²` on the (uncut) flowed unit cube `Ψ_τ(z'+[0,1]^d)`. -/
def cellMass (m : ℕ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z' : Fin d → ℤ) (F : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) *
    ∑ idx : Fin j → Fin d, ∫ x in flowCell Ψ τ z', (partialDeriv idx F x) ^ 2

/-- The time derivative of the cell energy `𝓕_c(τ)` along a classical solution of `∂_τF = νΔF + b·∇F + G`:
`∑_{j≤m}C(m,j)∑_{idx}∫[2(χ_c^τ)²∂^{idx}F ∂^{idx}(νΔF + b·∇F + G) + 2χ_c^τ (b·∇χ_c^τ)(∂^{idx}F)²]`
(`∂_τχ_c^τ = b·∇χ_c^τ`, `HRS.MS.FlowD.flow_cutoff_hasDerivWithinAt`, FlowD.lean:212). -/
def cellRate (m : ℕ) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (c : Euc d) (ν : ℝ) (b : Euc d → Euc d)
    (F G : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
    ∫ x, (2 * advCutoff χ Ψ τ c x ^ 2 * (partialDeriv idx F x *
        partialDeriv idx (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) +
      2 * advCutoff χ Ψ τ c x * inner ℝ (b x) (gradient (advCutoff χ Ψ τ c) x) * partialDeriv idx F x ^ 2)

/-- The offsets `E ⊂ ℤ^d` of fine-lattice centres whose unit balls cover `B̄(0,8)`: in preimage coordinates the support of
the cut `χ̂_c^τ` is `B(c,8)`, so the near part of the nonlocal operator only sees the cells `c + cellPt k`, `k ∈ E`. -/
def CoversBall8 (E : Finset (Fin d → ℤ)) : Prop :=
  Metric.closedBall (0 : Euc d) 8 ⊆ ⋃ k ∈ E, Metric.closedBall (cellPt d k) 1

/-- **(HN-E)** The Euclidean nonlocal cell inequality for the NEAR operator (compactly supported density
`a = χ̂_c^τ μ`, `eucNonlocal`): for every lattice centre, `-2·jetPair(χ_c^τ; F, 𝒢^{near}_aF) ≤ κ∑_{k∈E}D_{z+k} + A∑_{k∈E}𝓕_{z+k}`,
uniformly over the admissible data (advecting drift with flow, `M` with `hreg M`, a `(m+3,Λ)`-regular density, `F` with bounded
jets).  `κ = 0` in the regimes without dissipation. -/
def EucNlBound (s : ℝ) (m : ℕ) (Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (E : Finset (Fin d → ℤ)) (A κ : ℝ)
    (hreg : Matrix (Fin d) (Fin d) ℝ → Prop) : Prop :=
  ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d), IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
    ∀ M : Matrix (Fin d) (Fin d) ℝ, hreg M → ∀ μ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ →
    ∀ F : Euc d → ℝ, BddJets m F → ∀ τ ∈ Icc (0 : ℝ) T, ∀ z : Fin d → ℤ,
      -(2 * jetPair m (advCutoff χ Ψ τ (cellPt d z)) F
          (eucNonlocal s M (fun y => advCutoff χh Ψ τ (cellPt d z) y * μ y) F)) ≤
        κ * ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F +
          A * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F

/-- **(HN)** The nonlocal cell inequality for the periodic operator `perNonlocal`, uniformly in `L` and the admissible
data: near part and far part, the far part through Schur coefficients `Kc` (`screened_far_periodic`) acting on the cell
masses.  For all lattice centres `z`:
`-2·jetPair(χ_z; F, 𝒢_L[F]) ≤ κ∑_{k∈E}D_{z+k} + A(∑_{k∈E}𝓕_{z+k} + ∑_{z'}K_{zz'}·mass_{z'})`, with
`sup_z∑_{z'}K_{zz'} ≤ CK` and `∑_zω_zK_{zz'} ≤ CKω_{z'}`. -/
def NlCellBound (s : ℝ) (m : ℕ) (MB Λ ΛV νbar Cb T : ℝ) (χ χh : Euc d → ℝ) (E : Finset (Fin d → ℤ))
    (A κ CK L₁ : ℝ) (hreg : Matrix (Fin d) (Fin d) ℝ → Prop) : Prop :=
  ∀ (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ)
    (b : ℝ → Euc d → Euc d), L₁ ≤ L → PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b → hreg M →
    ∀ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
    ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
      (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal CK) ∧
      (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
        ENNReal.ofReal CK * ENNReal.ofReal (cellWeight d z')) ∧
      ∀ F : Euc d → ℝ, BddJets m F → (∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) →
        ∀ z : Fin d → ℤ,
          -(2 * jetPair m (advCutoff χ Ψ τ (cellPt d z)) F (fun x => perNonlocal L γ M (μ τ) F x)) ≤
            κ * ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F +
              A * (∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F +
                (∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)).toReal)

/-- The nonlocal test function of an `L`-periodic problem: with `h_ψ := γ_L * ψ = ∫_{ℝ^d} γ(· - u)ψ(u)du` (an `L`-periodic
smooth function for `ψ ∈ C_c^∞`), `∑_{ij} M_{ji} ∂_j(μ ∂_i h_ψ)`.  It is `L`-periodic. -/
def nonlocalTestPer (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, M j i *
    partialDeriv (fun _ : Fin 1 => j) (fun y => μ y * gradient (fun w => ∫ u, γ (w - u) * ψ u) y i) x

/-- The test-function operator of the weak form of an `L`-periodic solution against a compactly supported `ψ`:
`νΔψ - div(b^σψ) - 1_{centeredBox d L} · nonlocalTestPer`.  The box indicator is what makes `∫_{ℝ^d} F · A ψ` convergent
for a periodic (non-decaying) `F`: `∫_{ℝ^d} ψ · 𝒢_L[F] = ∫_{box} F · nonlocalTestPer ψ`, any period cell, by Fubini and periodicity
of `F`, `μ`, `γ`.  Here `μ, b` are the REVERSED paths (coefficients at forward time `σ`). -/
def weakOpPer (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ)
    (b : ℝ → Euc d → Euc d) (σ : ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ν * Laplacian.laplacian ψ x - movDiv (fun y => ψ y • b σ y) x -
    (centeredBox d L).indicator (nonlocalTestPer L γ M (μ σ) ψ) x

/-- `∑_{z ∈ ℤ^d} ‖g‖_{L²(B(cellPt z, 1))}`, the `ℓ¹(L²)` norm on the fine-lattice unit balls: the dual norm to the
`L²_uloc` norm (`|∫ F g| ≤ sup_z‖F‖_{L²(B_z)} · cellL2Sum g`). -/
def cellL2Sum (g : Euc d → ℝ) : ℝ≥0∞ :=
  ∑' z : Fin d → ℤ, (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ)

end HRS.MH.AdjointRd

