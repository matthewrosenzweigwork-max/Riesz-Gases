import HRS.Energy.Commutator.Basic
import HRS.Commutator.Whole.Defs

/-!
# Sub-Coulomb commutator estimate on `𝕋^d` (torus version of M. Rosenzweig's note): definitions

Torus version of `HRS/Commutator/Whole/*` (see `docs/external/subcoulomb-plan.md` §7).  Source `[N]` as there.
Namespace `HRS.Commutator.TorusNote` (directory `HRS/Commutator/Torus/`).  This file has no `sorry`.

## Representation decisions and deviations from the `ℝ^d` note (each with its reason)

* **Kernel**: the repository's `periodicRiesz d s` (`|x|^{-s}+` smooth for `s>0`, `-log|x|+` smooth for `s=0`;
  *no factor `s⁻¹`*, mean-free); energy/commutator for it.  Translation to the note: `periodicRiesz = tScale s • g_note`
  locally (`tScale s = s` for `s>0`, `1` for `s=0`), so `F^{repo} = tScale·F^{note}`, `𝖠₁^{repo} = tScale·𝖠₁^{note}`, and
  `C₀^{repo} = tScale·C₀^{note}`; the constants are existential, so the statements read identically.
* **Signed `μ`**: a function `ρ : Torus d → ℝ` (the repository's `withDensityReal` only keeps `ρ⁺`), integrals
  against `volume` (probability Haar measure).  For `ρ ≥ 0` the quantities agree with `rieszEnergy`, `commQuantity`
  (`Bridge.lean`).
* **No log-integrability hypothesis** (`(1.loghyp)`): automatic for `ρ ∈ L^∞`/`L^p`, `p>1`, on a compact torus.
* **Scales**: `0 < η ≤ 1` (period 1).  The lemma layer holds for `η ≤ η₀(d,s)` (where the periodised truncation
  separates scales: `η^d ≪ 1`); the range `(η₀,1]` is recovered in `Assembly` by an explicit algebraic argument
  (`range_extension`, proved).  `λ = (N‖μ‖_∞)^{-1/d} ≤ 1` because `‖μ‖_∞ ≥ ∫μ = 1`.
* **Transport norm**: `TorusSubTransport` is the torus analogue of `HasFracTransportBound`, in the repository's
  `IsLipschitzVF` / `IsFracDeriv` conventions: `ŵ(k) = (2π|k|)^{(d-s)/2} v̂(k)` for *all* `k` (so `w` has mean zero) and
  `‖w‖_{L^{2d/(d-s-2)}(𝕋^d)} ≤ F` with the *unit-volume* measure.
* **Configuration**: `X ∉ collisionSet d N` (pairwise distinct), `1 ≤ N`.
* **Unit-scale lemma layer in original variables** (`η`-form).  The note's unit-scale statements on `𝕋^d_R`, `R=1/η`, are
  written on `𝕋^d` itself: `x̃ = x/η`, frequencies `ξ = ηk`, cells of side `≈η`.  Dictionary (used in every docstring):
  `‖σ̃‖²_{Ḣ^t(𝕋_R)} = η^{d+2t} ∑_{k≠0}(2π|k|)^{2t}|σ̂(k)|²`, `‖σ̃‖²_{H^t(𝕋_R)} = η^d ∑_k (1+4π²η²|k|²)^t|σ̂(k)|²`,
  `F̃ = η^s F` (`s=0`: `F̃ = F`), `g̃_1(x̃) = η^s g_η(x)`, `f_η(x) = η^{-s}f_1(x/η)`, `𝒞̃ = η^s 𝒞`, `ũ = η^{s+1}u`;
  all unit-scale energies `Ẽ = η^s Q_η`, `Q_η = F - 1_{s=0} log η/(2N) + C_p(η^{-s}/N + ‖μ‖_p η^{d(1-1/p)-s})`.
  (For `s = 0` the torus kernel has no `log η` shift, `g_T(ηx̃) = G_R(x̃)`; the `-log η/(2N)` comes from `g_η(0) = -log η + O(1)`.)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ}

/-- `tScale s = s` (`s > 0`), `1` (`s = 0`): `periodicRiesz = tScale s • g_note` near `0`. -/
def tScale (s : ℝ) : ℝ := if s = 0 then 1 else s

/-! ### Energy, commutator, integrability (signed density) -/

/-- Deleted-diagonal pair functional on the torus for a signed density `ρ` (as `Whole.pairGen`). -/
def pairT (k : Torus d → Torus d → ℝ) (X : Config d N) (ρ : Torus d → ℝ) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)
    - (2 / (N : ℝ)) * ∑ i, (∫ y, k (X i) y * ρ y)
    + ∫ x, ∫ y, k x y * ρ x * ρ y

/-- Absolute convergence of `pairT`. -/
def PairIntegrableT (k : Torus d → Torus d → ℝ) (X : Config d N) (ρ : Torus d → ℝ) : Prop :=
  (∀ i, Integrable (fun y => k (X i) y * ρ y)) ∧
    Integrable (fun p : Torus d × Torus d => k p.1 p.2 * ρ p.1 * ρ p.2)

/-- `F_N(X, μ) = ½ ∬_{△ᶜ} g(x-y) d(μ_N-μ)^{⊗2}` for the repository's kernel `periodicRiesz d s`. -/
def modEnergyT (s : ℝ) (X : Config d N) (ρ : Torus d → ℝ) : ℝ :=
  (1 / 2) * pairT (fun x y => periodicRiesz d s (x - y)) X ρ

/-- `𝖠₁[X, μ, v] = ∬_{△ᶜ} (v(x)-v(y))·∇g(x-y) d(μ_N-μ)^{⊗2}` (repository's `commKernel`, `periodicRieszGrad`). -/
def commAT (s : ℝ) (X : Config d N) (ρ : Torus d → ℝ) (v : Torus d → Euc d) : ℝ :=
  pairT (commKernel (periodicRieszGrad d s) v) X ρ

/-- Absolute convergence of the integrals defining `F_N`. -/
def EnergyIntegrableT (s : ℝ) (X : Config d N) (ρ : Torus d → ℝ) : Prop :=
  PairIntegrableT (fun x y => periodicRiesz d s (x - y)) X ρ

/-- Absolute convergence of the integrals defining `𝖠₁`. -/
def CommIntegrableT (s : ℝ) (X : Config d N) (ρ : Torus d → ℝ) (v : Torus d → Euc d) : Prop :=
  PairIntegrableT (commKernel (periodicRieszGrad d s) v) X ρ

/-- `‖ρ‖_{L^p(𝕋^d)}` (unit volume). -/
def normT (p : ℝ≥0∞) (ρ : Torus d → ℝ) : ℝ := (eLpNorm ρ p volume).toReal

/-- `λ = (N‖μ‖_∞)^{-1/d}`. -/
def lamT (d N : ℕ) (ρ : Torus d → ℝ) : ℝ := ((N : ℝ) * normT ⊤ ρ) ^ (-(1 : ℝ) / d)

/-- A bounded measurable real density of mass one (the temporary assumption of the unit-scale layer). -/
structure BddDensityT (ρ : Torus d → ℝ) : Prop where
  measurable : Measurable ρ
  bdd : ∃ B : ℝ, ∀ x, |ρ x| ≤ B
  mass : ∫ x, ρ x = 1

/-- The transport bound of the torus Theorem 1.1: `‖∇v‖_∞ + ‖|∇|^{(d-s)/2}v‖_{L^{2d/(d-s-2)}(𝕋^d)} ≤ K`
(torus analogue of `HasFracTransportBound`, in the conventions of `HasTransportBound`). -/
def TorusSubTransport (d : ℕ) (s : ℝ) (v : Torus d → Euc d) (K : ℝ) : Prop :=
  ∃ L F : ℝ, 0 ≤ L ∧ 0 ≤ F ∧ IsLipschitzVF L v ∧
    (∃ w : Torus d → Euc d, IsFracDeriv (((d : ℝ) - s) / 2) v w ∧
      eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - s - 2))) volume ≤ ENNReal.ofReal F) ∧
    L + F ≤ K

/-- The bracket `Q_η = F_N - 1_{s=0} log η/(2N) + C_p(η^{-s}/N + ‖μ‖_{L^p}η^{d(1-1/p)-s})` of Prop. 1.2. -/
def scaleQT (s Cp : ℝ) (p : ℝ≥0∞) (η : ℝ) {N : ℕ} (X : Config d N) (ρ : Torus d → ℝ) : ℝ :=
  modEnergyT s X ρ - (if s = 0 then Real.log η / (2 * (N : ℝ)) else 0) +
    Cp * (η ^ (-s) / (N : ℝ) + normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s))

/-! ### Periodisation and the truncation at scale `η` -/

/-- Periodisation `∑_{m∈ℤ^d} f(x+m)` of `f : ℝ^d → ℝ` (`tsum`, summable for the decaying `f` used). -/
def perio (f : Euc d → ℝ) (x : Torus d) : ℝ :=
  ∑' m : Lattice d, f (Torus.rep x + Lattice.toEuc m)

/-- `f_η^𝕋 = tScale · (perio f_η - ∫ perio f_η)`: the periodised, mean-free positive truncation
(`f_η = Whole.fTrunc s η`, `[N] (2.positivecut)`). -/
def fTorus (s η : ℝ) (x : Torus d) : ℝ :=
  tScale s * (perio (Whole.fTrunc s η) x - ∫ y : Torus d, perio (Whole.fTrunc s η) y)

/-- Fourier side of `f_η`: `f̂_η(ξ) = c_φ ∫_0^η t^{d-s}φ̂(tξ) dt/t`. -/
def fHatEta (d : ℕ) (s η : ℝ) (ξ : Euc d) : ℝ :=
  Whole.cPhi d s * ∫ t in Set.Ioc (0 : ℝ) η,
    t ^ (2 * Whole.alphaE d s) * (𝓕 (fun x : Euc d => ((Whole.phi x : ℝ) : ℂ)) (t • ξ)).re / t

/-- The Fourier coefficients of `g_η^𝕋`: `ĝ(k) - tScale·f̂_η(k)` (`k ≠ 0`), `0` at `k = 0`. -/
def gTcoef (d : ℕ) (s η : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else rieszCoeff d s k - tScale s * fHatEta d s η (Lattice.toEuc k)

/-- The value `g_η^𝕋(0) = ∑_k ĝ_η(k)` of the smooth kernel `g_η^𝕋` at the origin
(`periodicRiesz d s 0` is a junk value). -/
def gTorus0 (d : ℕ) (s η : ℝ) : ℝ := ∑' k : Lattice d, gTcoef d s η k

/-- `g_η^𝕋 = periodicRiesz - f_η^𝕋` off the origin (mean-free; smooth; `g_η^𝕋(x) = η^{-s}g̃_1(x/η)`), with
the explicit value `gTorus0` at `0`. -/
def gTorus (s η : ℝ) (x : Torus d) : ℝ :=
  if x = 0 then gTorus0 d s η else periodicRiesz d s x - fTorus s η x

/-! ### Fourier objects on the lattice, with the scale `η` -/

/-- `‖·‖²_{Ḣ^t}`-sum `∑_{k≠0}(2π|k|)^{2t}|F(k)|²` (original variables; unit scale is `η^{d+2t}` times it). -/
def homSqT (t : ℝ) (F : Lattice d → ℂ) : ℝ≥0∞ :=
  ∑' k : Lattice d, if k = 0 then 0 else
    ENNReal.ofReal ((2 * Real.pi * Lattice.enorm k) ^ (2 * t)) * ‖F k‖ₑ ^ 2

/-- `η^d ∑_k (1+4π²η²|k|²)^t |F(k)|²`: the squared `H^t(𝕋_R)` norm of the rescaled object, `R = 1/η`. -/
def sobSqT (η t : ℝ) (F : Lattice d → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (η ^ d) * ∑' k : Lattice d,
    ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ t) * ‖F k‖ₑ ^ 2

/-- `F ↦ χ(ηk/L) F(k)`: the Fourier side of `P_{≤L}` at scale `η` (`χ = Whole.chi`). -/
def lowFreqT (η L : ℝ) (F : Lattice d → ℂ) : Lattice d → ℂ :=
  fun k => ((Whole.chi ((η / L) • Lattice.toEuc k) : ℝ) : ℂ) * F k

/-- `F` represents `⟨∇⟩_η^α f` (`⟨∇⟩_η^α` has symbol `(1+4π²η²|k|²)^{α/2}`): coefficientwise, as `IsFracDeriv`. -/
def IsBesselRepT (η α : ℝ) (f F : Torus d → ℝ) : Prop :=
  ∀ k : Lattice d, Torus.fcoef F k =
    (((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) : ℝ) : ℂ) * Torus.fcoef f k

/-- The low-pass `P^η_{≤} f = ψ^𝕋_{1/η} * f` (convolution with the periodised Schwartz kernel). -/
def PleqT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η : ℝ) (f : Torus d → E)
    (x : Torus d) : E :=
  ∫ y, perio (Whole.psiL η⁻¹) (x - y) • f y

/-- `P^η_> = I - P^η_≤`. -/
def PgtT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η : ℝ) (f : Torus d → E)
    (x : Torus d) : E :=
  f x - PleqT η f x

/-- `∇g^{𝕋}_{≤}`: the low-frequency part of the force. -/
def gloForceT (s η : ℝ) (x : Torus d) : Euc d := PleqT η (periodicRieszGrad d s) x

/-- `∇g^{𝕋}_{>}`. -/
def ghiForceT (s η : ℝ) (x : Torus d) : Euc d := periodicRieszGrad d s x - gloForceT s η x

/-! ### Signed measures on the torus, cells -/

/-- A real signed measure on `𝕋^d` as a pair of positive measures. -/
structure SMT (d : ℕ) where
  pos : Measure (Torus d)
  neg : Measure (Torus d)

namespace SMT

/-- `∫ f dσ`. -/
def int (σ : SMT d) (f : Torus d → ℝ) : ℝ := ∫ x, f x ∂σ.pos - ∫ x, f x ∂σ.neg

/-- `∫ F dσ`, `ℝ^d`-valued. -/
def intV (σ : SMT d) (F : Torus d → Euc d) : Euc d := ∫ x, F x ∂σ.pos - ∫ x, F x ∂σ.neg

/-- `σ(𝕋^d)`. -/
def mass (σ : SMT d) : ℝ := σ.int fun _ => 1

/-- Fourier coefficient `σ̂(k) = ∫ e^{-2πik·x} dσ`. -/
def coef (σ : SMT d) (k : Lattice d) : ℂ :=
  ∫ x, Torus.mode (-k) x ∂σ.pos - ∫ x, Torus.mode (-k) x ∂σ.neg

/-- `∬ k dσ dσ` (iterated). -/
def pair2 (σ : SMT d) (k : Torus d → Torus d → ℝ) : ℝ := σ.int fun x => σ.int fun y => k x y

/-- `(F*σ)(x) = ∫ F(x-y)dσ(y)`. -/
def convForce (σ : SMT d) (F : Torus d → Euc d) (x : Torus d) : Euc d := σ.intV fun y => F (x - y)

/-- Finite parts. -/
def IsFinite (σ : SMT d) : Prop := IsFiniteMeasure σ.pos ∧ IsFiniteMeasure σ.neg

/-- The signed measure `a dx`. -/
def ofDensity (a : Torus d → ℝ) : SMT d :=
  ⟨volume.withDensity fun x => ENNReal.ofReal (a x),
    volume.withDensity fun x => ENNReal.ofReal (-a x)⟩

end SMT

/-- `ν = μ_N - μ`. -/
def chargeT (X : Config d N) (ρ : Torus d → ℝ) : SMT d :=
  ⟨HRS.empirical X + volume.withDensity (fun x => ENNReal.ofReal (-ρ x)),
    volume.withDensity fun x => ENNReal.ofReal (ρ x)⟩

/-- `𝒞_h(v,σ)` for the force `F = ∇h`. -/
def CcommT (F : Torus d → Euc d) (v : Torus d → Euc d) (σ : SMT d) : ℝ :=
  σ.pair2 (commKernel F v)

/-- `𝒞_h(v,a)` for a density `a`. -/
def CcommFunT (F : Torus d → Euc d) (v : Torus d → Euc d) (a : Torus d → ℝ) : ℝ :=
  ∫ x, ∫ y, commKernel F v x y * a x * a y

/-- `‖σ‖²_h = ∬ h(x-y)dσ dσ`. -/
def kerEnergyT (h : Torus d → ℝ) (σ : SMT d) : ℝ := σ.pair2 fun x y => h (x - y)

/-- Number of cells per direction at scale `η`: `⌊1/η⌋` (so cell side `∈ [η, 2η)` for `η ≤ 1`). -/
def nCells (η : ℝ) : ℕ := ⌊η⁻¹⌋₊

/-- The cell `Q_j = ∏ [j_i/m, (j_i+1)/m)`, `m = nCells η`, `j ∈ {0..m-1}^d`. -/
def cellT (m : ℕ) (j : Fin d → Fin m) : Set (Torus d) :=
  {x | ∀ i, (j i : ℝ) / m ≤ Torus.rep x i ∧ Torus.rep x i < ((j i : ℝ) + 1) / m}

/-- `(∑_j sup_{Q_j}|f|^p)^{1/p}` over the cells of scale `η`, in `ℝ≥0∞`. -/
def cellSupNorm {E : Type*} [NormedAddCommGroup E] (η p : ℝ) (f : Torus d → E) : ℝ≥0∞ :=
  (∑ j : Fin d → Fin (nCells η), (⨆ x ∈ cellT (nCells η) j, ‖f x‖ₑ) ^ p) ^ (1 / p)

open Classical in
/-- Cell mass `n_j = μ_N(Q_j)`. -/
def occT (η : ℝ) (X : Config d N) (j : Fin d → Fin (nCells η)) : ℝ :=
  (1 / (N : ℝ)) * ((Finset.univ.filter fun i => X i ∈ cellT (nCells η) j).card : ℝ)

end HRS.Commutator.TorusNote
