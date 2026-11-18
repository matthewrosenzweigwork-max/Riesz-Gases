import HRS.MC.Sec7Vocab
import HRS.MC.RegSet
import HRS.MC.QRVocab
import HRS.Main.Headline

/-!
# Vocabulary of the `field_chaos` (row 7.6) packet statements (sorry-free)

Sorry-free definitions used by the statements of `HRS/MC/S7FCPlan.lean` and by their proofs: `s7fcPrep` (the `PreparedData` of a
regime), `FRKernel` (a smooth finite-rank symmetric kernel with a chosen decomposition), `fcGen`, `fcPartAt`, `fcGaussAt`,
`FCKernelData`.  Namespace `HRS.MC.Sec7.FCPlan`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCPlan

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec

variable {d : ℕ}

/-! ### Vocabulary -/

/-- The `PreparedData` (`HRS/Main/Headline.lean`) of a regime `R`, for the use of Theorem 2.5 (`T25`) and
`prepared_fluctuations_W2_proof` at `m = r = 2d+6`.  `PreparedData.hρ` asks for a GLOBAL function equality
`PDE.mfPath ρc = ρ`, whereas `Regime.sol` gives it for `t ≥ 0` only; hence `S.ρ t := R.ρ (max t 0)` and
`ρc' t := ρc (max t 0)` (`IsMFSolutionHK` only looks at `t ≥ 0`).  This definition is fully proved (no `sorry`). -/
def s7fcPrep (R : Regime d) : HRS.Main.PreparedData d where
  s := R.D.s
  hs0 := R.D.hs0
  hsd := R.D.hsd
  hd := R.hd
  β := R.β
  hβ := R.hβ
  V := R.D.V
  hV := R.hV
  ρ0 := R.ρ₀
  hρ0 := R.hρ₀
  ρ := fun t => R.ρ (max t 0)
  hρ_init := by simpa using R.init
  hρ := by
    intro K hK
    obtain ⟨ρc, hρc, hρ⟩ := R.sol K hK
    rw [R.hDβ] at hρc
    refine ⟨fun t => ρc (max t 0), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa using hρc.init
    · refine ⟨fun τ hτ => ?_, fun τ₀ hτ₀ => ?_⟩
      · simpa [max_eq_left (show (0 : ℝ) ≤ τ from hτ)] using hρc.cont.1 τ hτ
      · have h0 := hρc.cont.2 τ₀ hτ₀
        refine h0.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        simp [max_eq_left (show (0 : ℝ) ≤ τ from hτ), max_eq_left (show (0 : ℝ) ≤ τ₀ from hτ₀)]
    · intro k t ht
      refine (hρc.integrable k t ht).congr_fun (fun σ hσ => ?_) measurableSet_Icc
      simp [max_eq_left hσ.1]
    · intro k t ht
      rw [max_eq_left ht, hρc.eq k t ht]
      congr 1
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [Set.uIcc_of_le ht] at hσ
      simp [max_eq_left hσ.1]
    · funext t
      simp only [PDE.mfPath]
      exact (hρ (max t 0) (le_max_right _ _)).symm

/-- A smooth finite-rank symmetric pair kernel `k(x,y) = ∑_{ij} c_ij f_i(x) f_j(y)` WITH its decomposition
(`s7_IsFiniteRankSmooth` only asserts that a decomposition exists; the Gaussian quadratic functional `FRKernel.quad`
needs the decomposition). -/
structure FRKernel (d : ℕ) where
  n : ℕ
  f : Fin n → Torus d → ℝ
  c : Fin n → Fin n → ℝ
  smooth : ∀ i, Torus.IsSmooth (f i)
  symm : ∀ i j, c i j = c j i

namespace FRKernel

/-- The kernel `(x,y) ↦ ∑_{ij} c_ij f_i(x) f_j(y)`. -/
def toFun (K : FRKernel d) (x y : Torus d) : ℝ := ∑ i, ∑ j, K.c i j * K.f i x * K.f j y

/-- The Gaussian quadratic functional `Φ_K(F) = ½ ∑_{ij} c_ij F(f_i) F(f_j)` (`F(f) = NegSobolev.eval F f`). -/
def quad (K : FRKernel d) {r : ℝ} (F : NegSobolev d r) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, K.c i j * (NegSobolev.eval F (K.f i) * NegSobolev.eval F (K.f j))

end FRKernel

open Classical in
/-- Particle-side finite-rank field: `B̃_N^{S,K}(X, μ)(e_k) = N F_N^{K_k}(X, μ)` for `k ∈ S` and `0` otherwise. -/
def fcPartTilde {N : ℕ} (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    (μ : Measure (Torus d)) (X : Config d N) : NegSobolev d r :=
  NegSobolev.ofSeq r fun k => if k ∈ S then (N : ℝ) * modulatedEnergy (K k).toFun X μ else 0

/-- Centred particle-side finite-rank field (the analogue of `quadFieldAt`, same Bochner centring). -/
def fcPartAt {N : ℕ} (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    (μ : ℝ → Measure (Torus d)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N)
    (t : ℝ) (ω : Ω) : NegSobolev d r :=
  fcPartTilde r S K (μ t) (X t.toNNReal ω) - ∫ ω', fcPartTilde r S K (μ t) (X t.toNNReal ω') ∂P

open Classical in
/-- Gaussian-side finite-rank field: `B^{S,K}(e_k) = Φ_{K_k}(η) - E Φ_{K_k}(η)` for `k ∈ S` and `0` otherwise.  By
H1 this is the Wick chaos `½ I_2^{𝒞}(K_k)` (the kernel centring under `μ` is invisible because `η ∈ E_r` kills constants). -/
def fcGaussAt (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (η : ℝ → Ω → NegSobolev d r) (t : ℝ) (ω : Ω) : NegSobolev d r :=
  NegSobolev.ofSeq r fun k => if k ∈ S then (K k).quad (η t ω) - ∫ ω', (K k).quad (η t ω') ∂P else 0

/-- The generator `L_u f = β⁻¹ Δf - ∇V·∇f - ∫ h_f(·,y) μ^u(dy)` of the mode identity (F3), i.e. the linear part of the
drift of `η_N^t(f)`; `h_f = hTransport`, `μ^u = ρ^u dx`. -/
def fcGen (R : Regime d) (u : ℝ) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x) -
    ∫ y, hTransport d R.D.s f x y ∂(withDensityReal (R.ρ u))

/-- The kernel data of FC-B/FC-G for all modes: `K k L` (`L ∈ ℕ`) are smooth finite-rank, bounded by `B_k w`
(`w = g + c`, `EnvelopeConst`) uniformly in `L` for some `B_k`, and converge to `h_{∇e_k} = hTransport e_k` in
`L^{2+ε}(μ°_0 × μ°_0)` (`μ°_0 = ρ^0 dx`, as the hypothesis `hconv` of `s7_FC_G_strong_tail`), with `(2+ε) s < d`. -/
def FCKernelData (R : Regime d) (ε c : ℝ) (K : NonzeroLattice d → ℕ → FRKernel d) : Prop :=
  EnvelopeConst (d := d) R.D.s c ∧ 0 < ε ∧ (2 + ε) * R.D.s < d ∧
    (∀ k, ∃ B : ℝ, ∀ L x y, x ≠ y → |(K k L).toFun x y| ≤ B * (periodicRiesz d R.D.s (x - y) + c)) ∧
    ∀ k, Tendsto (fun L : ℕ => eLpNorm (fun p : Torus d × Torus d =>
        (K k L).toFun p.1 p.2 - hTransport d R.D.s (Torus.realMode k) p.1 p.2) (ENNReal.ofReal (2 + ε))
        ((withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0)))) atTop (𝓝 0)

end HRS.MC.Sec7.FCPlan

end
