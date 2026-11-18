import HRS.Uniform.Q54cAux16

/-!
# Q54c, part 17: the coefficient flow of the adjoint propagator in `ℝ × E_j`

For adjoint data at level `n + 4` and `φ ∈ Dom (n+4)`, `flow t φ τ = propagatorCoeff … (n+4) t (coeffOf φ) τ` is an
admissible path (`Adm j`, `j ≤ n+4`), with `‖flow τ‖_{H^j} ≤ Cop_j ‖φ‖_{H^j}`; its generator path
`gen τ = forwardGen (μ (t-τ)) (flow τ)` is its derivative in `ℝ × E_j` for `j + 2 ≤ n + 4`, hence the path is
Lipschitz in `τ` with respect to `‖φ‖_{H^{j+2}}`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem memHs_mono_q {a b : ℝ} (hab : a ≤ b) {c : Coeff d} (hc : MemHs b c) : MemHs a c :=
  Adm.mono.memSobolev_aux hab hc

theorem sobWeight_mono_q {a b : ℝ} (hab : a ≤ b) (k : Lattice d) : sobWeight a k ≤ sobWeight b k := by
  unfold sobWeight
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.pi * Lattice.enorm k)]) hab

theorem hsNorm_mono_q {a b : ℝ} (hab : a ≤ b) {c : Coeff d} (hc : MemHs b c) :
    HRS.PDE.hsNorm a c ≤ HRS.PDE.hsNorm b c := by
  unfold HRS.PDE.hsNorm hsNormSq
  refine Real.sqrt_le_sqrt ?_
  refine Summable.tsum_le_tsum (fun k => ?_) (memHs_mono_q hab hc) hc
  exact mul_le_mul_of_nonneg_right (sobWeight_mono_q hab k) (sq_nonneg _)

theorem hsNorm_nonneg_q (a : ℝ) (c : Coeff d) : 0 ≤ HRS.PDE.hsNorm a c := Real.sqrt_nonneg _

/-- the fixed uniform parameters of the PDE layer -/
structure PdeSetup (d : ℕ) where
  hd : 1 ≤ d
  s : ℝ
  hs0 : 0 ≤ s
  hsd : s < d
  n : ℕ
  hn : mStar d ≤ n + 4
  hnd : (d : ℝ) / 2 < n
  R : Regime
  hR : ∀ C ν₀ θ, R.lambdaM C ν₀ θ = C
  MB : ℝ
  Λ : ℝ
  VB : ℝ
  T : ℝ
  Bν : ℝ
  c : PdeConst d s n R MB Λ VB T Bν

namespace PdeSetup

variable (P : PdeSetup d)

/-- admissible dynamics `(D, μ)` for the setup -/
structure Data (D : DynData d) (ν₀ : ℝ) (μ : ℝ → Torus d → ℝ) : Prop where
  hA : AdjointData P.s (P.n + 4) P.R P.MB P.Λ P.VB D ν₀ P.T μ
  hν : D.invβ ≤ P.Bν

/-- the level `n + 4` as a real number -/
abbrev lev : ℝ := ((P.n + 4 : ℕ) : ℝ)

/-- the coefficient flow `τ ↦ F(τ)` of the adjoint propagator (`F(τ) = U^{t-τ,t}φ`) -/
def flow (D : DynData d) (μ : ℝ → Torus d → ℝ) (t : ℝ) (φ : Torus d → ℝ) : ℝ → Coeff d :=
  propagatorCoeff D μ P.lev t (coeffOf φ)

/-- the generator path -/
def gen (D : DynData d) (μ : ℝ → Torus d → ℝ) (t : ℝ) (φ : Torus d → ℝ) : ℝ → Coeff d :=
  fun τ => forwardGen D (μ (t - τ)) (P.flow D μ t φ τ)

theorem hJ1 : 1 ≤ P.n + 4 := by omega

theorem hJd : (d : ℝ) / 2 < P.lev := by
  have h1 := HRS.Uniform.Q54.mStar_gt d
  have h2 : (mStar d : ℝ) ≤ P.lev := by exact_mod_cast P.hn
  linarith

theorem hJ2 : (d : ℝ) / 2 + 2 < P.lev := by
  have h1 := HRS.Uniform.Q54.mStar_gt d
  have h2 : (mStar d : ℝ) ≤ P.lev := by exact_mod_cast P.hn
  linarith

variable {P} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.memHsφ {φ : Torus d → ℝ} (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) :
    MemHs P.lev (coeffOf φ) := (hsNormSq_coeffOf P.lev φ hφ.2).1

theorem Data.spec {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) :
    IsForwardSolution D μ t (coeffOf φ) (P.flow D μ t φ) ∧
      WeakContinuousInHs P.lev (P.flow D μ t φ) t := by
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec P.hd P.s P.hs0 P.hsd (P.n + 4) P.hJ1 P.R P.MB P.Λ P.VB
  obtain ⟨hsol, hw, -⟩ := hspec D ν₀ P.T μ h.hA t ht (coeffOf φ) (h.memHsφ hφ)
  exact ⟨hsol, hw⟩

theorem Data.flow_memHs {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    MemHs P.lev (P.flow D μ t φ τ) := (h.spec ht hφ).2.1 τ hτ

theorem Data.flow_adm {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) {j : ℝ} (hj : j ≤ P.lev) :
    Adm j (P.flow D μ t φ τ) := by
  obtain ⟨hre, hsum⟩ := HRS.Uniform.Q54.pc_data P.hd P.s P.hs0 P.hsd (P.n + 4) P.hJ1 P.hJd P.R P.MB P.Λ
    P.VB D ν₀ P.T μ h.hA ht hφ hτ
  exact ⟨hre, hsum, memHs_mono_q hj (h.flow_memHs ht hφ hτ)⟩

theorem Data.flow_prop {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {u : ℝ} (hu : u ∈ Set.Icc 0 t) :
    propagator D μ u t φ = toFun (P.flow D μ t φ (t - u)) ∧
      coeffOf (propagator D μ u t φ) = P.flow D μ t φ (t - u) := by
  obtain ⟨h1, -⟩ := HRS.Uniform.Q54.prop_facts P.hd P.s P.hs0 P.hsd (P.n + 4) P.hn P.R P.MB P.Λ P.VB D ν₀ P.T μ
    h.hA ht hφ hu
  have hτ : t - u ∈ Set.Icc 0 t := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hA := h.flow_adm ht hφ hτ (le_refl _)
  refine ⟨h1, ?_⟩
  rw [h1]
  exact hA.coeffOf_toFun

end PdeSetup

end HRS.Uniform.Q54c
