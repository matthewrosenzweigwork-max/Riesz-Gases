import HRS.Main.Headline
import HRS.Sections.Sec3
import HRS.Duality.PairingExpansion
import HRS.MH.DualityRdDefs

/-!
# Lemma 3.1 (`M:B:lem:pairing-expansion`) on `𝔻 = ℝ^d`

Statement only (the theorem ends in `sorry`; the definitions are complete); relocated from `HRS/SA/Drafts/SAD1.lean` after
the independent review recorded in `docs/ISSUES.md` and subsequent approval.  TeX L1518-1524: the statement is for
`𝔻 ∈ {𝕋^d, ℝ^d}` (`\mathbb D`, with the explicit clause "`∫⟨x⟩dμ < ∞` if `𝔻 = ℝ^d` and `s = 0`").  The torus case is
`HRS.Duality.pairing_expansion`; the vocabulary below is the whole-space copy of `HRS.Duality.pairKernelB`, `pairB`,
`pairBSigned`, `pairEmp`, `divConvB`.  Choices recorded in ISSUES: `α ≤ 1` is added (harmless: a global Hölder bound with
`α > 1` forces a constant density) and the moment hypothesis of the TeX is kept.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.Duality

open HRS

variable {d : ℕ} {N : ℕ}

/-- The symmetrized kernel `½ (∇f(x) - ∇f(y)) · M ∇g(x - y)` of `B:eq:B-symmetrized` on `ℝ^d`, `0` on the diagonal. -/
def pairKernelRdB (f : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (x y : Euc d) : ℝ :=
  if x = y then 0 else
    (1 / 2 : ℝ) * inner ℝ (gradient f x - gradient f y)
      (Torus.matVec M (Whole.rieszKernelGrad d s (x - y)))

/-- `B_f(α, λ)` in symmetrized, off-diagonal form on `ℝ^d`. -/
def pairBRd (f : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (α ν : Measure (Euc d)) : ℝ :=
  ∫ p, pairKernelRdB f M s p.1 p.2 ∂(α.prod ν)

/-- `B_f(ν - μ, ν - μ)` expanded bilinearly (four terms). -/
def pairBSignedRd (f : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (ν μ : Measure (Euc d)) : ℝ :=
  pairBRd f M s ν ν - pairBRd f M s ν μ - pairBRd f M s μ ν + pairBRd f M s μ μ

/-- `⟨φ, μ_N - μ⟩ = N⁻¹ ∑ φ(x_i) - ∫ φ dμ`. -/
def pairEmpRd (φ : Euc d → ℝ) (X : Whole.EucConfig d N) (μ : Measure (Euc d)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, φ (X i) - ∫ x, φ x ∂μ

/-- `Div g * (ρ M^* ∇f) = (∇g) * (ρ M^* ∇f)` (contracted) with the cancellation convention on `ℝ^d`. -/
def divConvBRd (f : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (ρ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ a : Fin d, Whole.convGradConvW (Whole.rieszKernelGrad d s)
    (fun y => ρ y * Torus.matVec M.transpose (gradient f y) a) x a

/-- Lemma 3.1 `B:lem:pairing-expansion` (TeX L1518-1524) on `𝔻 = ℝ^d`: for `f ∈ C²_b(ℝ^d)`, a probability density `ρ`
(`μ = ρ dx`) in `C^{0,α}_b(ℝ^d)` with `α > max(0, s+1-d)` (and `∫⟨x⟩ dμ < ∞` if `s = 0`), and pairwise distinct
`x_1, …, x_N`, the four quantities `B_f(μ,μ)`, `B_f(μ_N,μ)`, `B_f(μ,μ_N)` (absolutely convergent integrals), the
convolution `∇g * μ` and `Div g * (μ M^*∇f)` (cancellation convention integrals) are finite and
`B_f(μ_N,μ_N) - B_f(μ,μ) = ⟨∇f·M(∇g*μ), ρ_N⟩ - ⟨Div g*(μ M^*∇f), ρ_N⟩ + B_f(ρ_N,ρ_N)`.
Same shape and conclusions as `HRS.Duality.pairing_expansion`.  Reading: `C^{0,α}` is the Hölder space of exponent
`α ∈ (0,1]` (`hα1`; the torus statement leaves `α ≤ 1` implicit), boundedness of `ρ` is `hρb`, `⟨x⟩ = √(1+|x|²)`,
`μ_N = N⁻¹∑δ_{x_i}` with `N ≥ 1`. -/
theorem pairing_expansion_rd (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (f : Euc d → ℝ) (hf : MemCb 2 f)
    (ρ : Euc d → ℝ) (hρ : Whole.IsProbDensity ρ) (hρb : ∃ B, ∀ x, |ρ x| ≤ B)
    (C α : NNReal) (hα0 : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) (hα : s + 1 - d < α)
    (hHol : HolderWith C α ρ)
    (hmom : s = 0 → Integrable (fun x : Euc d => Real.sqrt (1 + ‖x‖ ^ 2)) (Whole.withDensityReal ρ))
    (hN : 1 ≤ N) (X : Whole.EucConfig d N) (hX : Pairwise fun i j => X i ≠ X j) :
    let μ := Whole.withDensityReal ρ
    let μN := Whole.empirical X
    let φ₁ : Euc d → ℝ := fun x =>
      inner ℝ (gradient f x) (Torus.matVec M (Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x))
    let φ₂ : Euc d → ℝ := divConvBRd f M s ρ
    (Integrable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2) (μ.prod μ) ∧
      Integrable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2) (μN.prod μ) ∧
      Integrable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2) (μ.prod μN) ∧
      (∀ x, Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • Whole.rieszKernelGrad d s (x - y)
        else ρ y • Whole.rieszKernelGrad d s (x - y))) ∧
      (∀ (a : Fin d) x, let ψ : Euc d → ℝ := fun y => ρ y * Torus.matVec M.transpose (gradient f y) a
        Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then (ψ y - ψ x) • Whole.rieszKernelGrad d s (x - y)
          else ψ y • Whole.rieszKernelGrad d s (x - y))) ∧
      Integrable φ₁ μ ∧ Integrable φ₂ μ) ∧
    pairBRd f M s μN μN - pairBRd f M s μ μ =
      pairEmpRd φ₁ X μ - pairEmpRd φ₂ X μ + pairBSignedRd f M s μN μ := by
  sorry

end HRS.Duality
