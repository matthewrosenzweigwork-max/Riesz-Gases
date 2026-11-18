import Mathlib

/-!
# S11.3 X2 part B (worker S11Z3), definitions: Euclidean setting, Laplacian, divergence, mollifier

Setting for the abstract power-chain inequality: `E = EuclideanSpace ℝ (Fin n)` with the Laplacian in the form used by
`HRS.MC.CepP2` (`∑_k D²f(e_k,e_k)`).  `s113b_Moll` is a fixed smooth mollifier; `s113b_mol δ u` is `u * ρ_δ`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS.MS.S113X2B

/-- Euclidean space `ℝⁿ`. -/
abbrev s113b_E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Smoothness `C^∞`. -/
abbrev s113b_Cinf {n : ℕ} (f : s113b_E n → ℝ) : Prop := ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f

/-- The Laplacian `∑_k D²f(e_k,e_k)` (as in `CepP2`). -/
def s113b_lap {n : ℕ} (f : s113b_E n → ℝ) (x : s113b_E n) : ℝ :=
  ∑ k : Fin n, fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)

/-- The divergence `∑_k ∂_k w_k` of a vector field. -/
def s113b_div {n : ℕ} (w : s113b_E n → s113b_E n) (x : s113b_E n) : ℝ :=
  ∑ k : Fin n, fderiv ℝ (fun y => w y k) x (EuclideanSpace.single k 1)

/-- A fixed mollifier: smooth, nonnegative, supported in the closed unit ball, with integral one. -/
structure s113b_Moll (n : ℕ) where
  ρ : s113b_E n → ℝ
  smooth : s113b_Cinf ρ
  nonneg : ∀ x, 0 ≤ ρ x
  supp : tsupport ρ ⊆ Metric.closedBall 0 1
  integral_one : ∫ x, ρ x = 1

/-- The scaled mollifier `ρ_δ(z) = δ^{-n} ρ(z/δ)`. -/
def s113b_Moll.scaled {n : ℕ} (m : s113b_Moll n) (δ : ℝ) (z : s113b_E n) : ℝ :=
  (δ ^ n)⁻¹ * m.ρ (δ⁻¹ • z)

/-- The mollification `u * ρ_δ`, `x ↦ ∫ ρ_δ(x-y) u(y) dy`. -/
def s113b_mol {n : ℕ} (m : s113b_Moll n) (δ : ℝ) (u : s113b_E n → ℝ) (x : s113b_E n) : ℝ :=
  ∫ y, m.scaled δ (x - y) * u y

/-- The commutator `c_δ[u](x) = ∫ u(y) [ Dρ_δ(x-y)(b(x)-b(y)) + (div b)(x) ρ_δ(x-y) ] dy`. -/
def s113b_comm {n : ℕ} (m : s113b_Moll n) (δ : ℝ) (b : s113b_E n → s113b_E n) (u : s113b_E n → ℝ)
    (x : s113b_E n) : ℝ :=
  ∫ y, u y * (fderiv ℝ (m.scaled δ) (x - y) (b x - b y) + s113b_div b x * m.scaled δ (x - y))

/-- The mollified drift-diffusion flux `g_δ[u](x) = ∫ u(y) [ν Δρ_δ(x-y) - Dρ_δ(x-y)(b(y))] dy`. -/
def s113b_gdel {n : ℕ} (m : s113b_Moll n) (δ ν : ℝ) (b : s113b_E n → s113b_E n) (u : s113b_E n → ℝ)
    (x : s113b_E n) : ℝ :=
  ∫ y, u y * (ν * s113b_lap (m.scaled δ) (x - y) - fderiv ℝ (m.scaled δ) (x - y) (b y))

end HRS.MS.S113X2B
