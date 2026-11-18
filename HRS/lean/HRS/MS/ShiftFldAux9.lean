import HRS.MS.ShiftFldAux8
import HRS.MS.WsStatFinal

/-!
# S79P: setup for the Gaussian window stationarity (Lyapunov identity for the stationary coefficient)

Thermal equilibrium `ρ` (`= thermalDensity d s a β`), `μ = withDensityReal ρ`, `D = quadraticGradientDyn d s a β`.
* `s79g_kdata`: the operator `K` of `IsKData` for `μ`.
* `s79g_drift`: `b := meanFieldDriftW D ρ = -(a x + ∇U)` and `∇ρ = β ρ b`.
* `s79g_gen`: `generatorW (D.coeff (fun _ => ρ)) r f x = -β⁻¹ 𝒜 f x - nlTermRd D ρ f x`, `𝒜 f = -Δf - β ⟨b, ∇f⟩`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

/-- The drift `b = M ∇g*ρ - ∇V` of the stationary dynamics. -/
abbrev bdr (d : ℕ) (s a β : ℝ) (ρ : Euc d → ℝ) (x : Euc d) : Euc d :=
  meanFieldDriftW (quadraticGradientDyn d s a β) ρ x

/-- `𝒜 f = -Δf - β ⟨b, ∇f⟩` (so that `div(ρ ∇f) = -ρ 𝒜 f`). -/
def Aop (d : ℕ) (s a β : ℝ) (ρ : Euc d → ℝ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  -(Laplacian.laplacian f x) - β * inner ℝ (bdr d s a β ρ x) (gradient f x)

theorem s79g_gradV (a : ℝ) (x : Euc d) : gradient (confinement a : Euc d → ℝ) x = a • x := by
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  rw [s21_confinement_eq, HRS.MS.Adj.ad_gradient_quadV hQ 0 x, s21_matVec_smul_one, add_zero]

theorem s79g_drift (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (x : Euc d) :
    bdr d s a β ρ x =
      -(a • x + gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x) := by
  have h1 := s21_gradU_eq hd hs0 hsd ha hβ hρ x
  unfold bdr meanFieldDriftW
  have : (quadraticGradientDyn d s a β).V = confinement a := rfl
  have h2 : (quadraticGradientDyn d s a β).M = -1 := rfl
  have h3 : (quadraticGradientDyn d s a β).s = s := rfl
  rw [this, s79g_gradV, h2, h3, h1, s21_matVec_neg_one]
  abel

theorem s79g_grad_rho (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (x : Euc d) :
    gradient ρ x = (β * ρ x) • bdr d s a β ρ x := by
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  rw [s79g_drift hd hs0 hsd ha hβ hρ, hρeq, hT.grad_rho x]
  module

theorem s79g_gen (D : WholeDyn d) (ρ : Euc d → ℝ) (r : ℝ) (f : Euc d → ℝ) (x : Euc d) :
    generatorW (D.coeff (fun _ => ρ)) r f x = D.invβ * Laplacian.laplacian f x +
      inner ℝ (meanFieldDriftW D ρ x) (gradient f x) - nlTermRd D ρ f x := rfl

end HRS.MS.S79G
