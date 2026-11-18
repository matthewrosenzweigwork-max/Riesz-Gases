import HRS.Uniform.Q54cAux34
import HRS.Uniform.Q48cCov
import HRS.Energy.Commutator.StressAux

/-!
# Q54c, part 35: the covariance form on `lpFun`s is `2q ∫ ∇ψ₁·∇ψ₂ ρ`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Torus HRS.Uniform

variable {d : ℕ}

theorem continuous_partialDeriv_of_lpFun {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {ψ : Torus d → ℝ}
    (hψ : MemSobolev n ψ) (hc : Continuous ψ) (hψ1 : Torus.IsCk 1 ψ) (j : Fin d) :
    Continuous fun a => Torus.partialDeriv j ψ a := by
  have : (fun a => Torus.partialDeriv j ψ a) = fun a => inner ℝ (bVec n j a) (lpFun n ψ) :=
    funext fun a => (inner_bVec_lpFun hn hψ hc hψ1 j a).symm
  rw [this]
  exact (HRS.Uniform.Q14.q14_continuous_bVec hn j).inner continuous_const

theorem covForm_lpFun {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {ψ₁ ψ₂ : Torus d → ℝ} (h₁ : MemSobolev n ψ₁)
    (c₁ : Continuous ψ₁) (d₁ : Torus.IsCk 1 ψ₁) (h₂ : MemSobolev n ψ₂) (c₂ : Continuous ψ₂)
    (d₂ : Torus.IsCk 1 ψ₂) :
    covForm n q (withDensityReal ρ) (lpFun n ψ₁) (lpFun n ψ₂) =
      2 * q * ∫ x, inner ℝ (Torus.grad ψ₁ x) (Torus.grad ψ₂ x) * ρ x := by
  haveI := HRS.Uniform.Q48c.isFiniteMeasure_withDensityReal_of_cont hρ
  rw [HRS.Uniform.Q14.q14_covForm_apply hn hq]
  have hpt : ∀ (j : Fin d) (a : Torus d),
      inner ℝ (Real.sqrt (2 * q) • bVec n j a) (lpFun n ψ₁) *
        inner ℝ (Real.sqrt (2 * q) • bVec n j a) (lpFun n ψ₂) =
      2 * q * (Torus.partialDeriv j ψ₁ a * Torus.partialDeriv j ψ₂ a) := by
    intro j a
    rw [inner_smul_left, inner_smul_left, inner_bVec_lpFun hn h₁ c₁ d₁ j a,
      inner_bVec_lpFun hn h₂ c₂ d₂ j a]
    have : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q := Real.mul_self_sqrt (by positivity)
    simp only [conj_trivial]
    calc Real.sqrt (2 * q) * Torus.partialDeriv j ψ₁ a * (Real.sqrt (2 * q) * Torus.partialDeriv j ψ₂ a)
        = (Real.sqrt (2 * q) * Real.sqrt (2 * q)) * (Torus.partialDeriv j ψ₁ a * Torus.partialDeriv j ψ₂ a) := by
          ring
      _ = _ := by rw [this]
  simp_rw [hpt]
  have hρm : Measurable ρ := hρ.measurable
  have hcont : ∀ j : Fin d, Continuous fun a =>
      Torus.partialDeriv j ψ₁ a * Torus.partialDeriv j ψ₂ a :=
    fun j => (continuous_partialDeriv_of_lpFun hn h₁ c₁ d₁ j).mul
      (continuous_partialDeriv_of_lpFun hn h₂ c₂ d₂ j)
  have hint : ∀ j : Fin d, Integrable (fun a => ρ a * (2 * q * (Torus.partialDeriv j ψ₁ a *
      Torus.partialDeriv j ψ₂ a))) := fun j =>
    (hρ.mul ((continuous_const.mul (hcont j)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e1 : ∀ j : Fin d, ∫ a, 2 * q * (Torus.partialDeriv j ψ₁ a * Torus.partialDeriv j ψ₂ a)
      ∂(withDensityReal ρ) = ∫ a, ρ a * (2 * q * (Torus.partialDeriv j ψ₁ a *
        Torus.partialDeriv j ψ₂ a)) :=
    fun j => HRS.integral_withDensityReal_eq ρ hρm hρ0 _
  simp_rw [e1]
  rw [← integral_finset_sum _ (fun j _ => hint j)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show _ = 2 * q * (inner ℝ (Torus.grad ψ₁ x) (Torus.grad ψ₂ x) * ρ x)
  rw [PiLp.inner_apply]
  simp only [HRS.Commutator.StressAux.grad_apply]
  rw [← Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm, mul_left_comm]

end HRS.Uniform.Q54c
