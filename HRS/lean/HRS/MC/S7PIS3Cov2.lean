import HRS.MC.S7PIS3Cov1

/-!
# Packet piS3, part 2b: `s7_PIS_cov_struct` (structure of the covariance of the observations)

NOTE (defect of the statement, see the report): in the Plan statement the clause "(b1)"
`∀ c, ∀ u ∈ [0,T], (obsRateR c u).PosSemidef` quantifies over all `u ∈ [0,T]`, but for `c < t_i < u` the
function `obsTestR c i u = propagator u t_i φ_i` is the value of `Classical.choose` of a classical solution
outside `[0,t_i]`, about which nothing is known; the clause is only provable (and only used) for
`u` with `c < t_i → u ≤ t_i`.  `s7_PIS_cov_struct_proof'` below is the repaired statement.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS3

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- The energy integrand `g_{ij}(v) = ∫ ∇U^{v,t_i}φ_i · ∇U^{v,t_j}φ_j ρ_v`. -/
def S7PIS3_g (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (i j : Fin q)
    (v : ℝ) : ℝ :=
  ∫ x, inner ℝ (Torus.grad (propagator R.D R.ρ v (t i) (φ i)) x)
    (Torus.grad (propagator R.D R.ρ v (t j) (φ j)) x) * R.ρ v x

/-- `g_{ij}` cut off to `[0, t_i ∧ t_j]`. -/
def S7PIS3_h (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (i j : Fin q) :
    ℝ → ℝ :=
  (Set.Icc 0 (min (t i) (t j))).indicator (S7PIS3_g R t φ i j)

theorem S7PIS3_invβ_pos (R : Regime d) : 0 < R.D.invβ := by
  rw [R.hDβ]; exact inv_pos.2 R.hβ

theorem S7PIS3_rho_nonneg (R : Regime d) {u : ℝ} (hu : 0 ≤ u) (x : Torus d) : 0 ≤ R.ρ u x := by
  obtain ⟨m₀, M₀, hm₀, hb⟩ := R.bounds
  exact hm₀.le.trans (hb u hu x).1

theorem S7PIS3_obsTest_grad_cont (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (i : Fin q) {u : ℝ} (hu0 : 0 ≤ u) : (u ≤ t i → Continuous (Torus.grad (obsTest R.D R.ρ t φ i u))) := by
  intro h
  unfold obsTest
  rw [if_pos h]
  exact HRS.PDE.MFLinear.continuous_grad (S7PIS3_prop_isCk _ _ _ _ hu0 h)

theorem S7PIS3_obsTest_grad_cont' (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (i : Fin q) {u : ℝ} (hu0 : 0 ≤ u) : Continuous (Torus.grad (obsTest R.D R.ρ t φ i u)) := by
  by_cases h : u ≤ t i
  · exact S7PIS3_obsTest_grad_cont R t φ i hu0 h
  · unfold obsTest
    rw [if_neg h]
    have : Torus.grad (0 : Torus d → ℝ) = fun _ => 0 := funext S7PIS3_grad_zero
    rw [this]
    exact continuous_const

theorem S7PIS3_cov_a (R : Regime d) {T : ℝ} {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) :
    ∀ u ∈ Set.Icc (0 : ℝ) T, (obsRate R.D R.ρ t φ u).PosSemidef := by
  intro u hu
  exact S7PIS3_gram_psd (2 * R.D.invβ) (by have := S7PIS3_invβ_pos R; positivity)
    (fun i => Torus.grad (obsTest R.D R.ρ t φ i u)) (fun i => S7PIS3_obsTest_grad_cont' R t φ i hu.1)
    (R.ρ u) (HRS.MC.Sec7.S7FCF5A.S7FCF5A_rho_cont_x R hu.1) (S7PIS3_rho_nonneg R hu.1)

theorem S7PIS3_obsTestR_zero (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (c : ℝ) (i : Fin q) (h : ¬ c < t i) (u : ℝ) : obsTestR R.D R.ρ t φ c i u = 0 := by
  unfold obsTestR
  rw [if_neg h]

theorem S7PIS3_cov_b (R : Regime d) {T : ℝ} {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) :
    ∀ c, ∀ u ∈ Set.Icc (0 : ℝ) T, (∀ i, c < t i → u ≤ t i) →
      (obsRateR R.D R.ρ t φ c u).PosSemidef := by
  intro c u hu hct
  refine S7PIS3_gram_psd (2 * R.D.invβ) (by have := S7PIS3_invβ_pos R; positivity)
    (fun i => Torus.grad (obsTestR R.D R.ρ t φ c i u)) (fun i => ?_)
    (R.ρ u) (HRS.MC.Sec7.S7FCF5A.S7FCF5A_rho_cont_x R hu.1) (S7PIS3_rho_nonneg R hu.1)
  by_cases h : c < t i
  · unfold obsTestR
    rw [if_pos h]
    exact HRS.PDE.MFLinear.continuous_grad (S7PIS3_prop_isCk _ _ _ _ hu.1 (hct i h))
  · rw [S7PIS3_obsTestR_zero R t φ c i h]
    have : Torus.grad (0 : Torus d → ℝ) = fun _ => 0 := funext S7PIS3_grad_zero
    rw [this]
    exact continuous_const

theorem S7PIS3_obsTestR_eq (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    {c c' : ℝ} (hno : ∀ i, ¬ (c < t i ∧ t i < c')) {u : ℝ} (hu : u ∈ Set.Ioc c c') (i : Fin q) :
    obsTestR R.D R.ρ t φ c i u = obsTest R.D R.ρ t φ i u := by
  unfold obsTestR obsTest
  by_cases hc : c < t i
  · have h1 : u ≤ t i := by
      have : ¬ t i < c' := fun h => hno i ⟨hc, h⟩
      exact hu.2.trans (not_lt.1 this)
    rw [if_pos hc, if_pos h1]
  · have h1 : ¬ u ≤ t i := fun h => hc (lt_of_lt_of_le hu.1 h)
    rw [if_neg hc, if_neg h1]

theorem S7PIS3_cov_c (R : Regime d) {T : ℝ} {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → (∀ i, ¬ (c < t i ∧ t i < c')) →
      (∀ i j, ContinuousOn (fun u => obsRateR R.D R.ρ t φ c u i j) (Set.Icc c c')) ∧
      ∀ u ∈ Set.Ioc c c', obsRateR R.D R.ρ t φ c u = obsRate R.D R.ρ t φ u := by
  intro c c' hc0 hcc' hc'T hno
  refine ⟨fun i j => ?_, fun u hu => ?_⟩
  · by_cases hi : c < t i
    · by_cases hj : c < t j
      · have hci : c' ≤ t i := by
          by_contra h; exact hno i ⟨hi, not_le.1 h⟩
        have hcj : c' ≤ t j := by
          by_contra h; exact hno j ⟨hj, not_le.1 h⟩
        have hg := S7PIS3_g_cont R (ht i).1 (ht j).1 (hφ i) (hφ j)
        have hsub : Set.Icc c c' ⊆ Set.Icc 0 (min (t i) (t j)) :=
          fun u hu => ⟨hc0.trans hu.1, le_min (hu.2.trans hci) (hu.2.trans hcj)⟩
        refine ((continuousOn_const (c := 2 * R.D.invβ)).mul (hg.mono hsub)).congr fun u hu => ?_
        unfold obsRateR obsTestR
        simp only [Matrix.of_apply, if_pos hi, if_pos hj]
        rfl
      · have : ∀ u, obsRateR R.D R.ρ t φ c u i j = 0 := fun u => by
          unfold obsRateR
          simp only [Matrix.of_apply, S7PIS3_obsTestR_zero R t φ c j hj, S7PIS3_grad_zero,
            inner_zero_right, zero_mul, integral_zero, mul_zero]
        simp_rw [this]
        exact continuousOn_const
    · have : ∀ u, obsRateR R.D R.ρ t φ c u i j = 0 := fun u => by
        unfold obsRateR
        simp only [Matrix.of_apply, S7PIS3_obsTestR_zero R t φ c i hi, S7PIS3_grad_zero,
          inner_zero_left, zero_mul, integral_zero, mul_zero]
      simp_rw [this]
      exact continuousOn_const
  · ext i j
    unfold obsRateR obsRate
    simp only [Matrix.of_apply, S7PIS3_obsTestR_eq R t φ hno hu]

end HRS.MC.Sec7.S7PIS3

end
