import HRS.MS.R26T8AA03

/-!
# S8.2 observed-time layer, packet T8A.A06 (helper a): the local pair generator of a corrector

For a `PairCorrector` `Q` and `x ≠ y`:
`(β⁻¹ Δ_x Q + ⟪b₀(x), ∇_x Q⟫) + (β⁻¹ Δ_y Q + ⟪b₀(y), ∇_y Q⟫) = -HSource x y - pairJ x y`,
from the Poisson equation `-pairA = HSource`, the definition of `oneJ`, and the stationarity `A03` of the local row generator.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_a06a_int {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d)) (g : Euc d → ℝ)
    (hint : Integrable (fun x => C.ν * Laplacian.laplacian g x +
      inner ℝ (C.drift 0 x) (gradient g x)) mu)
    (hzero : ∫ x, (C.ν * Laplacian.laplacian g x + inner ℝ (C.drift 0 x) (gradient g x)) ∂mu = 0) :
    ∫ x, generatorW C 0 g x ∂mu = ∫ x, oneJ C g x ∂mu := by
  have hsplit : ∀ x, generatorW C 0 g x = (C.ν * Laplacian.laplacian g x +
      inner ℝ (C.drift 0 x) (gradient g x)) + oneJ C g x := by
    intro x; unfold oneJ; ring
  by_cases hI : Integrable (oneJ C g) mu
  · simp only [hsplit]
    rw [integral_add hint hI, hzero, zero_add]
  · have hG : ¬ Integrable (generatorW C 0 g) mu := by
      intro hG
      apply hI
      have := hG.sub hint
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply, hsplit]
      ring
    rw [integral_undef hG, integral_undef hI]

theorem r26t8a_a06a_pair_local (d : ℕ) (hd : 2 ≤ d) (a beta M A : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ) (hQ : PairCorrector a beta rho M A f Q)
    (x y : Euc d) (hxy : x ≠ y) :
    (beta⁻¹ * Laplacian.laplacian (fun z => Q z y) x +
        inner ℝ ((critCoeff d a beta rho).drift 0 x) (HRS.MS.Phase2S82.pairGradX Q x y)) +
      (beta⁻¹ * Laplacian.laplacian (Q x) y +
        inner ℝ ((critCoeff d a beta rho).drift 0 y) (HRS.MS.Phase2S82.pairGradY Q x y)) =
      -HSource (HRS.Whole.withDensityReal rho) f x y -
        pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y := by
  set C := critCoeff d a beta rho with hC
  set mu := HRS.Whole.withDensityReal rho with hmu
  have hν : C.ν = beta⁻¹ := rfl
  have hQx : Q x = fun z => Q z x := funext fun z => hQ.symmetric x z
  have h1 := r26t8a_local_generator_rows d hd a beta M A ha hbeta rho hrho f Q hQ y
  have h2 := r26t8a_local_generator_rows d hd a beta M A ha hbeta rho hrho f Q hQ x
  have e1 := r26t8a_a06a_int C mu (fun z => Q z y) (by rw [hν]; exact h1.1) (by rw [hν]; exact h1.2)
  have e2 := r26t8a_a06a_int C mu (Q x) (by rw [hQx, hν]; exact h2.1) (by rw [hQx, hν]; exact h2.2)
  have hp := hQ.poisson x y hxy
  have hgx : HRS.MS.Phase2S82.pairGradY Q x y = gradient (Q x) y := rfl
  unfold pairA HRS.Whole.projGeneratorW at hp
  unfold pairJ HRS.Whole.projMean HRS.Whole.pair
  rw [e1, e2] at hp
  have s1 : generatorW C 0 (fun z => Q z y) x = (C.ν * Laplacian.laplacian (fun z => Q z y) x +
      inner ℝ (C.drift 0 x) (gradient (fun z => Q z y) x)) + oneJ C (fun z => Q z y) x := by
    unfold oneJ; ring
  have s2 : generatorW C 0 (Q x) y = (C.ν * Laplacian.laplacian (Q x) y +
      inner ℝ (C.drift 0 y) (gradient (Q x) y)) + oneJ C (Q x) y := by
    unfold oneJ; ring
  rw [s1, s2] at hp
  rw [hν] at hp
  have hgx1 : HRS.MS.Phase2S82.pairGradX Q x y = gradient (fun z => Q z y) x := rfl
  rw [hgx, hgx1]
  show _ = _ - ((oneJ C (fun w => Q w y) x - ∫ x', oneJ C (fun w => Q w y) x' ∂mu) +
      (oneJ C (Q x) y - ∫ y', oneJ C (Q x) y' ∂mu))
  linarith

end HRS.MS.R26T8A

end
