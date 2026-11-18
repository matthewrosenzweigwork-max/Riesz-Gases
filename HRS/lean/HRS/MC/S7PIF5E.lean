import HRS.MC.S7PIF5D

/-!
# Packet piF5, part E: the initial value of the observation vector is `ℱ_s`-measurable for all `s`

`obsVec (initProp ζ_0)_i = ζ_0(U^{0,t_i} φ_i) = √N (flucPair(X_0) - E flucPair(X_0))` (S1, S2, `S7PIF4_zeta_eval`), a Borel function of `X_0`, and
`X_0` is `ℱ_s`-measurable for every real `s` (`IsFilteredSolution.measurable_init`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF5

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF4 HRS.MC.Sec7.S7PIM

variable {d : ℕ}

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- the coordinates of the initial value -/
theorem S7PIF5_init_coord {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) (i : Fin q) (ω : Ω) :
    obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) i =
      NegSobolev.eval (zetaAt m P X 0 ω) (propagator R.D R.ρ 0 (t i) (φ i)) := by
  show NegSobolev.eval (pathAt (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) (t i)) (φ i) = _
  rw [(HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof R m hm T hT).2.1 _ _ (ht i)]
  exact HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof R m hm T hT 0 (t i) le_rfl (ht i).1 (ht i).2 _ _ (hφ i)

theorem S7PIF5_init_meas {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) (s : ℝ) :
    Measurable[ℱ s] (fun ω => obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω))) := by
  have hN0 : 0 < N := hN
  have hX : ∀ u, Measurable (X u) := fun u => (hF.adapted u).mono (ℱ.le _) le_rfl
  refine @Measurable.comp _ _ _ (ℱ s) _ _ _ _ (MeasurableEquiv.toLp 2 (Fin q → ℝ)).measurable
    (@measurable_pi_iff _ _ _ (ℱ s) _ _ |>.2 fun i => ?_)
  have hg : Torus.IsSmooth (propagator R.D R.ρ 0 (t i) (φ i)) :=
    (HRS.MC.L2C0.l2c0_proof R (φ i) (hφ i) 0 (t i) le_rfl (ht i).1).1
  have hgc : Continuous (propagator R.D R.ρ 0 (t i) (φ i)) :=
    HRS.MC.Sec7.S7PIS1.S7PIS1_cont_of_smooth hg
  have hm' : (d : ℝ) < 2 * m := by linarith
  have heq : (fun ω => obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) i) =
      fun ω => Real.sqrt N * ((N : ℝ)⁻¹ * ∑ j, propagator R.D R.ρ 0 (t i) (φ i) (X 0 ω j) -
        (pair (withDensityReal (R.ρ 0)) (propagator R.D R.ρ 0 (t i) (φ i)) +
          ∫ ω', flucPair (X (0 : ℝ).toNNReal ω') (R.ρ 0) (propagator R.D R.ρ 0 (t i) (φ i)) ∂P)) := by
    funext ω
    rw [S7PIF5_init_coord R m hm T hT N hN P X₀ W X hreal t φ ht hφ i ω,
      S7PIF4_zeta_eval m hm' hN P X hX 0 hg (R.ρ 0) ω]
    unfold flucPair
    rw [pair_empirical hN0]
    simp only [Real.toNNReal_zero]
    ring
  show Measurable[ℱ s] fun ω => obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) i
  rw [heq]
  refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
  exact (Finset.measurable_sum _ fun j _ => hgc.measurable.comp
    ((measurable_pi_apply j).comp (hF.measurable_init s))).const_mul _

end Prob

end HRS.MC.Sec7.S7PIF5

end
