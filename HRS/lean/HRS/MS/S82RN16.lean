import HRS.MS.S82RN15

/-!
# S8.2 R02 (S82R), N16: the exact cavity equation for the first marginal of a weak ensemble
`log p = c + phi - lam n (q*mu) - lam n (q*(f_nu - 1)) + D` where `p` is the density of the `(n+1)`-particle
marginal, `f_nu` the density of the `n`-particle marginal and `D` the cavity correction.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

theorem s82r_cav_formula (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n] {lam : ℝ}
    (hlam : lam = β / ((n + 1 : ℕ) : ℝ)) :
    ∃ c : ℝ, ∀ᵐ x ∂μ,
      0 < ((RefMarg.cavMarg V lam (n + 1)).rnDeriv μ x).toReal ∧
      Real.log (((RefMarg.cavMarg V lam (n + 1)).rnDeriv μ x).toReal) =
        c + V.φ x - lam * n * (∫ y, V.q y x ∂μ) -
          lam * n * (∫ y, V.q y x * (((RefMarg.cavMarg V lam n).rnDeriv μ y).toReal - 1) ∂μ) +
          (Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) +
            lam * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V lam n)) := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  subst hlam
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  set a0 : Empty → E := fun e => e.elim with ha0
  set θ := RefMarg.cavTheta V lam n a0 with hθ
  set Z : ℝ := ∫ x', θ x' ∂μ with hZdef
  have hZ : 0 < Z := RefMarg.integral_cavTheta_pos V hlam0 a0 n
  have hθm : Measurable θ := RefMarg.measurable_cavTheta V hlam0 a0 n
  have hmn : RefMarg.cavMarg V lam (n + 1) = μ.withDensity (fun x => ENNReal.ofReal (θ x / Z)) :=
    RefMarg.marginal_eq_normalized V hlam0 a0 (n := n) 0
  have hfm : Measurable (fun x => ENNReal.ofReal (θ x / Z)) := (hθm.div_const Z).ennreal_ofReal
  have hae := Measure.rnDeriv_withDensity μ hfm
  set ν := RefMarg.cavMarg V lam n with hν
  have hνle : ν ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)) • μ := by
    exact RefMarg.marginal_le_smul (B := Empty) V hβ hN0 (n := n) (by simp) a0 0
  haveI := isProb_pinnedLaw V hlam0 n a0
  haveI : IsProbabilityMeasure ν :=
    inferInstanceAs (IsProbabilityMeasure ((pinnedLaw V lam n a0).map (fun y => y 0)))
  have hνac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hνle
  refine ⟨-Real.log Z, ?_⟩
  rw [hmn]
  filter_upwards [hae] with x hx
  have hθpos : 0 < θ x := RefMarg.cavTheta_pos V hlam0 a0 n x
  have hp : ((μ.withDensity (fun x => ENNReal.ofReal (θ x / Z))).rnDeriv μ x).toReal = θ x / Z := by
    rw [hx, ENNReal.toReal_ofReal (by positivity)]
  rw [hp]
  refine ⟨by positivity, ?_⟩
  have hu : 0 < RefMarg.cavU V lam n a0 x := RefMarg.cavU_pos V hlam0 a0 n x
  have hθx : θ x = Real.exp (V.φ x) * RefMarg.cavU V lam n a0 x := by
    rw [hθ]; unfold RefMarg.cavTheta
    simp [pinField]
  rw [Real.log_div hθpos.ne' hZ.ne', hθx, Real.log_mul (Real.exp_pos _).ne' hu.ne', Real.log_exp]
  -- the integral identity
  have hgi : Integrable (fun y => V.q y x) ν := by
    have hμ : Integrable (fun y => V.q y x) μ := integrable_q_left V x
    exact Integrable.of_measure_le_smul ENNReal.ofReal_ne_top hνle hμ
  have hint : Integrable (fun y => (ν.rnDeriv μ y).toReal * V.q y x) μ :=
    (integrable_toReal_rnDeriv_mul_iff hνac).2 hgi
  have hgμ : Integrable (fun y => V.q y x) μ := integrable_q_left V x
  have hν_eq : ∫ y, V.q y x ∂ν = ∫ y, (ν.rnDeriv μ y).toReal * V.q y x ∂μ := by
    have := integral_rnDeriv_smul (μ := ν) (ν := μ) hνac (f := fun y => V.q y x)
    simpa [smul_eq_mul] using this.symm
  have hE : ∫ y, V.q y x * ((ν.rnDeriv μ y).toReal - 1) ∂μ =
      (∫ y, (ν.rnDeriv μ y).toReal * V.q y x ∂μ) - ∫ y, V.q y x ∂μ := by
    rw [← integral_sub hint hgμ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only; ring
  rw [hE, ← hν_eq]
  ring

end HRS.MS.S82R

end
