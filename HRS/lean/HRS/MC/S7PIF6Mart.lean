import HRS.Stochastic.Ito

/-!
# Packet piF6, part C: increments of a local Itô integral with a bounded integrand on `(a,b]`

If `Ψ` is progressive and locally square integrable and `|Ψ| ≤ C` on `(a,b] × Ω`, then the increment
`I_b - I_a` of the local Itô integral `I = ∫ Ψ dW` is a.s. equal to the (true, square integrable, centred)
Itô integral at time `b` of the restriction `1_{(a,b]} Ψ`.  Hence it is integrable with mean zero.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF6

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

/-- the restriction of a bounded progressive integrand to `(a,b]` is square integrable -/
theorem S7PIF6_restrict_L2 {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {Ψ : ℝ → Ω → ι → ℝ} (hprog : IsProgressive ℱ Ψ) {a b C : ℝ}
    (hC : ∀ s ∈ Set.Ioc a b, ∀ ω k, |Ψ s ω k| ≤ C) :
    IsProgressiveL2 P ℱ (restrictFun Ψ a b Set.univ) := by
  refine ⟨isProgressive_restrictFun hprog MeasurableSet.univ, fun T' => ?_⟩
  unfold sqIntegralOn
  have hpt : ∀ s ω k, ‖restrictFun Ψ a b Set.univ s ω k‖ₑ ≤ ENNReal.ofReal C := by
    intro s ω k
    unfold restrictFun
    by_cases h : ω ∈ (Set.univ : Set Ω) ∧ s ∈ Set.Ioc a b
    · rw [if_pos h, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hC s h.2 ω k)
    · rw [if_neg h]; simp
  have h1 : ∀ ω, ∫⁻ s in Set.Icc 0 T', ∑ k, ‖restrictFun Ψ a b Set.univ s ω k‖ₑ ^ 2 ≤
      ∫⁻ s in Set.Icc 0 T', (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal C ^ 2 := by
    intro ω
    refine lintegral_mono fun s => ?_
    calc ∑ k, ‖restrictFun Ψ a b Set.univ s ω k‖ₑ ^ 2
        ≤ ∑ _k : ι, ENNReal.ofReal C ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left' (hpt s ω k) 2
      _ = (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal C ^ 2 := by simp
  refine lt_of_le_of_lt (lintegral_mono h1) ?_
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, measure_univ, mul_one,
    Real.volume_Icc]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
    (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top

/-- the increment `I_b - I_a` of a local Itô integral with an integrand bounded on `(a,b]` is a
square integrable centred random variable -/
theorem S7PIF6_mart_incr {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W)
    {Ψ : ℝ → Ω → ι → ℝ} (hΨ : IsProgressiveLocL2 P ℱ Ψ) {a b C : ℝ} (hab : a ≤ b)
    (hC : ∀ s ∈ Set.Ioc a b, ∀ ω k, |Ψ s ω k| ≤ C) :
    ∃ Mart : Ω → ℝ, Integrable Mart P ∧ ∫ ω, Mart ω ∂P = 0 ∧
      ∀ᵐ ω ∂P, localItoIntegral P ℱ W Ψ b ω - localItoIntegral P ℱ W Ψ a ω = Mart ω := by
  classical
  have hΨ' := S7PIF6_restrict_L2 (P := P) hΨ.prog hC
  refine ⟨itoIntegral P ℱ W (restrictFun Ψ a b Set.univ) b,
    (memLp_two_itoIntegral hW hΨ' b).integrable one_le_two, integral_itoIntegral hW hΨ' b, ?_⟩
  have hτb : IsStoppingTime ℱ (fun _ : Ω => ((b : ℝ) : WithTop ℝ)) := isStoppingTime_const ℱ b
  have hτa : IsStoppingTime ℱ (fun _ : Ω => ((a : ℝ) : WithTop ℝ)) := isStoppingTime_const ℱ a
  have hsplit : stopIntegrand Ψ (fun _ : Ω => ((b : ℝ) : WithTop ℝ)) =
      fun s ω => stopIntegrand Ψ (fun _ : Ω => ((a : ℝ) : WithTop ℝ)) s ω +
        restrictFun Ψ a b Set.univ s ω := by
    funext s ω
    funext k
    simp only [stopIntegrand, restrictFun, Set.indicator, Set.mem_ofPred_eq, Pi.add_apply,
      WithTop.coe_le_coe, Set.mem_univ, true_and, Set.mem_Ioc]
    by_cases h1 : s ≤ a
    · have h2 : s ≤ b := h1.trans hab
      simp [h1, h2, not_lt.2 h1]
    · by_cases h2 : s ≤ b
      · simp [h1, h2, not_le.1 h1]
      · simp [h1, h2]
  have e1 := localItoIntegral_stopIntegrand hW hΨ hτb
  have e2 := localItoIntegral_stopIntegrand hW hΨ hτa
  have e3 := localItoIntegral_add hW (hΨ.stopIntegrand hτa) hΨ'.locL2
  have e4 := localItoIntegral_eq_itoIntegral hW hΨ'
  filter_upwards [e1, e2, e3, e4] with ω h1 h2 h3 h4
  have hb1 := h1 b
  rw [hsplit, h3 b, h4 b, h2 b] at hb1
  have hs1 : stoppedProcess (localItoIntegral P ℱ W Ψ) (fun _ : Ω => ((a : ℝ) : WithTop ℝ)) b ω =
      localItoIntegral P ℱ W Ψ (min b a) ω := stoppedProcess_apply_coe (M := localItoIntegral P ℱ W Ψ)
        (σ := fun _ : Ω => ((a : ℝ) : WithTop ℝ)) (ω := ω) (c := a) rfl b
  have hs2 : stoppedProcess (localItoIntegral P ℱ W Ψ) (fun _ : Ω => ((b : ℝ) : WithTop ℝ)) b ω =
      localItoIntegral P ℱ W Ψ (min b b) ω := stoppedProcess_apply_coe (M := localItoIntegral P ℱ W Ψ)
        (σ := fun _ : Ω => ((b : ℝ) : WithTop ℝ)) (ω := ω) (c := b) rfl b
  rw [hs1, hs2, min_eq_right hab, min_self] at hb1
  linarith

end HRS.MC.Sec7.S7PIF6

end
