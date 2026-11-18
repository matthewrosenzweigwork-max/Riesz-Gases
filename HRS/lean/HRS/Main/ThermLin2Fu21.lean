import HRS.Main.ThermLin2Dy6
import HRS.Main.ThermLin2Fu20

/-!
# THERMLIN2 Fu21: `tl2_remainder_bound_proof` (B5)

**Uses the plan statements `tl2_Delta_bound` (B2) and, through `tl2_dyson_fubini_proof` (B4), `tl2_dyson_pairing` (B1)
as black boxes**; the orchestrator swaps in the `_proof` versions at integration.

Proof: fixed-time pairing bound (`tl2fu_pairing_bound`, Fu19) for every smooth test, then the rational-grid argument
(`tl2fu_grid_bound`, Fu20) using continuity of `Zs - Zw` and the monotonicity `Rhs_s <= e^{c(t-s)} Rhs_t`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

/-- B5 (proved): the pathwise bound of the remainder `R = Zs - Zw`, simultaneously for all `t in [0,T']`.
Uses `tl2_Delta_bound` (B2) and (via B4) `tl2_dyson_pairing` (B1) as black boxes. -/
theorem tl2_remainder_bound_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
      ∀ {T' : ℝ}, 0 < T' → ∀ {K c : ℝ}, 0 ≤ K → 0 < c →
      ∀ (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
        IsDualEvolution S.dyn S.ρ m Vev → IsPlainEvolution Vev T' →
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T' → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u))) →
        IsDualEvolution S.dyn (fun _ => ρβ) m Wev → IsPlainEvolution Wev T' →
        (∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K) →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
        (G : ℝ → Ω → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r) →
        (∀ ω, Continuous fun s => G s ω) → (∀ ω, G 0 ω = 0) →
      ∀ (Zs Zw : ℝ → Ω → NegSobolev d m),
        (∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t)) →
        (∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t)) →
        (∀ t, Measurable (Zs t)) → (∀ t, Measurable (Zw t)) →
        (∀ᵐ ω ∂P, ContinuousOn (fun t => Zs t ω) (Set.Icc 0 T')) →
        (∀ᵐ ω ∂P, ContinuousOn (fun t => Zw t ω) (Set.Icc 0 T')) →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T',
          ‖Zs t ω - Zw t ω‖ₑ ≤ ENNReal.ofReal (C * K) *
            ∫⁻ r in Set.Icc (0 : ℝ) t,
              ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) *
                tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω) := by
  obtain ⟨C, κ, hC, hκ, hB⟩ := tl2_Delta_bound_proof S h m hm
  refine ⟨C, κ, hC, hκ, ?_⟩
  intro T' hT' K c hK hc Vev Wev hVd hVp hdec hWd hWp hWb Ω mΩ P _ ℱ G hG hGc hGz Zs Zw hZs hZw hZsm hZwm hZsc hZwc
  set Rhs : ℝ → Ω → ℝ≥0∞ := fun t ω => ENNReal.ofReal (C * K) *
    ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) *
      tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω) with hRhs
  have hmono : ∀ ω, ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      Rhs s ω ≤ ENNReal.ofReal (Real.exp (c * (t - s))) * Rhs t ω := by
    intro ω s t hs hst
    simp only [hRhs]
    have e : ∀ r : ℝ, ENNReal.ofReal (Real.exp (-c * (s - r)) * Real.exp (-κ * r)) *
        tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω) =
        ENNReal.ofReal (Real.exp (c * (t - s))) * (ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) *
          tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω)) := by
      intro r
      have : Real.exp (-c * (s - r)) * Real.exp (-κ * r) =
          Real.exp (c * (t - s)) * (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) := by
        simp only [← Real.exp_add]; congr 1; ring
      rw [this, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    calc ENNReal.ofReal (C * K) * ∫⁻ r in Set.Icc (0 : ℝ) s,
          ENNReal.ofReal (Real.exp (-c * (s - r)) * Real.exp (-κ * r)) *
            tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω)
        = ENNReal.ofReal (C * K) * (ENNReal.ofReal (Real.exp (c * (t - s))) *
            ∫⁻ r in Set.Icc (0 : ℝ) s, ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) *
              tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω)) := by
          simp_rw [e]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (C * K) * (ENNReal.ofReal (Real.exp (c * (t - s))) *
            ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) *
              tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω)) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp (c * (t - s))) * (ENNReal.ofReal (C * K) *
            ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) *
              tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω)) := mul_left_comm _ _ _
  have hRc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zs t ω - Zw t ω) (Set.Icc 0 T') := by
    filter_upwards [hZsc, hZwc] with ω h1 h2
    exact h1.sub h2
  have hpair : ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ∀ᵐ ω ∂P, ENNReal.ofReal |NegSobolev.eval (Zs t ω - Zw t ω) φ| ≤
        ENNReal.ofReal ‖lpFun m φ‖ * Rhs t ω := by
    intro t ht φ hφ
    exact tl2fu_pairing_bound S h m hm hC hB hT' hK hc Vev Wev hVd hVp hdec hWd hWp hWb P G hG hGc hGz Zs Zw
      hZs hZw hZsm hZwm hZwc ht hφ
  have := tl2fu_grid_bound P m T' c (fun t ω => Zs t ω - Zw t ω) Rhs hRc hmono hpair
  filter_upwards [this] with ω hω t ht
  exact hω t ht

example := (@tl2_remainder_bound_proof : type_of% @tl2_remainder_bound)

end HRS.ThermLin.Plan2
