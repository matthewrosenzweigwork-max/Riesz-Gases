import HRS.ME.BiasF

/-!
# Chunk E, row 2.10 (fixed-`β` closure): clauses 1 and 2 for one instance of the data

`instance_clauses`: for one `(β, ρ_β, u, N, P, X, P', Z)` and numbers `A`, `B_c`, `C` with
* `W_p(Law ζ, Law Z) ≤ A N^{-1/2}` (`1 ≤ p ≤ 2`), `d_k(Law ζ, Law Z) ≤ A N^{-1/2}` (`k ≥ 1`),
* `‖h_N - r_N b‖ ≤ B_c √(log N)/√N`,
* `(A N^{-1/2} + B_c √(log N)/√N + ½ r_N² ‖b‖²)/r_N ≤ C/√(log N)`,
the conclusions of clauses 1 and 2 of `critical_bias_constants` hold.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.Bias

variable {d : ℕ}

open HRS HRS.Main

theorem instance_clauses (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ) {m : ℝ}
    (hm : (d : ℝ) < 2 * m) {T : ℝ} (hT : 0 < T) {u : ℝ} (hu : 0 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β hβ (u + T) X₀ W X)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd hβ V ρβ m Z)
    {A Bc C : ℝ} (hA : 0 ≤ A)
    (hW : ∀ p : ℝ, 1 ≤ p → p ≤ 2 → wassersteinE p (law P (windowZeta m T u P X))
      (law P' (windowPath m T 0 Z)) ≤ ENNReal.ofReal (A * (N : ℝ) ^ (-(1 : ℝ) / 2)))
    (hdk : ∀ k : ℕ, 1 ≤ k → smoothDist k (law P (windowZeta m T u P X))
      (law P' (windowPath m T 0 Z)) ≤ A * (N : ℝ) ^ (-(1 : ℝ) / 2))
    (hshift : ‖shiftE d ((d : ℝ) / 2) V N β m ρβ -
        (Real.log N / Real.sqrt N) • criticalBias d ((d : ℝ) / 2) β m ρβ‖ ≤
      Bc * (Real.sqrt (Real.log N) / Real.sqrt N))
    (hC : (A * (N : ℝ) ^ (-(1 : ℝ) / 2) + Bc * (Real.sqrt (Real.log N) / Real.sqrt N) +
        (1 / 2) * (Real.log N / Real.sqrt N) ^ 2 * ‖criticalBias d ((d : ℝ) / 2) β m ρβ‖ ^ 2) /
      (Real.log N / Real.sqrt N) ≤ C / Real.sqrt (Real.log N)) :
    (∀ p : ℝ, 1 ≤ p → p ≤ 2 →
      wassersteinE p (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
          (law P' (windowPath m T 0 Z)) ≠ ⊤ ∧
        |(wassersteinE p (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
            (law P' (windowPath m T 0 Z))).toReal / (Real.log N / Real.sqrt N) -
            ‖criticalBias d ((d : ℝ) / 2) β m ρβ‖| ≤ C / Real.sqrt (Real.log N)) ∧
    (∀ k : ℕ, 2 ≤ k →
      (∀ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) k →
        |(∫ z, Φ z ∂(law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ))) -
            ∫ z, Φ z ∂(law P' (windowPath m T 0 Z))) / (Real.log N / Real.sqrt N) -
          ∫ ω, fderiv ℝ Φ (windowPath m T 0 Z ω)
            (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ)) ∂P'|
          ≤ C / Real.sqrt (Real.log N)) ∧
      |smoothDist k (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
            (law P' (windowPath m T 0 Z)) / (Real.log N / Real.sqrt N) -
          smoothConstant P' k (windowPath m T 0 Z)
            (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ))| ≤ C / Real.sqrt (Real.log N)) := by
  have hζ := HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ hN hu hT.le P hX hm
  have hint := windowZeta_integrable_norm hd hs0 hsd V hV hβ hN hu hT.le hm P hX
  have hη := windowFluc_ae_eq hd hs0 hsd V hV hβ hρβ hN hu hT.le hm P hX
  have hG : AEMeasurable (windowPath m T 0 Z) P' :=
    (HRS.MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ ρβ m T P' Z hZ 0 le_rfl).1
  have hsh' : ‖(constPath m T (shiftE d ((d : ℝ) / 2) V N β m ρβ) : PathSpace d m T) -
      (Real.log N / Real.sqrt N) • constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ)‖ ≤
      Bc * (Real.sqrt (Real.log N) / Real.sqrt N) := by
    rw [← constPath_smul, ← constPath_sub, norm_constPath hT.le]
    exact hshift
  have hnb : ‖(constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ) : PathSpace d m T)‖ =
      ‖criticalBias d ((d : ℝ) / 2) β m ρβ‖ := norm_constPath hT.le _
  refine ⟨fun p hp1 hp2 => ?_, fun k hk => ?_⟩
  · obtain ⟨hne, hb⟩ := core_wasserstein P P' (windowZeta m T u P X)
      (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)) (windowPath m T 0 Z) hζ hG hint
      (constPath m T (shiftE d ((d : ℝ) / 2) V N β m ρβ))
      (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ)) hη hN hA hsh' p hp1 (hW p hp1 hp2)
    refine ⟨hne, ?_⟩
    rw [hnb] at hb
    refine hb.trans (le_trans ?_ hC)
    have hr0 := rate_pos hN
    refine div_le_div_of_nonneg_right ?_ hr0.le
    have : 0 ≤ (1 / 2) * (Real.log N / Real.sqrt N) ^ 2 *
        ‖criticalBias d ((d : ℝ) / 2) β m ρβ‖ ^ 2 := by positivity
    linarith
  · obtain ⟨h1, h2⟩ := core_smooth P P' (windowZeta m T u P X)
      (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)) (windowPath m T 0 Z) hζ hG
      (constPath m T (shiftE d ((d : ℝ) / 2) V N β m ρβ))
      (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ)) hη hN k hk hsh' (hdk k (by omega))
    rw [hnb] at h1 h2
    exact ⟨fun Φ hΦ => (h1 Φ hΦ).trans hC, h2.trans hC⟩

end HRS.ME.Bias
