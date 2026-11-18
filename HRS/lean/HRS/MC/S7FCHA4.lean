import HRS.MC.S7FCHA3
import HRS.MC.S7FCW1W

/-!
# S7FCHA4: FC-H assembly, `s7_FC_H_every_B_proof`

Proof of `HRS.MC.Sec7.FCPlan.s7_FC_H_every_B` (statement copied verbatim; tied in `S7FCHATie.lean`).  The `W_q` conjunct is
`S7FCHA_Wq` (triangle inequality + H2, H3, H4, FC-B kernel data); the weak-convergence conjunct follows from
`W_1 → 0` by D7a applied to the shifted sequence `N ↦ N + 2` (the laws are probability measures only for `N ≥ 1`
because of the measurability input E).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH

variable {d : ℕ}

/-- **FC-H (assembly, `field_chaos` for EVERY admissible `B`)**, proof of `s7_FC_H_every_B`. -/
theorem s7_FC_H_every_B_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η)
    (B : ℝ → Ω' → NegSobolev d r) (hBm : Measurable (Function.uncurry B))
    (hBL2 : ∀ᵐ ω ∂P', MemLp (fun t => B t ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hBW : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) :
    (∀ G : PathSpace d r T × L2Path d r T → ℝ, Continuous G → (∃ M, ∀ z, |G z| ≤ M) →
      Tendsto (fun N : ℕ => ∫ ω, G (pairN r T 0 R.D.s R.ρ (P N) (X N) ω) ∂(P N)) atTop
        (𝓝 (∫ ω, G (pairLim r T 0 η B ω) ∂P'))) ∧
    (∀ q : ℝ, 1 ≤ q →
      Tendsto (fun N : ℕ => wassersteinE q (law (P N) (pairN r T 0 R.D.s R.ρ (P N) (X N)))
          (law P' (pairLim r T 0 η B))) atTop (𝓝 0)) := by
  have hW := S7FCHA_Wq R r hr T hT P X₀ W X hreal P' η hη B hBm hBL2 hBW
  refine ⟨?_, hW⟩
  intro G hG hGb
  obtain ⟨ε₂, c, K, hK⟩ := S7FCHA_kernelData R
  have hpN : ∀ N, 1 ≤ N → AEMeasurable (pairN r T 0 R.D.s R.ρ (P N) (X N)) (P N) := fun N hN =>
    HRS.MC.Sec7.S7FCW12.s7_FC_E_pair_measurable_proof R r hr T hT (P N) hN (X₀ N) (W N) (X N) (hreal N hN)
  have hpL : AEMeasurable (pairLim r T 0 η B) P' :=
    (HRS.MC.Sec7.S7FCW12.s7_FC_E4_limit_measurable_proof R r hr T hT P' η hη B hBm hBL2 ∅ (fun k => K k 0)).1
  obtain ⟨μ, hμ⟩ : ∃ μ : ℕ → Measure (PathSpace d r T × L2Path d r T),
      ∀ N, μ N = law (P N) (pairN r T 0 R.D.s R.ρ (P N) (X N)) := ⟨_, fun _ => rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (PathSpace d r T × L2Path d r T), ν = law P' (pairLim r T 0 η B) :=
    ⟨_, rfl⟩
  have hpμ : ∀ N, 1 ≤ N → IsProbabilityMeasure (μ N) := fun N hN => by
    rw [hμ]; exact (Measure.isProbabilityMeasure_map_iff (hpN N hN)).2 inferInstance
  haveI hpν : IsProbabilityMeasure ν := by
    rw [hν]; exact (Measure.isProbabilityMeasure_map_iff hpL).2 inferInstance
  haveI hpμ' : ∀ n, IsProbabilityMeasure (μ (n + 2)) := fun n => hpμ (n + 2) (by omega)
  have hW1 : Tendsto (fun N : ℕ => wassersteinE 1 (μ N) ν) atTop (𝓝 0) := by
    simp only [hμ, hν]; exact hW 1 le_rfl
  have hW1' : Tendsto (fun n : ℕ => wassersteinE 1 (μ (n + 2)) ν) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun N => wassersteinE 1 (μ N) ν) 2).2 hW1
  have h := HRS.MC.Sec7.S7FCW1.s7_FC_D7a_weak_proof (fun n => μ (n + 2)) ν hW1' G hG hGb
  have hint : ∀ N, 1 ≤ N → ∫ z, G z ∂(μ N) = ∫ ω, G (pairN r T 0 R.D.s R.ρ (P N) (X N) ω) ∂(P N) :=
    fun N hN => by rw [hμ]; exact integral_map (hpN N hN) hG.aestronglyMeasurable
  have hintν : ∫ z, G z ∂ν = ∫ ω, G (pairLim r T 0 η B ω) ∂P' := by
    rw [hν]; exact integral_map hpL hG.aestronglyMeasurable
  rw [← hintν]
  refine (tendsto_add_atTop_iff_nat (f := fun N : ℕ => ∫ ω, G (pairN r T 0 R.D.s R.ρ (P N) (X N) ω) ∂(P N))
    2).1 ?_
  exact h.congr fun n => hint (n + 2) (by omega)

end HRS.MC.Sec7.S7FCH

end
