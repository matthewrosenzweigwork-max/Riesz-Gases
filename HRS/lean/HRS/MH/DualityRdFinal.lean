import HRS.MH.DualityRdDefs
import HRS.MH.DualityRdA4
import HRS.MH.DualityRdB3
import HRS.MH.DualityRdC2

/-!
# DualityRd packet D: the frozen `HRS.Whole.AppendixA.duality_identity_rd` (Remark S.A.13)

Assembly from the packets `empirical_ito_rd_proof` (A4, Itô's formula for the empirical pairing), `mf_time_dependent_proof` (B3,
time-dependent weak form of the mean-field equation) and `fluc_pointwise_rd_proof` (C2, pointwise algebra of the interaction
term).  Plan: `HRS/MH/DualityRdPlan.md`.  The statement is the frozen one (with the Itô integrand truncated to `[0,t]` and the
integrability conjunct, applied in place by Session A after MH-REPAIRS-2).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

/-- The frozen `duality_identity_rd`, proved from the packets A4, B3, C2. -/
theorem duality_identity_rd_proof :
    type_of% @HRS.Whole.AppendixA.duality_identity_rd := by
  intro d N s Λ T ΛV G₀ D hs hs0 hsd hinv hV ρ hρ hreg Ω mΩ P hP X₀ W X hflow ℱ W' hF t ht φ f hf
  have hM : MFData s Λ T ΛV G₀ D ρ := ⟨hs, hs0, hsd, hinv, hV, hρ, hreg⟩
  have hC := hf.isC12TestRd
  have hd : 1 ≤ d := hM.one_le_d
  have hs0' : 0 ≤ D.s := hs ▸ hs0
  have hsd' : D.s < d := hs ▸ hsd
  unfold DualityIdentityRd
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    refine Filter.Eventually.of_forall fun ζ τ hτ => ?_
    have hτ0 : τ = 0 := le_antisymm hτ.2 hτ.1
    subst hτ0
    have hI : itoIntegral P ℱ W' (fun r ζ' (ia : Fin N × Fin d) =>
        if r ∈ Set.Icc (0 : ℝ) 0 then gradComp ia.2 (f r) (X (Real.toNNReal r) ζ' ia.1) else 0) 0 ζ = 0 :=
      itoIntegral_of_nonpos P ℱ W' _ le_rfl ζ
    refine ⟨?_, ?_⟩
    · have hv : volume (Set.Icc (0 : ℝ) 0) = 0 := by simp
      unfold IntegrableOn
      rw [Measure.restrict_eq_zero.2 hv]
      exact integrable_zero_measure
    · rw [hI]
      simp
  · obtain ⟨hX, hocc⟩ := flow_contact hflow
    have hito := empirical_ito_rd_proof D hinv (measurable_gradient_of_vhyp hV) hX hF hocc hpos ht.2 hC
    have hmf := mf_time_dependent_proof hM ht hC
    filter_upwards [hito] with ζ hζ
    intro τ hτ
    obtain ⟨hI1, hE1⟩ := hζ τ hτ
    obtain ⟨hI2, hE2⟩ := hmf τ hτ
    have hpt : ∀ r ∈ Set.Icc (0 : ℝ) τ,
        (Whole.pair (Whole.empirical (X (Real.toNNReal r) ζ))
            (driftTestRd D f (fun r x => -(generatorW (D.coeff ρ) r (f r) x)) r)
          + interactionPairingW D (f r) (Whole.empirical (X (Real.toNNReal r) ζ))
              (Whole.empirical (X (Real.toNNReal r) ζ)))
        - (Whole.pair (Whole.withDensityReal (ρ r))
            (driftTestRd D f (fun r x => -(generatorW (D.coeff ρ) r (f r) x)) r)
          + interactionPairingW D (f r) (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r)))
        = flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) (ρ r) := by
      intro r hr
      have hrt : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1, hr.2.trans hτ.2⟩
      have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hrt.2.trans ht.2⟩
      exact fluc_pointwise_rd_proof D hd hs0' hsd' ρ (hM.regSlice hrT) (hC.memCb hrt) (X (Real.toNNReal r) ζ)
    have hint : IntegrableOn (fun r => flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) (ρ r))
        (Set.Icc 0 τ) :=
      (hI1.sub hI2).congr_fun (fun r hr => hpt r hr) measurableSet_Icc
    refine ⟨hint, ?_⟩
    have hsub : ∫ r in Set.Icc (0 : ℝ) τ, flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) (ρ r)
        = (∫ r in Set.Icc (0 : ℝ) τ, (Whole.pair (Whole.empirical (X (Real.toNNReal r) ζ))
            (driftTestRd D f (fun r x => -(generatorW (D.coeff ρ) r (f r) x)) r)
          + interactionPairingW D (f r) (Whole.empirical (X (Real.toNNReal r) ζ))
              (Whole.empirical (X (Real.toNNReal r) ζ))))
        - ∫ r in Set.Icc (0 : ℝ) τ, (Whole.pair (Whole.withDensityReal (ρ r))
            (driftTestRd D f (fun r x => -(generatorW (D.coeff ρ) r (f r) x)) r)
          + interactionPairingW D (f r) (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r))) := by
      rw [← integral_sub hI1 hI2]
      exact setIntegral_congr_fun measurableSet_Icc fun r hr => (hpt r hr).symm
    rw [hsub]
    change _ = _ + (Real.sqrt (2 * D.invβ) / N) *
      itoIntegral P ℱ W' (truncGradIntegrand t f X) τ ζ + _
    linarith

end HRS.MH.DualityRd
