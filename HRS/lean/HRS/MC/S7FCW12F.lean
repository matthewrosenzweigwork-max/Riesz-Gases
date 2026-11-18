import HRS.MC.S7FCW12E

/-!
# FC-E packet, part F: the particle pair `pairN` is `AEMeasurable` (FC-E, prefix `s7fcw12_`)

`s7_FC_E_pair_measurable_proof`: statement copied from `HRS/MC/Sec7Spec.lean` (`s7_FC_E_pair_measurable`).
The zeta component is `s7fcw12_aemeasurable_zetaWin`; the quadratic component is the vector-centred
field `quadFieldAt` handled by `s7fcw12_centred_aemeasurable` with `s7fcw12_quadTilde_measurable`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

namespace HRS.MC.Sec7.S7FCW12

variable {d : ℕ}

theorem s7_FC_E_pair_measurable_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} (hN : 1 ≤ N)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X) :
    AEMeasurable (pairN r T 0 R.D.s R.ρ P X) P := by
  have hS := hreal.solution T
  have hm : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hN0 : 0 < N := by omega
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => (fun t ω => X t.toNNReal ω) t ω) (Set.Icc 0 T) :=
    hS.cont.mono fun ω hω => (continuous_pi fun i =>
      (hω i).comp (continuous_real_toNNReal.comp continuous_id)).continuousOn
  unfold pairN
  refine AEMeasurable.prodMk (s7fcw12_aemeasurable_zetaWin r T hT hm P X hS.adapted hS.cont hN0) ?_
  refine s7fcw12_centred_aemeasurable hT P (fun t ω => X t.toNNReal ω) (fun t => hS.adapted _) hc
    (fun _ => 0) (fun t x => quadFieldTilde r R.D.s (withDensityReal fun y => s7fcw12_rhoPos R (t, y)) x)
    (s7fcw12_quadTilde_measurable R r) (fun t ω => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (0 + t) ω) ?_
  intro t ht ω
  have hμ : withDensityReal (R.ρ t) = withDensityReal fun y => s7fcw12_rhoPos R (t, y) := by
    congr 1
    funext y
    rw [s7fcw12_rhoPos_eq R ht.1 y]
  unfold quadFieldAt
  simp only [zero_add]
  rw [hμ]

end HRS.MC.Sec7.S7FCW12
