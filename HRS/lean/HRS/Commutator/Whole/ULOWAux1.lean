import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Energy
import HRS.Commutator.Whole.Continuous

/-!
# Packet CMX-LOW: the low-frequency transport bound `(5.lowpartbound)` (`[N] L680-687`)

`|𝒞_{g_{≤1}}(v_{≤1},ν)| ≲ C(v) ‖P_{≤4}ν‖²_{Ḣ^{-α}} ≲ C(v) Ec`, from Lemma 4.1 (`low_velocity`)
applied to `σ = ν = chargeOf X ρ` (finite, compactly supported, of mass zero) and
`intro_control` (`(3.Scoercive)` and `(2.energy-control)`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.ULOW

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem ulow_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        |Ccomm (gloForce s) (Pleq 1 v) (chargeOf X ρ)| ≤
          C * K * (modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ)) := by
  obtain ⟨Cl, hCl, hlow⟩ := low_velocity hd hs0 hsd
  obtain ⟨Ci, hCi, hint⟩ := intro_control hd hs0 hsd
  obtain ⟨Cb, hCb, hEC⟩ := energy_control hd hs0 hsd
  refine ⟨Cl * Ci, mul_pos hCl hCi, fun p q hp hpq => ?_⟩
  obtain ⟨Cp1, hCp1, hI⟩ := hint p q hp hpq
  obtain ⟨Cp2, hCp2, hE⟩ := hEC p q hp hpq
  refine ⟨max Cp1 Cp2, lt_max_of_lt_left hCp1, fun Cp hCp ρ hρ N X hN hX v K hv => ?_⟩
  have h1 := hI Cp (le_trans (le_max_left _ _) hCp) ρ hρ N X hN hX
  obtain ⟨h0, -⟩ := hE Cp (le_trans (le_max_right _ _) hCp) ρ hρ N X hN hX
  set Ec := modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ) with hEc
  have hNpos : (0 : ℝ) < 1 / (N : ℝ) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hnp : 0 ≤ normE p ρ := ENNReal.toReal_nonneg
  have hf0 : 0 ≤ normE q (fTrunc s 1 : Euc d → ℝ) := ENNReal.toReal_nonneg
  have hEc0 : 0 ≤ Ec := by
    have : 0 ≤ (1 + normE q (fTrunc s 1 : Euc d → ℝ)) * normE p ρ :=
      mul_nonneg (by linarith) hnp
    linarith
  have hK0 : 0 ≤ K := by
    obtain ⟨L, F, hF, -, -, hLF⟩ := hv
    have := L.coe_nonneg
    linarith
  have hadm := chargeOf_admissible ρ hρ hN X
  have h2 := hlow v K hv (chargeOf X ρ) ⟨hadm.1, Or.inl hadm.2.1⟩ (fun _ => hadm.2.2)
  have h3 : homSqE (-alphaE d s) (lowFreq 4 (chargeOf X ρ).fourier) ≤ ENNReal.ofReal (Ci * Ec) :=
    le_trans (le_trans le_self_add le_self_add) h1
  calc |Ccomm (gloForce s) (Pleq 1 v) (chargeOf X ρ)|
      ≤ Cl * K * (Ci * Ec) := by
        rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
        calc ENNReal.ofReal |Ccomm (gloForce s) (Pleq 1 v) (chargeOf X ρ)|
            ≤ ENNReal.ofReal (Cl * K) *
                homSqE (-alphaE d s) (lowFreq 4 (chargeOf X ρ).fourier) := h2
          _ ≤ ENNReal.ofReal (Cl * K) * ENNReal.ofReal (Ci * Ec) := by gcongr
          _ = ENNReal.ofReal (Cl * K * (Ci * Ec)) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
    _ = Cl * Ci * K * Ec := by ring

end HRS.Commutator.Whole.ULOW
