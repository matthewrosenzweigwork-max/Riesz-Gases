import HRS.Energy.Commutator.SuperAssembly
import HRS.Commutator.Torus.Bridge
import HRS.Energy.Commutator.AbsConv
import HRS.Energy.Commutator.Coerc0

/-!
# Assembly of `HRS.commutator_estimate` from the packets (packet CM-FINAL)

`commutator_estimate_of_packets` has *exactly* the statement of `HRS.commutator_estimate`
(`Coercivity.lean` L166) and is proved here from

* `offDiagIntegrable_of_lipschitz` (clause (a), `AbsConv.lean`, packet CM-A),
* `energy_add_oN_nonneg` (`F_N + o_N ≥ 0`, `Coerc0.lean`, packet CM-NN; **proved**),
* `commutator_estimate_super` (regime `d-2 ≤ s < d`, Lipschitz norm only; `SuperAssembly.lean`,
  itself proved from `super_core` (Route S) and `nearField_control`),
* `commutator_estimate_sub_of_torus` (regime `0 ≤ s < d-2`, Lipschitz + fractional norm;
  `HRS/Commutator/Torus/Bridge.lean`, from the torus version of the sub-Coulomb note; **Route H**
  (`SubAssembly`, `SubCore`, `BesselKernel`, `EnergyH`, `KatoPonce`) is replaced and no longer imported here).

The final hookup `commutator_estimate := commutator_estimate_of_packets` needs the file split
described in the plan (§8) to avoid the import cycle `Coercivity → Assembly → Coercivity`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d N : ℕ}

/-- **Proposition 3.32 (commutator estimate), assembled from the packets.**  The statement is a
verbatim copy of `HRS.commutator_estimate`. -/
theorem commutator_estimate_of_packets (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), HasTransportBound d s v K →
        OffDiagIntegrable (commKernel (periodicRieszGrad d s) v) X (withDensityReal ρ) ∧
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  obtain ⟨Cn, hCn, hnn⟩ := energy_add_oN_nonneg hd hs0 hsd
  by_cases hsub : s < (d : ℝ) - 2
  · -- fractional regime
    have hd3 : 3 ≤ d := by
      have h2 : (2 : ℝ) < d := by linarith
      have : 2 < d := by exact_mod_cast h2
      omega
    obtain ⟨C₀', C', hC₀', hC', hreg⟩ := TorusNote.commutator_estimate_sub_of_torus hd3 hs0 hsub
    refine ⟨max C₀' Cn, C', le_max_of_le_left hC₀', hC', ?_⟩
    intro Λ hΛ N hN ρ hρ hρΛ X hX v K hK
    obtain ⟨L, F, hL, hF, hlip, hfrac, hLK⟩ := hK
    rw [if_pos hsub] at hLK
    have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
    refine ⟨offDiagIntegrable_of_lipschitz hd hs0 hsd hρ hρΛ X hL hlip, ?_⟩
    have hmain := hreg Λ hΛ N hN ρ hρ hρΛ X hX L F v hL hF hlip (hfrac hsub)
    have hY0 : 0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N :=
      le_trans (hnn Λ hΛ N hN ρ hρ hρΛ X hX)
        (by have := oNΛ_mono (d := d) (s := s) (N := N) hΛ0 (le_max_right C₀' Cn); linarith)
    have hmono := oNΛ_mono (d := d) (s := s) (N := N) hΛ0 (le_max_left C₀' Cn)
    have hCLF : 0 ≤ C' * (L + F) := by positivity
    calc |commQuantity d s v X (withDensityReal ρ)|
        ≤ C' * (L + F) * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀' Λ N) := hmain
      _ ≤ C' * (L + F) * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N) :=
          mul_le_mul_of_nonneg_left (by linarith) hCLF
      _ ≤ C' * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N) := by
          have : C' * (L + F) ≤ C' * K := mul_le_mul_of_nonneg_left hLK hC'.le
          exact mul_le_mul_of_nonneg_right this hY0
  · -- Lipschitz-only regime
    push_neg at hsub
    obtain ⟨C₀', C', hC₀', hC', hreg⟩ := commutator_estimate_super hd hs0 hsub hsd
    refine ⟨max C₀' Cn, C', le_max_of_le_left hC₀', hC', ?_⟩
    intro Λ hΛ N hN ρ hρ hρΛ X hX v K hK
    obtain ⟨L, F, hL, hF, hlip, hfrac, hLK⟩ := hK
    rw [if_neg (not_lt.mpr hsub)] at hLK
    have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
    refine ⟨offDiagIntegrable_of_lipschitz hd hs0 hsd hρ hρΛ X hL hlip, ?_⟩
    have hmain := hreg Λ hΛ N hN ρ hρ hρΛ X hX L v hL hlip
    have hY0 : 0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N :=
      le_trans (hnn Λ hΛ N hN ρ hρ hρΛ X hX)
        (by have := oNΛ_mono (d := d) (s := s) (N := N) hΛ0 (le_max_right C₀' Cn); linarith)
    have hmono := oNΛ_mono (d := d) (s := s) (N := N) hΛ0 (le_max_left C₀' Cn)
    have hCL : 0 ≤ C' * L := by positivity
    have hLK' : L ≤ K := by linarith
    calc |commQuantity d s v X (withDensityReal ρ)|
        ≤ C' * L * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀' Λ N) := hmain
      _ ≤ C' * L * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N) :=
          mul_le_mul_of_nonneg_left (by linarith) hCL
      _ ≤ C' * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N) := by
          have : C' * L ≤ C' * K := mul_le_mul_of_nonneg_left hLK' hC'.le
          exact mul_le_mul_of_nonneg_right this hY0

-- Exact-statement tie with the frozen `HRS.commutator_estimate` (Prop 3.32, `Coercivity.lean`).
example := (@commutator_estimate_of_packets : type_of% @HRS.commutator_estimate)

end HRS.Commutator
