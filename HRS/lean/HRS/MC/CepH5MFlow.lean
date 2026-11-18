import HRS.Stochastic.SelectedFlow

/-!
# Packet M (CEPH5 measure lemmas): `h5_flow_of_ac`, `h5_cond_brownian`, `h5_cond_indep`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

section Flow

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} [NeZero N]

theorem h5_flow_of_ac_proof {Q : Measure Ω} (hQP : Q ≪ P) {D : DynData 1} {T : ℝ} {X₀ : Ω → Config 1 N}
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) : IsCepaLepingleFlow Q D T X₀ W X := by
  refine ⟨⟨?_, hQP.ae_le hX.toContact.init, hQP.ae_le hX.toContact.cont, hX.toContact.adapted⟩, ?_, ?_⟩
  · obtain ⟨Y, hY, hXY⟩ := hX.toContact.lift
    exact ⟨Y, hQP.ae_le hY, hXY⟩
  · obtain ⟨π, hπ, h⟩ := hX.ordered
    exact ⟨π, hπ, hQP.ae_le h⟩
  · exact hQP.ae_le hX.occupation

end Flow

end HRS.MC.CepH5Pf
