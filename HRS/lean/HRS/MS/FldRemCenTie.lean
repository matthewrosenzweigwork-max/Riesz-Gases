import HRS.MS.FldRemCen5

/-!
# S5.3 tie: `field_remainder_centered`

`field_remainder_centered_proof` has exactly the type of the frozen `HRS.Whole.field_remainder_centered` (the frozen
declaration is `unproved`; a warning is expected).  Same orbit input and uniqueness as `field_remainder_proof`
(`FldRemTie.lean`); the maximal estimate is `s53_field_remainder_centered_of_orbit` (the mean functional of the
stationary process is bounded by a gliding-hump argument, `s53_mean_bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S52B

theorem field_remainder_centered_proof : HRS.Whole.FieldRemainderCenteredStatement := by
  intro d hd s hs0 hsd k hk m hm T ν hT hν Q ρ hρ CA
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have hO : UlOrb d s ν ρ (fun _ => (0 : Euc d)) (fun x => (fun _ : Euc d => (0 : Euc d)) x -
      convGradConvW (rieszKernelGrad d s) ρ x) θ :=
    ⟨hd, hs0, hsd, hν, hρ.2.elim fun ψ hψ => ⟨ψ, hψ⟩, fun i => ⟨0, by ext x; simp⟩, rfl, hθ⟩
  have huniq := s53_uniq hd hs0 hsd hν Q hρ T
  rw [s53_coeff_eq] at huniq
  obtain ⟨b, K, G0, G1, G2, Orb⟩ := s53_orbit_of_uniq hO (Torus.symPart Q) m hT huniq
    (s53_index_bound s hs0 hsd k hk m hm)
  rw [← s53_coeff_eq] at Orb
  exact s53_field_remainder_centered_of_orbit hd hs0 hsd m T hT hρ (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d) _ Orb CA

end HRS.MS.S53
