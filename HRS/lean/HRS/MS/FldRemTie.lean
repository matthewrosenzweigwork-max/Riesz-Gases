import HRS.MS.FldRemAux4

/-!
# S5.3 tie: `field_remainder` (first assertion)

`field_remainder_proof` has exactly the type of the frozen `HRS.Whole.field_remainder` (the frozen declaration is
`unproved`; a warning is expected).  Route: the frozen coefficient is `fixedViscosityCoeff s (-1) Q' ν c ρ` with
`Q' = (Q + Qᵀ)/2`, `c = -∇g*ρ` (`s53_coeff_eq`); classical adjoint solutions are unique (`s53_uniq`, F-CAU); the orbit
input is `s53_orbit_of_uniq` (explicit index `s52bIdx d s (K0 + 2)`, `K0 = ⌊4 + d/2⌋ + 1`, so that
`m - J > 2d`); the proof of the maximal estimate is `s53_field_remainder_of_orbit`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S52B

theorem s53_index_bound {d : ℕ} (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (k : ℕ)
    (hk : (d : ℝ) / 2 + 6 < k) (m : ℝ) (hm : ((2 * k + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < m) :
    ((s52bIdx d s (⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1 + 2) : ℕ) : ℝ) + 2 * d < m := by
  have h1 : ((⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ 4 + (d : ℝ) / 2 := Nat.floor_le (by positivity)
  have h2 : ((⌈s + 1⌉₊ : ℕ) : ℝ) < s + 1 + 1 := Nat.ceil_lt_add_one (by linarith)
  have h3 : ((⌊(d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
  have h4 : ((2 * k + 2 * d + 20 : ℕ) : ℝ) = 2 * (k : ℝ) + 2 * d + 20 := by push_cast; ring
  unfold s52bIdx
  push_cast
  rw [h4] at hm
  linarith

theorem field_remainder_proof : HRS.Whole.FieldRemainderStatement := by
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
  exact s53_field_remainder_of_orbit hd hs0 hsd m T hT hρ (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d) _ Orb CA

end HRS.MS.S53
