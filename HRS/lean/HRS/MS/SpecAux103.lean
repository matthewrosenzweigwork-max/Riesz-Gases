import HRS.MS.SpecAux102

/-!
# S8M: `HRS.Whole.spectral_space` (S8.7, lemma `S:R:lem:spectral`)

Namespace `HRS.MS.Spec`.  `spectral_space_proof` assembles the spectral data (`s8p_spectralData_of_eig`, SpecAux101) for one
spectral datum `D`, the `L⁴` gradient bound for the same witnesses (`s8p_L4_witness`, SpecAux102) and the coupling conjunct
(`s8p_coupling_claim`, SpecAux66).  The tie `example` checks the statement against the frozen `HRS.Whole.spectral_space`.
-/

noncomputable section

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin

/-- Proof of `HRS.Whole.spectral_space`. -/
theorem spectral_space_proof : type_of% @HRS.Whole.spectral_space := by
  intro d hd a β ha hβ ρβ hρ
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have H : Mov2dTh d ((d : ℝ) / 2) β a ρβ := ⟨hd, by positivity, by linarith, hβ, ha, hρ⟩
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  obtain ⟨M, h⟩ := s8p_rho_of_thermal H hs
  obtain ⟨D⟩ := s8p_eigData H h
  have hdata := s8p_spectralData_of_eig hd a β ha hβ ρβ hρ h D
  obtain ⟨t₀, C4, ht₀, hL4⟩ := s8p_L4_witness hd ha hβ hρ h D
  exact ⟨fun l => s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l), D.om, hdata, t₀, ht₀, ⟨C4, hL4⟩,
    fun τ hτ => s8p_coupling_claim hd ha hβ hρ hdata ht₀ hL4 hτ⟩

example := (@spectral_space_proof : type_of% @HRS.Whole.spectral_space)

end HRS.MS.Spec
