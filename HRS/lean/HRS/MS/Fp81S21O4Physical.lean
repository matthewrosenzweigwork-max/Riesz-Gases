import HRS.MS.Fp81S21ErrorEnvelopePhysicalAssembly
import HRS.MS.Fp81S21SkeletonPhysical

noncomputable section
open Filter Topology
namespace HRS.Fp81.S21
open HRS.MS.R26T3

theorem fp81s21_O4_physical (p : Parameters) : fp81s21_O4_common_radius p := by
  obtain ⟨δ₀, hδ₀, hhalf, hall⟩ := fp81s21_errorEnvelope_physical p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Q, O1, hκ, future, hf, α, hα, hinit, C, c, hC, hc, hDec⟩ :=
    hall δ hδ hδle R
  have hdec : ∀ L : ℝ, 0 < L → ∃ eL : ℕ → ℝ,
      Tendsto eL atTop (𝓝 0) ∧ ∀ N : ℕ, 2 ≤ N →
        fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N ≤
          α N + eL N + C * Real.exp (-c * L) := by
    intro L hL
    obtain ⟨eL, heL, hbound⟩ := hDec L hL
    exact ⟨eL, heL.2, hbound⟩
  exact ⟨O1, ⟨α, hα.2⟩, ⟨fp81s21_O5_of_physical p R O1 α hα.2 C c hc hdec⟩⟩

end HRS.Fp81.S21
end

#print axioms HRS.Fp81.S21.fp81s21_O4_physical
