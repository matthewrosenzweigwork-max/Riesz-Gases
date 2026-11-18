import HRS.MH.ScreenedS4Aux5

/-!
# Packet S4 (`kg_rep_of_symbol`): from the Fourier identity to a representative `w ∈ L²`

`W = 𝓕⁻(m_i v̂) ∈ L²` (Plancherel), `w = Re W`; the pairing `∫ w φ = -∫ v h_φ` is Parseval with
`ĥ_φ = m φ̂` (`ScreenedS4Aux1/2`), and `‖w‖₂ ≤ ‖m v̂‖₂ ≤ C ‖v‖_{H^{s+1-d}}` (`ScreenedS4Aux3/4`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem kg_rep_of_symbol_proof (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) (hs1 : (d : ℝ) - 1 ≤ s) (c : ℝ) (hc : 0 < c)
    (hid : ∀ (i : Fin d) (φ : SchwartzMap (Euc d) ℝ) (y : Euc d),
      Integrable (fun ξ : Euc d => ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
        𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) ∧
      ((HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y : ℝ) : ℂ) =
        ∫ ξ : Euc d, ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
          𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ *
          Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))) :
    ∃ C : ℝ, ∀ (i : Fin d) (v : Euc d → ℝ), sobolevNormE (s + 1 - d) v < ⊤ →
      ∃ w : Euc d → ℝ, IsGradKernelRep d s i v w ∧ MemLp w 2 volume ∧
        eLpNorm w 2 volume ≤ ENNReal.ofReal C * sobolevNormE (s + 1 - d) v :=
  s4_main hd hsd hs1 c hc hid

end HRS.MH.Screened
