import HRS.MS.R2InterpAux99

/-!
# S10.2 (worker S10R), part 100 (packet F5o): the stochastic integral of `Φc` in coordinates, and its stopping at `τ_i`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

theorem s102_loc_coord (hS : S102Std C m T r c) (hT : 0 < T) (L : ℕ) {N : ℕ} {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW : IsBrownianFiltration P ℱ W') (X : ℝ≥0 → Ω → EucConfig d N) (hX : IsProgressive ℱ (ofNNRealTime X))
    (i : Fin (s102_q d L)) :
    ∀ᵐ ζ ∂P, ∀ u : ℝ,
      (localItoIntegralE P ℱ W' (s102_PhicE C m hT L X) u ζ).ofLp i =
        (Real.sqrt N * (Real.sqrt (2 * C.ν) / N)) *
          itoIntegral P ℱ W' (s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X) u ζ ∧
      itoIntegral P ℱ W' (s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X) u ζ =
        itoIntegral P ℱ W' (s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X) (min u (s102_tk hT L i)) ζ := by
  set K : ℝ := Real.sqrt N * (Real.sqrt (2 * C.ν) / N) with hK
  have hf := s102_orb_classical hS hT L i
  obtain ⟨Bg, hBg⟩ := s102_Ig_bdd hf X
  have hIg : IsProgressiveL2 P ℱ (s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X) :=
    IsProgressiveL2.of_bounded P (s102_Ig_progressive hf hX) Bg hBg
  have hΦE := s102_PhicE_locL2 hS hT L P X hX
  have hsm : IsProgressiveL2 P ℱ (fun s ω => K • s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X s ω) :=
    hIg.smul K
  have hco : (fun s ω k => (s102_PhicE C m hT L X s ω k).ofLp i) =
      fun s ω => K • s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X s ω := by
    funext s ω k
    rw [show (s102_PhicE C m hT L X s ω k).ofLp i = s102_PhicE C m hT L X s ω k i from rfl,
      s102_PhicE_apply]
    rfl
  have h1 := localItoIntegralE_euclidean hW (s102_PhicE C m hT L X) hΦE i
  have h2 := localItoIntegral_eq_itoIntegral hW hsm
  have h3 := itoIntegral_smul hW hIg K
  have h4 := s102_ito_stop hW hIg (t := s102_tk hT L i) (s102_tauk hT L i).2.1
    (fun s ω k hs => by
      unfold s102_Ig
      rw [if_neg (fun h => absurd h.2 (not_le.2 hs))])
    (fun s ω k hs => by
      unfold s102_Ig
      rw [if_neg (fun h => absurd h.1 (not_le.2 hs))])
  filter_upwards [h1, h2, h3, h4] with ζ e1 e2 e3 e4 u
  refine ⟨?_, e4 u⟩
  rw [e1 u, hco, e2 u, e3 u]

end HRS.MS.R2Interp

end
