import HRS.MS.GenPathAux28

/-!
# S5.6 packet P6d: the mild identity for a fixed time and coordinate
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_mild_coord (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (M : ℝ → Ω → KSpace d b.m b.T)
    (hM : IsHilbertItoIntegral P ℱ W' (s56Phi (S.coeff N) b.m b.T (S.q N) X) M)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    ∀ᵐ ζ ∂P,
      OscDual.coord (S.σ N • OscDual.ofMeasureDiff b.m (HRS.Whole.empirical (X (Real.toNNReal t) ζ))
          (HRS.Whole.withDensityReal (S.ρ N t))) α =
        S.σ N * (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
          HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) +
        OscDual.coord (reconstructPath b.m b.T M ζ t) α +
        S.σ N * ∫ r in Set.Icc (0 : ℝ) t, HRS.Whole.AppendixA.flucInteractionRd (S.dyn N)
          (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r) := by
  have hm : (d : ℝ) < b.m := by
    have := hbv.hm
    have h1 : (0 : ℝ) ≤ b.J := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hcl := s56_osc_classical b hbv S N ht α
  have hdual := s56_duality b hbv S P X₀ W X hX ℱ W' hF t ht _ _ hcl
  have hW : IsCylindricalBrownian P ℱ W' := HRS.GF.gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hid := s56_ident (S.coeff N) b.m b.T (S.q N) N P ℱ W' X M hN hW
    (fun τ => s56_phi_isHS b hbv S N hC (S.q N) P ℱ X hF.progressive τ) hM hC t ht α
  have hprog := HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (P := P) ht.1 hcl.isC12TestRd hF.progressive
  have hsm := HRS.itoIntegral_smul hF.brownian hprog (Real.sqrt (2 * S.q N / N))
  have hψ : (fun (r : ℝ) (ζ' : Ω) (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) t then
      Real.sqrt (2 * S.q N / N) * gradComp ia.2 (propagatorW (S.coeff N) r t (oscTestFun b.m α))
        (X (Real.toNNReal r) ζ' ia.1) else 0) =
      fun s z => Real.sqrt (2 * S.q N / N) • HRS.MH.DualityRd.truncGradIntegrand t
        (fun r => propagatorW (S.coeff N) r t (oscTestFun b.m α)) X s z := by
    funext r ζ' ia
    by_cases hr : r ∈ Set.Icc (0 : ℝ) t <;> simp [HRS.MH.DualityRd.truncGradIntegrand, hr]
  filter_upwards [hdual, hid, hsm] with ζ hd hi hs
  obtain ⟨-, heq⟩ := hd t ⟨ht.1, le_rfl⟩
  rw [hψ] at hi
  rw [hi, hs t]
  have hterm : propagatorW (S.coeff N) t t (oscTestFun b.m α) = oscTestFun b.m α := hcl.terminal
  haveI : IsProbabilityMeasure (HRS.Whole.empirical (X (Real.toNNReal t) ζ)) :=
    HRS.Whole.empirical_isProbabilityMeasure (by omega) _
  haveI := HRS.MS.Thm.cb_withDensityReal_isProb ((S.mf N).density t ht)
  rw [OscDual.coord_smul, s56_coord_ofMeasureDiff hm]
  rw [hterm] at heq
  have e1 : ∫ x, oscTestFun b.m α x ∂(HRS.Whole.empirical (X (Real.toNNReal t) ζ)) =
      HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal t) ζ)) (oscTestFun b.m α) := rfl
  have e2 : ∫ x, oscTestFun b.m α x ∂(HRS.Whole.withDensityReal (S.ρ N t)) =
      HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) (oscTestFun b.m α) := rfl
  rw [e1, e2, s56_sqrt_q b S hN]
  have := congrArg (fun z => S.σ N * z) heq
  have hT : itoIntegral P ℱ W' (HRS.MH.DualityRd.truncGradIntegrand t
      (fun r => propagatorW (S.coeff N) r t (oscTestFun b.m α)) X) t ζ =
      itoIntegral P ℱ W' (fun r ζ' (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) t then
        gradComp ia.2 (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (X (Real.toNNReal r) ζ' ia.1) else 0) t ζ := rfl
  have hinv : (S.dyn N).invβ = S.invβ N := rfl
  rw [hinv] at this
  rw [hT]
  linear_combination this

end HRS.MS.GenPath
