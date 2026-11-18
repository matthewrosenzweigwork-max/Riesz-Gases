import HRS.MS.R2GenInitAux25

/-!
# S10.5 window comparison, packet B12: the mild identity at the window time `b+u` (stationary quadratic dynamics)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S21 HRS.MS.GenPath HRS.MS.S52

variable {d : ℕ}

theorem s105_sqrt_q {N : ℕ} (hN : 0 < N) {q : ℝ} (hq : 0 ≤ q) :
    Real.sqrt (2 * q / N) = Real.sqrt N * (Real.sqrt (2 * q) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  rw [Real.sqrt_div (by positivity)]
  have h2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
  field_simp
  rw [Real.sq_sqrt hNr.le]

theorem s105_mild_coord (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T b m : ℝ} (hb : 0 ≤ b) (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {N : ℕ} (hN : 1 ≤ N)
    (hm : (d : ℝ) < m) (C : WholeCoeff d) (hCdef : C = (quadraticGradientDyn d s a β).coeff (fun _ => ρ))
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) (b + T) X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (Mm : ℝ → Ω → KSpace d m T)
    (hΦ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' (s105Phi (fun a' r x => r2WindowFeature C m T (gradComp a') b r x)
      (b + T) β⁻¹ X))
    (hM : IsHilbertItoIntegral P ℱ W' (s105Phi (fun a' r x => r2WindowFeature C m T (gradComp a') b r x)
      (b + T) β⁻¹ X) Mm)
    (hC : OscAdjointInput C m (b + T))
    (hK : ∀ (a' : Fin d) (r : ℝ), r ∈ Set.Icc (0 : ℝ) (b + T) → ∀ x, S105WinK C m T b a' r x)
    (hcl : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t → IsClassicalAdjointW C t (oscTestFun m α)
      (fun r => propagatorW C r t (oscTestFun m α)))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d)
    (hprob : HRS.Whole.IsProbDensity ρ) :
    ∀ᵐ ζ ∂P,
      OscDual.coord (Real.sqrt N • OscDual.ofMeasureDiff m
          (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) (HRS.Whole.withDensityReal ρ)) α =
        Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) (propagatorW C 0 (b + u) (oscTestFun m α)) -
          HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (propagatorW C 0 (b + u) (oscTestFun m α))) +
        OscDual.coord (reconstructPath m T (fun τ ζ => Mm (b + τ) ζ) ζ u) α +
        Real.sqrt N * ∫ r in Set.Icc (0 : ℝ) (b + u), HRS.Whole.AppendixA.flucInteractionRd
          (quadraticGradientDyn d s a β) (propagatorW C r (b + u) (oscTestFun m α)) (X (Real.toNNReal r) ζ) ρ := by
  have ht0 : 0 ≤ b + u := by linarith [hu.1]
  have htτ : b + u ≤ b + T := by linarith [hu.2]
  have hτ : 0 < b + T := by linarith
  have ht : b + u ∈ Set.Icc (0 : ℝ) (b + T) := ⟨ht0, htτ⟩
  have hcl_t := hcl α (b + u) ht0
  have hcl_t' : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (b + u)
      (oscTestFun m α) (fun r => propagatorW C r (b + u) (oscTestFun m α)) := by
    rw [← hCdef]; exact hcl_t
  have hdual := s105_duality_stat hd hs0 hsd ha hβ hτ hρ P X₀ W X hX ℱ W' hF ht _ _ hcl_t'
  have hW : IsCylindricalBrownian P ℱ W' := HRS.GF.gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hid := s105_ident C m T b β⁻¹ N P ℱ W' X Mm hN hb hT.le hW hΦ hM hC hK u hu α
  have hprog := HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (P := P) ht0 hcl_t.isC12TestRd hF.progressive
  have hsm := HRS.itoIntegral_smul hF.brownian hprog (Real.sqrt (2 * β⁻¹ / N))
  have hψ : (fun (r : ℝ) (ζ' : Ω) (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) (b + u) then
      Real.sqrt (2 * β⁻¹ / N) * gradComp ia.2 (propagatorW C r (b + u) (oscTestFun m α))
        (X (Real.toNNReal r) ζ' ia.1) else 0) =
      fun s z => Real.sqrt (2 * β⁻¹ / N) • HRS.MH.DualityRd.truncGradIntegrand (b + u)
        (fun r => propagatorW C r (b + u) (oscTestFun m α)) X s z := by
    funext r ζ' ia
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (b + u) <;> simp [HRS.MH.DualityRd.truncGradIntegrand, hr]
  filter_upwards [hdual, hid, hsm] with ζ hd' hi hs'
  obtain ⟨-, heq⟩ := hd' (b + u) ⟨ht0, le_rfl⟩
  rw [hψ] at hi
  rw [hi, hs' (b + u)]
  have hterm : propagatorW C (b + u) (b + u) (oscTestFun m α) = oscTestFun m α := hcl_t.terminal
  haveI : IsProbabilityMeasure (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) :=
    HRS.Whole.empirical_isProbabilityMeasure (by omega) _
  haveI := HRS.MS.Thm.cb_withDensityReal_isProb hprob
  rw [OscDual.coord_smul, s56_coord_ofMeasureDiff hm]
  have heq' : HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) (propagatorW C (b + u) (b + u) (oscTestFun m α)) -
      HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (propagatorW C (b + u) (b + u) (oscTestFun m α)) =
      (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) (propagatorW C 0 (b + u) (oscTestFun m α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (propagatorW C 0 (b + u) (oscTestFun m α))) +
      (Real.sqrt (2 * β⁻¹) / N) * itoIntegral P ℱ W' (fun r ζ' (ia : Fin N × Fin d) =>
        if r ∈ Set.Icc (0 : ℝ) (b + u) then gradComp ia.2 (propagatorW C r (b + u) (oscTestFun m α))
          (X (Real.toNNReal r) ζ' ia.1) else 0) (b + u) ζ +
      ∫ r in Set.Icc (0 : ℝ) (b + u), HRS.Whole.AppendixA.flucInteractionRd (quadraticGradientDyn d s a β)
        (propagatorW C r (b + u) (oscTestFun m α)) (X (Real.toNNReal r) ζ) ρ := heq
  rw [hterm] at heq'
  have e1 : ∫ x, oscTestFun m α x ∂(HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) =
      HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) (oscTestFun m α) := rfl
  have e2 : ∫ x, oscTestFun m α x ∂(HRS.Whole.withDensityReal ρ) =
      HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (oscTestFun m α) := rfl
  rw [e1, e2, s105_sqrt_q (by omega : 0 < N) (inv_nonneg.2 hβ.le)]
  have := congrArg (fun z => Real.sqrt N * z) heq'
  have hT' : itoIntegral P ℱ W' (HRS.MH.DualityRd.truncGradIntegrand (b + u)
      (fun r => propagatorW C r (b + u) (oscTestFun m α)) X) (b + u) ζ =
      itoIntegral P ℱ W' (fun r ζ' (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) (b + u) then
        gradComp ia.2 (propagatorW C r (b + u) (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0) (b + u) ζ := rfl
  rw [hT']
  linear_combination this

end HRS.MS.R2GenInit
