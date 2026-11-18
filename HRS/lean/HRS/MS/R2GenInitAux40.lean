import HRS.MS.R2GenInitAux39
import HRS.Main.GFFinal1
import HRS.Main.GFSpec4

/-!
# S10.5 window comparison, packet F1: the master comparison on the coupling space

`s105_R_bound_dense`: the window remainder bound with the supremum over the dense sequence `s'` of window times (measurable minorant).
`s105_master`: for the stationary quadratic dynamics, a realization `(X₀, W, X)`, a prescribed field `η₀` and the linear window process `Y`, the laws of the particle window
and of the linear window are within `C(ε_b + F + W_t)` (smooth) and `C(ε_b + F + W_t^{1/2})` (`W_1`), where `ε_b` is the initial coupling cost, `F` bounds the
commutator forcing and `W_t` the covariance error (window analogue of `s56_master`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.GF HRS.Uniform HRS.MH.DualityRd

variable {d : ℕ}

lemma s105_memCb_at {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {u : ℝ → Euc d → ℝ}
    (hu : IsClassicalAdjointW C t φ u) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) : MemCb 2 (u r) := by
  refine ⟨hu.c2 r hr, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hu.bdd j hj
  exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩

theorem s105_R_bound_dense (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T b : ℝ} (hb : 0 ≤ b) (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ)
    (hS : S105Stat d s a β T b ρ) {N : ℕ} (hN : 1 ≤ N)
    (hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ))
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) (b + T) X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (Mm : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T)
    (hΦ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' (s105Phi (fun a' r x => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
      (b + T) β⁻¹ X))
    (hM : IsHilbertItoIntegral P ℱ W' (s105Phi (fun a' r x => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
      (b + T) β⁻¹ X) Mm)
    (s' : ℕ → Set.Icc (0 : ℝ) T) (hs' : DenseRange s') :
    ∀ᵐ ζ ∂P, ∀ u ∈ Set.Icc (0 : ℝ) T, ‖s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ‖ₑ ≤
      ⨆ n : ℕ, l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (fun _ => ρ) X α
          (b + (s' n)) r ζ) := by
  have hq : ∀ᵐ ζ ∂P, ∀ n : ℕ, ∀ α : MultiIndex d, OscDual.coord (s105R ((quadraticGradientDyn d s a β).coeff
      (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm (s' n) ζ) α =
      -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (fun _ => ρ) X α
          (b + (s' n)) r ζ := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro α
    filter_upwards [s105_R_coord hd hs0 hsd ha hβ hb hT hρ hS hN hm P X₀ W X hX ℱ W' hF Mm hΦ hM (s' n).2 α] with ζ h
    rw [h]
    have hcl := hS.hcl α (b + s' n) (by linarith [(s' n).2.1])
    have hmem : ∀ r ∈ Set.Icc (0 : ℝ) (b + s' n), MemCb 2 (propagatorW
        ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r (b + s' n)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) := fun r hr =>
      s105_memCb_at hcl hr
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [s105_fluc_eq_forcing (by omega) hs0 hsd a β hS.hreg (hmem r hr) (X (Real.toNNReal r) ζ)]
    unfold r2CommForcingMov
    ring
  filter_upwards [hq, hX.cont] with ζ hq1 hXc
  set L : ℝ≥0∞ := ⨆ n : ℕ, l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (fun _ => ρ) X α
          (b + (s' n)) r ζ) with hL
  have hRc := s105_R_cont (by omega) hT.le hb hS hN (Real.sqrt N) hm X ζ hXc Mm (hM.cont ζ).continuousOn
  have hcont : Continuous fun u : Set.Icc (0 : ℝ) T => s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ :=
    continuousOn_iff_continuous_domRestrict.1 hRc
  have hclosed : IsClosed {u : Set.Icc (0 : ℝ) T | ‖s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ‖ₑ ≤ L} :=
    isClosed_le (continuous_enorm.comp hcont) continuous_const
  have key : ∀ t0 : Set.Icc (0 : ℝ) T, ‖s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm t0 ζ‖ₑ ≤ L := fun t0 =>
    hs'.induction_on t0 hclosed (fun n => by
      show ‖s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm (s' n) ζ‖ₑ ≤ L
      rw [s56_enorm_eq_l2NormE]
      have : (fun α => OscDual.coord (s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm (s' n) ζ) α) = _ := funext (hq1 n)
      rw [this]
      exact le_iSup (fun n : ℕ => l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (fun _ => ρ) X α
          (b + (s' n)) r ζ)) n)
  intro u hu
  exact key ⟨u, hu⟩

end HRS.MS.R2GenInit
