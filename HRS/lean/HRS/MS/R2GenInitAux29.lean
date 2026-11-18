import HRS.MS.R2GenInitAux28

/-!
# S10.5 window comparison, packet C3: the window remainder is the interaction forcing; continuity and the bound by `F`

`S105Stat`: the stationary orbit/feature data used by the window comparison (packaged once from S10.3 in `R2GenInitAux31`).
`s105_R_cont`: a.s. continuity of `u ↦ R_b(u)`.  `s105_R_coord`: `coord_α R_b(u) = √N ∫_0^{b+u} flucInteractionRd`.
`s105_R_bound`: `‖R_b(u)‖ ≤ sup_{u'} l2NormE (√N ∫_0^{b+u'} flucInteractionRd)` a.s. for every `u ∈ [0,T]`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.MH.DualityRd

variable {d : ℕ}

/-- The stationary data of the window comparison (see the module docstring). -/
structure S105Stat (d : ℕ) (s a β T b : ℝ) (ρ : Euc d → ℝ) : Prop where
  hC : OscAdjointInput ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) (b + T)
  hK : ∀ (a' : Fin d) (r : ℝ), r ∈ Set.Icc (0 : ℝ) (b + T) → ∀ x,
    S105WinK ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T b a' r x
  hF : S105Feat d ((wholeSpaceIndex d : ℕ) : ℝ) T (b + T) (fun a' r x => r2WindowFeature
    ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
  hcl : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t → IsClassicalAdjointW
    ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)
    (fun r => propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t
      (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))
  hprob : HRS.Whole.IsProbDensity ρ
  hρ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ x)
  hreg : RegSliceRd ρ

theorem s105_R_cont (hd1 : 1 ≤ d) {s a β T b : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b) {ρ : Euc d → ℝ}
    (hS : S105Stat d s a β T b ρ) {N : ℕ} (hN : 1 ≤ N) (σ : ℝ)
    (hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ)) {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω)
    (hXc : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i)
    (M : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T)
    (hMc : ContinuousOn (fun t => M t ζ) (Set.Icc 0 (b + T))) :
    ContinuousOn (fun u => s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b σ ρ X M u ζ) (Set.Icc (0 : ℝ) T) := by
  unfold s105R s105Xi
  have hxi : ContinuousOn (fun t => σ • OscDual.ofMeasureDiff ((wholeSpaceIndex d : ℕ) : ℝ)
      (HRS.Whole.empirical (X (Real.toNNReal t) ζ)) (HRS.Whole.withDensityReal ρ)) (Set.Icc (0 : ℝ) (b + T)) := by
    have := s56_xi_cont_time hd1 hm σ (by omega : 0 < N) (T := b + T) (fun _ => ρ) (fun t _ => hS.hprob)
      (fun ψ _ _ => continuousOn_const) (fun t => X (Real.toNNReal t) ζ) (fun i => (hXc i).comp continuous_real_toNNReal)
    exact this
  have hxi' : ContinuousOn (fun u => σ • OscDual.ofMeasureDiff ((wholeSpaceIndex d : ℕ) : ℝ)
      (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) (HRS.Whole.withDensityReal ρ)) (Set.Icc (0 : ℝ) T) :=
    hxi.comp (by fun_prop) (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hshift : ContinuousOn (fun τ => M (b + τ) ζ) (Set.Icc 0 T) :=
    hMc.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  exact (hxi'.sub (HRS.MS.U9.u9_continuousOn_evalA hT _)).sub
    (continuousOn_iff_continuous_restrict.2 (HRS.MS.U9.u9_continuous_recon hT (fun τ ζ => M (b + τ) ζ) ζ hshift))

theorem s105_R_coord (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
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
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    ∀ᵐ ζ ∂P, OscDual.coord (s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ) α =
      Real.sqrt N * ∫ r in Set.Icc (0 : ℝ) (b + u), flucInteractionRd (quadraticGradientDyn d s a β)
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r (b + u)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) (X (Real.toNNReal r) ζ) ρ := by
  filter_upwards [s105_mild_coord hd hs0 hsd ha hβ hb hT hρ hN hm _ rfl P X₀ W X hX ℱ W' hF Mm hΦ hM hS.hC hS.hK hS.hcl hu α hS.hprob] with ζ h
  unfold s105R s105Xi s105K0
  rw [s56_coord_sub, s56_coord_sub, s105_k0_eval _ hb rfl hS.hC (Real.sqrt N) hS.hprob hS.hρ2 hN (X 0 ζ) hu α hS.hF
    (fun a' z => hS.hK a' 0 ⟨le_rfl, by linarith [hu.1, hu.2]⟩ z) (hS.hcl α (b + u) (by linarith [hu.1]))]
  linarith

theorem s105_R_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
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
      (b + T) β⁻¹ X) Mm) :
    ∀ᵐ ζ ∂P, ∀ u ∈ Set.Icc (0 : ℝ) T, ‖s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ‖ₑ ≤
      ⨆ u' : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
        Real.sqrt N * ∫ r in Set.Icc (0 : ℝ) (b + u'), flucInteractionRd (quadraticGradientDyn d s a β)
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r (b + u')
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) (X (Real.toNNReal r) ζ) ρ) := by
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  set s' : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hs'
  have hdense : DenseRange s' := TopologicalSpace.denseRange_denseSeq _
  have hq : ∀ᵐ ζ ∂P, ∀ n : ℕ, ∀ α : MultiIndex d, OscDual.coord (s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm (s' n) ζ) α =
      Real.sqrt N * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), flucInteractionRd (quadraticGradientDyn d s a β)
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r (b + (s' n))
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) (X (Real.toNNReal r) ζ) ρ := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro α
    exact s105_R_coord hd hs0 hsd ha hβ hb hT hρ hS hN hm P X₀ W X hX ℱ W' hF Mm hΦ hM (s' n).2 α
  filter_upwards [hq, hX.cont] with ζ hq1 hXc
  set L : ℝ≥0∞ := ⨆ u' : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
      Real.sqrt N * ∫ r in Set.Icc (0 : ℝ) (b + u'), flucInteractionRd (quadraticGradientDyn d s a β)
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r (b + u')
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) (X (Real.toNNReal r) ζ) ρ) with hL
  have hRc := s105_R_cont (by omega) hT.le hb hS hN (Real.sqrt N) hm X ζ hXc Mm (hM.cont ζ).continuousOn
  have hcont : Continuous fun u : Set.Icc (0 : ℝ) T => s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ :=
    continuousOn_iff_continuous_domRestrict.1 hRc
  have hclosed : IsClosed {u : Set.Icc (0 : ℝ) T | ‖s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ‖ₑ ≤ L} :=
    isClosed_le (continuous_enorm.comp hcont) continuous_const
  have key : ∀ t0 : Set.Icc (0 : ℝ) T, ‖s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm t0 ζ‖ₑ ≤ L := fun t0 =>
    hdense.induction_on t0 hclosed (fun n => by
      show ‖s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm (s' n) ζ‖ₑ ≤ L
      rw [s56_enorm_eq_l2NormE]
      have : (fun α => OscDual.coord (s105R ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm (s' n) ζ) α) = _ := funext (hq1 n)
      rw [this]
      exact le_iSup (fun u' : Set.Icc (0 : ℝ) T => l2NormE (fun α : MultiIndex d =>
        Real.sqrt N * ∫ r in Set.Icc (0 : ℝ) (b + u'), flucInteractionRd (quadraticGradientDyn d s a β)
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r (b + u')
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) (X (Real.toNNReal r) ζ) ρ)) (s' n))
  intro u hu
  exact key ⟨u, hu⟩

end HRS.MS.R2GenInit
