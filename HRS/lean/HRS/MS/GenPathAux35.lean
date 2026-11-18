import HRS.MS.GenPathAux34

/-!
# S5.6 packet P6g: a.s. continuity and the bound of the remainder `R`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_R_cont (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (M : ℝ → Ω → KSpace d b.m b.T)
    (hMc : ∀ ζ, Continuous fun τ => M τ ζ) :
    ∀ᵐ ζ ∂P, ContinuousOn (fun t => s56R S X M t ζ) (Set.Icc (0 : ℝ) b.T) := by
  filter_upwards [hX.cont] with ζ hζ
  have hT : 0 ≤ b.T := hbv.hT.le
  unfold s56R
  refine ContinuousOn.sub (ContinuousOn.sub (s56_xi_cont b hbv S (by omega) X ζ hζ)
    (HRS.MS.U9.u9_continuousOn_evalA hT _)) ?_
  exact continuousOn_iff_continuous_domRestrict.2
    (HRS.MS.U9.u9_continuous_recon hT M ζ (hMc ζ).continuousOn)

theorem s56_R_bound (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (M : ℝ → Ω → KSpace d b.m b.T)
    (hM : IsHilbertItoIntegral P ℱ W' (s56Phi (S.coeff N) b.m b.T (S.q N) X) M) :
    ∀ᵐ ζ ∂P, ∀ t ∈ Set.Icc (0 : ℝ) b.T, ‖s56R S X M t ζ‖ₑ ≤
      ⨆ t' : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
        S.σ N * ∫ r in Set.Icc (0 : ℝ) t', HRS.Whole.AppendixA.flucInteractionRd (S.dyn N)
          (propagatorW (S.coeff N) r t' (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r)) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  haveI : Nonempty (Set.Icc (0 : ℝ) b.T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) b.T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) b.T) with hs
  have hdense : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hq : ∀ᵐ ζ ∂P, ∀ n : ℕ, ∀ α : MultiIndex d, OscDual.coord (s56R S X M (s n) ζ) α =
      S.σ N * ∫ r in Set.Icc (0 : ℝ) (s n), HRS.Whole.AppendixA.flucInteractionRd (S.dyn N)
          (propagatorW (S.coeff N) r (s n) (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r) := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro α
    filter_upwards [s56_mild_coord b hbv S hN hC P X₀ W X hX ℱ W' hF M hM (s n).2 α] with ζ h
    unfold s56R s56Xi s56K0
    rw [s56_coord_sub, s56_coord_sub, s56_k0_eval b hbv S N hN hC (S.σ N) (X 0 ζ) (s n).2 α]
    linarith
  filter_upwards [hq, s56_R_cont b hbv S hN P X₀ W X hX ℱ W' M hM.cont] with ζ hq1 hRc
  set L : ℝ≥0∞ := ⨆ t' : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
        S.σ N * ∫ r in Set.Icc (0 : ℝ) t', HRS.Whole.AppendixA.flucInteractionRd (S.dyn N)
          (propagatorW (S.coeff N) r t' (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r)) with hL
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) b.T => s56R S X M t ζ :=
    continuousOn_iff_continuous_domRestrict.1 hRc
  have hclosed : IsClosed {t : Set.Icc (0 : ℝ) b.T | ‖s56R S X M t ζ‖ₑ ≤ L} :=
    isClosed_le (continuous_enorm.comp hcont) continuous_const
  have key : ∀ t0 : Set.Icc (0 : ℝ) b.T, ‖s56R S X M t0 ζ‖ₑ ≤ L := fun t0 => hdense.induction_on t0 hclosed
    (fun n => by
      show ‖s56R S X M (s n) ζ‖ₑ ≤ L
      rw [s56_enorm_eq_l2NormE]
      have : (fun α => OscDual.coord (s56R S X M (s n) ζ) α) = _ := funext (hq1 n)
      rw [this]
      exact le_iSup (fun t' : Set.Icc (0 : ℝ) b.T => l2NormE (fun α : MultiIndex d =>
        S.σ N * ∫ r in Set.Icc (0 : ℝ) t', HRS.Whole.AppendixA.flucInteractionRd (S.dyn N)
          (propagatorW (S.coeff N) r t' (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r))) (s n))
  intro t ht
  exact key ⟨t, ht⟩

end HRS.MS.GenPath
