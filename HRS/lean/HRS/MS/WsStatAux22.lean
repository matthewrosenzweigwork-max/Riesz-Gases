import HRS.MS.WsStatAux21

/-!
# S21 packet F3h: the dense-time bound of the centred remainder

`s21_Rt_bound`: if for every `t in [0,T]` and `alpha` the coordinate `coord (s21Rt .. t) alpha` is a.s. `g t alpha`, then a.s. for all
`t in [0,T]`, `||s21Rt t||_{B_m} <= sup_{t'} l2Norm (alpha |-> g t' alpha)`.  Proof as `s56_R_bound` (a dense sequence of times and the
continuity of the remainder, `s21_Rt_cont`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem
open HRS (Euc)

variable {d : ℕ}

theorem s21_Rt_bound (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N)
    (νb : Measure (Euc d)) [IsProbabilityMeasure νb] (M : ℝ → Ω → KSpace d b.m b.T)
    (hXc : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i)
    (hMc : ∀ ζ, Continuous fun τ => M τ ζ) (g : ℝ → MultiIndex d → Ω → ℝ)
    (hcoord : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (s21Rt S X νb M t ζ) α = g t α ζ) :
    ∀ᵐ ζ ∂P, ∀ t ∈ Set.Icc (0 : ℝ) b.T, ‖s21Rt S X νb M t ζ‖ₑ ≤
      ⨆ t' : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d => g t' α ζ) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  haveI : Nonempty (Set.Icc (0 : ℝ) b.T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) b.T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) b.T) with hs
  have hdense : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hq : ∀ᵐ ζ ∂P, ∀ n : ℕ, ∀ α : MultiIndex d,
      OscDual.coord (s21Rt S X νb M (s n) ζ) α = g (s n) α ζ := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro α
    exact hcoord (s n) (s n).2 α
  filter_upwards [hq, hXc] with ζ hq1 hXc1
  have hRc : ContinuousOn (fun t => s21Rt S X νb M t ζ) (Set.Icc (0 : ℝ) b.T) :=
    s21_Rt_cont b hbv S hN X νb M ζ hXc1 (hMc ζ).continuousOn
  set L : ℝ≥0∞ := ⨆ t' : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d => g t' α ζ) with hL
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) b.T => s21Rt S X νb M t ζ :=
    continuousOn_iff_continuous_domRestrict.1 hRc
  have hclosed : IsClosed {t : Set.Icc (0 : ℝ) b.T | ‖s21Rt S X νb M t ζ‖ₑ ≤ L} :=
    isClosed_le (continuous_enorm.comp hcont) continuous_const
  have key : ∀ t0 : Set.Icc (0 : ℝ) b.T, ‖s21Rt S X νb M t0 ζ‖ₑ ≤ L :=
    fun t0 => hdense.induction_on t0 hclosed (fun n => by
      show ‖s21Rt S X νb M (s n) ζ‖ₑ ≤ L
      rw [s56_enorm_eq_l2NormE]
      have : (fun α => OscDual.coord (s21Rt S X νb M (s n) ζ) α) = fun α => g (s n) α ζ := funext (hq1 n)
      rw [this]
      exact le_iSup (fun t' : Set.Icc (0 : ℝ) b.T => l2NormE (fun α : MultiIndex d => g t' α ζ)) (s n))
  intro t ht
  exact key ⟨t, ht⟩

end HRS.MS.S21
