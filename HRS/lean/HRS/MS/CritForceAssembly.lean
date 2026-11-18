import HRS.MS.CritForceWeights
import HRS.MS.CritForceHistory
import HRS.MS.CritForceIntegrability

/-!
# S8.2: conditional assembly of `HRS.Whole.weighted_critical_forcing`

`S82ScalarBlocks` is the statement of the one remaining analytic core of S8.2 (the sharp scalar
block estimates: recent block and every old unit block, in the observed time, with a geometric
factor `q^j`).  It is a `Prop`-valued definition, not an assumption of any theorem proved elsewhere.
`s82_weighted_critical_forcing_of_blocks` proves the exact type of the frozen row from it, using
the proved packets 01-06 (history partition, geometric and coordinate `L²` summation, genuine
integrals, Hermite weights, uniform-history assembly).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

/-- The scalar block estimate (core X of S8.2): constants `C, q` chosen before `ρ, N`, the
realization and the window start, with measurable block suprema in `L²` bounded by
`C w_α N^{-1/2}` (recent block) and `C w_α N^{-1/2} q^j` (old block `j`). -/
def S82ScalarBlocks : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) (a β : ℝ) (_ : 0 < a) (_ : 0 < β) (m : ℝ)
    (_ : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (_ : 0 < T),
    ∃ C q : ℝ, 0 ≤ C ∧ 0 < q ∧ q < 1 ∧
      ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ →
      ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ a₀ : ℝ, 0 ≤ a₀ → ∀ α : MultiIndex d,
        AEMeasurable (s82RecentSup (s82Centered d N a β m ρ P X) T a₀ α) P ∧
        (∫⁻ ζ, (s82RecentSup (s82Centered d N a β m ρ P X) T a₀ α ζ) ^ 2 ∂P) ^
            (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * s82Weight d m α * (N : ℝ) ^ (-(1 / 2 : ℝ))) ∧
        ∀ j : ℕ,
          AEMeasurable (s82PastSup (s82Centered d N a β m ρ P X) T a₀ j α) P ∧
          (∫⁻ ζ, (s82PastSup (s82Centered d N a β m ρ P X) T a₀ j α ζ) ^ 2 ∂P) ^
              (1 / 2 : ℝ) ≤
            ENNReal.ofReal
              (C * s82Weight d m α * (N : ℝ) ^ (-(1 / 2 : ℝ)) * q ^ j)

theorem s82_weighted_critical_forcing_of_blocks (h : S82ScalarBlocks) :
    type_of% @HRS.Whole.weighted_critical_forcing := by
  intro d hd a β ha hβ m hm T hT
  obtain ⟨C, q, hC, hq0, hq1, hblocks⟩ := h d hd a β ha hβ m hm T hT
  obtain ⟨hw, hws⟩ := s82_weight_summable d hd m hm
  refine ⟨s82HistoryConstant C q (s82Weight d m), ?_⟩
  intro ρ hρ N hN Ω _ P _ X₀ W X hX
  obtain ⟨hadj, hpath, hmean, hcent⟩ :=
    s82_well_defined d hd a β ha hβ m hm ρ hρ N hN P X₀ W X hX
  refine ⟨hadj, hpath, hmean, ?_⟩
  intro a₀ ha₀
  have hε : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hF : ∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t : Set.Icc (0 : ℝ) T,
      IntegrableOn (fun r => s82Centered d N a β m ρ P X α (a₀ + t) r ζ)
        (Set.Icc 0 (a₀ + t)) :=
    hcent.mono fun ζ hζ α t => hζ α (a₀ + t) (add_nonneg ha₀ t.property.1)
  have hbound := s82_history_bound P (s82Centered d N a β m ρ P X)
    (s82Weight d m) C q ((N : ℝ) ^ (-(1 / 2 : ℝ))) T a₀
    hC hq0 hq1 hε hT.le ha₀ hw hws hF
    (hblocks ρ hρ N hN P X₀ W X hX a₀ ha₀)
  simpa only [s82Centered] using hbound

end HRS.MS.S82BD
