import HRS.MS.CritForceAssembly
import HRS.MS.CritForceHistoryMaj

/-!
# S8.2: conditional assembly from the majorant form of the scalar block statement

`S82ScalarBlocksMaj` is the (strictly weaker) form of the remaining analytic core in which the recent
and old block suprema are only required to have AEMeasurable almost sure majorants with the stated
`L²` bounds, instead of being AEMeasurable themselves (no continuity in the observed time is needed
for the final estimate).  `S82ScalarBlocks` implies it, and it implies the exact type of the frozen row.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

/-- The scalar block estimate with measurable majorants (core X of S8.2, weakest useful form). -/
def S82ScalarBlocksMaj : Prop :=
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
        ∃ R : Ω → ℝ≥0∞, AEMeasurable R P ∧
        (∀ᵐ ζ ∂P, s82RecentSup (s82Centered d N a β m ρ P X) T a₀ α ζ ≤ R ζ) ∧
        (∫⁻ ζ, (R ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * s82Weight d m α * (N : ℝ) ^ (-(1 / 2 : ℝ))) ∧
        ∀ j : ℕ, ∃ A : Ω → ℝ≥0∞, AEMeasurable A P ∧
          (∀ᵐ ζ ∂P, s82PastSup (s82Centered d N a β m ρ P X) T a₀ j α ζ ≤ A ζ) ∧
          (∫⁻ ζ, (A ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
            ENNReal.ofReal
              (C * s82Weight d m α * (N : ℝ) ^ (-(1 / 2 : ℝ)) * q ^ j)

theorem s82_blocks_maj_of_blocks (h : S82ScalarBlocks) : S82ScalarBlocksMaj := by
  intro d hd a β ha hβ m hm T hT
  obtain ⟨C, q, hC, hq0, hq1, hb⟩ := h d hd a β ha hβ m hm T hT
  refine ⟨C, q, hC, hq0, hq1, fun ρ hρ N hN Ω _ P _ X₀ W X hX a₀ ha₀ α => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hb ρ hρ N hN P X₀ W X hX a₀ ha₀ α
  exact ⟨_, h1, Filter.Eventually.of_forall fun _ => le_rfl, h2,
    fun j => ⟨_, (h3 j).1, Filter.Eventually.of_forall fun _ => le_rfl, (h3 j).2⟩⟩

theorem s82_weighted_critical_forcing_of_blocks_maj (h : S82ScalarBlocksMaj) :
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
  have hbound := s82_history_bound_maj P (s82Centered d N a β m ρ P X)
    (s82Weight d m) C q ((N : ℝ) ^ (-(1 / 2 : ℝ))) T a₀
    hC hq0 hq1 hε ha₀ hw hws hF
    (hblocks ρ hρ N hN P X₀ W X hX a₀ ha₀)
  simpa only [s82Centered] using hbound

end HRS.MS.S82BD
