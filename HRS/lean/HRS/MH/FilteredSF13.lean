import HRS.MH.FilteredSF10
import HRS.Main.GFFinal5
import HRS.Dynamics.SetupFiltered

/-!
# Filtered packet SF13: `general_fluctuation_matrix_transport`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.GF HRS.Uniform

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
/-- **SF13**: `general_fluctuation_matrix_transport`, the minimum of the trace-norm coupling bound (`gff_core`) and the
transport coupling bound (`sf10_gff_core_transport_gen`), at level `γ + 2` and for a general matrix `M`. -/
theorem general_fluctuation_matrix_transport_proof :
    type_of% @HRS.GeneralSetup.general_fluctuation_matrix_transport := by
  intro d b M hM K
  obtain ⟨K', hK0, hev⟩ := gf_ev_mat_proof b M hM K
  have hev' : ∀ S : GeneralSetup d, S.Within { b with C₀ := S.C₀ } → S.MFHypM M →
      (S.AdjointInput M K ∧ S.PosDensityWith b.c) → ∀ N : ℕ,
      ∃ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d ((S.γ : ℝ) + 2)),
        GFEvo S M N ((S.γ : ℝ) + 2) K' EV ∧ ∀ x, EV.j x = NegSobolev.embed ((S.γ : ℝ) + 2) x :=
    fun S hS hMF hH N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hH.1 N
      exact ⟨EV, hEV, fun x => hEV.j_eq x⟩
  obtain ⟨C₀a, hcore⟩ := gff_core b M (fun S => S.AdjointInput M K ∧ S.PosDensityWith b.c)
    (fun S => (S.γ : ℝ) + 2) (fun S => by linarith) (fun S => NegSobolev.embed ((S.γ : ℝ) + 2)) K' hev'
  obtain ⟨C₀b, hcoreT⟩ := sf10_gff_core_transport_gen b M
    (fun S => S.AdjointInput M K ∧ S.PosDensityWith b.c)
    (fun S => (S.γ : ℝ) + 2) (fun S => by linarith) (fun S => NegSobolev.embed ((S.γ : ℝ) + 2)) K' hev'
  refine ⟨max C₀a C₀b, fun C₀ hC₀ => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := hcore C₀ (le_trans (le_max_left _ _) hC₀)
  obtain ⟨C₂, hC₂, h₂⟩ := hcoreT C₀ (le_trans (le_max_right _ _) hC₀)
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro S hS hMF hAdj hPos N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  have hq0 := qN_nonneg S N
  have hσ0 := sigN_nonneg S N
  have hA0 := AN_nonneg S N
  have hE0 := gff_energyMoment_nonneg S M hMF N hN P X₀ W X hX hF hE
  have hε1 := initialError_nonneg S P 1 X₀ η₀
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  obtain ⟨-, hW1a, hW2a⟩ := h₁ S hS hMF ⟨hAdj, hPos⟩ N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY
  obtain ⟨hW1b, hW2b⟩ := h₂ S hS hMF ⟨hAdj, hPos⟩ hPos N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY
  dsimp only
  have hmax1 : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hmax2 : C₂ ≤ max C₁ C₂ := le_max_right _ _
  refine ⟨?_, fun hE2 hI hfin2 => ?_⟩
  · rcases le_total (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d)) with h | h
    · rw [min_eq_left h]
      refine hW1a.trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / 4)
        positivity
      exact mul_le_mul_of_nonneg_right hmax1 hz
    · rw [min_eq_right h]
      refine hW1b.trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) +
            (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / max 2 ((d : ℝ) - S.s))
        positivity
      exact mul_le_mul_of_nonneg_right hmax2 hz
  · have hE20 : 0 ≤ S.energyMoment2 P N X := by
      unfold GeneralSetup.energyMoment2
      exact Real.iSup_nonneg fun t => Real.sqrt_nonneg _
    have hε2 := initialError_nonneg S P 2 X₀ η₀
    rcases le_total (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d)) with h | h
    · rw [min_eq_left h]
      refine (hW2a hE2 hI hfin2).trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 2 X₀ η₀ + sigN S N * S.energyMoment2 P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / 4)
        positivity
      exact mul_le_mul_of_nonneg_right hmax1 hz
    · rw [min_eq_right h]
      refine (hW2b hE2 hI hfin2).trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 2 X₀ η₀ + sigN S N * S.energyMoment2 P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) +
            (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / max 2 ((d : ℝ) - S.s))
        positivity
      exact mul_le_mul_of_nonneg_right hmax2 hz

end HRS.MH.FilteredP
