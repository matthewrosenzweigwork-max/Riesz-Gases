import HRS.MS.MainRdStatAux21

/-!
# SA2: the relocated proof of Theorem S.A.2 (`HRS.Whole.AppendixA.main_rd_stat`)

Route (see `HRS/MS/MainRdStatAux1.lean` for the plan): the torus proof of Proposition A.8 transplanted to `ℝ^d`,
with the adjoint propagator controlled by the M3 hypothesis `AdjointInputRd` (S.A.12 is not used).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

theorem main_rd_stat_proof (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      max 0 ((d : ℝ) - 2) ≤ s → S.RegimeHolds Rg ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈 →
        (∀ N : ℕ, 1 ≤ N → AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 (S.coeff N) S.T Kad) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
          RdStatParts S R C ΛT (ulocClass (mStar d) χ) χ Cin C₀ Λ 𝔈 m₂ (fun _ => 0) := by
  by_cases hok : 1 ≤ d ∧ 0 ≤ s ∧ s < d ∧ (d : ℝ) - 2 ≤ s
  · obtain ⟨hd, hs0, hsd, hsc⟩ := hok
    obtain ⟨Lm, hLm⟩ := sa2_logmoment d Λ
    obtain ⟨C₀a, Cq, hC₀a, hCq, hcomm⟩ := sa2_comm_data hd hs0 hsd hsc Lm
    obtain ⟨C₀b, C₁, hC₀b, hpair⟩ := HRS.MH.CoercTest.p_assembly d hd s hs0 hsd
    obtain ⟨Ct, hCt0, hCt⟩ := sa2_test_h hd hs0 hsd hsc hχ C₁
    obtain ⟨Cy, hCy0, hCy⟩ := sa2_y0 hχ
    set C₀c : ℝ := max C₀a C₀b with hC₀cdef
    have hC₀c0 : 0 ≤ C₀c := hC₀a.trans (le_max_left _ _)
    have hcommC : Sa2Comm d s Lm C₀c Cq := sa2_comm_mono hCq.le (le_max_left _ _) hcomm
    have hTestC : Sa2Test d s χ C₀c Ct := fun Λ' hΛ' N hN ρ hρ hρΛ hmom X hX f g hf hg Xf Xg hXf hXg hcf
        hcg hul R hR =>
      hCt C₀c (hpair C₀c (le_max_right _ _)) Λ' hΛ' N hN ρ hρ hρΛ hmom X hX f g hf hg Xf Xg hXf hXg hcf
        hcg hul R hR
    refine ⟨sa2C0min d s Λ C₀c, fun C₀ hC₀ => ?_⟩
    refine ⟨max 2 (2 + ((1 / 2 * (Cq * ((d : ℝ) * d * MB)) * T + Cy + Ct * T + 2 * d * T) +
        (Cy + Real.sqrt (2 * Ct * T) + 1 / 2 * (Cq * ((d : ℝ) * d * MB)) * T)) *
          (2 * max Kad 0 + (2 * max Kad 0) ^ 2)), 1,
      lt_of_lt_of_le two_pos (le_max_left _ _), one_pos, ?_⟩
    intro S hSs hST hinv hmax hreg R 𝔈 hS hAdj m₂ hm₂ hmom
    exact sa2_parts hd hS hχ (fun {N} hN {t} ht => hLm hS hN ht) (by rw [hSs]; exact hcommC) hCq.le hC₀c0
      hCt0 hCy0 (by rw [hSs]; exact hC₀) (by rw [hSs]; exact hTestC) hCy hAdj hm₂ hmom hST
  · refine ⟨0, fun C₀ _ => ⟨1, 1, one_pos, one_pos, fun S hSs _ _ hmax => ?_⟩⟩
    exact (hok ⟨S.hd, by rw [← hSs]; exact S.hs0, by rw [← hSs]; exact S.hsd,
      (le_max_right _ _).trans hmax⟩).elim

example := (@main_rd_stat_proof : type_of% @HRS.Whole.AppendixA.main_rd_stat)

end HRS.MS.MainRdStat
