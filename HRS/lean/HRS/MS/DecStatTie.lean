import HRS.MS.DecStatAux9

/-!
# SA4 tie: S.A.4 `main_rd_dec_stat`

`main_rd_dec_stat_proof : type_of% @HRS.Whole.AppendixA.main_rd_dec_stat`.

Route: the S.A.2 engine for the test class `wClass m_𝔠 p_𝔠` (`DecStatAux1..9`).  The `C_b^{m_*}` bound of the adjoint input replaces the
uniformly local bounds of S.A.2 (`Sa4Test`, `Sa4Y0`); the commutator along the orbit is the sub-Coulomb S.B.5 (ii),(iii) with the weak jet
(`sa4_rem_pt`); the extra error `c₂ e_N^𝔠` enters additively (`Sa4Rem`).  Constants: `C₀min = sa2C0min d s Λ (max C₀a C₀t)`,
`c₀ = ½ Cs d² max(MB,0)(1+Ctr)`, `C = max 2 (2 + (K₁ + K₂)(κ + κ²))`, `Λ_T = 1`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.MainRdStat HRS.MS.ZeroTemp
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.DecStat

variable {d : ℕ}

theorem sa4_commSub_mono {s Lm C₁ C₂ Cs : ℝ} {c : DecayingDensity d s} (hCs : 0 ≤ Cs) (h : C₁ ≤ C₂)
    (hc : Sa4CommSub d s Lm C₁ Cs c) : Sa4CommSub d s Lm C₂ Cs c := by
  intro Λ' hΛ' N hN ρ hρ hρΛ hlog X hX v K hK
  have h2 := hc Λ' hΛ' N hN ρ hρ hρΛ hlog X hX v K hK
  refine h2.trans ?_
  have hK0 : 0 ≤ K := by
    obtain ⟨L, F, hF, -, -, hLK⟩ := hK
    exact (add_nonneg (NNReal.coe_nonneg L) hF).trans hLK
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCs hK0)
  have hΛp : 0 ≤ Λ' ^ (s / d) := Real.rpow_nonneg (by linarith) _
  have hNp : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have : C₁ * Λ' ^ (s / d) * (N : ℝ) ^ (s / d - 1) ≤ C₂ * Λ' ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
    gcongr
  unfold oNΛ
  linarith

theorem sa4_two_le_mStar_sob {s : ℝ} (c : DecayingDensity d s) : mStar d ≤ c.sobolevIndex := by
  unfold DecayingDensity.sobolevIndex; omega

theorem main_rd_dec_stat_proof (s : ℝ) (c : DecayingDensity d s) (Rg : PDE.Regime)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      s < (d : ℝ) - 2 → S.RegimeHolds Rg ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (c.sobolevIndex + 3) (c.sobolevIndex + 4) C₀ 𝔈 →
        (∀ N : ℕ, 1 ≤ N → AdjointInputRd (wClass c.sobolevIndex c.integrability)
          (wWeakClass c.sobolevIndex c.integrability) (mStar d) (S.coeff N) S.T Kad) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
          RdStatParts S R C ΛT (wClass c.sobolevIndex c.integrability) χ Cin C₀ Λ 𝔈 m₂
            c.errorRate := by
  by_cases hok : 1 ≤ d ∧ 0 ≤ s ∧ s < (d : ℝ) - 2
  swap
  · refine ⟨0, fun C₀ _ => ⟨1, 1, one_pos, one_pos, fun S hSs _ _ hsd' => ?_⟩⟩
    exfalso
    exact hok ⟨S.hd, by rw [← hSs]; exact S.hs0, hsd'⟩
  obtain ⟨hd, hs0, hsd⟩ := hok
  haveI : Fact (2 ≤ c.integrability) := ⟨sa4_two_le_p hs0 hsd c⟩
  have hsdd : s < (d : ℝ) := by linarith
  obtain ⟨Lm, hLm⟩ := sa2_logmoment d Λ
  obtain ⟨C₀a, Cs, hC₀a, hCs, hcomm⟩ := sa4_commSub_exists hs0 hsd c Lm
  obtain ⟨Ctr, hCtr0, hTr⟩ := sa4_transport_exists hd hs0 hsd c
  obtain ⟨C₀t, Ct, hC₀t, hCt0, hTest⟩ := sa4_test_exists hd hs0 hsdd hχ
  obtain ⟨Cy, hCy0, hY⟩ := sa4_y0 hχ
  set C₀c : ℝ := max C₀a C₀t with hC₀cdef
  have hC₀c0 : 0 ≤ C₀c := hC₀a.trans (le_max_left _ _)
  have hcommC : Sa4CommSub d s Lm C₀c Cs c := sa4_commSub_mono hCs.le (le_max_left _ _) hcomm
  have hTestC : Sa4Test d s χ C₀c Ct := hTest C₀c (le_max_right _ _)
  set c0 : ℝ := 1 / 2 * Cs * ((d : ℝ) ^ 2 * max MB 0 * (1 + Ctr)) with hc0def
  have hc0 : 0 ≤ c0 := by rw [hc0def]; positivity
  have hm := sa4_two_le_mStar_sob c
  refine ⟨sa2C0min d s Λ C₀c, fun C₀ hC₀ => ?_⟩
  refine ⟨max 2 (2 + ((c0 * T * (1 + Cs) + Cy + Ct * T + 2 * d * T) +
        (Cy + Real.sqrt (2 * Ct * T) + c0 * T * (1 + Cs))) *
          (2 * max Kad 0 + (2 * max Kad 0) ^ 2)), 1,
      lt_of_lt_of_le two_pos (le_max_left _ _), one_pos, ?_⟩
  intro S hSs hST hinv hsd' hreg R 𝔈 hS hAdj m₂ hm₂ hmom
  subst hSs
  have hS' : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈 :=
    sa4_standing_mono hS (by omega) (by omega)
  refine sa4_parts (m := c.sobolevIndex) (p := c.integrability) hm hd hS' (c0 := c0) (Cs := Cs) (Kad := Kad)
    (fun N => sa4_errorRate_nonneg hs0 c N) hc0 hCs.le hC₀c0 hCt0 hCy0 hC₀ hTestC hY ?_ hAdj hm₂ hmom hST
  intro N hN2 q ts' φ' hts' hφ'
  have hN1 : 1 ≤ N := by omega
  intro a rr hrr X hX
  have hφ2 : ContDiff ℝ 2 (φ' a) := (hφ' a).1.of_le (by exact_mod_cast (by unfold mStar at hm; omega : 2 ≤ c.sobolevIndex))
  have key := sa4_rem_pt c hS (by omega) hd hN2 hCs.le hCtr0 hTr
    (fun {t} ht => hLm hS hN1 ht) hcommC (hAdj N hN1) hφ2 (hφ' a) hrr (hts' a).2 X hX
  refine key.trans (le_of_eq ?_)
  congr 2
  unfold sa4Kb
  rw [hc0def]
  ring

end HRS.MS.DecStat

example := (@HRS.MS.DecStat.main_rd_dec_stat_proof : type_of% @HRS.Whole.AppendixA.main_rd_dec_stat)
