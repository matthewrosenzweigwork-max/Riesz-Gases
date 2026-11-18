import HRS.MS.MainRdStatTie
import HRS.MS.MainRdStatAux22

/-!
# SA2: the relocated proof of Corollary S.A.3 (`HRS.Whole.AppendixA.fourier_statistics_rd`)

A corollary of the smooth-metric estimate of `sa2_smooth_iota` for the real and imaginary parts of the plane waves,
whose `H^{m_*}_uloc` norms are `≤ C ⟨ξ⟩^{m_*}` (S.A.31(ii), `uloc_embedding_modes_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

theorem fourier_statistics_rd_proof (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      max 0 ((d : ℝ) - 2) ≤ s → S.RegimeHolds Rg ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈 →
        (∀ N : ℕ, 1 ≤ N → AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 (S.coeff N) S.T Kad) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ) (n : ℕ) (ξ : Fin (n + 1) → Euc d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
          InitialFluctuationRd S R χ m₀ Cin ε
            (transportedTestsRd S (fun ab : Fin (n + 1) × Bool => t)
              (realImPartsRd fun a => planeWave (ξ a))) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            smoothDist 2
              (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N)
                (fun _ : Fin (n + 1) × Bool => t) (realImPartsRd fun a => planeWave (ξ a)))
              (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N)
                (fun _ : Fin (n + 1) × Bool => t) (realImPartsRd fun a => planeWave (ξ a))
                (R N).P (R N).η) ≤
            HRS.Main.statBound C ΛT t (∑ a, jbracket (ξ a) ^ mStar d)
              (rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) 0) := by
  by_cases hok : 1 ≤ d ∧ 0 ≤ s ∧ s < d ∧ (d : ℝ) - 2 ≤ s
  · obtain ⟨hd, hs0, hsd, hsc⟩ := hok
    obtain ⟨Lm, hLm⟩ := sa2_logmoment d Λ
    obtain ⟨C₀a, Cq, hC₀a, hCq, hcomm⟩ := sa2_comm_data hd hs0 hsd hsc Lm
    obtain ⟨C₀b, C₁, hC₀b, hpair⟩ := HRS.MH.CoercTest.p_assembly d hd s hs0 hsd
    obtain ⟨Ct, hCt0, hCt⟩ := sa2_test_h hd hs0 hsd hsc hχ C₁
    obtain ⟨Cy, hCy0, hCy⟩ := sa2_y0 hχ
    obtain ⟨Cpw, hCpw0, hCpw⟩ := sa2_plane_data hχ
    set C₀c : ℝ := max C₀a C₀b with hC₀cdef
    have hC₀c0 : 0 ≤ C₀c := hC₀a.trans (le_max_left _ _)
    have hcommC : Sa2Comm d s Lm C₀c Cq := sa2_comm_mono hCq.le (le_max_left _ _) hcomm
    have hTestC : Sa2Test d s χ C₀c Ct := fun Λ' hΛ' N hN ρ hρ hρΛ hmom X hX f g hf hg Xf Xg hXf hXg hcf
        hcg hul R hR =>
      hCt C₀c (hpair C₀c (le_max_right _ _)) Λ' hΛ' N hN ρ hρ hρΛ hmom X hX f g hf hg Xf Xg hXf hXg hcf
        hcg hul R hR
    refine ⟨sa2C0min d s Λ C₀c, fun C₀ hC₀ => ?_⟩
    set Kp : ℝ := max Kad 0 with hKp
    set κ : ℝ := Kp * Cpw with hκ
    set K1 : ℝ := 1 / 2 * (Cq * ((d : ℝ) * d * MB)) * T + Cy + Ct * T + 2 * d * T with hK1def
    refine ⟨max 2 (2 + K1 * (κ + κ ^ 2)), 1, lt_of_lt_of_le two_pos (le_max_left _ _), one_pos, ?_⟩
    intro S hSs hST hinv hmax hreg R 𝔈 hS hAdj m₂ hm₂ hmom m₀ ε n ξ t ht hIF N hN
    have hKp0 : 0 ≤ Kp := le_max_right _ _
    have hκ0 : 0 ≤ κ := mul_nonneg hKp0 hCpw0
    have hT0 : 0 ≤ T := by rw [← hST]; exact S.hT.le
    have hMB := sa2_cMB_nonneg (d := d) (MB := MB) (M := S.M) hS.matrix_bound
    have hc0 : 0 ≤ 1 / 2 * (Cq * ((d : ℝ) * d * MB)) := by positivity
    have hK1 : 0 ≤ K1 := by rw [hK1def]; positivity
    have hM0 : 0 ≤ κ + κ ^ 2 := by positivity
    set C : ℝ := max 2 (2 + K1 * (κ + κ ^ 2)) with hCdef
    have hC2 : 2 ≤ C := le_max_left _ _
    have hCK1 : K1 * (κ + κ ^ 2) ≤ C := le_trans (by linarith) (le_max_right _ _)
    have hN2' : 2 ≤ N := by
      have : (2 : ℝ) ≤ N := hC2.trans hN
      exact_mod_cast this
    have hN1 : 1 ≤ N := by omega
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have htS : t ∈ Set.Icc (0 : ℝ) S.T := by rw [hST]; exact ht
    obtain ⟨hmem, hXb⟩ := hCpw ξ
    have key := sa2_smooth_iota hS hd hN2' (fun {t} ht => hLm hS hN1 ht) (by rw [hSs]; exact hcommC) hCq.le
      hC₀c0 hCt0 hCy0 (by rw [hSs]; exact hC₀) hχ (by rw [hSs]; exact hTestC) hCy (hAdj N hN1) hm₂ hmom
      (fun _ : Fin (n + 1) × Bool => t) (fun _ => htS) (realImPartsRd fun a => planeWave (ξ a)) hmem hIF
      (fun ab => Submodule.subset_span ⟨ab, rfl⟩)
    rw [hST] at key
    refine key.trans ?_
    have hr := sa2_rate_nonneg hε (sa2_q_nonneg S N) (sa2_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂)
      (sa2_sigma_nonneg S N) (hS.energy.pos N hN1).le
    have hJ0 : 0 ≤ ∑ a, jbracket (ξ a) ^ mStar d :=
      Finset.sum_nonneg fun a _ => pow_nonneg (Real.sqrt_nonneg _) _
    refine sa2_stat_arith hK1 hM0 hJ0 hr ht.1 ?_ hCK1
    refine sa2_Bs_final (mul_nonneg hKp0 (sa2X_nonneg _ _)) ?_ hκ0 hJ0
    calc Kp * sa2X χ (realImPartsRd fun a => planeWave (ξ a)) ≤ Kp * (Cpw * ∑ a, jbracket (ξ a) ^ mStar d) :=
          mul_le_mul_of_nonneg_left hXb hKp0
      _ = κ * ∑ a, jbracket (ξ a) ^ mStar d := by rw [hκ]; ring
  · refine ⟨0, fun C₀ _ => ⟨1, 1, one_pos, one_pos, fun S hSs _ _ hmax => ?_⟩⟩
    exact (hok ⟨S.hd, by rw [← hSs]; exact S.hs0, by rw [← hSs]; exact S.hsd,
      (le_max_right _ _).trans hmax⟩).elim

example := (@fourier_statistics_rd_proof : type_of% @HRS.Whole.AppendixA.fourier_statistics_rd)

end HRS.MS.MainRdStat
