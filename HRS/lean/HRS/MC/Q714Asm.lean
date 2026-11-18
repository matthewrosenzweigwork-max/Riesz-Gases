import HRS.MC.Q714AsmWin
import HRS.MC.Q714HI
import HRS.MC.Q714CT

/-!
# Packet ASM (row 7.14): the assemblies

`assembly_critical_edgeworth_proof` and `assembly_equal_temperature_proof` (statements copied from `Q714Spec.lean`, with the
packets replaced by their proved forms).  Ties: `HRS/MC/Q714AsmTie.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.Asm

open HRS HRS.Sec7

theorem assembly_critical_edgeworth_proof
    (hGT : type_of% @HRS.MC.Q714.GT.gaussian_taylor_proof)
    (hGW : type_of% @HRS.MC.Q714.GW.gaussian_window_proof)
    (hHI : type_of% @HRS.MC.Q714.HI.haar_invariance_proof)
    (hCT : type_of% @HRS.MC.Q714.CT.cos_test_proof) :
    type_of% @HRS.Sec7.critical_edgeworth := by
  intro d hd s β β₀ hs0 hs hβ hβ₀ hne m hm T hT D hD Ω _ P _ X₀ W X hreal Ω' _ P' _ Z hZ Ω'' _ P'' _
    Zs hZs Kinf hKmem hK
  have hm' : (d : ℝ) / 2 + 1 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨hlam, C, hP2, hP3⟩ := asm_windows hGT hGW hd hβ hβ₀ hne D hD m hm' T hT P' Z hZ P'' Zs hZs
  refine ⟨?_, ?_, ?_⟩
  · -- Haar mean
    intro N hN t ht
    have hH := hHI hd hs0 hs hβ hβ₀ D hD (P N) hN (X₀ N) (W N) (X N) (hreal N hN) t ht
    refine ⟨hH, fun ω => ?_⟩
    unfold zetaAt zetaE etaE flucE
    rw [hH]
  · -- the critical expansion
    intro a τ hτ ε hε
    obtain ⟨hatop, -⟩ := asm_tendsto_shift hlam a hτ
    obtain ⟨N₁, hN₁⟩ := asm_seq_expansion hlam (CbUnitBall (PathSpace d m T) 5)
      (fun a Φ => ∫ ω, Φ (procWin m T a Z ω) ∂P' - ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'')
      (fun Φ => ∫ ω, slowTensor d s β β₀ m T (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂P'')
      C hP2 hP3 a hτ (ε / 2) (by positivity)
    obtain ⟨N₂, hN₂⟩ := hK a hatop (ε / 2) (by positivity)
    refine ⟨max N₁ N₂, fun N hN hN1 Φ hΦ => ?_⟩
    have h1 := hN₁ N (le_trans (le_max_left _ _) hN) hN1 Φ hΦ
    have h2 := hN₂ N (le_trans (le_max_right _ _) hN) hN1 Φ hΦ
    have e : Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
          ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') -
        (Real.exp (-2 * lamStar d s β * τ) / 2 *
            ∫ ω, slowTensor d s β β₀ m T (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂P'' +
          (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P'') =
        (Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
            ∫ ω, Φ (procWin m T (a N) Z ω) ∂P') -
          (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P'') +
        (Real.sqrt N * (∫ ω, Φ (procWin m T (a N) Z ω) ∂P' - ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') -
          Real.exp (-2 * lamStar d s β * τ) / 2 *
            ∫ ω, slowTensor d s β β₀ m T (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂P'') := by
      ring
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h2 h1
      _ = ε := by ring
  · -- waiting time
    intro a hatop
    refine ⟨⟨fun hstat => ?_, fun hr => ?_⟩, asm_waiting_iff hlam a⟩
    · -- necessity
      obtain ⟨Φ₀, hΦ₀, c, hc, a₀, hlow⟩ := hCT hd hβ hβ₀ hne D hD m hm' T hT P' Z hZ P'' Zs hZs
      refine asm_seq_necessary
        (fun a => ∫ ω, Φ₀ (procWin m T a Z ω) ∂P' - ∫ ω, Φ₀ (procWin m T 0 Zs ω) ∂P'') c a₀ hc
        (fun a ha => hlow a ha) a hatop ?_
      intro ε hε
      obtain ⟨N₁, hN₁⟩ := hstat (ε / 2) (by positivity)
      obtain ⟨N₂, hN₂⟩ := hK a hatop (ε / 2) (by positivity)
      refine ⟨max N₁ N₂, fun N hN hN1 => ?_⟩
      have h1 := hN₁ N (le_trans (le_max_left _ _) hN) hN1 Φ₀ hΦ₀
      have h2 := hN₂ N (le_trans (le_max_right _ _) hN) hN1 Φ₀ hΦ₀
      have e : Real.sqrt N * (∫ ω, Φ₀ (procWin m T (a N) Z ω) ∂P' -
            ∫ ω, Φ₀ (procWin m T 0 Zs ω) ∂P'') =
          (Real.sqrt N * (∫ ω, Φ₀ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
              ∫ ω, Φ₀ (procWin m T 0 Zs ω) ∂P'') -
            (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ₀ (procWin m T 0 Zs ω)) ∂P'') -
          (Real.sqrt N * (∫ ω, Φ₀ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
              ∫ ω, Φ₀ (procWin m T (a N) Z ω) ∂P') -
            (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ₀ (procWin m T 0 Zs ω)) ∂P'') := by
        ring
      rw [e]
      calc _ ≤ _ := abs_sub _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
        _ = ε := by ring
    · -- sufficiency
      intro ε hε
      obtain ⟨N₁, hN₁⟩ := asm_seq_small (CbUnitBall (PathSpace d m T) 5)
        (fun a Φ => ∫ ω, Φ (procWin m T a Z ω) ∂P' - ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') C hP2 a
        hatop hr (ε / 2) (by positivity)
      obtain ⟨N₂, hN₂⟩ := hK a hatop (ε / 2) (by positivity)
      refine ⟨max N₁ N₂, fun N hN hN1 Φ hΦ => ?_⟩
      have h1 := hN₁ N (le_trans (le_max_left _ _) hN) hN1 Φ hΦ
      have h2 := hN₂ N (le_trans (le_max_right _ _) hN) hN1 Φ hΦ
      have e : Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
            ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') -
          (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P'' =
          (Real.sqrt N * (∫ ω, Φ (zetaWin m T (a N) (P N) (X N) ω) ∂(P N) -
              ∫ ω, Φ (procWin m T (a N) Z ω) ∂P') -
            (1 / 6) * ∫ ω, Kinf (iteratedFDeriv ℝ 3 Φ (procWin m T 0 Zs ω)) ∂P'') +
          Real.sqrt N * (∫ ω, Φ (procWin m T (a N) Z ω) ∂P' -
            ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'') := by
        ring
      rw [e]
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add h2 h1
        _ = ε := by ring

theorem assembly_equal_temperature_proof
    (hGT : type_of% @HRS.MC.Q714.GT.gaussian_taylor_proof)
    (hGW : type_of% @HRS.MC.Q714.GW.gaussian_window_proof) :
    type_of% @HRS.Sec7.critical_edgeworth_equal_temperature := by
  intro d hd s β hs0 hs hβ m hm T hT D hD Ω _ P _ X₀ W X hreal Ω' _ P' _ Z hZ Ω'' _ P'' _
    Zs hZs Kinf hKmem hK a ha ε hε
  have hm' : (d : ℝ) / 2 + 1 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨N₁, hN₁⟩ := hK a ha ε hε
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (ha.eventually_ge_atTop 0)
  refine ⟨max N₁ N₂, fun N hN hN1 Φ hΦ => ?_⟩
  have h0 : 0 ≤ a N := hN₂ N (le_trans (le_max_right _ _) hN)
  have hΔ0 := quench_equal_temperature_proof hd hβ D hD m hm' T hT P' Z hZ P'' Zs hZs (a N) h0
  obtain ⟨L, -, h1, -⟩ := asm_gt_step hGT hGW hd hβ hβ D hD m hm' T hT P' Z hZ P'' Zs hZs (a N) h0
    (fun M => ∫ ω, M ![procWin m T (a N) Z ω, procWin m T (a N) Z ω] ∂P' -
      ∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂P'') (fun M => rfl) 0
    (fun M _ => by simp only [hΔ0 M, sub_self, abs_zero, le_refl]) Φ hΦ
  have h2 : ∫ ω, Φ (procWin m T (a N) Z ω) ∂P' = ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'' := by
    have : |∫ ω, Φ (procWin m T (a N) Z ω) ∂P' - ∫ ω, Φ (procWin m T 0 Zs ω) ∂P''| ≤ 0 := by
      simpa using h1
    have := abs_nonpos_iff.1 this
    linarith
  have := hN₁ N (le_trans (le_max_left _ _) hN) hN1 Φ hΦ
  rwa [h2] at this

end HRS.MC.Q714.Asm

end
