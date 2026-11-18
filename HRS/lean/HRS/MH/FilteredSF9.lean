import HRS.Main.GFFinal4

/-!
# Filtered packet SF9: transport moment for a general constant matrix `M`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.GF HRS.Uniform

variable {d : ℕ}

theorem sf9_transport_moment_M (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → S.PosDensityWith b.c →
      ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        S.EnergyMomentFinite P N X →
        AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
            (withDensityReal (S.ρ N r))).toReal ^ 2)) P ∧
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
            (withDensityReal (S.ρ N r))).toReal ^ 2)) ∂P ≤
          ENNReal.ofReal (C * (S.energyMoment P N X ^ ((2 : ℝ) / max 2 ((d : ℝ) - S.s)) +
            (N : ℝ) ^ (-(2 : ℝ) / d))) := by
  classical
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.s = b.s ∧ S₀.PosDensityWith b.c
  · obtain ⟨S₀, hs₀, hPD₀⟩ := hex
    have hd1 : 1 ≤ d := by have := S₀.hd; omega
    have hs0 : 0 ≤ b.s := hs₀ ▸ S₀.hs0
    have hsd : b.s < d := hs₀ ▸ S₀.hsd
    have hm0 : 0 < b.c := hPD₀.1
    obtain ⟨C₀min, h⟩ := Uniform.Q12.energy_W2_proof hd1 b.s hs0 hsd b.Λ b.c hm0
    refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
    obtain ⟨C, hCpos, hpt⟩ := h C₀ hC₀
    refine ⟨2 * C ^ 2 * (|b.T| + 1), by positivity, ?_⟩
    intro S hS hMF hPD N hN Ω _ P _ X₀ W X hX hF hE
    unfold GeneralSetup.Within at hS
    obtain ⟨hs, hT, hγ', hΛ, hβ, hC0, hV⟩ := hS
    have hC0' : S.C₀ = C₀ := hC0
    set a : ℝ := (1 : ℝ) / max 2 ((d : ℝ) - b.s) with ha
    have hmax : (2 : ℝ) ≤ max 2 ((d : ℝ) - b.s) := le_max_left _ _
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have ha1 : 2 * a ≤ 1 := by
      rw [ha, mul_one_div, div_le_one (by linarith)]; exact hmax
    have hn : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    obtain ⟨hMFN, hReg⟩ := hMF N
    have hpt' : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Config d N, x ∉ collisionSet d N →
        torusWassersteinE 2 (empirical x) (withDensityReal (S.ρ N r)) ≤
          ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / d) + S.energyCompletion N x r ^ a)) := by
      intro r hr x hx
      have hup : ∀ y, S.ρ N r y ≤ b.Λ := fun y =>
        (le_abs_self _).trans ((gfb2_sup_le_cbNorm (hReg r hr).1 y).trans ((hReg r hr).2.trans hΛ.le))
      have hlow : ∀ y, b.c ≤ S.ρ N r y := fun y => hPD.2 N r hr y
      have h1 := (hpt N hN (S.ρ N r) (hMFN.density r hr) hup hlow x hx).2
      unfold GeneralSetup.energyCompletion
      rw [hs, hC0']
      exact h1
    have hcore := gfb2_transport_core S M hMF N hN P X₀ W X hX hF hE C a _ hCpos.le ha0 ha1 hn hpt'
    refine ⟨hcore.1, hcore.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hnn := (gf_energy_integral_moment_proof S M hMF N hN P X₀ W X hX hF hE).1
    have hEm : 0 ≤ S.energyMoment P N X := by
      unfold GeneralSetup.energyMoment
      refine Real.iSup_nonneg fun t => integral_nonneg_of_ae ?_
      filter_upwards [hnn] with ω hω using hω t.1 t.2
    have hexp : (2 : ℝ) / max 2 ((d : ℝ) - S.s) = 2 * a := by
      rw [hs, ha]; ring
    have hnsq : ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2 = (N : ℝ) ^ (-(2 : ℝ) / d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1; push_cast; ring
    rw [hexp, ← hnsq]
    have hB : 0 ≤ 2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2) :=
      mul_nonneg (by positivity) (add_nonneg (Real.rpow_nonneg hEm _) (sq_nonneg _))
    have hTle : S.T ≤ |b.T| + 1 := by rw [hT]; linarith [le_abs_self b.T]
    calc S.T * (2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2))
        ≤ (|b.T| + 1) * (2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2)) :=
          mul_le_mul_of_nonneg_right hTle hB
      _ = 2 * C ^ 2 * (|b.T| + 1) * (S.energyMoment P N X ^ (2 * a) + ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2) := by ring
  · refine ⟨0, fun C₀ _ => ⟨1, one_pos, ?_⟩⟩
    intro S hS _ hPD
    exact absurd ⟨S, hS.1, hPD⟩ hex

end HRS.MH.FilteredP
