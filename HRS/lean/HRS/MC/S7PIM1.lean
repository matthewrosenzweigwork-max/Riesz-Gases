import HRS.MC.S7PIM1d

/-!
# Packet piM, M1: `s7_PIM_B_integrable_proof` (namespace `HRS.MC.Sec7.S7PIM`)

The statement is copied verbatim from `HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PIM_B_integrable`); the tie is in
`HRS/MC/S7PIMTie.lean`.  Proof: the first moment `E ‖ℬ_N^u‖_{E_m} ≤ C` uniformly in `u ≥ 0` (`S7PIM_B_moment`: FC-F6a for
`N ≥ 2`, boundedness for `N = 1`), the joint strong measurability (`S7PIM_B_jointly`) and Tonelli.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIM

open HRS HRS.Sec7 HRS.MC.Sec7

variable {d : ℕ}

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

theorem s7_PIM_B_integrable_proof :
    (∀ᵐ ω ∂P, MemLp (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω) 1
      (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
    AEStronglyMeasurable (fun p : ℝ × Ω => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) ∧
    Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) T, ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω‖) P := by
  have hS := hreal.solution T
  have hb := S7PIM_B_jointly R m hT P X hS.adapted hS.cont
  obtain ⟨C, hC⟩ := S7PIM_B_moment R m hm hN P X₀ W X hreal
  -- the integrand, jointly
  set B : ℝ × Ω → NegSobolev d m :=
    fun p => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X p.1 p.2 with hBdef
  have hbs : AEStronglyMeasurable (fun p : Ω × ℝ => B p.swap)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hb.prod_swap
  have hen : AEMeasurable (fun p : ℝ × Ω => ‖B p‖ₑ) ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) :=
    hb.enorm
  have hen' : AEMeasurable (fun p : Ω × ℝ => ‖B p.swap‖ₑ)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hbs.enorm
  -- Tonelli bound
  have hTon : ∫⁻ ω, (∫⁻ u in Set.Icc (0 : ℝ) T, ‖B (u, ω)‖ₑ) ∂P ≤
      ENNReal.ofReal C * ENNReal.ofReal T := by
    calc ∫⁻ ω, (∫⁻ u in Set.Icc (0 : ℝ) T, ‖B (u, ω)‖ₑ) ∂P
        = ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖B (u, ω)‖ₑ ∂P :=
          lintegral_lintegral_swap (f := fun ω u => ‖B (u, ω)‖ₑ) hen'
      _ ≤ ∫⁻ _u in Set.Icc (0 : ℝ) T, ENNReal.ofReal C := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
          exact hC u hu.1
      _ = ENNReal.ofReal C * ENNReal.ofReal T := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hTon' : ∫⁻ ω, (∫⁻ u in Set.Icc (0 : ℝ) T, ‖B (u, ω)‖ₑ) ∂P ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hTon
  refine ⟨?_, hb, ?_⟩
  · -- (a)
    have h1 : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun u => B (u, ω)) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      hbs.prodMk_left
    have hmeas : AEMeasurable (fun ω => ∫⁻ u in Set.Icc (0 : ℝ) T, ‖B (u, ω)‖ₑ) P :=
      hen'.lintegral_prod_right'
    have h2 : ∀ᵐ ω ∂P, ∫⁻ u in Set.Icc (0 : ℝ) T, ‖B (u, ω)‖ₑ < ∞ := ae_lt_top' hmeas hTon'
    filter_upwards [h1, h2] with ω hω1 hω2
    refine memLp_iff.2 ?_
    rw [eLpNorm_one_eq_lintegral_enorm hω1]
    exact hω2
  · -- (c)
    have hg : AEStronglyMeasurable (fun p : Ω × ℝ => ‖B p.swap‖)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hbs.norm
    refine ⟨hg.integral_prod_right', ?_⟩
    calc ∫⁻ ω, ‖(∫ u in Set.Icc (0 : ℝ) T, ‖B (u, ω)‖)‖ₑ ∂P
        ≤ ∫⁻ ω, (∫⁻ u in Set.Icc (0 : ℝ) T, ‖B (u, ω)‖ₑ) ∂P := by
          refine lintegral_mono fun ω => ?_
          refine (enorm_integral_le_lintegral_enorm _).trans ?_
          simp only [enorm_norm]
          exact le_rfl
      _ < ∞ := lt_top_iff_ne_top.2 hTon'

end Prob

end HRS.MC.Sec7.S7PIM

end
