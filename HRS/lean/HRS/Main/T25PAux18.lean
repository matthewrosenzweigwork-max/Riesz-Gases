import HRS.Main.T25PAux17

/-!
# T25P, part 18: measurability of `Ψ_a` and the evolution package at level `m`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_Psi_aemeas (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (m cr a T : ℝ)
    (hT' : 0 < a + T) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (X : ℝ≥0 → Ω → Config d N)
    (hX : IsProgressive ℱ (ofNNRealTime X)) :
    AEMeasurable (t25p_Psi d s ρ m cr a T X) P := by
  have hwm : Measurable (t25p_w cr a) := (t25p_w_cont cr a).measurable
  have hmeasj : ∀ j : NonzeroLattice d, AEMeasurable (fun ω => ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      ∫⁻ r in Set.Ioc (0 : ℝ) (a + T), ENNReal.ofReal (t25p_w cr a r) * ‖t25p_y d s ρ X j r ω‖ₑ) P := by
    intro j
    have hf : AEMeasurable (fun p : ℝ × Ω => ENNReal.ofReal (t25p_w cr a p.1) * ‖t25p_y d s ρ X j p.1 p.2‖ₑ)
        ((volume.restrict (Set.Ioc (0 : ℝ) (a + T))).prod P) :=
      (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst)).aemeasurable.mul
        (t25p_y_aemeas hd htr hT' P hX j).1.enorm
    exact (hf.lintegral_prod_left').const_mul _
  unfold t25p_Psi
  exact AEMeasurable.ennreal_tsum hmeasj

/-- The evolution package at level `m`: constants `C_r, c_r`, one dual evolution, and for each window length `T` the
constant of the measurable maximal estimate. -/
theorem t25p_ev_pkg (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (m : ℝ) :
    ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧ ∃ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution htr.dyn ρ m Vev ∧
      ∀ T : ℝ, 0 < T → ∃ Cmax : ℝ, 0 ≤ Cmax ∧ T25Ev m Cr cr T Cmax Vev := by
  obtain ⟨Cr, cr, hCr, hcr, VA, hdualA, -, hdecA, -⟩ := adjk_evolution_along_trajectory hd htr m
  obtain ⟨VB, hdualB, hplainB, hB1⟩ := adjk_evolution_moment_proof hd htr m 2 le_rfl
  refine ⟨Cr, cr, hCr, hcr, VB, hdualB, fun T hT => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hB1 T hT
  have hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖VB t u‖ ≤ Cr * Real.exp (-cr * (t - u)) := by
    intro u t hu hut
    rw [t25p_dual_unique hdualB hdualA hu hut]
    exact hdecA u t hu hut
  refine ⟨C, hC0, ?_⟩
  refine ⟨hplainB, hdec, ?_, ?_⟩
  · exact t25p_maxWindowsM_of_B1 hT VB hC0 (fun Ω _ P _ ℱ a h ha hh hhT M Sg hM => hC Ω P ℱ a h ha hh hhT M Sg hM)
  · intro T' hT' Ω _ P _ ℱ M Sg hM
    obtain ⟨C', hC'0, hC'⟩ := hB1 T' hT'
    have hM' : IsHilbertMartingaleWithCovariation P ℱ (0 + T') M Sg := by rwa [zero_add]
    obtain ⟨Z, hZS, hZc, hZm, -⟩ := hC' Ω P ℱ 0 T' le_rfl hT' le_rfl M Sg hM'
    simp only [zero_add] at hZS hZc hZm
    exact ⟨Z, hZS, hZc, hZm⟩

end HRS.T25P
