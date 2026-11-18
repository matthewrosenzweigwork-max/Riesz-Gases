import HRS.MH.DualityRdB1
import HRS.MS.Fp81S21RawIto

/-! The compact-test empirical Itô stage for SOL169 U2. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd
open HRS.MS.R26T3 HRS.MS.R2Interp

/-- Empirical Itô for a time-constant compact smooth test along the filtered
particle realization. This is the pre-subtraction stage: its drift is the
empirical generator plus interaction pairing, and its martingale retains the
truncated raw gradient integrand from `empirical_ito_rd_proof`. -/
theorem fp81s21_particle_empirical_compact_ito
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (Fp : FilteredParticle A)
    {T : ℝ} (hT : 0 < T) {f : Euc p.d → ℝ} (hf : IsR2Test f) :
    ∀ᵐ ζ ∂A.P, ∀ u ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn
        (fun v =>
          Whole.pair (Whole.empirical (Fp.X v.toNNReal ζ))
            (driftTestRd (quadraticGradientDyn p.d p.s p.a p.β)
              (fun _ => f) (fun _ _ => 0) v) +
          interactionPairingW (quadraticGradientDyn p.d p.s p.a p.β) f
            (Whole.empirical (Fp.X v.toNNReal ζ))
            (Whole.empirical (Fp.X v.toNNReal ζ)))
        (Set.Icc (0 : ℝ) u) ∧
      Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ)) f =
        Whole.pair (Whole.empirical (Fp.X 0 ζ)) f +
          (∫ v in Set.Icc (0 : ℝ) u,
            Whole.pair (Whole.empirical (Fp.X v.toNNReal ζ))
              (driftTestRd (quadraticGradientDyn p.d p.s p.a p.β)
                (fun _ => f) (fun _ _ => 0) v) +
            interactionPairingW (quadraticGradientDyn p.d p.s p.a p.β) f
              (Whole.empirical (Fp.X v.toNNReal ζ))
              (Whole.empirical (Fp.X v.toNNReal ζ))) +
          (Real.sqrt (2 * (quadraticGradientDyn p.d p.s p.a p.β).invβ) / (N : ℝ)) *
            itoIntegral A.P Fp.ℱ Fp.Wc
              (HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X) u ζ := by
  classical
  let D : WholeDyn p.d := quadraticGradientDyn p.d p.s p.a p.β
  let ftime : ℝ → Euc p.d → ℝ := fun _ => f
  let ft : ℝ → Euc p.d → ℝ := fun _ _ => 0
  have hfMemCb : MemCb 2 f := HRS.MH.DualityRd.db1_memCb_of_compact
    (hf.1.of_le (by norm_num)) hf.2
  have hfC12 : IsC12TestRd T ftime ft := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact hf.1.of_le (by norm_num)
    · intro j hj
      obtain ⟨B, hB⟩ := hfMemCb.2 j hj
      exact ⟨B, fun r hr x => by
        simpa [ftime] using hB (Set.mem_range_self x)⟩
    · intro j hj
      have hc : Continuous (iteratedFDeriv ℝ j f) :=
        hf.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
      simpa [ftime, Function.comp_def] using hc.comp continuous_snd
    · intro x r hr
      simpa [ftime, ft] using (hasDerivAt_const r (f x))
    · exact continuous_const
    · exact ⟨0, fun r hr x => by simp [ft]⟩
  have hX : IsWholeStrongSolution A.P D T A.X₀ A.W Fp.X := by
    simpa [D] using Fp.strong T
  have hXc : IsWholeContactStrongSolution A.P D T A.X₀ A.W Fp.X :=
    ⟨hX.init, hX.eqn, hX.cont, hX.adapted⟩
  have hQ : (p.a • (1 : Matrix (Fin p.d) (Fin p.d) ℝ)).IsSymm := by
    simp [Matrix.IsSymm]
  obtain ⟨ΛV, G₀, hV⟩ := HRS.MS.Go.s55f_vhyp_quadV hQ 0 2
  have hVD : VHypRd 2 ΛV G₀ D.V := by
    show VHypRd 2 ΛV G₀ (confinement p.a)
    rw [HRS.MS.S21.s21_confinement_eq]
    exact hV
  have hinv : 0 ≤ D.invβ := (inv_pos.2 p.hβ).le
  have hocc : D.M = 0 ∨ ∀ᵐ ζ ∂A.P,
      volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧
        Fp.X (Real.toNNReal s) ζ ∈ eucCollisionSet p.d N} = 0 := by
    right
    filter_upwards [hX.no_collision] with ζ hζ
    have hempty : {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧
        Fp.X (Real.toNNReal s) ζ ∈ eucCollisionSet p.d N} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      intro s hs
      have htime : (Real.toNNReal s : ℝ) ≤ T := by
        rw [Real.coe_toNNReal _ hs.1.1]
        exact hs.1.2
      exact hζ (Real.toNNReal s) htime hs.2
    rw [hempty, measure_empty]
  have hito := HRS.MH.DualityRd.empirical_ito_rd_proof D hinv
    (HRS.MH.DualityRd.measurable_gradient_of_vhyp hVD)
    hXc Fp.filtered hocc hT le_rfl hfC12
  filter_upwards [hito] with ζ hζ
  intro u hu
  simpa [ftime, ft] using hζ u hu

#print axioms HRS.Fp81.S21.fp81s21_particle_empirical_compact_ito

end HRS.Fp81.S21
