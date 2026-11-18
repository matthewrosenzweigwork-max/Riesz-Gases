import HRS.MS.R2InterpAux25
import HRS.MS.R2InterpAux6
import HRS.MC.S7PIS2Cb

/-!
# HRS S2.1(iii), packet 20: collapse of the heat function at the terminal time

The cylindrical terminal identity passes to the full path test by strong
projection convergence and dominated convergence against the terminal future law.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set ProbabilityTheory

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- At the terminal time the future heat operator fixes every `C_b^5` test. -/
theorem fp81s21_heat_terminal_of_future {d : ℕ} {m H : ℝ}
    (C : WholeCoeff d) (hH : 0 < H) (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) H, IsR2FutureGaussian C m H t (γ t))
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ) (y : OscPath d m H) :
    r2HeatFn γ Ψ H y = Ψ y := by
  have hHmem : H ∈ Icc (0 : ℝ) H := ⟨hH.le, le_rfl⟩
  haveI : IsGaussian (γ H) := (hγ H hHmem).1.1
  have hc : Continuous Ψ := hΨ.1.continuous
  have hconv := (s102_projection_strong (d := d) m H hH).2.1
  have hterminal (L : ℕ) :
      r2HeatFn γ (fun w => Ψ (s102_Pj H hH L w)) H y =
        Ψ (s102_Pj H hH L y) := by
    let G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ :=
      fun x => Ψ (s102_Lam H L x)
    have hG5 : MemCb 5 G :=
      (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (s102_Lam H L) hΨ).1
    have hG2 : MemCb 2 G :=
      ⟨hG5.1.of_le (by norm_num), fun j hj => hG5.2 j (by omega)⟩
    have hfactor : (fun w => Ψ (s102_Pj H hH L w)) =
        fun w => G (s102_obs (s102_tauk hH L) (s102_alk L) w) := by
      funext w
      exact congrArg Ψ (s102_Pj_eq_Lam hH L w)
    rw [hfactor, s102_heat_obs C γ hγ _ _ G hG2 H hHmem y,
      s102_gaussHeat_T]
    exact congrArg Ψ (s102_Pj_eq_Lam hH L y).symm
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x, ‖Ψ x‖ ≤ K := by
    obtain ⟨K, hK⟩ := hΨ.2 0 (Nat.zero_le _)
    exact ⟨K, fun x => by simpa only [norm_iteratedFDeriv_zero] using hK ⟨x, rfl⟩⟩
  have hlim : Tendsto
      (fun L => r2HeatFn γ (fun w => Ψ (s102_Pj H hH L w)) H y)
      atTop (𝓝 (r2HeatFn γ Ψ H y)) := by
    unfold r2HeatFn
    refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun L => ?_)
      (integrable_const K) (fun L => Eventually.of_forall fun z => hK _)
      (Eventually.of_forall fun z => ?_)
    · exact (hc.comp ((s102_Pj H hH L).continuous.comp
        (continuous_const.add continuous_id))).aestronglyMeasurable
    · exact (hc.tendsto _).comp (hconv _)
  exact tendsto_nhds_unique hlim
    (by simpa only [hterminal, Function.comp_def] using (hc.tendsto y).comp (hconv y))

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_heat_terminal_of_future
