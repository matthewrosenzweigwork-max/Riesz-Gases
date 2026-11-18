import HRS.MS.Fp81S21MovingG6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MC.Sec7.S7PIG6

/-- The expected projected heat endpoint converges to the unprojected endpoint. -/
theorem fp81s21_moving_heat_endpoint_expectation_projection_limit
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (D : fp81s21_finproj_shared_data p R a A F)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (t : ℝ) (ht0 : 0 ≤ t) (htH : t ≤ a + p.T) :
    Tendsto (fun L => ∫ ω, fp81s21_moving_heat_ito_endpoint
      p R A a ha hH future L Φ t ω ∂A.P) atTop
      (𝓝 (∫ ω, r2HeatFn (future (a + p.T))
        (fun w => Φ (HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
          (H := a + p.T) ha le_rfl w)) t
        (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (a + p.T) A.P A.X ω t) ∂A.P)) := by
  classical
  let H : ℝ := a + p.T
  let B := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  let W : B →L[ℝ] Window p := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl
  let Ψ : B → ℝ := fun w => Φ (W w)
  have hΨ : MemCb 5 Ψ := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x, |Ψ x| ≤ K := by
    obtain ⟨K, hK⟩ := hΨ.2 0 (Nat.zero_le _)
    exact ⟨K, fun x => by simpa [norm_iteratedFDeriv_zero] using hK ⟨x, rfl⟩⟩
  have hc : Continuous Ψ := hΨ.1.continuous
  have hp := hfuture.2.2.2 H hH
  letI : IsProbabilityMeasure (future H t) := hfuture.1 H t
  have hlim : Tendsto (fun L => ∫ ω, r2HeatFn (future H)
      (fun w => Ψ (s102_Pj H hH L w)) t (D.Yh ω t) ∂A.P) atTop
      (𝓝 (∫ ω, r2HeatFn (future H) Ψ t (D.Yh ω t) ∂A.P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun L => ?_)
      (integrable_const K) (fun L => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => ?_)
    · exact ((S7PIG6_heat_cont (future H t)
        (hc.comp (s102_Pj H hH L).continuous) K (fun x => hK _)).measurable.comp
          (D.Yh_measurable t)).aestronglyMeasurable
    · have hh := norm_integral_le_of_norm_le_const (μ := future H t)
        (f := fun z : B => Ψ (s102_Pj H hH L (D.Yh ω t + z))) (C := K)
        (Eventually.of_forall fun z => by simpa using hK _)
      simpa [r2HeatFn] using hh
    · unfold r2HeatFn
      refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun L => ?_)
        (integrable_const K) (fun L => Eventually.of_forall fun z => ?_)
        (Eventually.of_forall fun z => ?_)
      · exact (hc.comp ((s102_Pj H hH L).continuous.comp
          (continuous_const.add continuous_id))).aestronglyMeasurable
      · simpa using hK _
      · exact (hc.tendsto _).comp (hp.2.1 _)
  have heq (L : ℕ) : (∫ ω, fp81s21_moving_heat_ito_endpoint
      p R A a ha hH future L Φ t ω ∂A.P) =
      ∫ ω, r2HeatFn (future H) (fun w => Ψ (s102_Pj H hH L w)) t (D.Yh ω t) ∂A.P := by
    apply integral_congr_ae
    filter_upwards [D.Yh_ae] with ω hω
    simp only [fp81s21_moving_heat_ito_endpoint]
    simpa [H, W, Ψ] using congrArg
      (fun y : B => r2HeatFn (future H) (fun w => Ψ (s102_Pj H hH L w)) t y)
      (hω t ⟨ht0, htH⟩).symm
  have heq' : (∫ ω, r2HeatFn (future H) Ψ t (D.Yh ω t) ∂A.P) =
      ∫ ω, r2HeatFn (future H) Ψ t
        (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P A.X ω t) ∂A.P := by
    apply integral_congr_ae
    filter_upwards [D.Yh_ae] with ω hω
    rw [hω t ⟨ht0, htH⟩]
  simpa only [heq, heq'] using hlim

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_heat_endpoint_expectation_projection_limit
