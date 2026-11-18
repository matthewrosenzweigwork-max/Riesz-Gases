import HRS.MS.Fp81S21CovRS4
import HRS.MS.Fp81S21MovingPrediction3
import HRS.MS.Fp81S21CovCumulative10

/-! Physical moving covariance RS families at a fixed horizon and future. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
theorem fp81s21_cov_weightedSup_le_of_iteratedFDeriv_bound_covRS
    {d k : ℕ} {f : Euc d → ℝ} {B : ℝ}
    (hbound : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    weightedSupE k 0 f ≤ ENNReal.ofReal B := by
  apply HRS.MS.Go.s55_dse_le
  intro j hj idx x
  have hdir := (iteratedFDeriv ℝ j f x).le_opNorm
    (fun l => EuclideanSpace.single (idx l) 1)
  have hpartial : |partialDeriv idx f x| ≤ B := by
    calc
      |partialDeriv idx f x| ≤ ‖iteratedFDeriv ℝ j f x‖ := by
        simpa [partialDeriv, EuclideanSpace.norm_single] using hdir
      _ ≤ B := hbound j hj x
  simpa [Real.rpow_zero] using hpartial


/-- The moving orbit regularity fields imply the covariance measure's orbit
summability hypothesis. -/
theorem fp81s21_R2OrbitSummable_of_S101Data
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ}
    (hD : S101Data C m H r c) : R2OrbitSummable C m H r := by
  refine ⟨?_, ?_⟩
  · intro α u hu t ht
    refine ⟨?_, ?_, ?_⟩
    · exact (hD.smoothU α u hu t ht).of_le (by norm_num)
    · intro x
      exact hD.diffT α u hu x t ht
    · simpa [s101Dt] using hD.smoothD α u hu t ht
  · have hsq : Summable (fun α : MultiIndex d => c α ^ 2) := hD.summable
    have hnonneg : ∀ α, 0 ≤ c α := hD.nonneg
    refine lt_of_le_of_lt
      (ENNReal.tsum_le_tsum fun α => ?_)
      (hsq.mul_left 2).tsum_ofReal_lt_top
    refine iSup_le fun u => iSup_le fun hu =>
      iSup_le fun t => iSup_le fun ht => ?_
    have hU := fp81s21_cov_weightedSup_le_of_iteratedFDeriv_bound_covRS
      (fun j hj x => hD.bddU α u hu t ht j hj x)
    have hD' := fp81s21_cov_weightedSup_le_of_iteratedFDeriv_bound_covRS
      (fun j hj x => hD.bddD α u hu t ht j hj x)
    calc
      weightedSupE (r + 1) 0 (propagatorW C u t (oscTestFun m α)) ^ 2 +
          weightedSupE (r + 1) 0
            (fun x => s101Dt C m H u t α x) ^ 2 ≤
          ENNReal.ofReal (c α) ^ 2 + ENNReal.ofReal (c α) ^ 2 := by
            exact add_le_add (by gcongr) (by gcongr)
      _ = ENNReal.ofReal (2 * c α ^ 2) := by
        rw [← ENNReal.ofReal_pow (hnonneg α)]
        rw [← ENNReal.ofReal_add (sq_nonneg (c α)) (sq_nonneg (c α))]
        congr 1
        ring

/-- At one physical start, the measurable prediction and raw covariance
cumulative produce projected covariance RS windows with a common integrable
supremum-times-variation majorant. The heat future is shared by all levels. -/
theorem fp81s21_moving_covariance_rsbv_window_fixed
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (a : ℝ) (ha : 0 ≤ a)
    (hH : 0 < a + p.T) {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (F : FilteredParticle A) {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) (2 * p.d + 8) c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hphys : Fp81MovingPhysicalInputs R hN A (a + p.T))
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future) :
    ∃ (Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
      (Fj : A.Ω → ℝ → projTensor
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
      (V : A.Ω → ℝ),
      (∀ t, Measurable (fun ω => Yh ω t)) ∧
      (∀ t, Measurable (fun ω => Fj ω t)) ∧ Integrable V A.P ∧
      (∀ ω, Fj ω 0 = 0) ∧
      (∀ᵐ ω ∂A.P,
        (∀ t ∈ Icc (0 : ℝ) (a + p.T),
          Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (a + p.T) A.P A.X ω t) ∧
        ContinuousOn (Yh ω) (Icc 0 (a + p.T)) ∧
        (∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
          IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
            (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
            (((Fj ω r - Fj ω q : projTensor
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) : TensorDual
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2))) ∧
        ContinuousOn (Fj ω) (Icc 0 (a + p.T)) ∧
        BoundedVariationOn (Fj ω) (Icc 0 (a + p.T)) ∧
        (eVariationOn (Fj ω) (Icc 0 (a + p.T))).toReal ≤ V ω) ∧
      ∀ (Φ : Window p → ℝ), MemCb 5 Φ →
        let W := HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
          (H := a + p.T) ha le_rfl
        let Ψ := fun w => Φ (W w)
        let Ad := fun L ω τ => fp81s21_covariance_pairingCLM
          (iteratedFDeriv ℝ 2
            (r2HeatFn (future (a + p.T))
              (fun w => Ψ (s102_Pj (a + p.T) hH L w)) τ) (Yh ω τ))
        ∃ M : A.Ω → ℝ, Integrable M A.P ∧ ∀ L,
          Nonempty (fp81s21_RSBVWindow A.P (a + p.T) (Ad L) Fj) ∧
          ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
            Integrable (fp81s21_rs_bv_variation_majorant (Ad L) Fj q r) A.P ∧
            ∀ᵐ ω ∂A.P,
              fp81s21_rs_bv_variation_majorant (Ad L) Fj q r ω ≤ M ω := by
  have hH' : 0 < a + p.T := hH
  obtain ⟨Yh, hYm, hYe, hYc⟩ :=
    fp81s21_moving_prediction p R hδ hδh hH' hN A F hstd hlin hphys
  have horb : R2OrbitSummable (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) (a + p.T) (2 * p.d + 8) :=
    fp81s21_R2OrbitSummable_of_S101Data hstd.hD
  obtain ⟨Fj, V, hFm, hVi, hF0, hFg⟩ :=
    fp81s21_moving_raw_eta_measurable_cumulative_fixed p R hδ hδh hH'
      horb hlin hN A hphys
  refine ⟨Yh, Fj, V, hYm, hFm, hVi, hF0, ?_, ?_⟩
  · filter_upwards [hYe, hYc, hFg] with ω he hc hf
    exact ⟨he, hc, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩
  · intro Φ hΦ
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := a + p.T) ha le_rfl
    let Ψ := fun w => Φ (W w)
    have hΨ : MemCb 5 Ψ :=
      (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
    have hp := hfuture.2.2.2 (a + p.T) hH'
    exact fp81s21_projected_heat_covariance_rsbv_window A.P
      (future (a + p.T)) (hfuture.1 (a + p.T))
      (fun L => s102_Pj (a + p.T) hH' L) hp.1 hp.2.1
      (hfuture.2.2.1 (a + p.T) hH') Ψ hΨ Yh Fj V hYm hFm hYc
      (hFg.mono fun _ h => h.2.1) hVi
      (hFg.mono fun _ h => ⟨h.2.2.1, h.2.2.2⟩)

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_cov_weightedSup_le_of_iteratedFDeriv_bound_covRS
#print axioms HRS.Fp81.S21.fp81s21_R2OrbitSummable_of_S101Data
#print axioms HRS.Fp81.S21.fp81s21_moving_covariance_rsbv_window_fixed
end
