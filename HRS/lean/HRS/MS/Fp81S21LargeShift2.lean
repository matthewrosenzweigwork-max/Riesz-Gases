import HRS.MS.Fp81S21LargeShift
import HRS.MS.Fp81S21InitialLinear3

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open S45
open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-- The actual-law linear coefficients inherit the decay of the compatible gradients. -/
theorem fp81s21_initial_Aterm_qwin_exp_envelope
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    (F : fp81s21_CompatPotentialFamily R)
    {C c Cwin : ℝ} (hC : 0 ≤ C) (hCwin : 0 ≤ Cwin)
    (hdecay : ∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
      HasCbBound (fp81s21_k0 p.d)
        (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
        (gradient ((F a).χ j)))
    (hφ : ∀ a : Set.Ici (0 : ℝ),
      IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)))
    (hwin : ∀ a : Set.Ici (0 : ℝ), ∀ k : ℕ,
      cbNorm (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ) k) ≤
        Cwin * r26t3_feature_weight p.d k) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ a : Set.Ici (0 : ℝ),
      ∀ N : ℕ, 2 ≤ N → ∀ f : SeqL2 → ℝ, S99.SteinCl f → ∀ j k : ℕ,
      |fp81s21_initial_Aterm (F a) N f (j, k)| ≤
        KA * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j *
          r26t3_feature_weight p.d k := by
  obtain ⟨KT, hKT, hT⟩ := fp81s21_initial_T_L1 hδ hδh E hγ
  refine ⟨KT * (p.γ⁻¹ * C * Cwin), by positivity, ?_⟩
  intro a N hN f hf j k
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  letI : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let w := InitialFamData.wF (F a) j k
  let B := p.γ⁻¹ * (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j) *
    (Cwin * r26t3_feature_weight p.d k)
  have hwgt : ∀ i, 0 ≤ r26t3_feature_weight p.d i := by
    intro i
    dsimp [r26t3_feature_weight]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (oscEigenvalue_pos _).le _)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hγ.le)
      (mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (hwgt j)))
      (mul_nonneg hCwin (hwgt k))
  have hwcb := fp81s21_initial_wF_cb (hφ a).1 (F a) hγ j k
  have hwm : Measurable w := hwcb.1.1.continuous.measurable
  have hwbd : ∀ x, |w x| ≤ B := by
    intro x
    have hχ : ‖gradient ((F a).χ j) x‖ ≤
        C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j := by
      simpa using (hdecay a j).2 0 (Nat.zero_le _) x
    have hq : ‖gradient (r26t3_qwin R (a : ℝ) k) x‖ ≤
        Cwin * r26t3_feature_weight p.d k := by
      have h := s45_cb_deriv_le (by exact_mod_cast (show 1 ≤ fp81s21_J1 p.d by unfold fp81s21_J1; omega)) ((hφ a).1 k) x
      rw [← s45_norm_gradient] at h
      exact h.trans (hwin a k)
    dsimp [w, InitialFamData.wF, B]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul hχ hq (norm_nonneg _)
          (mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (hwgt j)))) (inv_nonneg.2 hγ.le)
  have hpairμ : |HRS.Whole.pair (r26t3_mu R 0) w| ≤ B :=
    HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hwbd x)
  have hdiffm : Measurable (fun X : EucConfig p.d N =>
      HRS.Whole.pair (HRS.Whole.empirical X) w - HRS.Whole.pair (r26t3_mu R 0) w) :=
    (s45_measurable_pair_empirical hN1 hwm).sub measurable_const
  have hdiffbd : ∀ X : EucConfig p.d N,
      |HRS.Whole.pair (HRS.Whole.empirical X) w - HRS.Whole.pair (r26t3_mu R 0) w| ≤ 2 * B := by
    intro X
    calc
      _ ≤ |HRS.Whole.pair (HRS.Whole.empirical X) w| +
          |HRS.Whole.pair (r26t3_mu R 0) w| := abs_sub _ _
      _ ≤ B + B := add_le_add (s45_abs_pair_empirical_le hN1 hwbd X) hpairμ
      _ = 2 * B := by ring
  have hdiffint : Integrable (fun X : EucConfig p.d N =>
      |HRS.Whole.pair (HRS.Whole.empirical X) w - HRS.Whole.pair (r26t3_mu R 0) w|) (r26t3_Q R N) := by
    apply Integrable.of_bound hdiffm.abs.aestronglyMeasurable (2 * B)
    filter_upwards with X
    simpa only [Real.norm_eq_abs, abs_abs] using hdiffbd X
  have hCf : fp81s21_initial_Cf (F a) j k = HRS.Whole.pair (r26t3_mu R 0) w := by
    simpa [w, HRS.Whole.pair] using fp81s21_initial_Cf_eq_wF E hγ (hφ a) (F a) j k
  have htest : ∀ X : EucConfig p.d N,
      |S99.pd (S99.pd f j) k (featureVec (r26t3_qwin R (a : ℝ)) (r26t3_marg R N) X)| ≤ 1 :=
    fun X => ((hf.pd j).pd k).abs_le _
  have hbound : |∫ X : EucConfig p.d N,
      (fp81s21_initial_Cf (F a) j k - HRS.Whole.pair (HRS.Whole.empirical X) w) *
        S99.pd (S99.pd f j) k (featureVec (r26t3_qwin R (a : ℝ)) (r26t3_marg R N) X)
      ∂(r26t3_Q R N)| ≤ KT * B / Real.sqrt N := by
    calc
      _ ≤ ∫ X : EucConfig p.d N,
          ‖(fp81s21_initial_Cf (F a) j k - HRS.Whole.pair (HRS.Whole.empirical X) w) *
            S99.pd (S99.pd f j) k (featureVec (r26t3_qwin R (a : ℝ)) (r26t3_marg R N) X)‖
          ∂(r26t3_Q R N) := by
            rw [← Real.norm_eq_abs]
            exact norm_integral_le_integral_norm _
      _ ≤ ∫ X : EucConfig p.d N,
          |HRS.Whole.pair (HRS.Whole.empirical X) w - HRS.Whole.pair (r26t3_mu R 0) w| ∂(r26t3_Q R N) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) hdiffint
        filter_upwards with X
        rw [Real.norm_eq_abs, abs_mul, hCf, abs_sub_comm]
        simpa using mul_le_mul_of_nonneg_left (htest X) (abs_nonneg _)
      _ ≤ KT * B / Real.sqrt N := hT N hN B hB w hwm hwbd
  unfold fp81s21_initial_Aterm
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt N * (KT * B / Real.sqrt N) := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)
    _ = KT * (p.γ⁻¹ * C * Cwin) * Real.exp (-c * (a : ℝ)) *
        r26t3_feature_weight p.d j * r26t3_feature_weight p.d k := by
      dsimp [B]
      field_simp
      <;> ring

#print axioms fp81s21_initial_Aterm_qwin_exp_envelope
end HRS.Fp81.S21
end
