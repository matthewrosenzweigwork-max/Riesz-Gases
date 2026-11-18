import HRS.MS.Fp81S21LargeShift2
import HRS.MS.Fp81S21LargeShift3
import HRS.MS.Fp81S21InitialMainL22
import HRS.MS.Fp81S21WindowFeature15

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- A common exponential envelope for the scaled actual-versus-Gaussian expectation. -/
theorem fp81s21_initial_scaled_expectation_exp_bound
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
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, ∀ ha : 0 ≤ a,
      ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
        IsCenteredGaussianSeq G (fun i j =>
          HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (r26t3_qwin R a i) (r26t3_qwin R a j)) →
        ∀ Φ : SeqL2 → ℝ, ContDiff ℝ 5 Φ →
          (∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1) →
          |Real.sqrt N * ((∫ X, Φ (featureVec (r26t3_qwin R a)
              (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂G)| ≤
            D * Real.exp (-c * a) := by
  obtain ⟨KA, hKA, hA⟩ := fp81s21_initial_Aterm_qwin_exp_envelope
    hδ hδh R E hγ F hC hCwin hdecay hφ hwin
  obtain ⟨KB, hKB, hB⟩ := fp81s21_initial_Bterm_qwin_exp_envelope_uniform
    hδ hδh R E hγ F hC hdecay hφ
  let w : ℕ → ℝ := r26t3_feature_weight p.d
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w, r26t3_feature_weight]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (oscEigenvalue_pos _).le _)
  have hws : Summable w := fp81s21_qwin_weight_summable p
  have hpair : Summable (fun q : ℕ × ℕ => w q.1 * w q.2) :=
    Summable.mul_of_nonneg hws hws hw hw
  let W : ℝ := ∑' j, w j
  let P : ℝ := ∑' q : ℕ × ℕ, w q.1 * w q.2
  have hW : 0 ≤ W := tsum_nonneg hw
  have hP : 0 ≤ P := tsum_nonneg (fun q => mul_nonneg (hw _) (hw _))
  refine ⟨KA * P + (KB * C) * W, by positivity, ?_⟩
  intro N hN a ha G _ hG Φ hΦ hb
  let aI : Set.Ici (0 : ℝ) := ⟨a, ha⟩
  obtain ⟨f, hf, hst, -⟩ := fp81s21_initial_stein_package R hG hΦ hb
  have hΦb : ∀ z, |Φ z| ≤ 1 := fun z => by
    have h := hb 0 (by norm_num) z
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hD1 := fp81s21_initial_D1_scaled E hγ (hφ aI) (F aI) hG
    hΦ.continuous hΦb hf hst hN
  let A : ℕ × ℕ → ℝ := fun q => fp81s21_initial_Aterm (F aI) N f q
  let B : ℕ → ℝ := fun j => fp81s21_initial_Bterm R (r26t3_qwin R a) N
    (commutatorKernel p.d p.s (gradient ((F aI).χ j))) (S99.pd f j)
  let e : ℝ := Real.exp (-c * a)
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hAbd : ∀ q, ‖A q‖ ≤ (KA * e) * (w q.1 * w q.2) := by
    intro q
    have h := hA aI N hN f hf q.1 q.2
    simpa only [A, Real.norm_eq_abs, e, w, aI, mul_assoc] using h
  have hBbd : ∀ j, ‖B j‖ ≤ ((KB * C) * e) * w j := by
    intro j
    have h := hB a ha N hN j (S99.pd f j) (hf.pd j)
    simpa only [B, Real.norm_eq_abs, e, w, aI] using h
  have hAenv : Summable (fun q : ℕ × ℕ => (KA * e) * (w q.1 * w q.2)) := hpair.mul_left _
  have hBenv : Summable (fun j => ((KB * C) * e) * w j) := hws.mul_left _
  have hAs : Summable (fun q => ‖A q‖) := Summable.of_nonneg_of_le (fun q => norm_nonneg _) hAbd hAenv
  have hBs : Summable (fun j => ‖B j‖) := Summable.of_nonneg_of_le (fun j => norm_nonneg _) hBbd hBenv
  have hAsum : |∑' q, A q| ≤ (KA * e) * P := by
    calc
      _ = ‖∑' q, A q‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' q, ‖A q‖ := norm_tsum_le_tsum_norm hAs
      _ ≤ ∑' q : ℕ × ℕ, (KA * e) * (w q.1 * w q.2) := Summable.tsum_le_tsum hAbd hAs hAenv
      _ = (KA * e) * P := by rw [tsum_mul_left]
  have hBsum : |∑' j, B j| ≤ ((KB * C) * e) * W := by
    calc
      _ = ‖∑' j, B j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' j, ‖B j‖ := norm_tsum_le_tsum_norm hBs
      _ ≤ ∑' j, ((KB * C) * e) * w j := Summable.tsum_le_tsum hBbd hBs hBenv
      _ = ((KB * C) * e) * W := by rw [tsum_mul_left]
  rw [hD1]
  change |(∑' q, A q) + ∑' j, B j| ≤ _
  calc
    _ ≤ |∑' q, A q| + |∑' j, B j| := abs_add_le _ _
    _ ≤ (KA * e) * P + ((KB * C) * e) * W := add_le_add hAsum hBsum
    _ = (KA * P + KB * C * W) * Real.exp (-c * a) := by dsimp [e]; ring

#print axioms fp81s21_initial_scaled_expectation_exp_bound
end HRS.Fp81.S21
end
