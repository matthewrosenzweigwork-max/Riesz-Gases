import HRS.MS.Fp81S21WeightedGenNL11

/-! A common integrable envelope for source jets. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.Who HRS.MS.ProClosureS111

/-- Source jets of a weighted test and its cutoff family share an L¹ and L² envelope. -/
theorem fp81s21_b3_source_jet_envelope {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) (f : Euc p.d → ℝ) (K : ℝ)
    (h : ℕ → Euc p.d → ℝ) {B c : ℝ}
    (hB : 0 ≤ B) (hc : 0 < c)
    (hdata : fp81s21_b3_Data R B c) (hu : 0 ≤ u)
    (hf : IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f)
    (hK : 0 ≤ K)
    (hreg : ∀ n, IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) ∧
      HasCompactSupport (h n))
    (hb : ∀ n x, ‖weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) x‖ ≤
      K * ‖weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f x‖) :
    ∃ H : Euc p.d → ℝ,
      Continuous H ∧ Integrable H ∧ MemLp H 2 volume ∧
      (∀ x, 0 ≤ H x) ∧
      (∀ j m, m ≤ fp81s21_b3_q p + 1 → ∀ x,
        ‖iteratedFDeriv ℝ m (fp81s21_b3_source R u f j) x‖ ≤ H x) ∧
      (∀ n j m, m ≤ fp81s21_b3_q p + 1 → ∀ x,
        ‖iteratedFDeriv ℝ m (fp81s21_b3_source R u (h n) j) x‖ ≤ H x) := by
  let q := fp81s21_b3_q p
  let P := fp81s21_b3_P p
  let W : ℝ := ∑ j : Fin p.d, ‖ul1w (r26t3_coeff R).M j‖
  let D : ℝ := (2 : ℝ) ^ (q + 1) * B * W * ((p.d : ℝ) + 1) ^ (q + 2)
  let A : ℝ := max 1 K * D
  let g : Euc p.d → ℝ := fun x => Real.exp (-c * ‖x‖ ^ 2) * jbracket x ^ P
  let J : Euc p.d → ℝ := fun x => ‖weightedJets (q + 2) P f x‖
  have hP : 0 ≤ P := by dsimp [P, fp81s21_b3_P]; positivity
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨C, hC, hgb, hg2⟩ := fp81s21_gaussian_weight_bounds (d := p.d) hP hc
  have hgc : Continuous g := by
    dsimp [g]
    apply Continuous.mul (by fun_prop)
    apply Continuous.rpow_const
    · unfold jbracket; fun_prop
    · intro x; exact Or.inl (who_jb_pos x).ne'
  have hJc : Continuous J := (weightedJets_continuous hf.1).norm
  have hJ2 : MemLp J 2 volume := ((weightedJets_memLp_iff hf.1).2 hf.2).norm
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    dsimp [g]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (who_jb_pos x).le _)
  let H : Euc p.d → ℝ := fun x => A * (g x * J x)
  have hHc : Continuous H := (hgc.mul hJc).const_mul A
  have hHi : Integrable H := (hg2.integrable_mul hJ2).const_mul A
  have hH2 : MemLp H 2 volume := by
    refine (hJ2.const_mul (A * C)).mono' hHc.aestronglyMeasurable ?_
    filter_upwards [] with x
    have hj : 0 ≤ J x := norm_nonneg _
    have hx := hgb x
    change ‖g x‖ ≤ C at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)] at hx
    change ‖A * (g x * J x)‖ ≤ (A * C) * J x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA (mul_nonneg (hg0 x) hj))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) hj,
      mul_nonneg (sub_nonneg.mpr hx) (mul_nonneg hA hj)]
  have hbound : ∀ (z : Euc p.d → ℝ), ContDiff ℝ (q + 2) z →
      (∀ x, ‖weightedJets (q + 2) P z x‖ ≤ max 1 K * J x) →
      ∀ j m, m ≤ q + 1 → ∀ x, ‖iteratedFDeriv ℝ m (fp81s21_b3_source R u z j) x‖ ≤ H x := by
    intro z hz hzj j m hm x
    have hw : ‖ul1w (r26t3_coeff R).M j‖ ≤ W :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    have hm0 : 0 ≤ max 1 K := by positivity
    have hj0 : 0 ≤ J x := norm_nonneg _
    have hcoeff : (2 : ℝ) ^ (q + 1) * B * ‖ul1w (r26t3_coeff R).M j‖ *
        ((p.d : ℝ) + 1) ^ (q + 2) ≤ D := by
      dsimp [D]
      gcongr
    have hpoint := fp81s21_b3_source_jet_pointwise R u hB hdata hu z hz j m hm x
    have hrest : 0 ≤ g x * ‖weightedJets (q + 2) P z x‖ := mul_nonneg (hg0 x) (norm_nonneg _)
    have ht := mul_le_mul_of_nonneg_right hcoeff hrest
    have hu' := mul_le_mul_of_nonneg_left (hzj x) (mul_nonneg hD (hg0 x))
    dsimp [H, A]
    dsimp [g] at ht hu'
    dsimp [q, P] at *
    nlinarith
  refine ⟨H, hHc, hHi, hH2, ?_, ?_, ?_⟩
  · intro x; exact mul_nonneg hA (mul_nonneg (hg0 x) (norm_nonneg _))
  · apply hbound f hf.1
    intro x
    have hmax : 1 ≤ max 1 K := le_max_left _ _
    dsimp [J]
    nlinarith [norm_nonneg (weightedJets (q + 2) P f x)]
  · intro n
    apply hbound (h n) (hreg n).1.1
    intro x
    exact (hb n x).trans (mul_le_mul_of_nonneg_right (le_max_right 1 K) (norm_nonneg _))

#print axioms HRS.Fp81.S21.fp81s21_b3_source_jet_envelope
end HRS.Fp81.S21
