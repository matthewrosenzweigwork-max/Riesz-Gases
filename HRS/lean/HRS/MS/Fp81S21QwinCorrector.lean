import HRS.MS.Fp81S21CorrectorExplicit
import HRS.MS.Fp81S21QwinDecay4

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-- A global derivative bound and a finite second moment control the centered L² norm.
The constant part is removed by `projMean`; the remaining function is bounded by
`L * ‖x‖` through the mean value theorem. -/
theorem fp81s21_centeredL2_of_deriv_bound
    {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (q : Euc d → ℝ) (L M₂ : ℝ)
    (hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ)
    (hM₂ : ∫ x, ‖x‖ ^ 2 ∂μ ≤ M₂)
    (hq : ContDiff ℝ 1 q)
    (hderiv : ∀ x, ‖fderiv ℝ q x‖ ≤ L) :
    HRS.Whole.l2Norm μ (HRS.Whole.projMean μ q) ≤ L * Real.sqrt M₂ := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hderiv 0)
  have hqLp : MemLp q 2 μ := HRS.MS.S48.s48_memLp_lip hint2 hq hderiv
  have hshiftLp : MemLp (fun x => q x - q 0) 2 μ := hqLp.sub (memLp_const _)
  have hpoint : ∀ x, |q x - q 0| ≤ L * ‖x‖ := by
    intro x
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := q) (C := L) (s := Set.univ) (x := 0) (y := x)
      (fun y _ => (hq.differentiable (by norm_num)) y)
      (fun y _ => hderiv y) convex_univ (Set.mem_univ _) (Set.mem_univ _)
    rw [sub_zero] at hmvt
    simpa [Real.norm_eq_abs] using hmvt
  have hintScaled : Integrable (fun x : Euc d => L ^ 2 * ‖x‖ ^ 2) μ := by
    simpa [mul_comm] using hint2.const_mul (L ^ 2)
  have hshiftSq : ∫ x, (q x - q 0) ^ 2 ∂μ ≤ L ^ 2 * M₂ := by
    calc
      ∫ x, (q x - q 0) ^ 2 ∂μ ≤ ∫ x, L ^ 2 * ‖x‖ ^ 2 ∂μ := by
        apply integral_mono hshiftLp.integrable_sq hintScaled
        intro x
        have hnonneg : 0 ≤ L * ‖x‖ := mul_nonneg hL0 (norm_nonneg _)
        have hgap : 0 ≤ L * ‖x‖ - |q x - q 0| := sub_nonneg.mpr (hpoint x)
        have habs0 : 0 ≤ |q x - q 0| := abs_nonneg (q x - q 0)
        have hprod := mul_nonneg hgap (add_nonneg hnonneg habs0)
        have hsquare : |q x - q 0| ^ 2 ≤ (L * ‖x‖) ^ 2 := by nlinarith
        have habsSq : |q x - q 0| ^ 2 = (q x - q 0) ^ 2 := by rw [sq_abs]
        calc
          (q x - q 0) ^ 2 = |q x - q 0| ^ 2 := habsSq.symm
          _ ≤ (L * ‖x‖) ^ 2 := hsquare
          _ = L ^ 2 * ‖x‖ ^ 2 := by ring
      _ = L ^ 2 * (∫ x, ‖x‖ ^ 2 ∂μ) := by rw [integral_const_mul]
      _ ≤ L ^ 2 * M₂ := mul_le_mul_of_nonneg_left hM₂ (sq_nonneg L)
  have hM₂0 : 0 ≤ M₂ := le_trans
    (integral_nonneg fun x => sq_nonneg ‖x‖) hM₂
  have hshiftNorm : HRS.Whole.l2Norm μ (fun x => q x - q 0) ≤
      L * Real.sqrt M₂ := by
    unfold HRS.Whole.l2Norm
    calc
      Real.sqrt (∫ x, (q x - q 0) ^ 2 ∂μ) ≤ Real.sqrt (L ^ 2 * M₂) :=
        Real.sqrt_le_sqrt hshiftSq
      _ = L * Real.sqrt M₂ := by
        rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL0]
  have hpair : HRS.Whole.pair μ (fun x => q x - q 0) =
      HRS.Whole.pair μ q - q 0 := by
    dsimp [HRS.Whole.pair]
    rw [integral_sub (hqLp.integrable one_le_two) (integrable_const _), integral_const]
    simp
  have hproj : HRS.Whole.projMean μ (fun x => q x - q 0) =
      HRS.Whole.projMean μ q := by
    funext x
    simp only [HRS.Whole.projMean]
    rw [hpair]
    ring
  rw [← hproj]
  exact (HRS.Whole.S71.s71_l2Norm_projMean_le hshiftLp).trans hshiftNorm

private theorem fp81s21_s48_Dn_le_mul
    {d J : ℕ} {q : Euc d → ℝ} {A : ℝ}
    (hmem : MemCb J q) (hA0 : 0 ≤ A)
    (hderiv : ∀ i, 1 ≤ i → i ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ i q x‖ ≤ A) :
    HRS.MS.S48.s48_Dn J q ≤ (J : ℝ) * A := by
  unfold HRS.MS.S48.s48_Dn
  calc
    (∑ j ∈ Finset.range J, ⨆ y, ‖iteratedFDeriv ℝ (j + 1) q y‖) ≤
        ∑ j ∈ Finset.range J, A := by
      apply Finset.sum_le_sum
      intro j hj
      have hji : j + 1 ≤ J := by
        have := Finset.mem_range.mp hj
        omega
      letI : BddAbove (Set.range fun y =>
          ‖iteratedFDeriv ℝ (j + 1) q y‖) := hmem.2 (j + 1) hji
      exact ciSup_le (fun y => hderiv (j + 1) (by omega) hji y)
    _ = (J : ℝ) * A := by simp

/-- The derivative-only S4.8 norm is controlled by the centered L² estimate and
the sum of the `J` positive-order derivative suprema. -/
theorem fp81s21_s48Q_of_deriv_bounds
    {d J : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (q : Euc d → ℝ) (A M₂ : ℝ)
    (hJ : 1 ≤ J) (hmem : MemCb J q)
    (hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ)
    (hM₂ : ∫ x, ‖x‖ ^ 2 ∂μ ≤ M₂)
    (hA0 : 0 ≤ A)
    (hderiv : ∀ i, 1 ≤ i → i ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ i q x‖ ≤ A) :
    HRS.MS.S48.s48_Q μ J q ≤ (Real.sqrt M₂ + (J : ℝ)) * A := by
  have hq1 : ContDiff ℝ 1 q := (HRS.MS.Tc5.tc5_cb_mono hJ hmem).1.1
  have hfd : ∀ x, ‖fderiv ℝ q x‖ ≤ A := by
    intro x
    rw [← norm_iteratedFDeriv_one]
    exact hderiv 1 (by omega) hJ x
  have hcenter := fp81s21_centeredL2_of_deriv_bound μ q A M₂ hint2 hM₂ hq1 hfd
  have hDn := fp81s21_s48_Dn_le_mul hmem hA0 hderiv
  unfold HRS.MS.S48.s48_Q
  calc
    HRS.Whole.l2Norm μ (HRS.Whole.projMean μ q) + HRS.MS.S48.s48_Dn J q ≤
        A * Real.sqrt M₂ + (J : ℝ) * A := add_le_add hcenter hDn
    _ = (Real.sqrt M₂ + (J : ℝ)) * A := by ring

/-- The actual initial law is a probability measure with a finite second moment.
The bound is the moment parameter from its S4.8 drift package. -/
theorem fp81s21_initial_secondMoment
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧
      IsProbabilityMeasure (r26t3_mu R 0) ∧
      Integrable (fun x : Euc p.d => ‖x‖ ^ 2) (r26t3_mu R 0) ∧
      ∫ x, ‖x‖ ^ 2 ∂(r26t3_mu R 0) ≤ M₂ := by
  obtain ⟨B, Mb, M₂, hB, hlog, hinv, hint2, hM₂⟩ :=
    HRS.MS.R26T3.r26t3_initial_drift hδ hδh R 0
  have hM₂0 : 0 ≤ M₂ := le_trans
    (integral_nonneg fun x => sq_nonneg ‖x‖) hM₂
  exact ⟨M₂, hM₂0, hinv.1, hint2, hM₂⟩

/-- Shifted cosine observations have exponentially decaying S4.8 norms at the
explicit corrector order. The common radius intersects the uniform `MemCb`
certificate and the positive-derivative decay radius. -/
theorem fp81s21_qwin_s48Q_decay (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧
          ∀ a : ℝ, 0 ≤ a → ∀ j : ℕ,
            HRS.MS.S48.s48_Q (r26t3_mu R 0) (fp81s21_correctorOrder p.d)
              (r26t3_qwin R a j) ≤
                C * Real.exp (-c * a) * r26t3_feature_weight p.d j := by
  obtain ⟨δu, hδu, hδuhalf, hu⟩ := fp81s21_qwin_uniform p
  obtain ⟨δd, hδd, hδdhalf, hd⟩ := fp81s21_qwin_shifted_decay p
  let δ0 := min δu δd
  have hδ0 : 0 < δ0 := lt_min hδu hδd
  have hδ0half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδuhalf
  refine ⟨δ0, hδ0, hδ0half, fun δ hδ hδle R => ?_⟩
  obtain ⟨Cu, hCu, huR⟩ := hu δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨Cd, hCd, c, hc, hdecay⟩ := hd δ hδ (hδle.trans (min_le_right _ _)) R
  obtain ⟨M₂, hM₂0, hprob, hint2, hM₂⟩ :=
    fp81s21_initial_secondMoment hδ (hδle.trans hδ0half) R
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hprob
  have hJ : 1 ≤ fp81s21_correctorOrder p.d := by
    unfold fp81s21_correctorOrder fp81s21_k0
    omega
  have hJle : fp81s21_correctorOrder p.d ≤ r26t3_J p.d :=
    fp81s21_correctorOrder_le p.d p.hd
  let C : ℝ := (Real.sqrt M₂ + (fp81s21_correctorOrder p.d : ℝ)) * Cd
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, c, hc, fun a ha j => ?_⟩
  let q := r26t3_qwin R a j
  have hmemJ : MemCb (r26t3_J p.d) q := (huR a ha).1.1 j
  have hmem : MemCb (fp81s21_correctorOrder p.d) q :=
    (HRS.MS.Tc5.tc5_cb_mono hJle hmemJ).1
  have hweight : 0 < r26t3_feature_weight p.d j := by
    rw [fp81s21_qwin_feature_weight_eq p j]
    exact mul_pos
      (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (HRS.Whole.oscEv_pos _) _)
  have hA0 : 0 ≤ Cd * Real.exp (-c * a) * r26t3_feature_weight p.d j :=
    mul_nonneg (mul_nonneg hCd (Real.exp_pos _).le) hweight.le
  have hderiv : ∀ i, 1 ≤ i → i ≤ fp81s21_correctorOrder p.d → ∀ x,
      ‖iteratedFDeriv ℝ i q x‖ ≤
        Cd * Real.exp (-c * a) * r26t3_feature_weight p.d j := by
    intro i hi1 hiJ x
    exact hdecay a ha j i hi1 (hiJ.trans hJle) x
  have hQ := fp81s21_s48Q_of_deriv_bounds (r26t3_mu R 0)
    q (Cd * Real.exp (-c * a) * r26t3_feature_weight p.d j) M₂
    hJ hmem hint2 hM₂ hA0 hderiv
  have hrewrite :
      (Real.sqrt M₂ + (fp81s21_correctorOrder p.d : ℝ)) *
          (Cd * Real.exp (-c * a) * r26t3_feature_weight p.d j) =
        C * Real.exp (-c * a) * r26t3_feature_weight p.d j := by
    dsimp [C]
    ring
  exact hrewrite ▸ hQ

#print axioms fp81s21_centeredL2_of_deriv_bound
#print axioms fp81s21_s48Q_of_deriv_bounds
#print axioms fp81s21_initial_secondMoment
#print axioms fp81s21_qwin_s48Q_decay

end HRS.Fp81.S21

end
