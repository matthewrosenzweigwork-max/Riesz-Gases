import HRS.MS.QsfIbp1

/-!
# S4.5 packet B2, part 2: integrability toolkit, bound on `dH_ε`, integration by parts at fixed `ε > 0`

Namespace `S45`.  For `ε ∈ (0,1]` and a differentiable `G` with bounded `G` and bounded directional derivative
`∂_e G`, Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` gives
`∫ w_ε ∂_e G = β ∫ w_ε (∂_e H_ε) G` (`s45_ibp_eps`): everything is smooth, so no collision cutoff is needed.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-! ### Gaussian domination toolkit -/

theorem s45_poly_le {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → 1 + t ≤ C * Real.exp (c * t ^ 2) := by
  refine ⟨1 + 1 / (4 * c), by positivity, fun t ht => ?_⟩
  have h1 : t ≤ c * t ^ 2 + 1 / (4 * c) := by
    have : 0 ≤ c * (t - 1 / (2 * c)) ^ 2 := by positivity
    have e : c * (t - 1 / (2 * c)) ^ 2 = c * t ^ 2 - t + 1 / (4 * c) := by
      field_simp; ring
    linarith
  have h2 : c * t ^ 2 + 1 ≤ Real.exp (c * t ^ 2) := by linarith [Real.add_one_le_exp (c * t ^ 2)]
  have h3 : 1 ≤ Real.exp (c * t ^ 2) := Real.one_le_exp (by positivity)
  have h4 : 0 ≤ 1 / (4 * c) := by positivity
  nlinarith

theorem s45_integrable_gauss {c : ℝ} (hc : 0 < c) :
    Integrable (fun X : EucConfig d N => Real.exp (-(c * ‖X‖ ^ 2))) :=
  HRS.MP.SelfSimP4Impl.p4g_integrable_gauss_pi hc

theorem s45_integrable_of_dom {c : ℝ} (hc : 0 < c) {f : EucConfig d N → ℝ}
    (hf : AEStronglyMeasurable f volume) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ X, |f X| ≤ K * (1 + ‖X‖) * Real.exp (-(c * ‖X‖ ^ 2))) : Integrable f := by
  obtain ⟨C, hC0, hC⟩ := s45_poly_le (half_pos hc)
  refine Integrable.mono' ((s45_integrable_gauss (d := d) (N := N) (half_pos hc)).const_mul (K * C))
    hf (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs]
  refine (hK X).trans ?_
  have h1 := hC ‖X‖ (norm_nonneg _)
  have h2 : Real.exp (c / 2 * ‖X‖ ^ 2) * Real.exp (-(c * ‖X‖ ^ 2)) =
      Real.exp (-(c / 2 * ‖X‖ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc K * (1 + ‖X‖) * Real.exp (-(c * ‖X‖ ^ 2))
      ≤ K * (C * Real.exp (c / 2 * ‖X‖ ^ 2)) * Real.exp (-(c * ‖X‖ ^ 2)) := by
        gcongr
    _ = K * C * (Real.exp (c / 2 * ‖X‖ ^ 2) * Real.exp (-(c * ‖X‖ ^ 2))) := by ring
    _ = K * C * Real.exp (-(c / 2 * ‖X‖ ^ 2)) := by rw [h2]

theorem s45_integrable_w_mul {s a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {f : EucConfig d N → ℝ} (hf : AEStronglyMeasurable f volume) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ X, |f X| ≤ K * (1 + ‖X‖)) : Integrable (fun X => s45_w s a β ε X * f X) := by
  obtain ⟨Cw, hCw0, hCw⟩ := s45_w_le (d := d) (N := N) (s := s) ha hβ hN
  refine s45_integrable_of_dom (c := β * a / 4) (by positivity)
    ((s45_measurable_w s a β ε).aestronglyMeasurable.mul hf) (K := Cw * K) (by positivity) fun X => ?_
  rw [abs_mul, abs_of_pos (s45_w_pos s a β ε X)]
  calc s45_w s a β ε X * |f X| ≤ (Cw * Real.exp (-((β * a / 4) * ‖X‖ ^ 2))) * (K * (1 + ‖X‖)) :=
        mul_le_mul (hCw ε hε hε1 X) (hK X) (abs_nonneg _) (by positivity)
    _ = Cw * K * (1 + ‖X‖) * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) := by ring

/-! ### The force and `dH_ε` -/

theorem s45_F_norm_le {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (z : Euc d) :
    ‖s45_F s ε z‖ ≤ movtr_sigma s * ε ^ (-s - 1) := by
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  by_cases h0 : s45_F s ε z = 0
  · rw [h0, norm_zero]
    exact mul_nonneg hσ (Real.rpow_nonneg hε.le _)
  · have hn : 0 < ‖s45_F s ε z‖ := norm_pos_iff.2 h0
    set e : Euc d := ‖s45_F s ε z‖⁻¹ • s45_F s ε z with he
    have hen : ‖e‖ ≤ 1 := by
      rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hin : inner ℝ (s45_F s ε z) e = ‖s45_F s ε z‖ := by
      rw [he, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hd : movtr_dEps d s ε e z = inner ℝ (s45_F s ε z) e := by
      unfold movtr_dEps s45_F
      rw [inner_smul_left]
      simp
    have := movtr_dEps_abs_le hs0 hε e z hen
    rw [hd, hin, abs_of_pos hn] at this
    exact this

theorem s45_dH_apply (s a ε : ℝ) (X e : EucConfig d N) :
    s45_dH s a ε X e = ∑ i, a * ⟪X i, e i⟫ + (1 / (N : ℝ)) *
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), ⟪s45_F s ε (X i - X j), e i - e j⟫ := by
  simp [s45_dH, inner_sub_right]

theorem s45_dH_le {s : ℝ} (hs0 : 0 ≤ s) {a : ℝ} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 < ε)
    (X e : EucConfig d N) :
    |s45_dH s a ε X e| ≤ (a * N * ‖X‖ + 2 * N * (movtr_sigma s * ε ^ (-s - 1))) * ‖e‖ := by
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  have hB0 : 0 ≤ movtr_sigma s * ε ^ (-s - 1) := mul_nonneg hσ (Real.rpow_nonneg hε.le _)
  rw [s45_dH_apply]
  have h1 : |∑ i, a * ⟪X i, e i⟫| ≤ a * N * ‖X‖ * ‖e‖ := by
    calc |∑ i, a * ⟪X i, e i⟫| ≤ ∑ i, |a * ⟪X i, e i⟫| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, a * (‖X‖ * ‖e‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg ha]
          refine mul_le_mul_of_nonneg_left ?_ ha
          calc |⟪X i, e i⟫| ≤ ‖X i‖ * ‖e i‖ := abs_real_inner_le_norm _ _
            _ ≤ ‖X‖ * ‖e‖ := mul_le_mul (norm_le_pi_norm X i) (norm_le_pi_norm e i)
                (norm_nonneg _) (norm_nonneg _)
      _ = a * N * ‖X‖ * ‖e‖ := by simp; ring
  have h2 : |∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      ⟪s45_F s ε (X i - X j), e i - e j⟫| ≤
      (movtr_sigma s * ε ^ (-s - 1) * (2 * ‖e‖)) * ((N : ℝ) * N) := by
    have hterm : ∀ i j : Fin N, |⟪s45_F s ε (X i - X j), e i - e j⟫| ≤
        movtr_sigma s * ε ^ (-s - 1) * (2 * ‖e‖) := by
      intro i j
      calc |⟪s45_F s ε (X i - X j), e i - e j⟫| ≤ ‖s45_F s ε (X i - X j)‖ * ‖e i - e j‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ (movtr_sigma s * ε ^ (-s - 1)) * (2 * ‖e‖) := by
            refine mul_le_mul (s45_F_norm_le hs0 hε _) ?_ (norm_nonneg _) hB0
            calc ‖e i - e j‖ ≤ ‖e i‖ + ‖e j‖ := norm_sub_le _ _
              _ ≤ ‖e‖ + ‖e‖ := add_le_add (norm_le_pi_norm e i) (norm_le_pi_norm e j)
              _ = 2 * ‖e‖ := by ring
    calc _ ≤ ∑ i : Fin N, |∑ j ∈ Finset.univ.filter (fun j => i < j), ⟪s45_F s ε (X i - X j), e i - e j⟫| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            |⟪s45_F s ε (X i - X j), e i - e j⟫| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            movtr_sigma s * ε ^ (-s - 1) * (2 * ‖e‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = (movtr_sigma s * ε ^ (-s - 1) * (2 * ‖e‖)) *
            ∑ i : Fin N, ((Finset.univ.filter fun j : Fin N => i < j).card : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [mul_comm]
      _ ≤ (movtr_sigma s * ε ^ (-s - 1) * (2 * ‖e‖)) * ((N : ℝ) * N) :=
          mul_le_mul_of_nonneg_left (s45_card_pairs_le N) (by positivity)
  calc _ ≤ |∑ i, a * ⟪X i, e i⟫| + |(1 / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪s45_F s ε (X i - X j), e i - e j⟫| := abs_add_le _ _
    _ ≤ a * N * ‖X‖ * ‖e‖ + (1 / (N : ℝ)) * ((movtr_sigma s * ε ^ (-s - 1) * (2 * ‖e‖)) * ((N : ℝ) * N)) := by
        refine add_le_add h1 ?_
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ _ := by
        rcases Nat.eq_zero_or_pos N with hN | hN
        · subst hN; simp
        · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
          have : (1 / (N : ℝ)) * ((movtr_sigma s * ε ^ (-s - 1) * (2 * ‖e‖)) * ((N : ℝ) * N)) =
              2 * N * (movtr_sigma s * ε ^ (-s - 1)) * ‖e‖ := by field_simp
          rw [this]; nlinarith

/-! ### Integration by parts at fixed `ε` -/

theorem s45_ibp_eps {s a β : ℝ} (hs0 : 0 ≤ s) (ha : 0 < a) (hβ : 0 < β) (hN : 1 ≤ N) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {G : EucConfig d N → ℝ} (hG : Differentiable ℝ G)
    (e : EucConfig d N) {K1 K2 : ℝ} (hK1 : ∀ X, |G X| ≤ K1) (hK2 : ∀ X, |fderiv ℝ G X e| ≤ K2) :
    Integrable (fun X => s45_w s a β ε X * fderiv ℝ G X e) ∧
      Integrable (fun X => s45_w s a β ε X * (s45_dH s a ε X e * G X)) ∧
      ∫ X, s45_w s a β ε X * fderiv ℝ G X e =
        β * ∫ X, s45_w s a β ε X * (s45_dH s a ε X e * G X) := by
  have hK10 : 0 ≤ K1 := (abs_nonneg _).trans (hK1 0)
  have hK20 : 0 ≤ K2 := (abs_nonneg _).trans (hK2 0)
  have hε0 : ε ≠ 0 := hε.ne'
  set Kd : ℝ := (a * N + 2 * N * (movtr_sigma s * ε ^ (-s - 1))) * ‖e‖ with hKd
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  have hKd0 : 0 ≤ Kd := by rw [hKd]; positivity
  have hG1 : Integrable (fun X => s45_w s a β ε X * G X) :=
    s45_integrable_w_mul ha hβ hN hε hε1 hG.continuous.aestronglyMeasurable hK10
      (fun X => (hK1 X).trans (by nlinarith [norm_nonneg X]))
  have hG2 : Integrable (fun X => s45_w s a β ε X * fderiv ℝ G X e) :=
    s45_integrable_w_mul ha hβ hN hε hε1
      (measurable_fderiv_apply_const ℝ G e).aestronglyMeasurable hK20
      (fun X => (hK2 X).trans (by nlinarith [norm_nonneg X]))
  have hG3 : Integrable (fun X => s45_w s a β ε X * (s45_dH s a ε X e * G X)) := by
    refine s45_integrable_w_mul ha hβ hN hε hε1
      (((s45_measurable_dH_apply s a hε0 e).mul hG.continuous.measurable).aestronglyMeasurable)
      (K := Kd * K1) (by positivity) (fun X => ?_)
    rw [abs_mul]
    have h1 := s45_dH_le hs0 ha.le hε X e
    calc |s45_dH s a ε X e| * |G X| ≤ ((a * N * ‖X‖ + 2 * N * (movtr_sigma s * ε ^ (-s - 1))) * ‖e‖) * K1 :=
          mul_le_mul h1 (hK1 X) (abs_nonneg _) (by positivity)
      _ ≤ Kd * K1 * (1 + ‖X‖) := by
          rw [hKd]
          have hn : 0 ≤ ‖X‖ := norm_nonneg _
          have hB : 0 ≤ 2 * (N : ℝ) * (movtr_sigma s * ε ^ (-s - 1)) := by positivity
          have : (a * N * ‖X‖ + 2 * N * (movtr_sigma s * ε ^ (-s - 1))) ≤
              (a * N + 2 * N * (movtr_sigma s * ε ^ (-s - 1))) * (1 + ‖X‖) := by
            nlinarith [mul_nonneg (mul_nonneg ha.le (Nat.cast_nonneg N)) hn,
              mul_nonneg hB hn]
          calc _ ≤ ((a * N + 2 * N * (movtr_sigma s * ε ^ (-s - 1))) * (1 + ‖X‖)) * ‖e‖ * K1 := by
                gcongr
            _ = _ := by ring
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (EucConfig d N)))
    (f := s45_w s a β ε) (g := G) (v := e) ?_ hG2 hG1
    (fun X _ => (s45_differentiable_w s a β hε0) X) (fun X _ => hG X)
  · refine ⟨hG2, hG3, ?_⟩
    rw [key]
    simp_rw [s45_fderiv_w s a β hε0, smul_apply, smul_eq_mul]
    rw [← integral_neg, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    ring
  · have : (fun X => fderiv ℝ (s45_w s a β ε) X e * G X) =
        fun X => -β * (s45_w s a β ε X * (s45_dH s a ε X e * G X)) := by
      funext X
      rw [s45_fderiv_w s a β hε0, smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact hG3.const_mul _

end S45

end
