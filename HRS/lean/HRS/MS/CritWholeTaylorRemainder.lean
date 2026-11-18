import HRS.MS.CritWholePoleProduct
import HRS.MS.CritWholeTailProduct
import HRS.Equilibrium.TaylorAux8

/-!
# S8.1 XS, TT07: the integrated Taylor remainder in `L²(pole law)`

Whole-space port of `HRS.integrated_taylor_remainder_proof`: pointwise `H(v) ≤ e^K v_H² + (v - v_H)` gives the envelope
`B = TT05 + TT06` (at `H = 2ν⁵`, `ν = N^{1/8}`), the TT04 transfer `taylor_transfer_wrap` gives `∫ B² d pole ≤ C N^{-9/8}`,
and the real remainder `∫ f H(v) dμ` is read off from the (finite) extended integral.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr HRS.TaylorAux

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

theorem s81b_field_meas (hd : 1 ≤ d) (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1)) :
    Measurable (fun p : EucConfig d (N - 1) × Euc d => field D N i p.1 p.2) := by
  unfold field
  refine Measurable.sub ?_ ?_
  · refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _
    exact (s81b_critG_meas hd).comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
  · exact ((s81b_conv_meas hd D).comp measurable_snd).const_mul _

theorem s81b_pointwise (hd : 2 ≤ d) (D : Data d M βm βp) (hβm : 0 < βm) (N : ℕ) (hN : 2 ≤ N)
    (H : ℝ) (hH : 2 ≤ H) (i : Fin (N - 1)) (φ f : Euc d → ℝ)
    (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y) (hfφ : ∀ y, f y ≤ φ y) (Y : EucConfig d (N - 1)) :
    ∫⁻ y, ENNReal.ofReal (f y * taylorH (field D N i Y y)) ∂(mu D) ≤
      quadraticEnvelope D N i H φ Y + ENNReal.ofReal (D.beta / N) *
        ∑ j ∈ Finset.univ.erase i, tailConv D φ H (Y j) := by
  have hd1 : 1 ≤ d := by omega
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : (0 : ℝ) ≤ D.beta / N := by positivity
  have hK0 : 0 ≤ fieldLowerBound d M βp := by
    unfold fieldLowerBound
    have : 0 ≤ βp := (hβm.trans_le D.beta_mem.1).le.trans D.beta_mem.2
    positivity
  have hprob : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  set μ : Measure (Euc d) := mu D with hμdef
  set lam : ℝ := D.beta / N with hlamdef
  set K : ℝ := fieldLowerBound d M βp with hKdef
  set J : Finset (Fin (N - 1)) := Finset.univ.erase i with hJ
  have hGm := s81b_tailG_meas hd1 H
  have hvm : Measurable fun y => fieldH D N i H Y y :=
    Measurable.of_uncurry_left (f := fun (Y : EucConfig d (N - 1)) (y : Euc d) =>
      fieldH D N i H Y y) (s81b_fieldH_meas hd1 D N i H)
  have hreal : ∀ y, f y * taylorH (field D N i Y y) ≤
      φ y * (Real.exp K * fieldH D N i H Y y ^ 2) + φ y * (lam * ∑ j ∈ J, tailG d H (y - Y j)) := by
    intro y
    set v := field D N i Y y with hv
    set w := fieldH D N i H Y y with hw
    have hvw : v - w = lam * ∑ j ∈ J, tailG d H (y - Y j) := by
      simp only [hv, hw, field, fieldH, tailG, hlamdef, hJ]
      rw [Finset.sum_sub_distrib]
      ring
    have hGnn : 0 ≤ ∑ j ∈ J, tailG d H (y - Y j) :=
      Finset.sum_nonneg fun j _ => s81b_tailG_nonneg hd1 H (by linarith) _
    have hwv : w ≤ v := by
      have : 0 ≤ lam * ∑ j ∈ J, tailG d H (y - Y j) := mul_nonneg hlam hGnn
      linarith
    have h1 : taylorH v ≤ Real.exp K * w ^ 2 + lam * ∑ j ∈ J, tailG d H (y - Y j) := by
      have := taylor_H_lip hwv
      have h2 := taylor_H_le hK0 (s81b_field_lower hd D hβm N i H (by linarith) Y y)
      linarith
    calc f y * taylorH v ≤ φ y * taylorH v :=
          mul_le_mul_of_nonneg_right (hfφ y) (taylor_H_nonneg v)
      _ ≤ φ y * (Real.exp K * w ^ 2 + lam * ∑ j ∈ J, tailG d H (y - Y j)) :=
          mul_le_mul_of_nonneg_left h1 (hφ0 y)
      _ = _ := by ring
  have hmeas1 : Measurable fun y => ENNReal.ofReal (φ y) *
      ENNReal.ofReal (Real.exp K * fieldH D N i H Y y ^ 2) :=
    hφm.ennreal_ofReal.mul ((measurable_const.mul (hvm.pow_const 2)).ennreal_ofReal)
  have hpt : ∀ y, ENNReal.ofReal (f y * taylorH (field D N i Y y)) ≤
      ENNReal.ofReal (φ y) * ENNReal.ofReal (Real.exp K * fieldH D N i H Y y ^ 2) +
        ENNReal.ofReal lam * ∑ j ∈ J, (ENNReal.ofReal (φ y) * ENNReal.ofReal (tailG d H (y - Y j))) := by
    intro y
    refine (ENNReal.ofReal_le_ofReal (hreal y)).trans ?_
    have hGnn : 0 ≤ ∑ j ∈ J, tailG d H (y - Y j) :=
      Finset.sum_nonneg fun j _ => s81b_tailG_nonneg hd1 H (by linarith) _
    rw [ENNReal.ofReal_add (mul_nonneg (hφ0 y) (by positivity)) (mul_nonneg (hφ0 y) (mul_nonneg hlam hGnn)),
      ENNReal.ofReal_mul (hφ0 y), ENNReal.ofReal_mul (hφ0 y), ENNReal.ofReal_mul hlam,
      ENNReal.ofReal_sum_of_nonneg fun j _ => s81b_tailG_nonneg hd1 H (by linarith) _]
    refine add_le_add le_rfl (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc ∫⁻ y, ENNReal.ofReal (f y * taylorH (field D N i Y y)) ∂μ
      ≤ ∫⁻ y, (ENNReal.ofReal (φ y) * ENNReal.ofReal (Real.exp K * fieldH D N i H Y y ^ 2) +
          ENNReal.ofReal lam * ∑ j ∈ J, (ENNReal.ofReal (φ y) *
            ENNReal.ofReal (tailG d H (y - Y j)))) ∂μ := lintegral_mono hpt
    _ = (∫⁻ y, ENNReal.ofReal (φ y) * ENNReal.ofReal (Real.exp K * fieldH D N i H Y y ^ 2) ∂μ) +
        ∫⁻ y, ENNReal.ofReal lam * ∑ j ∈ J, (ENNReal.ofReal (φ y) *
            ENNReal.ofReal (tailG d H (y - Y j))) ∂μ := lintegral_add_left hmeas1 _
    _ = _ := by
        congr 1
        have hmT : ∀ j : Fin (N - 1), Measurable fun y => ENNReal.ofReal (φ y) *
            ENNReal.ofReal (tailG d H (y - Y j)) := fun j =>
          hφm.ennreal_ofReal.mul (hGm.comp (measurable_id.sub measurable_const)).ennreal_ofReal
        rw [lintegral_const_mul (f := fun y => ∑ j ∈ J, (ENNReal.ofReal (φ y) *
            ENNReal.ofReal (tailG d H (y - Y j)))) _ (Finset.measurable_sum _ fun j _ => hmT j),
          lintegral_finset_sum _ fun j _ => hmT j]
        rfl

set_option maxHeartbeats 1600000 in
theorem s81b_integrated_taylor_remainder (hd : 2 ≤ d) (M βm βp : ℝ)
    (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ i : Fin (N - 1), ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ φ ∈ tests d x, ∀ f : Euc d → ℝ, Measurable f →
      (∀ y, 0 ≤ f y ∧ f y ≤ φ y) →
        (∀ᵐ Y ∂(pole D N x t),
          Integrable (fun y => f y * taylorH (field D N i Y y)) (mu D)) ∧
        Measurable (remainder D N i f) ∧
        MemLp (remainder D N i f) 2 (pole D N x t) ∧
        eLpNorm (remainder D N i f) 2 (pole D N x t) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(9 / 16 : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨q, hq2, C0, hC00, hC0⟩ := s81b_pole_product_transfer hd M βm βp hβm hβ
  obtain ⟨CB1, hCB10, hCB1⟩ := s81b_truncated_quadratic_product hd M βm βp hβm hβ q (by omega)
  obtain ⟨Ct, hCt0, hCt⟩ := s81b_integrated_tail_product hd M βm βp hβm hβ q (by omega)
  have hβp : 0 < βp := hβm.trans_le hβ
  set Cb : ℝ := 12 * CB1 + Ct with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨C0 * Cb, by positivity, fun D N hN i x t ht φ hφ f hfm hf => ?_⟩
  have hprob : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set ν : ℝ := taylorNu N with hν
  have hν1 : 1 ≤ ν := one_le_taylorNu N (by omega)
  have hν8 : ν ^ 8 = N := taylorNu_pow8 N
  have hν0 : 0 < ν := by linarith
  set H : ℝ := 2 * ν ^ 5 with hHdef
  have hH : 2 ≤ H := by
    have : 1 ≤ ν ^ 5 := one_le_pow₀ hν1
    rw [hHdef]; linarith
  have hp0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
  have hp1 : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * q)
  set μ : Measure (Euc d) := mu D with hμdef
  set P : Measure (EucConfig d (N - 1)) := pole D N x t with hP
  set Pm : Measure (EucConfig d (N - 1)) := product D (N - 1) with hPm
  have hgm := s81b_critG_meas hd1
  have hφm : Measurable φ := by
    rcases hφ with rfl | rfl
    · exact measurable_const
    · exact hgm.comp (measurable_const.sub measurable_id)
  have hφ0 : ∀ y, 0 ≤ φ y := by
    rcases hφ with rfl | rfl
    · intro y; exact zero_le_one
    · intro y; show 0 ≤ critG d (x - y); exact s81b_critG_nonneg hd1 _
  -- the envelope
  set B : EucConfig d (N - 1) → ℝ≥0∞ := fun Y => quadraticEnvelope D N i H φ Y +
    ENNReal.ofReal (D.beta / N) * ∑ j ∈ Finset.univ.erase i, tailConv D φ H (Y j) with hB
  obtain ⟨hEm, hB1⟩ := hCB1 D N hN i H hH x φ hφ
  obtain ⟨hTm, hB2⟩ := hCt D N hN i x φ hφ
  have hB1' : taylorLp Pm ((2 * q : ℕ) : ℝ) (quadraticEnvelope D N i H φ) ≤
      ENNReal.ofReal (CB1 * (12 * (ν ^ 5)⁻¹)) := by
    refine hB1.trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left ?_ hCB10
    have := taylor_theta_le hν1
    rw [hν8] at this
    simpa [hHdef] using this
  have hB2' : taylorLp Pm ((2 * q : ℕ) : ℝ) (fun Y => ENNReal.ofReal (D.beta / N) *
      ∑ j ∈ Finset.univ.erase i, tailConv D φ H (Y j)) ≤ ENNReal.ofReal (Ct * (ν ^ 5)⁻¹) := by
    simpa [hHdef, hν] using hB2
  have hBm : Measurable B := by
    refine hEm.add ?_
    exact (Finset.measurable_sum _ fun j _ => hTm.comp (measurable_pi_apply j)).const_mul _
  have hLp : taylorLp Pm ((2 * q : ℕ) : ℝ) B ≤ ENNReal.ofReal (Cb * (ν ^ 5)⁻¹) := by
    refine (taylorLp_add hp1 hEm.aemeasurable
      ((Finset.measurable_sum _ fun j _ => hTm.comp (measurable_pi_apply j)).const_mul _).aemeasurable).trans ?_
    refine (add_le_add hB1' hB2').trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hCb]; ring))
  have hb : ∫⁻ a, B a ^ (2 * q) ∂Pm ≤ (ENNReal.ofReal (Cb * (ν ^ 5)⁻¹)) ^ (2 * q) := by
    have h1 := taylorLp_rpow hp0 B (P := Pm)
    have h3 := ENNReal.rpow_le_rpow hLp hp0.le
    rw [h1] at h3
    simp only [ENNReal.rpow_natCast] at h3
    exact h3
  have hwrap := taylor_transfer_wrap P Pm q (by omega) (ENNReal.ofReal (C0 * (N : ℝ) ^ ((1 : ℝ) / 16)))
    (fun Y hY => hC0 D N hN x t ht Y hY) B hBm _ hb
  -- the constant
  have hnu : (N : ℝ) ^ ((1 : ℝ) / 16) * (ν ^ 5)⁻¹ = (N : ℝ) ^ (-(9 / 16 : ℝ)) := by
    have : ν ^ 5 = (N : ℝ) ^ ((5 : ℝ) / 8) := by
      rw [hν]; unfold taylorNu
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    rw [this, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; norm_num
  have hX : ENNReal.ofReal (C0 * (N : ℝ) ^ ((1 : ℝ) / 16)) * ENNReal.ofReal (Cb * (ν ^ 5)⁻¹) =
      ENNReal.ofReal (C0 * Cb * (N : ℝ) ^ (-(9 / 16 : ℝ))) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← hnu]
    congr 1; ring
  rw [hX] at hwrap
  -- pointwise domination of the extended remainder
  set E : EucConfig d (N - 1) → ℝ≥0∞ := fun Y =>
    ∫⁻ y, ENNReal.ofReal (f y * taylorH (field D N i Y y)) ∂μ with hE
  have hEB : ∀ Y, E Y ≤ B Y := fun Y =>
    s81b_pointwise hd D hβm N hN H hH i φ f hφm hφ0 (fun y => (hf y).2) Y
  have hHm : Measurable taylorH := by
    unfold taylorH
    exact ((Real.measurable_exp.comp measurable_neg).sub_const 1).add measurable_id
  have hEmeas : Measurable E := by
    refine Measurable.lintegral_prod_right' (f := fun p : EucConfig d (N - 1) × Euc d =>
      ENNReal.ofReal (f p.2 * taylorH (field D N i p.1 p.2))) ?_
    exact (((hfm.comp measurable_snd).mul
      (hHm.comp (s81b_field_meas hd1 D N i)))).ennreal_ofReal
  have hE2 : ∫⁻ Y, E Y ^ 2 ∂P ≤ ENNReal.ofReal (C0 * Cb * (N : ℝ) ^ (-(9 / 16 : ℝ))) ^ 2 :=
    (lintegral_mono fun Y => pow_le_pow_left' (hEB Y) 2).trans hwrap
  have hg0 : ∀ Y y, 0 ≤ f y * taylorH (field D N i Y y) := fun Y y =>
    mul_nonneg (hf y).1 (taylor_H_nonneg _)
  have hgm : ∀ Y, Measurable fun y => f y * taylorH (field D N i Y y) := fun Y =>
    hfm.mul (hHm.comp (Measurable.of_uncurry_left (s81b_field_meas hd1 D N i)))
  have hRE : ∀ Y, remainder D N i f Y = (E Y).toReal := fun Y => by
    unfold remainder
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hg0 Y))
      (hgm Y).aestronglyMeasurable
  have hRmeas : Measurable (remainder D N i f) := by
    have : remainder D N i f = fun Y => (E Y).toReal := funext hRE
    rw [this]; exact hEmeas.ennreal_toReal
  have hEfin : ∀ᵐ Y ∂P, E Y < ⊤ := by
    have hfin : ∫⁻ Y, E Y ^ 2 ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hE2
    filter_upwards [ae_lt_top (hEmeas.pow_const 2) hfin] with Y hY
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at hY
    simp at hY
  refine ⟨?_, hRmeas, ?_⟩
  · filter_upwards [hEfin] with Y hY
    have := Q34.integrable_of_lintegral_le (μ := μ) (f := fun y => f y * taylorH (field D N i Y y))
      (hgm Y) (hg0 Y) (c := (E Y).toReal) ENNReal.toReal_nonneg
      (by rw [ENNReal.ofReal_toReal hY.ne])
    exact this.1
  · have hn : eLpNorm (remainder D N i f) 2 P ≤ ENNReal.ofReal (C0 * Cb * (N : ℝ) ^ (-(9 / 16 : ℝ))) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hRmeas.aestronglyMeasurable]
      simp only [ENNReal.toReal_ofNat]
      have h1 : ∫⁻ Y, ‖remainder D N i f Y‖ₑ ^ (2 : ℝ) ∂P ≤ ∫⁻ Y, E Y ^ 2 ∂P := by
        refine lintegral_mono fun Y => ?_
        rw [ENNReal.rpow_two]
        refine pow_le_pow_left' ?_ 2
        rw [hRE Y, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.ofReal_toReal_le
      calc (∫⁻ Y, ‖remainder D N i f Y‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
          ≤ (ENNReal.ofReal (C0 * Cb * (N : ℝ) ^ (-(9 / 16 : ℝ))) ^ 2) ^ (1 / (2 : ℝ)) :=
            ENNReal.rpow_le_rpow (h1.trans hE2) (by norm_num)
        _ = _ := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    refine ⟨?_, hn⟩
    exact lt_of_le_of_lt hn ENNReal.ofReal_lt_top

end HRS.Whole.S81b
