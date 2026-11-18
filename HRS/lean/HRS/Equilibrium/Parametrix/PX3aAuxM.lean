import HRS.Equilibrium.Parametrix.PX3aAuxL

/-!
# Packet PX3a auxiliaries M: class transfer for source derivatives
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

namespace SrcCls

variable {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}

lemma iteratedFDeriv_far_zero (h : SrcCls d σ b m A g) {q : Euc d × Euc d} (hq : 1 / 16 < ‖q.2‖) (k : ℕ) :
    iteratedFDeriv ℝ k g q = 0 := by
  have : g =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds hq]
      with p hp using h.supp p.1 p.2 hp
  rw [(this.iteratedFDeriv ℝ k).eq_of_nhds]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · ext v; simp [iteratedFDeriv_zero_eq_comp]
  · have := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d × Euc d) (by omega : k ≠ 0) (0 : ℝ)
    exact congrFun this q

lemma mixedDeriv_far_zero (h : SrcCls d σ b m A g) {a c : ℕ} (hac : a + c ≤ m) {X w : Euc d}
    (hw : 1 / 16 < ‖w‖) : ‖mixedDeriv a c g X w‖ ≤ 0 := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hw)
  have hT : TB g (X, w) a c 0 := fun u v => by
    rw [h.iteratedFDeriv_far_zero (q := (X, w)) hw]; simp
  exact norm_le_of_tb isOpen_ne_snd (h.smooth.of_le (by exact_mod_cast hac)) (show (X, w) ∈ {p : Euc d × Euc d | p.2 ≠ 0} from hw0)
    le_rfl hT

lemma mono_sigma (h : SrcCls d σ b m A g) (hA : 0 ≤ A) {σ' : ℝ} (hσ : σ ≤ σ') : SrcCls d σ' b m A g where
  smooth := h.smooth
  supp := h.supp
  bound a c hac X w hw := by
    by_cases hw1 : ‖w‖ ≤ 1 / 16
    · refine (h.bound a c hac X w hw).trans ?_
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have h1 : ‖w‖ ^ (-(σ + c)) ≤ ‖w‖ ^ (-(σ' + c)) :=
        Real.rpow_le_rpow_of_exponent_ge hwpos (by linarith) (by linarith)
      have h2 : 0 ≤ (1 + |Real.log ‖w‖|) ^ b := pow_nonneg (by positivity) _
      exact mul_le_mul_of_nonneg_left (by nlinarith) hA
    · have := h.mixedDeriv_far_zero hac (X := X) (not_le.mp hw1)
      refine this.trans ?_
      have : 0 ≤ ‖w‖ ^ (-(σ' + c)) * (1 + |Real.log ‖w‖|) ^ b :=
        mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
      exact mul_nonneg hA (by linarith)

lemma dirD_snd (h : SrcCls d σ b (m + 1) A g) (hA : 0 ≤ A) (e : Euc d) :
    SrcCls d (σ + 1) b m (A * ‖e‖) (dirD ((0 : Euc d), e) g) where
  smooth := contDiffOn_dirD isOpen_ne_snd h.smooth ((0 : Euc d), e)
  supp X w hw := by
    have : g =ᶠ[𝓝 (X, w)] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
        (show (1 / 16 : ℝ) < ‖((X, w) : Euc d × Euc d).2‖ from hw)] with p hp using h.supp p.1 p.2 hp
    simp only [dirD]
    rw [this.fderiv_eq]
    simp
  bound a c hac X w hw := by
    have hq : (X, w) ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hw
    have hTB : TB g (X, w) a (c + 1) (A * (1 + ‖w‖ ^ (-(σ + ((c + 1 : ℕ) : ℝ))) * (1 + |Real.log ‖w‖|) ^ b)) :=
      tb_of_norm_le isOpen_ne_snd (h.smooth.of_le (by exact_mod_cast (by omega : a + (c + 1) ≤ m + 1))) hq
        (h.bound a (c + 1) (by omega) X w hw)
    have hd1 := tb_dirD_snd (i := a) (j := c) e
      ((h.smooth.contDiffAt (isOpen_ne_snd.mem_nhds hq)).of_le (by exact_mod_cast (by omega : a + c + 1 ≤ m + 1))) hTB
    have hpos : 0 ≤ ‖w‖ ^ (-(σ + ((c + 1 : ℕ) : ℝ))) * (1 + |Real.log ‖w‖|) ^ b :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
    have := norm_le_of_tb isOpen_ne_snd (contDiffOn_dirD isOpen_ne_snd h.smooth ((0 : Euc d), e) |>.of_le
      (by exact_mod_cast (by omega : a + c ≤ m))) hq
      (mul_nonneg (mul_nonneg hA (by linarith)) (norm_nonneg e)) hd1
    have ee : -(σ + ((c + 1 : ℕ) : ℝ)) = -(σ + 1 + c) := by push_cast; ring
    rw [ee] at this
    refine this.trans (le_of_eq ?_)
    ring

end SrcCls

lemma zeta_fderiv_bound : ∃ S : ℝ, 0 ≤ S ∧ ∀ ε : ℝ, 0 < ε → ∀ w : Euc d,
    ‖fderiv ℝ (px3a_zeta d ε) w‖ ≤ S * ε⁻¹ ∧
      ((‖w‖ < ε / 2 ∨ ε < ‖w‖) → fderiv ℝ (px3a_zeta d ε) w = 0) := by
  obtain ⟨S, hS0, hS⟩ := px3a_zeta_deriv_bound (d := d) 1
  refine ⟨S, hS0, fun ε hε w => ⟨?_, ?_⟩⟩
  · have := hS ε hε 1 le_rfl w
    rw [norm_iteratedFDeriv_one] at this
    simpa using this
  · rintro (h | h)
    · have : px3a_zeta d ε =ᶠ[𝓝 w] fun _ => (1 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h] with u hu
        exact px3a_zeta_eq_one hε hu.le
      rw [this.fderiv_eq]; simp
    · have : px3a_zeta d ε =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h] with u hu
        exact px3a_zeta_eq_zero hε hu.le
      rw [this.fderiv_eq]; simp

lemma tendsto_rpow_lw {κ : ℝ} (hκ : 0 < κ) (b : ℕ) :
    Tendsto (fun ε : ℝ => ε ^ κ * lw ε ^ b) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := rpow_log_pow_le (κ / 2) (by linarith) b
  have h1 : Tendsto (fun ε : ℝ => ε ^ (κ / 2)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const (0 : ℝ) (κ / 2) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ => C * ε ^ (κ / 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using h1.const_mul C
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hε) _) (pow_nonneg (lw_pos _).le _)
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    have := hC ε hε.1 hε.2.le
    calc ε ^ κ * lw ε ^ b = ε ^ (κ / 2) * (ε ^ (κ / 2) * lw ε ^ b) := by
          rw [← mul_assoc, ← Real.rpow_add hε.1]; congr 2; ring
      _ ≤ ε ^ (κ / 2) * C := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hε.1.le _)
      _ = C * ε ^ (κ / 2) := by ring

set_option maxHeartbeats 800000 in
lemma I2_tendsto (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < (d : ℝ) - 1) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) (X e : Euc d) {φ : Euc d → ℝ} {M : ℝ}
    (hM : ∀ y, ‖φ y‖ ≤ M) :
    Tendsto (fun ε : ℝ => ∫ w, φ w * (fderiv ℝ (px3a_zeta d ε) w e) * g (X, w)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨S, hS0, hS⟩ := zeta_fderiv_bound (d := d)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set V : ℝ := (volume (Metric.ball (0 : Euc d) 1)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set M0 : ℝ := max M 0 with hM0
  have hM00 : 0 ≤ M0 := le_max_right _ _
  set Kσ : ℝ := 1 + (2 : ℝ) ^ σ with hKσ
  have hKσ1 : 1 ≤ Kσ := by
    have : 0 ≤ (2 : ℝ) ^ σ := Real.rpow_nonneg (by norm_num) _
    linarith
  set Cc : ℝ := M0 * S * ‖e‖ * A * V with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  set U : ℝ → ℝ := fun ε => Cc * (ε ^ ((d : ℝ) - 1) + Kσ * 2 ^ b * (ε ^ ((d : ℝ) - 1 - σ) * lw ε ^ b)) with hU
  have hUt : Tendsto U (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ ((d : ℝ) - 1)) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const (0 : ℝ) ((d : ℝ) - 1) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith)] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := tendsto_rpow_lw (κ := (d : ℝ) - 1 - σ) (by linarith) b
    have h3 := (h1.add (h2.const_mul (Kσ * 2 ^ b))).const_mul Cc
    simpa [hU] using h3
  refine squeeze_zero_norm' ?_ hUt
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 16)] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  set Kε : ℝ := M0 * (S * ε⁻¹ * ‖e‖) * (A * (1 + Kσ * ε ^ (-σ) * (2 * lw ε) ^ b)) with hKε
  have hKε0 : 0 ≤ Kε := by
    have : 0 ≤ ε ^ (-σ) := Real.rpow_nonneg hε0.le _
    have := lw_pos ε
    positivity
  have hbd : ∀ᵐ w : Euc d ∂volume, ‖φ w * (fderiv ℝ (px3a_zeta d ε) w e) * g (X, w)‖ ≤
      (Metric.closedBall (0 : Euc d) ε).indicator (fun _ => Kε) w := by
    have hae : ∀ᵐ w : Euc d, w ≠ 0 := ae_ne_zero_euc (d := d) (by omega)
    filter_upwards [hae] with w hw0
    by_cases hz : ‖w‖ < ε / 2 ∨ ε < ‖w‖
    · rw [(hS ε hε0 w).2 hz]
      simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hKε0) w
    · push_neg at hz
      obtain ⟨hz1, hz2⟩ := hz
      have hwc : w ∈ Metric.closedBall (0 : Euc d) ε := by simpa using hz2
      rw [Set.indicator_of_mem hwc]
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have e1 : ‖fderiv ℝ (px3a_zeta d ε) w e‖ ≤ S * ε⁻¹ * ‖e‖ :=
        ((fderiv ℝ (px3a_zeta d ε) w).le_opNorm e).trans
          (mul_le_mul_of_nonneg_right (hS ε hε0 w).1 (norm_nonneg _))
      have e2 : ‖g (X, w)‖ ≤ A * (1 + Kσ * ε ^ (-σ) * (2 * lw ε) ^ b) := by
        have hb := h.slice_bound (Nat.zero_le m) X w hw0
        have hb' : ‖g (X, w)‖ ≤ A * (1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b) := by
          simpa [iteratedFDeriv_zero_eq_comp, lw] using hb
        refine hb'.trans (mul_le_mul_of_nonneg_left ?_ hA)
        have hp : ‖w‖ ^ (-σ) ≤ Kσ * ε ^ (-σ) := by
          have hε0' : 0 ≤ ε ^ (-σ) := Real.rpow_nonneg hε0.le _
          by_cases hs : 0 ≤ -σ
          · have : ‖w‖ ^ (-σ) ≤ ε ^ (-σ) := Real.rpow_le_rpow hwpos.le hz2 hs
            nlinarith
          · have : ‖w‖ ^ (-σ) ≤ (ε / 2) ^ (-σ) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hz1 (by linarith)
            refine this.trans ?_
            rw [Real.div_rpow hε0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            rw [div_inv_eq_mul, hKσ]
            have : (2 : ℝ) ^ σ * ε ^ (-σ) ≤ (1 + 2 ^ σ) * ε ^ (-σ) :=
              mul_le_mul_of_nonneg_right (by linarith) hε0'
            linarith [this, mul_comm (ε ^ (-σ)) ((2 : ℝ) ^ σ)]
        have hl : lw ‖w‖ ≤ 2 * lw ε := lw_le_two_mul hε0 hz1 (by linarith)
        have hl0 : 0 ≤ lw ‖w‖ := (lw_pos _).le
        have : lw ‖w‖ ^ b ≤ (2 * lw ε) ^ b := pow_le_pow_left₀ hl0 hl b
        have h5 : 0 ≤ ‖w‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg _) _
        calc 1 + ‖w‖ ^ (-σ) * lw ‖w‖ ^ b ≤ 1 + (Kσ * ε ^ (-σ)) * (2 * lw ε) ^ b := by
              gcongr
          _ = _ := by ring
      rw [norm_mul, norm_mul]
      calc ‖φ w‖ * ‖fderiv ℝ (px3a_zeta d ε) w e‖ * ‖g (X, w)‖
          ≤ M0 * (S * ε⁻¹ * ‖e‖) * (A * (1 + Kσ * ε ^ (-σ) * (2 * lw ε) ^ b)) := by
            refine mul_le_mul (mul_le_mul ((hM w).trans (le_max_left _ _)) e1 (norm_nonneg _) hM00) e2
              (norm_nonneg _) (mul_nonneg hM00 (mul_nonneg (mul_nonneg hS0 (inv_nonneg.mpr hε0.le)) (norm_nonneg _)))
        _ = Kε := rfl
  have hint : Integrable ((Metric.closedBall (0 : Euc d) ε).indicator (fun _ => Kε)) :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  refine (norm_integral_le_of_norm_le hint hbd).trans (le_of_eq ?_)
  rw [integral_indicator measurableSet_closedBall, setIntegral_const]
  have hvol : volume.real (Metric.closedBall (0 : Euc d) ε) = ε ^ d * V := by
    rw [measureReal_def, Measure.addHaar_closedBall volume (0 : Euc d) hε0.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin]
  rw [hvol, smul_eq_mul]
  have r1 : ε ^ ((d : ℝ) - 1) = ε ^ d * ε⁻¹ := by
    rw [Real.rpow_sub hε0, Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv]
  have r2 : ε ^ ((d : ℝ) - 1 - σ) = ε ^ ((d : ℝ) - 1) * ε ^ (-σ) := by
    rw [← Real.rpow_add hε0]; congr 1
  rw [hU]
  simp only []
  rw [r2, r1, hKε, hCc, mul_pow]
  ring

lemma dct_cut (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}
    (h : SrcCls d σ b m A g) (X : Euc d) {ψ : Euc d → ℝ} (hψc : Continuous ψ) {M : ℝ}
    (hψ : ∀ y, ‖ψ y‖ ≤ M) :
    Tendsto (fun ε : ℝ => ∫ w, ψ w * ((1 - px3a_zeta d ε w) * g (X, w))) (𝓝[>] 0)
      (𝓝 (∫ w, ψ w * g (X, w))) := by
  have hint : Integrable (fun w => g (X, w)) := h.slice_integrable (by omega) hσ X
  have haesm : AEStronglyMeasurable (fun w => g (X, w)) volume := h.slice_aesm (by omega) X
  refine tendsto_integral_filter_of_dominated_convergence (fun w => M * ‖g (X, w)‖) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hz : Continuous (px3a_zeta d ε) := (px3a_zeta_contDiff (d := d) ε 0).continuous
    exact (hψc.aestronglyMeasurable).mul (((continuous_const.sub hz).aestronglyMeasurable).mul haesm)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun w => ?_
    have hε0 : (0 : ℝ) < ε := hε
    have h1 := px3a_zeta_nonneg (d := d) ε w
    have h2 := px3a_zeta_le_one (d := d) ε w
    rw [norm_mul, norm_mul, Real.norm_eq_abs (1 - _), abs_of_nonneg (by linarith)]
    calc ‖ψ w‖ * ((1 - px3a_zeta d ε w) * ‖g (X, w)‖) ≤ M * (1 * ‖g (X, w)‖) := by
          refine mul_le_mul (hψ w) (mul_le_mul (by linarith) le_rfl (norm_nonneg _) zero_le_one)
            (mul_nonneg (by linarith) (norm_nonneg _)) ((norm_nonneg _).trans (hψ w))
      _ = _ := by ring
  · exact hint.norm.const_mul M
  · filter_upwards [ae_ne_zero_euc (d := d) (by omega)] with w hw0
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hwpos] with ε hε
    rw [px3a_zeta_eq_zero hε.1 hε.2.le]; simp

lemma integrable_of_bdd_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {k F : α → ℝ}
    (hk : Integrable k μ) (hF : AEStronglyMeasurable F μ) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C * ‖k x‖) :
    Integrable F μ :=
  Integrable.mono' (hk.norm.const_mul C) hF (Eventually.of_forall hC)

set_option maxHeartbeats 1600000 in
lemma ibp_cut (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < (d : ℝ) - 1) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b (m + 1) A g) (X e : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ 1 φ) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) (hM' : ∀ y, ‖fderiv ℝ φ y‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ w, φ w * ((1 - px3a_zeta d ε w) * dirD ((0 : Euc d), e) g (X, w))) -
      (∫ w, φ w * (fderiv ℝ (px3a_zeta d ε) w e) * g (X, w)) =
    -∫ w, fderiv ℝ φ w e * ((1 - px3a_zeta d ε w) * g (X, w)) := by
  have hd1 : 1 ≤ d := by omega
  have hσd : σ < d := by linarith
  have h' := h.dirD_snd hA e
  have hg_int : Integrable (fun w => g (X, w)) := h.slice_integrable hd1 hσd X
  have hg_aesm : AEStronglyMeasurable (fun w => g (X, w)) volume := h.slice_aesm hd1 X
  have hDg_int : Integrable (fun w => dirD ((0 : Euc d), e) g (X, w)) :=
    h'.slice_integrable hd1 (by linarith) X
  have hDg_aesm : AEStronglyMeasurable (fun w => dirD ((0 : Euc d), e) g (X, w)) volume :=
    h'.slice_aesm hd1 X
  obtain ⟨S, hS0, hS⟩ := zeta_fderiv_bound (d := d)
  have hζ : ContDiff ℝ ∞' (px3a_zeta d ε) := px3a_zeta_contDiff ε ⊤
  have hζc : Continuous (px3a_zeta d ε) := hζ.continuous
  have hζ' : Continuous (fun w => fderiv ℝ (px3a_zeta d ε) w e) :=
    (hζ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφc : Continuous φ := hφ.continuous
  have hφ' : Continuous (fun w => fderiv ℝ φ w e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hζ0 : ∀ w, 0 ≤ px3a_zeta d ε w := px3a_zeta_nonneg ε
  have hζ1 : ∀ w, px3a_zeta d ε w ≤ 1 := px3a_zeta_le_one ε
  have hω : ∀ w, ‖1 - px3a_zeta d ε w‖ ≤ 1 := fun w => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hζ1 w])]; linarith [hζ0 w]
  set G : Euc d → ℝ := fun w => (1 - px3a_zeta d ε w) * g (X, w) with hG
  have hGd : ∀ x, DifferentiableAt ℝ G x := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have : G =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
          (show ‖(0 : Euc d)‖ < ε / 2 by simp; positivity)] with u hu
        simp [hG, px3a_zeta_eq_one hε hu.le]
      exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq this
    · have hq : ((X, x) : Euc d × Euc d) ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hx
      have hgd : DifferentiableAt ℝ g (X, x) :=
        ((h.smooth.contDiffAt (isOpen_ne_snd.mem_nhds hq)).differentiableAt (by simp))
      have hgX : DifferentiableAt ℝ (fun w : Euc d => g (X, w)) x :=
        hgd.comp x (differentiableAt_const X |>.prodMk differentiableAt_id)
      exact ((hζ.differentiable (by simp)).differentiableAt.const_sub 1 |>.mul hgX)
  have hform : ∀ x, fderiv ℝ G x e = (1 - px3a_zeta d ε x) * dirD ((0 : Euc d), e) g (X, x) -
      fderiv ℝ (px3a_zeta d ε) x e * g (X, x) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have : G =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
          (show ‖(0 : Euc d)‖ < ε / 2 by simp; positivity)] with u hu
        simp [hG, px3a_zeta_eq_one hε hu.le]
      rw [this.fderiv_eq]
      rw [(hS ε hε 0).2 (Or.inl (by simp; positivity)), px3a_zeta_eq_one hε (by simp; positivity)]
      simp
    · have hq : ((X, x) : Euc d × Euc d) ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hx
      have hgd : DifferentiableAt ℝ g (X, x) :=
        ((h.smooth.contDiffAt (isOpen_ne_snd.mem_nhds hq)).differentiableAt (by simp))
      have hgX : DifferentiableAt ℝ (fun w : Euc d => g (X, w)) x :=
        hgd.comp x (differentiableAt_const X |>.prodMk differentiableAt_id)
      have h1 : HasFDerivAt (fun w => 1 - px3a_zeta d ε w) (-(fderiv ℝ (px3a_zeta d ε) x)) x :=
        ((hζ.differentiable (by simp)).differentiableAt.hasFDerivAt.const_sub 1)
      have h2 := h1.mul hgX.hasFDerivAt
      show (fderiv ℝ (fun w => (1 - px3a_zeta d ε w) * g (X, w)) x) e = _
      rw [(show HasFDerivAt (fun w => (1 - px3a_zeta d ε w) * g (X, w)) _ x from h2).fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
        smul_eq_mul]
      rw [show fderiv ℝ (fun w : Euc d => g (X, w)) x e = dirD ((0 : Euc d), e) g (X, x) from
        fderiv_slice_snd hgd e]
      ring
  -- integrability
  have iP1 : Integrable (fun x => φ x * ((1 - px3a_zeta d ε x) * dirD ((0 : Euc d), e) g (X, x))) :=
    integrable_of_bdd_mul hDg_int (hφc.aestronglyMeasurable.mul
      ((continuous_const.sub hζc).aestronglyMeasurable.mul hDg_aesm)) (C := M) fun x => by
      rw [norm_mul, norm_mul]
      calc ‖φ x‖ * (‖1 - px3a_zeta d ε x‖ * ‖dirD ((0 : Euc d), e) g (X, x)‖)
          ≤ M * (1 * ‖dirD ((0 : Euc d), e) g (X, x)‖) :=
            mul_le_mul (hM x) (mul_le_mul (hω x) le_rfl (norm_nonneg _) zero_le_one)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hM0
        _ = _ := by ring
  have iP2 : Integrable (fun x => φ x * (fderiv ℝ (px3a_zeta d ε) x e) * g (X, x)) :=
    integrable_of_bdd_mul hg_int ((hφc.aestronglyMeasurable.mul hζ'.aestronglyMeasurable).mul hg_aesm)
      (C := M * (S * ε⁻¹ * ‖e‖)) fun x => by
      rw [norm_mul, norm_mul]
      have e1 : ‖fderiv ℝ (px3a_zeta d ε) x e‖ ≤ S * ε⁻¹ * ‖e‖ :=
        ((fderiv ℝ (px3a_zeta d ε) x).le_opNorm e).trans
          (mul_le_mul_of_nonneg_right (hS ε hε x).1 (norm_nonneg _))
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hM x) e1 (norm_nonneg _) hM0) (norm_nonneg _)
  have hf'g : Integrable (fun x => fderiv ℝ φ x e * G x) :=
    integrable_of_bdd_mul hg_int (hφ'.aestronglyMeasurable.mul
      ((continuous_const.sub hζc).aestronglyMeasurable.mul hg_aesm)) (C := M * ‖e‖) fun x => by
      rw [norm_mul, hG]
      simp only []
      rw [norm_mul]
      have e1 : ‖fderiv ℝ φ x e‖ ≤ M * ‖e‖ :=
        ((fderiv ℝ φ x).le_opNorm e).trans (mul_le_mul_of_nonneg_right (hM' x) (norm_nonneg _))
      calc ‖fderiv ℝ φ x e‖ * (‖1 - px3a_zeta d ε x‖ * ‖g (X, x)‖)
          ≤ (M * ‖e‖) * (1 * ‖g (X, x)‖) :=
            mul_le_mul e1 (mul_le_mul (hω x) le_rfl (norm_nonneg _) zero_le_one)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hM0 (norm_nonneg _))
        _ = _ := by ring
  have hfg : Integrable (fun x => φ x * G x) :=
    integrable_of_bdd_mul hg_int (hφc.aestronglyMeasurable.mul
      ((continuous_const.sub hζc).aestronglyMeasurable.mul hg_aesm)) (C := M) fun x => by
      rw [norm_mul, hG]
      simp only []
      rw [norm_mul]
      calc ‖φ x‖ * (‖1 - px3a_zeta d ε x‖ * ‖g (X, x)‖) ≤ M * (1 * ‖g (X, x)‖) :=
            mul_le_mul (hM x) (mul_le_mul (hω x) le_rfl (norm_nonneg _) zero_le_one)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hM0
        _ = _ := by ring
  have hfg' : Integrable (fun x => φ x * fderiv ℝ G x e) := by
    have : (fun x => φ x * fderiv ℝ G x e) = fun x =>
        φ x * ((1 - px3a_zeta d ε x) * dirD ((0 : Euc d), e) g (X, x)) -
          φ x * (fderiv ℝ (px3a_zeta d ε) x e) * g (X, x) := by
      funext x; rw [hform x]; ring
    rw [this]; exact iP1.sub iP2
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := φ) (g := G) (v := e)
    hf'g hfg' hfg (fun x _ => (hφ.differentiable (by simp)) x) (fun x _ => hGd x)
  have e1 : (fun x => φ x * fderiv ℝ G x e) = fun x =>
      φ x * ((1 - px3a_zeta d ε x) * dirD ((0 : Euc d), e) g (X, x)) -
        φ x * (fderiv ℝ (px3a_zeta d ε) x e) * g (X, x) := by
    funext x; rw [hform x]; ring
  rw [e1] at key
  rw [integral_sub iP1 iP2] at key
  exact key

lemma ibp_sing (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < (d : ℝ) - 1) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b (m + 1) A g) (X e : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ 1 φ) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) (hM' : ∀ y, ‖fderiv ℝ φ y‖ ≤ M) :
    ∫ w, φ w * dirD ((0 : Euc d), e) g (X, w) = -∫ w, fderiv ℝ φ w e * g (X, w) := by
  have hσd : σ < d := by linarith
  have h' := h.dirD_snd hA e
  have hφc : Continuous φ := hφ.continuous
  have hφ' : Continuous (fun w => fderiv ℝ φ w e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hT1 := dct_cut hd (σ := σ + 1) (by linarith) h' X hφc hM
  have hT3 := dct_cut hd hσd h X hφ' (M := M * ‖e‖) (fun y =>
    ((fderiv ℝ φ y).le_opNorm e).trans (mul_le_mul_of_nonneg_right (hM' y) (norm_nonneg _)))
  have hT2 := I2_tendsto hd hσ hA h X e hM
  have hlim := hT1.sub hT2
  rw [sub_zero] at hlim
  have hlim' := hT3.neg
  refine tendsto_nhds_unique_of_eventuallyEq hlim hlim' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ibp_cut hd hσ hA h X e hφ hM hM' hε

lemma pat_zero_one (e : Euc d) :
    pat (Fin.elim0 : Fin 0 → Euc d) (fun _ : Fin 1 => e) = fun _ => ((0 : Euc d), e) := by
  funext i
  have hi : i = Fin.natAdd 0 (0 : Fin 1) := Fin.ext (by have := i.isLt; simp at this ⊢)
  rw [hi]
  unfold pat
  exact Fin.append_right _ _ _

lemma iteratedFDeriv_one_pat (f : Euc d × Euc d → ℝ) (p : Euc d × Euc d) (e : Euc d) :
    iteratedFDeriv ℝ (0 + 1) f p (pat (Fin.elim0 : Fin 0 → Euc d) (fun _ : Fin 1 => e)) =
      dirD ((0 : Euc d), e) f p := by
  rw [pat_zero_one]
  show iteratedFDeriv ℝ 1 f p _ = _
  rw [iteratedFDeriv_one_apply]
  rfl

set_option maxHeartbeats 1600000 in
lemma newtonPot_dirD (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < (d : ℝ) - 1) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b (m + 1) A g) {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 8)
    (X z : Euc d) (hz : ‖z‖ = r) (e : Euc d) :
    dirD ((0 : Euc d), e) (newtonPot d g) (X, z) = newtonPot d (dirD ((0 : Euc d), e) g) (X, z) := by
  have hσd : σ < d := by linarith
  have h' := h.dirD_snd hA e
  have hρ : 0 < r / 8 := by positivity
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, -, hs⟩ := newtonPot_split hd (σ := σ + 1) (by linarith) (mul_nonneg hA (norm_nonneg e)) h'
    hr hr1 hz (p := (X, z)) (by simp; positivity) 0
  have hL := newtonPot_pat_eq hd hσd hA h (a := 0) (c := 1) (by omega) le_rfl hr hr1 X z hz 0
    Fin.elim0 (fun _ => e)
  rw [iteratedFDeriv_one_pat] at hL
  simp only [iteratedFDeriv_one_pat] at hL
  rw [hL, hs]
  simp only [zero_mul, zero_add]
  congr 1
  -- far parts
  obtain ⟨C, hC0, hC⟩ := (Lf_hasCompactSupport (d := d) (r / 8) 0).exists_bound_iteratedFDeriv
    (Lf_contDiff hρ 0 (⊤ : ℕ∞)) 1
  set φ : Euc d → ℝ := fun w => Lf d 0 (r / 8) (z - w) with hφ
  have hLf1 : ContDiff ℝ 1 (Lf d 0 (r / 8)) := by exact_mod_cast Lf_contDiff (d := d) hρ 0 1
  have hφ1 : ContDiff ℝ 1 φ := hLf1.comp (contDiff_const.sub contDiff_id)
  have hφd : ∀ w, HasFDerivAt φ ((fderiv ℝ (Lf d 0 (r / 8)) (z - w)).comp
      (-(ContinuousLinearMap.id ℝ (Euc d)))) w := by
    intro w
    have h1 : HasFDerivAt (fun w : Euc d => z - w) (-(ContinuousLinearMap.id ℝ (Euc d))) w :=
      (hasFDerivAt_id w).const_sub z
    exact ((hLf1.differentiable (by simp)) (z - w)).hasFDerivAt.comp w h1
  have hM : ∀ y, ‖φ y‖ ≤ C := fun y => by
    have := hC 0 (by norm_num) (z - y)
    rwa [norm_iteratedFDeriv_zero] at this
  have hM' : ∀ y, ‖fderiv ℝ φ y‖ ≤ C := fun y => by
    rw [(hφd y).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := hC 1 le_rfl (z - y)
    rw [norm_iteratedFDeriv_one] at h1
    have h2 : ‖-(ContinuousLinearMap.id ℝ (Euc d))‖ ≤ 1 := by
      rw [norm_neg]; exact ContinuousLinearMap.norm_id_le
    calc _ ≤ C * 1 := mul_le_mul h1 h2 (norm_nonneg _) hC0
      _ = C := mul_one C
  have hibp := ibp_sing hd hσ hA h X e hφ1 hM hM'
  have hfd : ∀ w, fderiv ℝ φ w e = -(fderiv ℝ (Lf d 0 (r / 8)) (z - w) e) := fun w => by
    rw [(hφd w).fderiv]; simp
  simp only [hfd] at hibp
  have hae := ae_ne_zero_euc (d := d) hd1
  have e1 : ∫ w, farPsi d g 0 (r / 8) X z Fin.elim0 (fun _ : Fin 1 => e) w =
      ∫ w, fderiv ℝ (Lf d 0 (r / 8)) (z - w) e * g (X, w) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw0
    rw [farPsi_eq h hρ 0 (by omega) X z Fin.elim0 (fun _ => e) hw0]
    simp [iteratedFDeriv_one_apply, iteratedFDeriv_zero_apply]
  rw [e1]
  simp only [neg_mul, integral_neg, neg_neg] at hibp
  exact hibp.symm

end HRS.Parx

end
