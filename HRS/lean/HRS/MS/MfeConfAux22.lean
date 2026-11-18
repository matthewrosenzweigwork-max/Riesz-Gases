import HRS.MS.MfeConfAux21

/-!
# S.B.1, packet F3 (part 3): bounds of `G = k * ρ`, `c`, and of the Gibbs weight (uniform in the admissible kernel)

`Sb1Rho ρ C_ρ M₁`: `ρ` is a probability density with `ρ ≤ C_ρ` and `∫ ρ|y| ≤ M₁`.  For `k ∈ Sb1KerU d s` (which contains `g` and
all truncations `k_M`), `d ≥ 1`, `0 ≤ s < d`:

* `sb1_G_abs_le`: `|G(x)| ≤ log(1+|x|) + C_G`;
* `sb1_G_upper`: `G(x) ≤ -κ log(1+|x|) + C_G`;  `sb1_G_lower`: `G(x) ≥ -κ(log(1+|x|) + M₁)`;
* `sb1_c_lower`: `c ≥ -2κ M₁`, `sb1_c_abs_le`;
* `sb1_E_le`: `exp(-βN F_N^k(X,ρ)) ≤ exp(βN(C_G + κ M₁))` for every configuration `X`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_ae_ne (hd : 1 ≤ d) (x : Euc d) : ∀ᵐ y : Euc d ∂(volume : Measure (Euc d)), y ≠ x := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  rw [ae_iff]
  simpa using measure_singleton (μ := (volume : Measure (Euc d))) x

/-- a probability density with sup bound and first moment bound -/
structure Sb1Rho (ρ : Euc d → ℝ) (Cρ M1 : ℝ) : Prop where
  dens : Whole.IsProbDensity ρ
  le : ∀ y, ρ y ≤ Cρ
  mom : Integrable (fun y => ρ y * ‖y‖)
  momle : ∫ y, ρ y * ‖y‖ ≤ M1

variable {ρ : Euc d → ℝ} {Cρ M1 : ℝ}

theorem Sb1Rho.integrable (R : Sb1Rho ρ Cρ M1) : Integrable ρ := HRS.MS.Canon.cn_integrable_of_prob ρ R.dens

theorem Sb1Rho.int_one (R : Sb1Rho ρ Cρ M1) : ∫ y, ρ y = 1 := R.dens.integral_one

theorem Sb1Rho.M1_nonneg (R : Sb1Rho ρ Cρ M1) : 0 ≤ M1 :=
  (integral_nonneg fun y => mul_nonneg (R.dens.nonneg y) (norm_nonneg y)).trans R.momle

theorem Sb1Rho.C_nonneg (R : Sb1Rho ρ Cρ M1) : 0 ≤ Cρ := (R.dens.nonneg 0).trans (R.le 0)

/-- the constant `C_G` -/
def sb1CG (d : ℕ) (s Cρ M1 : ℝ) : ℝ := M1 + 1 + 2 * (Cρ * sb1Isig d (sb1sig s) + 1)

theorem sb1CG_nonneg {s : ℝ} (R : Sb1Rho ρ Cρ M1) : 0 ≤ sb1CG d s Cρ M1 := by
  unfold sb1CG
  have := R.M1_nonneg
  have := R.C_nonneg
  have := sb1Isig_nonneg (d := d) (sb1sig s)
  positivity

theorem sb1_log_le_norm (y : Euc d) : Real.log (1 + ‖y‖) ≤ ‖y‖ := by
  have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ‖y‖)
  linarith

theorem sb1_log_nonneg (y : Euc d) : 0 ≤ Real.log (1 + ‖y‖) :=
  Real.log_nonneg (by linarith [norm_nonneg y])

theorem sb1_log_sub (x y : Euc d) :
    Real.log (1 + ‖x - y‖) ≤ Real.log (1 + ‖x‖) + Real.log (1 + ‖y‖) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  nlinarith [norm_sub_le x y, norm_nonneg x, norm_nonneg y]

theorem sb1_log_tri (x y : Euc d) :
    Real.log (1 + ‖x‖) ≤ Real.log (1 + ‖y‖) + Real.log (1 + ‖x - y‖) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  have : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    have := norm_le_norm_add_norm_sub' x y
    linarith
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y)]

/-- `Ω`-convolution bound -/
theorem sb1_Om_conv (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ0 : ∀ y, 0 ≤ ψ y) (hψm : Measurable ψ) (hψi : Integrable ψ) {Cψ : ℝ} (hψb : ∀ y, ψ y ≤ Cψ)
    (hψ1 : Integrable (fun y => ψ y * ‖y‖)) (x : Euc d) :
    Integrable (fun y => ψ y * sb1Om s (x - y)) ∧
      ∫ y, ψ y * sb1Om s (x - y) ≤ Real.log (1 + ‖x‖) * (∫ y, ψ y) + (∫ y, ψ y * ‖y‖) +
        2 * (Cψ * sb1Isig d (sb1sig s) + ∫ y, ψ y) := by
  obtain ⟨hI, hIb⟩ := sb1_conv_loc hd (sb1sig_nonneg hs0) (sb1sig_lt hd hsd) hψ0 hψm hψi hψb x
  have hlogm : Measurable (fun y : Euc d => Real.log (1 + ‖x - y‖)) :=
    Real.measurable_log.comp (measurable_const.add (measurable_norm.comp (measurable_const.sub measurable_id)))
  have hlogb : ∀ y : Euc d, Real.log (1 + ‖x - y‖) ≤ Real.log (1 + ‖x‖) + ‖y‖ := fun y =>
    (sb1_log_sub x y).trans (by linarith [sb1_log_le_norm y])
  have hbd : Integrable (fun y => Real.log (1 + ‖x‖) * ψ y + ψ y * ‖y‖) :=
    (hψi.const_mul _).add hψ1
  have hI1 : Integrable (fun y => ψ y * Real.log (1 + ‖x - y‖)) := by
    refine hbd.mono' (hψm.mul hlogm).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    have h0 := sb1_log_nonneg (x - y)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hψ0 y) h0)]
    nlinarith [hψ0 y, hlogb y]
  have e : (fun y => ψ y * sb1Om s (x - y)) =
      fun y => ψ y * Real.log (1 + ‖x - y‖) + 2 * (ψ y * ‖x - y‖ ^ (-(sb1sig s))) := by
    funext y; unfold sb1Om; ring
  rw [e]
  refine ⟨hI1.add (hI.const_mul 2), ?_⟩
  rw [integral_add hI1 (hI.const_mul 2), integral_const_mul]
  have h1 : ∫ y, ψ y * Real.log (1 + ‖x - y‖) ≤ ∫ y, (Real.log (1 + ‖x‖) * ψ y + ψ y * ‖y‖) := by
    refine integral_mono hI1 hbd fun y => ?_
    nlinarith [hψ0 y, hlogb y]
  rw [integral_add (hψi.const_mul _) hψ1, integral_const_mul] at h1
  linarith

theorem sb1_neg_log_aux {a : ℝ} (ha : 0 < a) :
    -Real.log a ≤ -Real.log (1 + a) + 1 + 2 * a ^ (-(1 / 2 : ℝ)) := by
  have hr : 0 ≤ a ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ha.le _
  by_cases h : 1 ≤ a
  · have h1 : Real.log (1 + a) ≤ Real.log 2 + Real.log a := by
      rw [← Real.log_mul (by norm_num) ha.ne']
      exact Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  · push_neg at h
    have h1 := sb1_neg_log_le ha
    have h2 : Real.log (1 + a) ≤ a := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + a)
      linarith
    linarith

theorem sb1_k_upper_pt {s : ℝ} (hs0 : 0 ≤ s) {k : Euc d → ℝ} (hk : Sb1KerU d s k) {x y : Euc d} (hxy : y ≠ x) :
    k (x - y) ≤ -(sb1kap s * Real.log (1 + ‖x‖)) + Real.log (1 + ‖y‖) + 1 + 2 * ‖x - y‖ ^ (-(sb1sig s)) := by
  have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hz
  have hu := hk.upper _ hz
  have hly := sb1_log_nonneg y
  have hr : 0 ≤ ‖x - y‖ ^ (-(sb1sig s)) := Real.rpow_nonneg hn.le _
  by_cases h0 : s = 0
  · subst h0
    simp only [sb1kap, sb1sig, ite_true, one_mul] at hr ⊢
    have h2 : k (x - y) ≤ -Real.log ‖x - y‖ := by
      refine hu.trans (le_of_eq ?_)
      unfold Whole.rieszKernel
      simp
    have h3 := sb1_neg_log_aux hn
    have h4 := sb1_log_tri x y
    linarith
  · simp only [sb1kap, sb1sig, h0, ite_false, zero_mul, neg_zero] at hr ⊢
    have h2 : k (x - y) ≤ ‖x - y‖ ^ (-s) := by
      refine hu.trans (le_of_eq ?_)
      unfold Whole.rieszKernel
      simp [h0]
    linarith

section Rho

variable {s : ℝ} {k : Euc d → ℝ}

theorem sb1_rhoG_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (R : Sb1Rho ρ Cρ M1)
    (x : Euc d) : Integrable (fun y => ρ y * k (x - y)) := by
  obtain ⟨hI, -⟩ := sb1_Om_conv hd hs0 hsd R.dens.nonneg R.dens.measurable R.integrable R.le R.mom x
  refine hI.mono' ((R.dens.measurable.mul (hk.meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable) ?_
  filter_upwards [sb1_ae_ne hd x] with y hy
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg y)]
  exact mul_le_mul_of_nonneg_left (sb1_k_abs_le hs0 hk (sub_ne_zero.2 (Ne.symm hy))) (R.dens.nonneg y)

theorem sb1_G_abs_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (R : Sb1Rho ρ Cρ M1)
    (x : Euc d) : |sb1G k ρ x| ≤ Real.log (1 + ‖x‖) + sb1CG d s Cρ M1 := by
  obtain ⟨hI, hIb⟩ := sb1_Om_conv hd hs0 hsd R.dens.nonneg R.dens.measurable R.integrable R.le R.mom x
  have h := norm_integral_le_of_norm_le hI (f := fun y => ρ y * k (x - y)) (by
    filter_upwards [sb1_ae_ne hd x] with y hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg y)]
    exact mul_le_mul_of_nonneg_left (sb1_k_abs_le hs0 hk (sub_ne_zero.2 (Ne.symm hy))) (R.dens.nonneg y))
  rw [Real.norm_eq_abs] at h
  unfold sb1G sb1CG
  rw [R.int_one] at hIb
  have := R.momle
  nlinarith [h, hIb]

theorem sb1_G_upper (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (R : Sb1Rho ρ Cρ M1)
    (x : Euc d) : sb1G k ρ x ≤ -(sb1kap s * Real.log (1 + ‖x‖)) + sb1CG d s Cρ M1 := by
  obtain ⟨hI, hIb⟩ := sb1_conv_loc hd (sb1sig_nonneg hs0) (sb1sig_lt hd hsd) R.dens.nonneg
    R.dens.measurable R.integrable R.le x
  have hlog : Integrable (fun y => ρ y * Real.log (1 + ‖y‖)) := by
    refine R.mom.mono' (R.dens.measurable.mul (Real.measurable_log.comp
      (measurable_const.add measurable_norm))).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (R.dens.nonneg y) (sb1_log_nonneg y))]
    exact mul_le_mul_of_nonneg_left (sb1_log_le_norm y) (R.dens.nonneg y)
  have hlogI : ∫ y, ρ y * Real.log (1 + ‖y‖) ≤ M1 := by
    refine (integral_mono hlog R.mom fun y => ?_).trans R.momle
    exact mul_le_mul_of_nonneg_left (sb1_log_le_norm y) (R.dens.nonneg y)
  set a := -(sb1kap s * Real.log (1 + ‖x‖)) + 1 with ha
  have hg1 : Integrable (fun y => a * ρ y + ρ y * Real.log (1 + ‖y‖)) := (R.integrable.const_mul a).add hlog
  have hg2 : Integrable (fun y => 2 * (ρ y * ‖x - y‖ ^ (-(sb1sig s)))) := hI.const_mul 2
  have hg : Integrable (fun y => a * ρ y + ρ y * Real.log (1 + ‖y‖) + 2 * (ρ y * ‖x - y‖ ^ (-(sb1sig s)))) :=
    hg1.add hg2
  have hle : ∀ᵐ y : Euc d ∂volume, ρ y * k (x - y) ≤
      a * ρ y + ρ y * Real.log (1 + ‖y‖) + 2 * (ρ y * ‖x - y‖ ^ (-(sb1sig s))) := by
    filter_upwards [sb1_ae_ne hd x] with y hy
    have := sb1_k_upper_pt hs0 hk hy
    have h0 := R.dens.nonneg y
    rw [ha]
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  have := integral_mono_ae (sb1_rhoG_int hd hs0 hsd hk R x) hg hle
  rw [integral_add hg1 hg2, integral_add (R.integrable.const_mul a) hlog, integral_const_mul,
    integral_const_mul, R.int_one] at this
  unfold sb1G sb1CG
  rw [ha] at this
  rw [R.int_one] at hIb
  nlinarith [this, hlogI, hIb]

theorem sb1_G_lower (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (R : Sb1Rho ρ Cρ M1)
    (x : Euc d) : -(sb1kap s * (Real.log (1 + ‖x‖) + M1)) ≤ sb1G k ρ x := by
  have hκ := sb1kap_nonneg s
  have hg : Integrable (fun y => -(sb1kap s * Real.log (1 + ‖x‖)) * ρ y - sb1kap s * (ρ y * ‖y‖)) :=
    (R.integrable.const_mul _).sub (R.mom.const_mul _)
  have hle : ∀ y : Euc d, -(sb1kap s * Real.log (1 + ‖x‖)) * ρ y - sb1kap s * (ρ y * ‖y‖) ≤ ρ y * k (x - y) := by
    intro y
    have h1 := hk.lower (x - y)
    have h2 := sb1_log_sub x y
    have h3 := sb1_log_le_norm y
    have h4 : sb1kap s * Real.log (1 + ‖x - y‖) ≤ sb1kap s * (Real.log (1 + ‖x‖) + ‖y‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hκ
    have h0 := R.dens.nonneg y
    nlinarith [mul_le_mul_of_nonneg_left h1 h0, mul_le_mul_of_nonneg_left h4 h0]
  have := integral_mono hg (sb1_rhoG_int hd hs0 hsd hk R x) hle
  rw [integral_sub (R.integrable.const_mul _) (R.mom.const_mul _), integral_const_mul, integral_const_mul,
    R.int_one] at this
  unfold sb1G
  have := R.momle
  nlinarith [this, mul_le_mul_of_nonneg_left R.momle hκ]

theorem sb1_G_meas (hk : Sb1KerU d s k) (R : Sb1Rho ρ Cρ M1) : Measurable (sb1G k ρ) :=
  sb1_meas_conv R.dens.measurable hk.meas

theorem sb1_rhoGc_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (R : Sb1Rho ρ Cρ M1) :
    Integrable (fun x => ρ x * sb1G k ρ x) := by
  have hb : Integrable (fun x => ρ x * ‖x‖ + sb1CG d s Cρ M1 * ρ x) := R.mom.add (R.integrable.const_mul _)
  refine hb.mono' (R.dens.measurable.mul (sb1_G_meas hk R)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have h := sb1_G_abs_le hd hs0 hsd hk R x
  have h0 := R.dens.nonneg x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  nlinarith [mul_le_mul_of_nonneg_left h h0, sb1_log_le_norm x]

theorem sb1_c_lower (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (R : Sb1Rho ρ Cρ M1) :
    -(2 * sb1kap s * M1) ≤ sb1c k ρ := by
  have hκ := sb1kap_nonneg s
  have hlog : Integrable (fun y => ρ y * Real.log (1 + ‖y‖)) := by
    refine R.mom.mono' (R.dens.measurable.mul (Real.measurable_log.comp
      (measurable_const.add measurable_norm))).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (R.dens.nonneg y) (sb1_log_nonneg y))]
    exact mul_le_mul_of_nonneg_left (sb1_log_le_norm y) (R.dens.nonneg y)
  have hlogI : ∫ y, ρ y * Real.log (1 + ‖y‖) ≤ M1 := by
    refine (integral_mono hlog R.mom fun y => ?_).trans R.momle
    exact mul_le_mul_of_nonneg_left (sb1_log_le_norm y) (R.dens.nonneg y)
  have hg : Integrable (fun x => -(sb1kap s) * (ρ x * Real.log (1 + ‖x‖)) - sb1kap s * M1 * ρ x) :=
    (hlog.const_mul _).sub (R.integrable.const_mul _)
  have hle : ∀ x : Euc d, -(sb1kap s) * (ρ x * Real.log (1 + ‖x‖)) - sb1kap s * M1 * ρ x ≤ ρ x * sb1G k ρ x := by
    intro x
    have := sb1_G_lower hd hs0 hsd hk R x
    have h0 := R.dens.nonneg x
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  have := integral_mono hg (sb1_rhoGc_int hd hs0 hsd hk R) hle
  rw [integral_sub (hlog.const_mul _) (R.integrable.const_mul _), integral_const_mul, integral_const_mul,
    R.int_one] at this
  unfold sb1c
  nlinarith [this, mul_le_mul_of_nonneg_left hlogI hκ, R.M1_nonneg]

theorem sb1_c_abs_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (R : Sb1Rho ρ Cρ M1) :
    |sb1c k ρ| ≤ M1 + sb1CG d s Cρ M1 := by
  have hb : Integrable (fun x => ρ x * ‖x‖ + sb1CG d s Cρ M1 * ρ x) := R.mom.add (R.integrable.const_mul _)
  have h := norm_integral_le_of_norm_le hb (f := fun x => ρ x * sb1G k ρ x) (Eventually.of_forall fun x => by
    have h := sb1_G_abs_le hd hs0 hsd hk R x
    have h0 := R.dens.nonneg x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    nlinarith [mul_le_mul_of_nonneg_left h h0, sb1_log_le_norm x])
  rw [Real.norm_eq_abs] at h
  rw [integral_add R.mom (R.integrable.const_mul _), integral_const_mul, R.int_one] at h
  unfold sb1c
  have := R.momle
  linarith

end Rho

/-- `∑_i ∑_{j≠i} (f_i + f_j) = 2(N-1) ∑ f` -/
theorem sb1_double_sum (f : Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, (f i + f j) = 2 * ((N : ℝ) - 1) * ∑ i, f i := by
  have h : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, (f i + f j) = ((N : ℝ) - 1) * f i + (∑ j, f j - f i) := by
    intro i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; exact i.elim0
    · rw [Nat.cast_sub hN]; push_cast; ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end HRS.MS.MfeConf
