import HRS.MC.S7FCBInt

/-!
# FC-B, part 4: the Landau kernel on the torus

`V n x = ∏_k ((1 + cos 2π x_k)/2)^n` (a positive trigonometric polynomial), `K n = V n / ∫ V n`.
Bounds: `∫ K n = 1`, `K n x ≤ (6 √n)^d exp(-4 n ‖x‖²)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

/-- `cos(2π x_k)` as a function on the torus. -/
def fcbCs (k : Fin d) (x : Torus d) : ℝ := Torus.cosMode (Pi.single k (1 : ℤ)) x
/-- `sin(2π x_k)` as a function on the torus. -/
def fcbSn (k : Fin d) (x : Torus d) : ℝ := Torus.sinMode (Pi.single k (1 : ℤ)) x

theorem fcb_dot_single (k : Fin d) (y : Euc d) : Lattice.dot (Pi.single k (1 : ℤ)) y = y k := by
  simp [Lattice.dot, Pi.single_apply]

theorem fcbCs_mk (k : Fin d) (y : Euc d) : fcbCs k (Torus.mk y) = Real.cos (2 * Real.pi * y k) := by
  rw [fcbCs, Torus.cosMode_mk, fcb_dot_single]

theorem fcbSn_mk (k : Fin d) (y : Euc d) : fcbSn k (Torus.mk y) = Real.sin (2 * Real.pi * y k) := by
  rw [fcbSn, Torus.sinMode_mk, fcb_dot_single]

theorem fcbCs_cen (k : Fin d) (x : Torus d) :
    fcbCs k x = Real.cos (2 * Real.pi * KernelGrad.centeredRep x k) := by
  conv_lhs => rw [← KernelGrad.mk_centeredRep x]
  rw [fcbCs_mk]

theorem fcbSn_cen (k : Fin d) (x : Torus d) :
    fcbSn k x = Real.sin (2 * Real.pi * KernelGrad.centeredRep x k) := by
  conv_lhs => rw [← KernelGrad.mk_centeredRep x]
  rw [fcbSn_mk]

theorem fcbCs_boxPt (k : Fin d) (y : Fin d → ℝ) :
    fcbCs k (boxPt y) = Real.cos (2 * Real.pi * y k) :=
  fcbCs_mk k (WithLp.toLp 2 y)

theorem fcbCs_sub (k : Fin d) (x x' : Torus d) :
    fcbCs k (x - x') = fcbCs k x * fcbCs k x' + fcbSn k x * fcbSn k x' := by
  have hx := KernelGrad.mk_centeredRep x
  have hx' := KernelGrad.mk_centeredRep x'
  have : x - x' = Torus.mk (KernelGrad.centeredRep x - KernelGrad.centeredRep x') := by
    rw [KernelGrad.mk_sub, hx, hx']
  rw [this, fcbCs_mk, fcbCs_cen, fcbCs_cen, fcbSn_cen, fcbSn_cen, PiLp.sub_apply, mul_sub, Real.cos_sub]

/-- the one-coordinate factor `(1 + cos 2π x_k)/2 = cos²(π x_k)`. -/
def fcbU (k : Fin d) (x : Torus d) : ℝ := (1 + fcbCs k x) / 2

theorem fcbU_eq (k : Fin d) (x : Torus d) :
    fcbU k x = Real.cos (Real.pi * KernelGrad.centeredRep x k) ^ 2 := by
  rw [fcbU, fcbCs_cen, Real.cos_sq]
  rw [show 2 * (Real.pi * KernelGrad.centeredRep x k) = 2 * Real.pi * KernelGrad.centeredRep x k by ring]
  ring

theorem fcbU_nonneg (k : Fin d) (x : Torus d) : 0 ≤ fcbU k x := by
  rw [fcbU_eq]; positivity

theorem fcbU_le_one (k : Fin d) (x : Torus d) : fcbU k x ≤ 1 := by
  rw [fcbU, fcbCs_cen]
  have := Real.cos_le_one (2 * Real.pi * KernelGrad.centeredRep x k)
  linarith

/-- the unnormalised Landau kernel -/
def fcbV (n : ℕ) (x : Torus d) : ℝ := ∏ k, fcbU k x ^ n

theorem fcbV_nonneg (n : ℕ) (x : Torus d) : 0 ≤ fcbV n x :=
  Finset.prod_nonneg fun k _ => pow_nonneg (fcbU_nonneg k x) _

theorem fcbV_le_one (n : ℕ) (x : Torus d) : fcbV n x ≤ 1 :=
  Finset.prod_le_one₀ (fun k _ => pow_nonneg (fcbU_nonneg k x) _)
    fun k _ => pow_le_one₀ (fcbU_nonneg k x) (fcbU_le_one k x)

theorem fcbCs_continuous (k : Fin d) : Continuous (fcbCs k) :=
  Complex.continuous_re.comp (Torus.continuous_mode _)

theorem fcbV_continuous (n : ℕ) : Continuous (fcbV (d := d) n) := by
  unfold fcbV fcbU
  refine continuous_finsetProd _ fun k _ => ?_
  exact (((continuous_const.add (fcbCs_continuous k)).div_const 2).pow n)

/-- scalar Gaussian bound -/
theorem fcb_cos_sq_pow_le {c : ℝ} (hc : |c| ≤ 1 / 2) (n : ℕ) :
    (Real.cos (Real.pi * c) ^ 2) ^ n ≤ Real.exp (-(4 * n * c ^ 2)) := by
  have hpc : |Real.pi * c| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, abs_nonneg c]
  have h1 := Real.cos_le_one_sub_mul_cos_sq hpc
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  have h2 : 1 - 2 / Real.pi ^ 2 * (Real.pi * c) ^ 2 = 1 - 2 * c ^ 2 := by field_simp
  rw [h2] at h1
  have h3 : 1 - 2 * c ^ 2 ≤ Real.exp (-(2 * c ^ 2)) := by
    have := Real.add_one_le_exp (-(2 * c ^ 2)); linarith
  have h4 : 0 ≤ Real.cos (Real.pi * c) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;>
      · nlinarith [abs_le.mp hc, Real.pi_pos]
  have h5 : Real.cos (Real.pi * c) ≤ Real.exp (-(2 * c ^ 2)) := h1.trans h3
  calc (Real.cos (Real.pi * c) ^ 2) ^ n ≤ (Real.exp (-(2 * c ^ 2)) ^ 2) ^ n := by gcongr
    _ = Real.exp (-(4 * n * c ^ 2)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

theorem fcbV_le_exp (hd : 0 < d) (n : ℕ) (x : Torus d) :
    fcbV n x ≤ Real.exp (-(4 * n * ‖x‖ ^ 2)) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun k => ‖x k‖)
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hnorm : ‖x‖ ≤ ‖x k‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hk i (Finset.mem_univ i)
  have hnorm' : ‖x k‖ ≤ ‖x‖ := norm_le_pi_norm x k
  have heq : ‖x k‖ = |KernelGrad.centeredRep x k| := KernelGrad.norm_apply_eq x k
  have hc : |KernelGrad.centeredRep x k| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x k
  unfold fcbV
  rw [← Finset.mul_prod_erase Finset.univ (fun i => fcbU i x ^ n) (Finset.mem_univ k)]
  have h1 : ∏ i ∈ Finset.univ.erase k, fcbU i x ^ n ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => pow_nonneg (fcbU_nonneg i x) _)
      fun i _ => pow_le_one₀ (fcbU_nonneg i x) (fcbU_le_one i x)
  have h2 : 0 ≤ ∏ i ∈ Finset.univ.erase k, fcbU i x ^ n :=
    Finset.prod_nonneg fun i _ => pow_nonneg (fcbU_nonneg i x) _
  have h3 : fcbU k x ^ n ≤ Real.exp (-(4 * n * KernelGrad.centeredRep x k ^ 2)) := by
    rw [fcbU_eq]; exact fcb_cos_sq_pow_le hc n
  have h4 : ‖x‖ = |KernelGrad.centeredRep x k| := by rw [← heq]; exact le_antisymm hnorm hnorm'
  have h5 : Real.exp (-(4 * n * KernelGrad.centeredRep x k ^ 2)) = Real.exp (-(4 * n * ‖x‖ ^ 2)) := by
    rw [h4, sq_abs]
  calc fcbU k x ^ n * ∏ i ∈ Finset.univ.erase k, fcbU i x ^ n
      ≤ fcbU k x ^ n * 1 := mul_le_mul_of_nonneg_left h1 (pow_nonneg (fcbU_nonneg k x) _)
    _ ≤ Real.exp (-(4 * n * ‖x‖ ^ 2)) := by rw [mul_one, ← h5]; exact h3

/-- lower bound for the cosine power near zero -/
theorem fcb_cos_sq_pow_ge {c : ℝ} {n : ℕ} (hn : 1 ≤ n) (hc : (n : ℝ) * c ^ 2 ≤ 1 / 16) :
    1 / 3 ≤ (Real.cos (Real.pi * c) ^ 2) ^ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc2 : c ^ 2 ≤ 1 / 16 := by nlinarith [sq_nonneg c]
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  set q : ℝ := 1 - (Real.pi * c) ^ 2 / 2 with hq
  have hq0 : 0 ≤ q := by
    rw [hq, mul_pow]; nlinarith [sq_nonneg c, Real.pi_pos]
  have hcos : q ≤ Real.cos (Real.pi * c) := Real.one_sub_sq_div_two_le_cos
  have h1 : q ^ (2 * n) ≤ (Real.cos (Real.pi * c) ^ 2) ^ n := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hq0 2) (pow_le_pow_left₀ hq0 hcos 2) n
  have h2 : 1 + ((2 * n : ℕ) : ℝ) * (-((Real.pi * c) ^ 2 / 2)) ≤ q ^ (2 * n) := by
    have := one_add_mul_le_pow (a := -((Real.pi * c) ^ 2 / 2)) (by nlinarith [sq_nonneg (Real.pi * c), mul_pow Real.pi c 2]) (2 * n)
    rw [hq]; simpa [sub_eq_add_neg] using this
  have h3 : 1 + ((2 * n : ℕ) : ℝ) * (-((Real.pi * c) ^ 2 / 2)) = 1 - n * Real.pi ^ 2 * c ^ 2 := by
    push_cast; ring
  have h4 : (n : ℝ) * Real.pi ^ 2 * c ^ 2 ≤ Real.pi ^ 2 / 16 := by
    have : (n : ℝ) * Real.pi ^ 2 * c ^ 2 = Real.pi ^ 2 * ((n : ℝ) * c ^ 2) := by ring
    rw [this]; nlinarith [sq_nonneg Real.pi]
  linarith

/-- the normalising constant -/
def fcbZ (d n : ℕ) : ℝ := ∫ x : Torus d, fcbV n x

theorem fcbZ_lower (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) :
    (1 / (6 * Real.sqrt n)) ^ d ≤ fcbZ d n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
  set a : ℝ := 1 / (4 * Real.sqrt n) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha4 : a ≤ 1 / 4 := by
    rw [ha]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsub : ball (0 : Fin d → ℝ) a ⊆ Box d := by
    intro y hy
    rw [mem_ball_zero_iff] at hy
    intro i
    have := (norm_le_pi_norm y i).trans hy.le
    rw [Real.norm_eq_abs, abs_le] at this
    simp only [mem_Ioc]
    constructor <;> linarith [this.1, this.2]
  have hcont : Continuous fun y : Fin d → ℝ => fcbV (d := d) n (boxPt y) :=
    (fcbV_continuous n).comp (continuous_boxPt d)
  have hint : IntegrableOn (fun y : Fin d → ℝ => fcbV (d := d) n (boxPt y)) (Box d) := by
    refine Measure.integrableOn_of_bounded (M := 1) (measure_Box_ne_top d) hcont.aestronglyMeasurable ?_
    exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (fcbV_nonneg _ _)]; exact fcbV_le_one _ _
  unfold fcbZ
  rw [integral_torus_box]
  have hge : ∀ y ∈ ball (0 : Fin d → ℝ) a, (1 / 3 : ℝ) ^ d ≤ fcbV (d := d) n (boxPt y) := by
    intro y hy
    rw [mem_ball_zero_iff] at hy
    unfold fcbV
    calc (1 / 3 : ℝ) ^ d = ∏ _k : Fin d, (1 / 3 : ℝ) := by simp
      _ ≤ _ := by
        refine Finset.prod_le_prod₀ (fun _ _ => by norm_num) fun k _ => ?_
        have hyk : |y k| < a := by
          have := (norm_le_pi_norm y k).trans_lt hy; rwa [Real.norm_eq_abs] at this
        have hu : fcbU k (boxPt y) = Real.cos (Real.pi * y k) ^ 2 := by
          rw [fcbU, fcbCs_boxPt, Real.cos_sq]
          rw [show 2 * (Real.pi * y k) = 2 * Real.pi * y k by ring]; ring
        rw [hu]
        refine fcb_cos_sq_pow_ge hn ?_
        have h1 : (y k) ^ 2 ≤ a ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hyk.le 2
        have h2 : a ^ 2 = 1 / (16 * n) := by
          rw [ha, div_pow, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
        calc (n : ℝ) * y k ^ 2 ≤ n * (1 / (16 * n)) := by rw [← h2]; gcongr
          _ = 1 / 16 := by field_simp
  calc (1 / (6 * Real.sqrt n)) ^ d = (1 / 3 : ℝ) ^ d * (volume (ball (0 : Fin d → ℝ) a)).toReal := by
        rw [Real.volume_pi_ball _ ha0, ENNReal.toReal_ofReal (by positivity)]
        simp only [Fintype.card_fin]
        rw [← mul_pow, ha]
        congr 1
        field_simp
        ring
    _ = ∫ y in ball (0 : Fin d → ℝ) a, (1 / 3 : ℝ) ^ d := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
    _ ≤ ∫ y in ball (0 : Fin d → ℝ) a, fcbV (d := d) n (boxPt y) := by
        refine setIntegral_mono_on (integrableOn_const (by
          rw [Real.volume_pi_ball _ ha0]; exact ENNReal.ofReal_ne_top))
          (hint.mono_set hsub) measurableSet_ball hge
    _ ≤ ∫ y in Box d, fcbV (d := d) n (boxPt y) :=
        setIntegral_mono_set hint (Eventually.of_forall fun y => fcbV_nonneg _ _)
          (Eventually.of_forall hsub)

theorem fcbZ_pos (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) : 0 < fcbZ d n :=
  lt_of_lt_of_le (by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
    positivity) (fcbZ_lower hd hn)

/-- the Landau kernel (a probability density on the torus) -/
def fcbK (d n : ℕ) (x : Torus d) : ℝ := fcbV n x / fcbZ d n

theorem fcbK_nonneg (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (x : Torus d) : 0 ≤ fcbK d n x :=
  div_nonneg (fcbV_nonneg _ _) (fcbZ_pos hd hn).le

theorem fcbK_continuous (n : ℕ) : Continuous (fcbK d n) :=
  (fcbV_continuous n).div_const _

theorem fcbK_integral (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) : ∫ x : Torus d, fcbK d n x = 1 := by
  unfold fcbK
  rw [integral_div]
  exact div_self (fcbZ_pos hd hn).ne'

theorem fcbK_integrable (n : ℕ) : Integrable (fcbK d n) :=
  (fcbK_continuous n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem fcb_invZ_le (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) : (fcbZ d n)⁻¹ ≤ (6 * Real.sqrt n) ^ d := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have h := fcbZ_lower hd hn
  have h1 : 0 < (1 / (6 * Real.sqrt n)) ^ d := by positivity
  calc (fcbZ d n)⁻¹ ≤ ((1 / (6 * Real.sqrt n)) ^ d)⁻¹ := inv_anti₀ h1 h
    _ = (6 * Real.sqrt n) ^ d := by rw [one_div, inv_pow, inv_inv]

theorem fcbK_le_sup (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (x : Torus d) :
    fcbK d n x ≤ (6 * Real.sqrt n) ^ d := by
  unfold fcbK
  rw [div_eq_mul_inv]
  calc fcbV n x * (fcbZ d n)⁻¹ ≤ 1 * (6 * Real.sqrt n) ^ d :=
        mul_le_mul (fcbV_le_one _ _) (fcb_invZ_le hd hn) (inv_nonneg.2 (fcbZ_pos hd hn).le) zero_le_one
    _ = _ := one_mul _

theorem fcbK_le (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (x : Torus d) :
    fcbK d n x ≤ (6 * Real.sqrt n) ^ d * Real.exp (-(4 * n * ‖x‖ ^ 2)) := by
  unfold fcbK
  rw [div_eq_mul_inv]
  calc fcbV n x * (fcbZ d n)⁻¹ ≤ Real.exp (-(4 * n * ‖x‖ ^ 2)) * (6 * Real.sqrt n) ^ d :=
        mul_le_mul (fcbV_le_exp hd n x) (fcb_invZ_le hd hn) (inv_nonneg.2 (fcbZ_pos hd hn).le)
          (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem fcb_tail_tendsto (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (6 * Real.sqrt n) ^ d * Real.exp (-(4 * n * δ ^ 2))) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((d : ℝ) / 2) (4 * δ ^ 2) (by positivity)
  have h2 := (h.comp tendsto_natCast_atTop_atTop).const_mul ((6 : ℝ) ^ d)
  rw [mul_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp]
  have e1 : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ d = (n : ℝ) ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; congr 1; ring
  rw [mul_pow, Real.sqrt_eq_rpow, e1, mul_assoc]
  congr 3
  ring

end HRS.MC.Sec7.FCB
