import HRS.MS.CritWholeLinear
import HRS.MS.CritWholePrefactor

/-!
# S8.1 XS (S81c), CR07: the conditional singular observation `T_i = E[g(x - Y_i) | Y_{j≠i}]` under the pole law

Exact quotient identity `T - F/B = (-L_f + R_f + (F/B)(L_b - R_b))/Z_Y`, where `L` is the linear part (CR06, Fubini) and `R`
the Taylor remainder (TT07); all summands are `O(N^{-1/2})` in `L²`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

theorem s81c_quot {B F L1 R1 Lb Rb Z N : ℝ} (hB : 0 < B) (hZ : 0 < Z) (hN : N = F - L1 + R1)
    (hZe : Z = B - Lb + Rb) : N / Z - F / B = (-L1 + R1 + F / B * (Lb - Rb)) / Z := by
  rw [hN]
  have : Z = B - Lb + Rb := hZe
  field_simp
  rw [hZe]
  ring

theorem s81c_delta_le (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    deltaN d ((d : ℝ) / 2) N ≤ 3 * ((N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  set r : ℝ := Real.sqrt N with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hN0
  have hrr : r * r = N := Real.mul_self_sqrt hN0.le
  have hr1 : 1 ≤ r := by rw [hr, Real.one_le_sqrt]; exact hN1
  have hNr : (N : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / r := by
    rw [Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hNr, s81c_delta_eq hd hN]
  have hlog : Real.log N ≤ 2 * r - 2 := by
    have h1 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr0
    have h2 : Real.log N = 2 * Real.log r := by
      rw [← hrr, Real.log_mul hr0.ne' hr0.ne']; ring
    linarith
  rw [← hrr]
  have : (1 + Real.log (r * r)) ≤ 2 * r := by rw [hrr]; linarith
  rw [hrr, inv_mul_eq_div, div_le_iff₀ hN0]
  rw [← hrr]
  have h3 : 1 + Real.log ((r * r : ℝ)) ≤ 2 * r := by rw [hrr]; linarith
  calc 1 + Real.log (r * r) ≤ 2 * r := h3
    _ ≤ 3 * (1 / r) * (r * r) := by
        have : 3 * (1 / r) * (r * r) = 3 * r := by field_simp
        rw [this]; linarith

theorem s81c_sq_exp_le {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) : u ^ 2 * Real.exp (-s * u) ≤ 4 / s ^ 2 := by
  set w : ℝ := Real.exp (-(s * u / 2)) with hw
  have hw0 : 0 < w := Real.exp_pos _
  have h1 : s * u / 2 ≤ Real.exp (s * u / 2) := by linarith [Real.add_one_le_exp (s * u / 2)]
  have h2 : Real.exp (s * u / 2) * w = 1 := by rw [hw, ← Real.exp_add]; simp
  have h3 : (s / 2) * (u * w) ≤ 1 := by
    calc (s / 2) * (u * w) = (s * u / 2) * w := by ring
      _ ≤ Real.exp (s * u / 2) * w := mul_le_mul_of_nonneg_right h1 hw0.le
      _ = 1 := h2
  have h4 : u * w ≤ 2 / s := by
    rw [le_div_iff₀ hs]; nlinarith
  have h5 : Real.exp (-s * u) = w ^ 2 := by rw [hw, sq, ← Real.exp_add]; congr 1; ring
  rw [h5]
  have : u ^ 2 * w ^ 2 = (u * w) ^ 2 := by ring
  rw [this]
  calc (u * w) ^ 2 ≤ (2 / s) ^ 2 := pow_le_pow_left₀ (mul_nonneg hu hw0.le) h4 2
    _ = 4 / s ^ 2 := by rw [div_pow]; norm_num

theorem s81c_gsq_int (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 < D.beta) (N : ℕ) (hN : 0 < N) (x : Euc d) {t : ℝ}
    (ht : 0 < t) : Integrable (fun y => critG d (x - y) ^ 2 * poleFactor D N x t y) (mu D) := by
  haveI := s81c_prob D
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < t * (D.beta / N) := by positivity
  refine Integrable.of_bound (C := 4 / (t * (D.beta / N)) ^ 2)
    ((((s81b_critG_meas hd).comp (measurable_const.sub measurable_id)).pow_const 2).mul
      (s81c_poleFactor_meas hd D N x t)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
    (show 0 ≤ poleFactor D N x t y from (Real.exp_pos _).le))]
  exact s81c_sq_exp_le hs (s81b_critG_nonneg hd _)

theorem s81c_B_lower (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 < D.beta) {N : ℕ} (hN : 1 ≤ N) (x : Euc d) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-(D.beta * potentialBound d ((d : ℝ) / 2) M)) ≤ poleB D N x t := by
  haveI := s81c_prob D
  have hs0 := s81c_hs0 hd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hgx : Integrable (fun y => critG d (x - y)) (mu D) :=
    (wr13a_potential_bound hd hs0 (s81c_hsd hd) D.prob D.bound x).1
  set u : Euc d → ℝ := fun y => t * (D.beta / N) * critG d (x - y) with hu
  have hui : Integrable u (mu D) := hgx.const_mul _
  have hu0 : ∀ y, 0 ≤ u y := fun y => mul_nonneg (by have := ht.1; positivity) (wr13a_g_nonneg hs0 _)
  have hint : ∫ y, u y ∂(mu D) ≤ D.beta * potentialBound d ((d : ℝ) / 2) M := by
    rw [hu, integral_const_mul]
    have h1 : ∫ y, critG d (x - y) ∂(mu D) ≤ potentialBound d ((d : ℝ) / 2) M := s81c_conv_le hd D x
    have h2 : 0 ≤ ∫ y, critG d (x - y) ∂(mu D) := integral_nonneg fun y => wr13a_g_nonneg hs0 _
    have h3 : t * (D.beta / N) ≤ D.beta := by
      have : D.beta / N ≤ D.beta := div_le_self hβ0.le hN1
      nlinarith [ht.1, ht.2]
    have h4 := s81c_Mg_nonneg hd D
    calc t * (D.beta / N) * ∫ y, critG d (x - y) ∂(mu D) ≤ D.beta * ∫ y, critG d (x - y) ∂(mu D) :=
          mul_le_mul_of_nonneg_right h3 h2
      _ ≤ D.beta * potentialBound d ((d : ℝ) / 2) M := mul_le_mul_of_nonneg_left h1 hβ0.le
  have := wr13a_jensen (mu D) hui hu0 hint
  refine this.trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)))
  simp only [hu, poleFactor]
  congr 1; ring

theorem s81c_F_upper (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 < D.beta) (N : ℕ) (x : Euc d) {t : ℝ}
    (ht : 0 ≤ t) : poleF D N x t ≤ potentialBound d ((d : ℝ) / 2) M := by
  haveI := s81c_prob D
  have hs0 := s81c_hs0 hd
  have hgx : Integrable (fun y => critG d (x - y)) (mu D) :=
    (wr13a_potential_bound hd hs0 (s81c_hsd hd) D.prob D.bound x).1
  have hpf1 := s81c_poleFactor_le_one hd D hβ0.le N x ht
  unfold poleF
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
    mul_nonneg (wr13a_g_nonneg hs0 _) (Real.exp_pos _).le) hgx (Filter.Eventually.of_forall fun y => ?_))
    (s81c_conv_le hd D x)
  calc critG d (x - y) * poleFactor D N x t y ≤ critG d (x - y) * 1 :=
        mul_le_mul_of_nonneg_left (hpf1 y) (wr13a_g_nonneg hs0 _)
    _ = _ := mul_one _

theorem s81c_evar_le_eLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hmem : MemLp X 2 P) (c : ℝ) :
    evariance X P ≤ (eLpNorm (fun ω => X ω - c) 2 P) ^ 2 := by
  have hsq : Integrable (fun ω => (X ω - c) ^ 2) P :=
    (memLp_two_iff_integrable_sq (hX.sub_const c).aestronglyMeasurable).1 (hmem.sub (memLp_const c))
  rw [s81c_eLp_sq (hX.sub_const c) hsq, ← hmem.ofReal_variance_eq,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : variance (fun ω => X ω + (-c)) P = variance X P := variance_add_const hX.aestronglyMeasurable (-c)
  have h2 := variance_le_expectation_sq (μ := P) (X := fun ω => X ω + (-c)) (hX.add_const (-c)).aestronglyMeasurable
  rw [h1] at h2
  refine h2.trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.pow_apply]; ring

theorem s81c_taylor_split {μ : Measure (Euc d)} {f v : Euc d → ℝ} (hf : Integrable f μ)
    (hfv : Integrable (fun y => f y * v y) μ) (hfH : Integrable (fun y => f y * taylorH (v y)) μ) :
    ∫ y, f y * Real.exp (-v y) ∂μ = ∫ y, f y ∂μ - ∫ y, f y * v y ∂μ + ∫ y, f y * taylorH (v y) ∂μ := by
  rw [← integral_sub hf hfv]
  have h2 : Integrable (fun y => f y - f y * v y) μ := hf.sub hfv
  rw [← integral_add h2 hfH]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [taylorH]; ring

set_option maxHeartbeats 800000 in
theorem s81c_obs_pointwise (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 < D.beta) {m : ℕ} (i : Fin (m + 1)) (x : Euc d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {K : ℝ} (hK : D.beta * potentialBound d ((d : ℝ) / 2) M ≤ K)
    (Y : EucConfig d (m + 1))
    (hbI : Integrable (fun y => poleFactor D (m + 2) x t y * field D (m + 2) i Y y) (mu D))
    (hbE : ∫ y, poleFactor D (m + 2) x t y * field D (m + 2) i Y y ∂(mu D) =
      linearPart D (m + 2) i (poleFactor D (m + 2) x t) Y)
    (h1I : Integrable (fun y => (critG d (x - y) * poleFactor D (m + 2) x t y) * field D (m + 2) i Y y) (mu D))
    (h1E : ∫ y, (critG d (x - y) * poleFactor D (m + 2) x t y) * field D (m + 2) i Y y ∂(mu D) =
      linearPart D (m + 2) i (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) Y)
    (hbR : Integrable (fun y => poleFactor D (m + 2) x t y * taylorH (field D (m + 2) i Y y)) (mu D))
    (h1R : Integrable (fun y => (critG d (x - y) * poleFactor D (m + 2) x t y) *
      taylorH (field D (m + 2) i Y y)) (mu D)) :
    |condMean D (m + 2) i x t (fun y => critG d (x - y)) Y - poleF D (m + 2) x t / poleB D (m + 2) x t| ≤
      Real.exp K * (|linearPart D (m + 2) i (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) Y| +
        |remainder D (m + 2) i (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) Y| +
        poleF D (m + 2) x t / poleB D (m + 2) x t *
          (|linearPart D (m + 2) i (poleFactor D (m + 2) x t) Y| +
            |remainder D (m + 2) i (poleFactor D (m + 2) x t) Y|)) := by
  haveI := s81c_prob D
  have hs0 := s81c_hs0 hd
  have hpf := s81c_poleFactor_meas hd D (m + 2) x t
  have hpf0 : ∀ y, 0 ≤ poleFactor D (m + 2) x t y := fun y => (Real.exp_pos _).le
  have hpf1 := s81c_poleFactor_le_one hd D hβ0.le (m + 2) x ht.1
  have hpfI : Integrable (poleFactor D (m + 2) x t) (mu D) :=
    Integrable.of_bound (C := 1) hpf.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpf0 y)]; exact hpf1 y)
  have hgx : Integrable (fun y => critG d (x - y)) (mu D) :=
    (wr13a_potential_bound hd hs0 (s81c_hsd hd) D.prob D.bound x).1
  have hf1I : Integrable (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) (mu D) := by
    refine Integrable.mono' hgx (((s81b_critG_meas hd).comp (measurable_const.sub measurable_id)).mul hpf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wr13a_g_nonneg hs0 _) (hpf0 y))]
    calc _ ≤ critG d (x - y) * 1 := mul_le_mul_of_nonneg_left (hpf1 y) (wr13a_g_nonneg hs0 _)
      _ = _ := mul_one _
  set B := poleB D (m + 2) x t with hB
  set F := poleF D (m + 2) x t with hF
  have hBlow := s81c_B_lower hd D hβ0 (by omega : 1 ≤ m + 2) x ht
  have hB0 : 0 < B := lt_of_lt_of_le (Real.exp_pos _) hBlow
  have hF0 : 0 ≤ F := integral_nonneg fun y => mul_nonneg (wr13a_g_nonneg hs0 _) (hpf0 y)
  obtain ⟨hz1, hz2⟩ : Real.exp (-(D.beta * potentialBound d ((d : ℝ) / 2) M)) ≤ condZ D (m + 2) i x t Y ∧
      condZ D (m + 2) i x t Y ≤ Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M) := by
    rw [s81c_condZ_eq D i x t Y]; exact s81c_Z_bounds hd D hβ0.le x ht (Fin.removeNth i Y)
  have hZK : Real.exp (-K) ≤ condZ D (m + 2) i x t Y := le_trans (Real.exp_le_exp.2 (by linarith)) hz1
  have hZ0 : 0 < condZ D (m + 2) i x t Y := lt_of_lt_of_le (Real.exp_pos _) hZK
  set Lb := linearPart D (m + 2) i (poleFactor D (m + 2) x t) Y with hLb
  set Rb := remainder D (m + 2) i (poleFactor D (m + 2) x t) Y with hRb
  set L1 := linearPart D (m + 2) i (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) Y with hL1
  set R1 := remainder D (m + 2) i (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) Y with hR1
  have hNum : ∫ y, critG d (x - y) * poleFactor D (m + 2) x t y * Real.exp (-field D (m + 2) i Y y) ∂(mu D) =
      F - L1 + R1 := by
    have := s81c_taylor_split (μ := mu D) (f := fun y => critG d (x - y) * poleFactor D (m + 2) x t y)
      (v := fun y => field D (m + 2) i Y y) hf1I h1I h1R
    rw [this, h1E]; rfl
  have hDen : condZ D (m + 2) i x t Y = B - Lb + Rb := by
    have := s81c_taylor_split (μ := mu D) (f := poleFactor D (m + 2) x t)
      (v := fun y => field D (m + 2) i Y y) hpfI hbI hbR
    unfold condZ
    rw [this, hbE]; rfl
  have hT : condMean D (m + 2) i x t (fun y => critG d (x - y)) Y =
      (F - L1 + R1) / condZ D (m + 2) i x t Y := by
    unfold condMean
    rw [hNum]
  have hq := s81c_quot (B := B) (F := F) (L1 := L1) (R1 := R1) (Lb := Lb) (Rb := Rb)
    (Z := condZ D (m + 2) i x t Y) (N := F - L1 + R1) hB0 hZ0 rfl hDen
  rw [hT, hq, abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
  have h4 : 1 ≤ Real.exp K * condZ D (m + 2) i x t Y := by
    calc (1 : ℝ) = Real.exp K * Real.exp (-K) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hZK (Real.exp_pos _).le
  have hc0 : 0 ≤ F / B := div_nonneg hF0 hB0.le
  have hS : |-L1 + R1 + F / B * (Lb - Rb)| ≤ |L1| + |R1| + F / B * (|Lb| + |Rb|) := by
    calc _ ≤ |-L1 + R1| + |F / B * (Lb - Rb)| := abs_add_le _ _
      _ ≤ (|L1| + |R1|) + F / B * (|Lb| + |Rb|) := by
          refine add_le_add ?_ ?_
          · calc |-L1 + R1| ≤ |-L1| + |R1| := abs_add_le _ _
              _ = |L1| + |R1| := by rw [abs_neg]
          · rw [abs_mul, abs_of_nonneg hc0]
            exact mul_le_mul_of_nonneg_left (abs_sub _ _) hc0
  have hS0 : 0 ≤ |L1| + |R1| + F / B * (|Lb| + |Rb|) := by positivity
  calc |-L1 + R1 + F / B * (Lb - Rb)| ≤ |L1| + |R1| + F / B * (|Lb| + |Rb|) := hS
    _ ≤ (Real.exp K * condZ D (m + 2) i x t Y) * (|L1| + |R1| + F / B * (|Lb| + |Rb|)) :=
        le_mul_of_one_le_left hS0 h4
    _ = _ := by ring

theorem s81c_evar_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ} (h : X =ᵐ[P] Y) :
    evariance X P = evariance Y P := by
  have h1 : ∫ ω, X ω ∂P = ∫ ω, Y ω ∂P := integral_congr_ae h
  unfold evariance
  rw [h1]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with ω hω
  rw [hω]

theorem s81c_eLp_comb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {u1 u2 u3 u4 : Ω → ℝ} {k c : ℝ}
    (hk : 0 ≤ k) (hc : 0 ≤ c) (m1 : AEStronglyMeasurable u1 P) (m2 : AEStronglyMeasurable u2 P)
    (m3 : AEStronglyMeasurable u3 P) (m4 : AEStronglyMeasurable u4 P)
    {e1 e2 e3 e4 : ℝ≥0∞} (h1 : eLpNorm u1 2 P ≤ e1) (h2 : eLpNorm u2 2 P ≤ e2)
    (h3 : eLpNorm u3 2 P ≤ e3) (h4 : eLpNorm u4 2 P ≤ e4) :
    eLpNorm (fun Y => k * (‖u1 Y‖ + ‖u2 Y‖ + c * (‖u3 Y‖ + ‖u4 Y‖))) 2 P ≤
      ENNReal.ofReal k * (e1 + e2 + ENNReal.ofReal c * (e3 + e4)) := by
  have e : (fun Y => k * (‖u1 Y‖ + ‖u2 Y‖ + c * (‖u3 Y‖ + ‖u4 Y‖))) =
      k • (((fun Y => ‖u1 Y‖) + (fun Y => ‖u2 Y‖)) + c • ((fun Y => ‖u3 Y‖) + (fun Y => ‖u4 Y‖))) := by
    funext Y; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hk]
  refine mul_le_mul' le_rfl ?_
  refine (eLpNorm_add_le one_le_two).trans (add_le_add ?_ ?_)
  · refine (eLpNorm_add_le one_le_two).trans (add_le_add ?_ ?_)
    · rw [eLpNorm_norm _ m1]; exact h1
    · rw [eLpNorm_norm _ m2]; exact h2
  · rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
    refine mul_le_mul' le_rfl ((eLpNorm_add_le one_le_two).trans (add_le_add ?_ ?_))
    · rw [eLpNorm_norm _ m3]; exact h3
    · rw [eLpNorm_norm _ m4]; exact h4

set_option maxHeartbeats 1600000 in
theorem s81c_conditional_observation (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ i : Fin (N - 1), ∀ x : Euc d, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        MemLp (fun Y => critG d (x - Y i)) 2 (pole D N x t) ∧
        eLpNorm (fun Y => singularConditional D N i x t Y - poleF D N x t / poleB D N x t)
          2 (pole D N x t) ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) ∧
        evariance (singularConditional D N i x t) (pole D N x t) ≤ ENNReal.ofReal (C / N) ∧
        (∫⁻ Y, ‖singularConditional D N i x t Y‖ₑ ^ 2 ∂(pole D N x t)) ≤
          ENNReal.ofReal C := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C6, hC60, hC6⟩ := s81c_conditional_linear_L2 hd M βm βp hβm hβ
  obtain ⟨C7, hC70, hC7⟩ := s81b_integrated_taylor_remainder hd M βm βp hβm hβ
  set Mg : ℝ := |potentialBound d ((d : ℝ) / 2) M| with hMg
  have hβp : 0 < βp := hβm.trans_le hβ
  set K : ℝ := βp * Mg with hK
  have hK0 : 0 ≤ K := by positivity
  set cF : ℝ := Mg * Real.exp K with hcF
  have hcF0 : 0 ≤ cF := by positivity
  set CE : ℝ := Real.exp K * ((1 + cF) * (4 * C6 + C7)) with hCE
  have hCE0 : 0 ≤ CE := by positivity
  set Tb : ℝ := Real.exp (2 * K) * Mg with hTb
  refine ⟨CE + CE ^ 2 + Tb ^ 2, by positivity, fun D N hN i x t ht => ?_⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI := s81c_prob D
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have hMgnn : 0 ≤ potentialBound d ((d : ℝ) / 2) M := s81c_Mg_nonneg hd1 D
  have hMg' : potentialBound d ((d : ℝ) / 2) M = Mg := by rw [hMg, abs_of_nonneg hMgnn]
  have hDK : D.beta * potentialBound d ((d : ℝ) / 2) M ≤ K := by
    rw [hMg']; exact mul_le_mul_of_nonneg_right hββp (abs_nonneg _)
  obtain ⟨P, hP⟩ : ∃ P : Measure (EucConfig d (m + 1)), P = pole D (m + 2) x t := ⟨_, rfl⟩
  have hPprob : IsProbabilityMeasure P := by rw [hP]; exact s81c_pole_prob hd1 D hβ0.le _ x ht.1.le
  have hpf := s81c_poleFactor_meas hd1 D (m + 2) x t
  have hpf0 : ∀ y, 0 ≤ poleFactor D (m + 2) x t y := fun y => (Real.exp_pos _).le
  have hpf1 := s81c_poleFactor_le_one hd1 D hβ0.le (m + 2) x ht.1.le
  have hg := s81b_critG_meas hd1
  have hfgm : Measurable fun y : Euc d => critG d (x - y) := hg.comp (measurable_const.sub measurable_id)
  have hf1m : Measurable fun y : Euc d => critG d (x - y) * poleFactor D (m + 2) x t y := hfgm.mul hpf
  have hfg2 := s81c_gsq_int hd1 D hβ0 (m + 2) (by omega) x ht.1
  obtain ⟨hmem, hsm, hce⟩ := s81c_cond_kernel_m hd1 D hβ0.le x ht' i hfgm hfg2 P hP
  have hm : othersSigma (d := d) i ≤ MeasurableSpace.pi :=
    (measurable_pi_iff.2 fun j => measurable_pi_apply _ :
      Measurable (fun (Y : EucConfig d (m + 1)) (j : {j : Fin (m + 1) // j ≠ i}) => Y j)).comap_le
  set T : EucConfig d (m + 1) → ℝ := condMean D (m + 2) i x t (fun y => critG d (x - y)) with hT
  have hTm : Measurable T := (hsm.mono hm).measurable
  have hsing : singularConditional D (m + 2) i x t =ᵐ[pole D (m + 2) x t] T := by subst hP; exact hce
  -- T bounds
  have hTb : ∀ Y, 0 ≤ T Y ∧ T Y ≤ Tb := by
    intro Y
    have hF := s81c_F_upper hd1 D hβ0 (m + 2) x ht.1.le
    have h := s81c_Tbound hd1 D hβ0.le x ht' (Fin.removeNth i Y) hfgm (fun y => wr13a_g_nonneg (s81c_hs0 hd1) _)
      (s81c_int_f_pf hd1 D hβ0.le (m + 2) x ht.1.le hfgm hfg2)
    have hTe : T Y = s81c_Nr D (m + 2) x t (fun y => critG d (x - y)) (Fin.removeNth i Y) /
        s81c_Zr D (m + 2) x t (Fin.removeNth i Y) := s81c_condMean_eq D i x t _ Y
    rw [hTe]
    refine ⟨h.1, h.2.trans ?_⟩
    have e : ∫ y, critG d (x - y) * poleFactor D (m + 2) x t y ∂(mu D) = poleF D (m + 2) x t := rfl
    rw [e, hTb]
    have h1 : Real.exp (2 * (D.beta * potentialBound d ((d : ℝ) / 2) M)) ≤ Real.exp (2 * K) :=
      Real.exp_le_exp.2 (by linarith)
    calc _ ≤ Real.exp (2 * K) * poleF D (m + 2) x t := mul_le_mul_of_nonneg_right h1
          (integral_nonneg fun y => mul_nonneg (wr13a_g_nonneg (s81c_hs0 hd1) _) (hpf0 y))
      _ ≤ Real.exp (2 * K) * Mg := mul_le_mul_of_nonneg_left (hF.trans (le_of_eq hMg')) (Real.exp_pos _).le
  -- the L² estimate of T - F/B
  set c : ℝ := poleF D (m + 2) x t / poleB D (m + 2) x t with hc
  have hBlow := s81c_B_lower hd1 D hβ0 (by omega : 1 ≤ m + 2) x ht'
  have hB0 : 0 < poleB D (m + 2) x t := lt_of_lt_of_le (Real.exp_pos _) hBlow
  have hc0 : 0 ≤ c := div_nonneg (integral_nonneg fun y => mul_nonneg (wr13a_g_nonneg (s81c_hs0 hd1) _) (hpf0 y)) hB0.le
  have hcb : c ≤ cF := by
    rw [hc, div_le_iff₀ hB0]
    have hF := s81c_F_upper hd1 D hβ0 (m + 2) x ht.1.le
    rw [hMg'] at hF
    calc poleF D (m + 2) x t ≤ Mg := hF
      _ = cF * Real.exp (-K) := by rw [hcF, mul_assoc, ← Real.exp_add]; simp
      _ ≤ cF * poleB D (m + 2) x t := mul_le_mul_of_nonneg_left (le_trans (Real.exp_le_exp.2 (by
          rw [← hMg'] at hK; linarith)) hBlow) hcF0
  -- CR06 and TT07 inputs
  have hb6 := hC6 D (m + 2) hN i x t ht' (poleFactor D (m + 2) x t) (by simp [weightedTests])
  have h16 := hC6 D (m + 2) hN i x t ht'
    (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) (by simp [weightedTests])
  have hb7 := hC7 D (m + 2) hN i x t ht' (fun _ => 1) (by simp [tests]) (poleFactor D (m + 2) x t) hpf
    (fun y => ⟨hpf0 y, hpf1 y⟩)
  have h17 := hC7 D (m + 2) hN i x t ht' (fun y => critG d (x - y)) (by simp [tests])
    (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) hf1m
    (fun y => ⟨mul_nonneg (wr13a_g_nonneg (s81c_hs0 hd1) _) (hpf0 y),
      by simpa using mul_le_mul_of_nonneg_left (hpf1 y) (wr13a_g_nonneg (s81c_hs0 hd1) (x - y))⟩)
  -- the scale `r = N^{-1/2}`
  set N' : ℝ := ((m + 2 : ℕ) : ℝ) with hN'
  have hN'1 : (1 : ℝ) ≤ N' := by rw [hN']; exact_mod_cast (by omega : 1 ≤ m + 2)
  have hN'0 : 0 < N' := by linarith
  set r : ℝ := N' ^ (-(1 / 2 : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hN'0.le _
  have hrr : r ^ 2 = 1 / N' := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hN'0.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hδ3 := s81c_delta_le hd1 hN
  set δ : ℝ := deltaN d ((d : ℝ) / 2) (m + 2) with hδ
  have hδ3' : δ ≤ 3 * r := hδ3
  have hN9 : N' ^ (-(9 / 16 : ℝ)) ≤ r := Real.rpow_le_rpow_of_exponent_le hN'1 (by norm_num)
  have eL : ∀ {f : Euc d → ℝ}, eLpNorm (linearPart D (m + 2) i f) 2 (pole D (m + 2) x t) ≤
      ENNReal.ofReal (C6 * (r + δ)) → eLpNorm (linearPart D (m + 2) i f) 2 (pole D (m + 2) x t) ≤
      ENNReal.ofReal (4 * C6 * r) := fun h =>
    h.trans (ENNReal.ofReal_le_ofReal (by nlinarith [hC60, hr0]))
  have eR : ∀ {f : Euc d → ℝ}, eLpNorm (remainder D (m + 2) i f) 2 (pole D (m + 2) x t) ≤
      ENNReal.ofReal (C7 * N' ^ (-(9 / 16 : ℝ))) → eLpNorm (remainder D (m + 2) i f) 2 (pole D (m + 2) x t) ≤
      ENNReal.ofReal (C7 * r) := fun h =>
    h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hN9 hC70))
  obtain ⟨hbA, hbMem, hbN⟩ := hb6
  obtain ⟨h1A, h1Mem, h1N⟩ := h16
  obtain ⟨hbRI, hbRm, hbRMem, hbRN⟩ := hb7
  obtain ⟨h1RI, h1Rm, h1RMem, h1RN⟩ := h17
  have hnorm_ae : ∀ᵐ Y ∂(pole D (m + 2) x t), ‖T Y - c‖ ≤
      ‖Real.exp K * (‖linearPart D (m + 2) i (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) Y‖ +
        ‖remainder D (m + 2) i (fun y => critG d (x - y) * poleFactor D (m + 2) x t y) Y‖ +
        c * (‖linearPart D (m + 2) i (poleFactor D (m + 2) x t) Y‖ +
          ‖remainder D (m + 2) i (poleFactor D (m + 2) x t) Y‖))‖ := by
    filter_upwards [hbA, h1A, hbRI, h1RI] with Y hbA' h1A' hbRI' h1RI'
    have := s81c_obs_pointwise hd1 D hβ0 i x ht' hDK Y hbA'.1 hbA'.2 h1A'.1 h1A'.2 hbRI' h1RI'
    rw [Real.norm_eq_abs (T Y - c)]
    refine le_trans ?_ (Real.le_norm_self _)
    simpa only [Real.norm_eq_abs] using this
  have hE : eLpNorm (fun Y => T Y - c) 2 (pole D (m + 2) x t) ≤ ENNReal.ofReal (CE * r) := by
    have ha : 0 ≤ 4 * C6 * r := by positivity
    have hb : 0 ≤ C7 * r := by positivity
    have hcomb := s81c_eLp_comb (P := pole D (m + 2) x t) (k := Real.exp K) (c := c) (Real.exp_pos _).le hc0
      h1Mem.aestronglyMeasurable h1RMem.aestronglyMeasurable hbMem.aestronglyMeasurable hbRMem.aestronglyMeasurable
      (eL h1N) (eR h1RN) (eL hbN) (eR hbRN)
    refine (eLpNorm_mono_ae (hTm.sub_const c).aestronglyMeasurable hnorm_ae).trans (hcomb.trans ?_)
    have e : ENNReal.ofReal (Real.exp K) * (ENNReal.ofReal (4 * C6 * r) + ENNReal.ofReal (C7 * r) +
        ENNReal.ofReal c * (ENNReal.ofReal (4 * C6 * r) + ENNReal.ofReal (C7 * r))) =
        ENNReal.ofReal (Real.exp K * (4 * C6 * r + C7 * r + c * (4 * C6 * r + C7 * r))) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_add (add_nonneg ha hb) (mul_nonneg hc0 (add_nonneg ha hb)),
        ENNReal.ofReal_add ha hb, ENNReal.ofReal_mul hc0, ENNReal.ofReal_add ha hb]
    rw [e]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp K * (4 * C6 * r + C7 * r + c * (4 * C6 * r + C7 * r))
        = Real.exp K * ((4 * C6 * r + C7 * r) * (1 + c)) := by ring
      _ ≤ Real.exp K * ((4 * C6 * r + C7 * r) * (1 + cF)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (add_nonneg ha hb)) (Real.exp_pos _).le
      _ = CE * r := by rw [hCE]; ring
  haveI : IsProbabilityMeasure (pole D (m + 2) x t) := by rw [← hP]; exact hPprob
  have hMemT : MemLp T 2 (pole D (m + 2) x t) :=
    MemLp.of_bound hTm.aestronglyMeasurable Tb (Filter.Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hTb Y).1]; exact (hTb Y).2)
  have hsing' : ∀ f : EucConfig d (m + 1) → ℝ, True → True := fun _ _ => trivial
  have hCr : CE * r ≤ (CE + CE ^ 2 + Tb ^ 2) * r :=
    mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg CE, sq_nonneg Tb]) hr0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hP] at hmem; exact hmem
  · have e : eLpNorm (fun Y => singularConditional D (m + 2) i x t Y - poleF D (m + 2) x t / poleB D (m + 2) x t)
        2 (pole D (m + 2) x t) = eLpNorm (fun Y => T Y - c) 2 (pole D (m + 2) x t) :=
      eLpNorm_congr_ae (hsing.mono fun Y hY => by simp only [hY]; rfl)
    rw [e]
    exact hE.trans (ENNReal.ofReal_le_ofReal hCr)
  · rw [s81c_evar_congr hsing]
    refine (s81c_evar_le_eLp (pole D (m + 2) x t) hTm hMemT c).trans ?_
    calc (eLpNorm (fun Y => T Y - c) 2 (pole D (m + 2) x t)) ^ 2 ≤ (ENNReal.ofReal (CE * r)) ^ 2 :=
          pow_le_pow_left' hE 2
      _ = ENNReal.ofReal ((CE * r) ^ 2) := (ENNReal.ofReal_pow (by positivity) 2).symm
      _ ≤ ENNReal.ofReal ((CE + CE ^ 2 + Tb ^ 2) / N') := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : (CE * r) ^ 2 = CE ^ 2 / N' := by rw [mul_pow, hrr]; ring
          rw [this]
          exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg CE, sq_nonneg Tb]) hN'0.le
  · calc ∫⁻ Y, ‖singularConditional D (m + 2) i x t Y‖ₑ ^ 2 ∂(pole D (m + 2) x t) =
        ∫⁻ Y, ‖T Y‖ₑ ^ 2 ∂(pole D (m + 2) x t) :=
          lintegral_congr_ae (hsing.mono fun Y hY => by simp only [hY])
      _ ≤ ∫⁻ _Y, ENNReal.ofReal (Tb ^ 2) ∂(pole D (m + 2) x t) := by
          refine lintegral_mono fun Y => ?_
          rw [Real.enorm_of_nonneg (hTb Y).1, ← ENNReal.ofReal_pow (hTb Y).1]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hTb Y).1 (hTb Y).2 2)
      _ = ENNReal.ofReal (Tb ^ 2) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg CE, sq_nonneg Tb])

end HRS.Whole.S81b
