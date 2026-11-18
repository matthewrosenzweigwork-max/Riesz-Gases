import HRS.Sections.IIDAux1

/-!
# IID helper chain, part 2: smoothing along a line (see the chain plan in `IIDAux1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Taylor1D

lemma nonneg_of_deriv_nonneg_aux {f F' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (F' s) s)
    (hF' : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F' s) (h0 : f 0 = 0) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f s := by
  intro s hs
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (fun x _ => (hf x).continuousAt.continuousWithinAt)
      (fun x _ => (hf x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [(hf x).deriv]
    exact hF' x (interior_subset hx)
  have := hmono (Set.left_mem_Icc.2 zero_le_one) hs hs.1
  linarith

/-- One-dimensional Taylor estimate: if `φ''` moves at most linearly then the second-order
Taylor remainder on `[0,1]` is at most `K/6`. -/
lemma taylor_two_one_dim {φ φ1 φ2 : ℝ → ℝ} (h1 : ∀ s, HasDerivAt φ (φ1 s) s)
    (h2 : ∀ s, HasDerivAt φ1 (φ2 s) s) {K : ℝ}
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, |φ2 s - φ2 0| ≤ K * s) :
    |φ 1 - φ 0 - φ1 0 - φ2 0 / 2| ≤ K / 6 := by
  have hK0 : 0 ≤ K := by
    have := hK 1 ⟨zero_le_one, le_rfl⟩
    exact (abs_nonneg _).trans (by simpa using this)
  set u : ℝ → ℝ := fun s => φ1 s - φ1 0 - s * φ2 0 with hu
  have hud : ∀ s, HasDerivAt u (φ2 s - φ2 0) s := by
    intro s
    have := ((h2 s).sub_const (φ1 0)).sub ((hasDerivAt_id s).mul_const (φ2 0))
    convert this using 1
    · funext x; simp [hu]
    · simp
  have hA1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ K * s ^ 2 / 2 - u s := by
    refine nonneg_of_deriv_nonneg_aux (F' := fun s => K * s - (φ2 s - φ2 0)) (fun s => ?_) (fun s hs => ?_) (by simp [hu])
    · have := ((hasDerivAt_pow 2 s).const_mul K).div_const 2 |>.sub (hud s)
      convert this using 1
      simp
      ring
    · have := (abs_le.1 (hK s hs)).2
      linarith
  have hA2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ K * s ^ 2 / 2 + u s := by
    refine nonneg_of_deriv_nonneg_aux (F' := fun s => K * s + (φ2 s - φ2 0)) (fun s => ?_) (fun s hs => ?_) (by simp [hu])
    · have := ((hasDerivAt_pow 2 s).const_mul K).div_const 2 |>.add (hud s)
      convert this using 1
      simp
      ring
    · have := (abs_le.1 (hK s hs)).1
      linarith
  set g : ℝ → ℝ := fun s => φ s - φ 0 - s * φ1 0 - s ^ 2 * φ2 0 / 2 with hg
  have hgd : ∀ s, HasDerivAt g (u s) s := by
    intro s
    have := (((h1 s).sub_const (φ 0)).sub ((hasDerivAt_id s).mul_const (φ1 0))).sub
      (((hasDerivAt_pow 2 s).mul_const (φ2 0)).div_const 2)
    convert this using 1
    · funext x; simp [hg]
    · simp [hu]; ring
  have hB1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ K * s ^ 3 / 6 - g s := by
    refine nonneg_of_deriv_nonneg_aux (F' := fun s => K * s ^ 2 / 2 - u s) (fun s => ?_) (fun s hs => hA1 s hs) (by simp [hg])
    have := ((hasDerivAt_pow 3 s).const_mul K).div_const 6 |>.sub (hgd s)
    convert this using 1
    simp
    ring
  have hB2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ K * s ^ 3 / 6 + g s := by
    refine nonneg_of_deriv_nonneg_aux (F' := fun s => K * s ^ 2 / 2 + u s) (fun s => ?_) (fun s hs => hA2 s hs) (by simp [hg])
    have := ((hasDerivAt_pow 3 s).const_mul K).div_const 6 |>.add (hgd s)
    convert this using 1
    simp
    ring
  have h1' := hB1 1 ⟨zero_le_one, le_rfl⟩
  have h2' := hB2 1 ⟨zero_le_one, le_rfl⟩
  simp only [hg, one_pow, one_mul, mul_one] at h1' h2'
  rw [abs_le]
  constructor <;> linarith

end Taylor1D

section Line

variable {p : ℕ}

lemma Rsh_smul (c z : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Rsh (s • c) z = Real.exp (s * inner ℝ c z - s ^ 2 * ‖c‖ ^ 2 / 2) := by
  unfold Rsh
  rw [real_inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma hasDerivAt_Rs (c z : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Rsh (s • c) z)
      ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z) s := by
  have h : HasDerivAt (fun s : ℝ => s * inner ℝ c z - s ^ 2 * ‖c‖ ^ 2 / 2)
      (inner ℝ c z - s * ‖c‖ ^ 2) s := by
    have h1 := (hasDerivAt_id s).mul_const (inner ℝ c z)
    have h2 := ((hasDerivAt_pow 2 s).mul_const (‖c‖ ^ 2)).div_const 2
    convert h1.sub h2 using 1
    · funext x; simp
    · simp; ring
  have := h.exp
  simp_rw [Rsh_smul]
  convert this using 1
  ring

lemma hasDerivAt_Rs1 (c z : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z)
      (((inner ℝ c z - s * ‖c‖ ^ 2) ^ 2 - ‖c‖ ^ 2) * Rsh (s • c) z) s := by
  have h1 : HasDerivAt (fun s : ℝ => inner ℝ c z - s * ‖c‖ ^ 2) (-‖c‖ ^ 2) s := by
    have := ((hasDerivAt_id s).mul_const (‖c‖ ^ 2)).const_sub (inner ℝ c z)
    convert this using 1
    · funext x; simp
    · ring
  have := h1.mul (hasDerivAt_Rs c z s)
  convert this using 1
  ring

lemma Rsh_smul_le (c z : EuclideanSpace ℝ (Fin p)) {s S : ℝ} (hs : |s| ≤ S) :
    Rsh (s • c) z ≤ Real.exp (S * |inner ℝ c z|) := by
  rw [Rsh_smul]
  refine Real.exp_le_exp.2 ?_
  have h1 : s * inner ℝ c z ≤ |s| * |inner ℝ c z| := by
    rw [← abs_mul]; exact le_abs_self _
  have h2 : |s| * |inner ℝ c z| ≤ S * |inner ℝ c z| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  nlinarith [sq_nonneg s, sq_nonneg ‖c‖, mul_nonneg (sq_nonneg s) (sq_nonneg ‖c‖)]

lemma integrable_exp_abs_inner (c : EuclideanSpace ℝ (Fin p)) (T : ℝ) :
    Integrable (fun z => Real.exp (T * |inner ℝ c z|)) (gam p) := by
  have h1 := (integrable_Rsh (T • c)).const_mul (Real.exp (T ^ 2 * ‖c‖ ^ 2 / 2))
  have h2 := (integrable_Rsh ((-T) • c)).const_mul (Real.exp (T ^ 2 * ‖c‖ ^ 2 / 2))
  refine (h1.add h2).mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Rsh_smul, Rsh_smul, ← Real.exp_add,
    ← Real.exp_add]
  have e1 : T ^ 2 * ‖c‖ ^ 2 / 2 + (T * inner ℝ c z - T ^ 2 * ‖c‖ ^ 2 / 2) = T * inner ℝ c z := by ring
  have e2 : T ^ 2 * ‖c‖ ^ 2 / 2 + ((-T) * inner ℝ c z - (-T) ^ 2 * ‖c‖ ^ 2 / 2) =
      -(T * inner ℝ c z) := by ring
  rw [e1, e2]
  rcases abs_cases (inner ℝ c z) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    have := Real.exp_pos (-(T * inner ℝ c z))
    linarith
  · rw [h]
    have := Real.exp_pos (T * inner ℝ c z)
    have e3 : T * -inner ℝ c z = -(T * inner ℝ c z) := by ring
    rw [e3]
    linarith

lemma integral_shift_poly (c : EuclideanSpace ℝ (Fin p)) (q : EuclideanSpace ℝ (Fin p) → ℝ)
    (h : ℝ → ℝ) (s : ℝ) :
    ∫ z, q (z + s • c) * h (inner ℝ c z) ∂(gam p) =
      ∫ z, q z * h (inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z ∂(gam p) := by
  have := integral_gam_shift (fun w => q w * h (inner ℝ c w - s * ‖c‖ ^ 2)) (s • c)
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at this
  simp only [add_sub_cancel_right] at this
  exact this

lemma real_bd1 (x s S a : ℝ) (ha : 0 ≤ a) (hs : |s| ≤ S) :
    |x - s * a| * Real.exp (S * |x|) ≤ (1 + S * a) * Real.exp ((S + 1) * |x|) := by
  have hS : 0 ≤ S := (abs_nonneg _).trans hs
  have h1 : |x - s * a| ≤ |x| + S * a := by
    calc |x - s * a| ≤ |x| + |s * a| := abs_sub _ _
      _ = |x| + |s| * a := by rw [abs_mul, abs_of_nonneg ha]
      _ ≤ |x| + S * a := by gcongr
  have h2 : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  have h3 : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg _)
  have h4 : |x - s * a| ≤ (1 + S * a) * Real.exp |x| := by
    nlinarith [mul_nonneg hS ha]
  calc |x - s * a| * Real.exp (S * |x|) ≤ ((1 + S * a) * Real.exp |x|) * Real.exp (S * |x|) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = (1 + S * a) * Real.exp ((S + 1) * |x|) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma real_bd2 (x s S a : ℝ) (ha : 0 ≤ a) (hs : |s| ≤ S) :
    |(x - s * a) ^ 2 - a| * Real.exp (S * |x|) ≤ ((1 + S * a) ^ 2 + a) * Real.exp ((S + 2) * |x|) := by
  have hS : 0 ≤ S := (abs_nonneg _).trans hs
  have h1 : |x - s * a| ≤ |x| + S * a := by
    calc |x - s * a| ≤ |x| + |s * a| := abs_sub _ _
      _ = |x| + |s| * a := by rw [abs_mul, abs_of_nonneg ha]
      _ ≤ |x| + S * a := by gcongr
  have h2 : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  have h3 : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg _)
  have h4 : |x - s * a| ≤ (1 + S * a) * Real.exp |x| := by
    nlinarith [mul_nonneg hS ha]
  have h5 : (x - s * a) ^ 2 ≤ (1 + S * a) ^ 2 * Real.exp (2 * |x|) := by
    have : (x - s * a) ^ 2 = |x - s * a| ^ 2 := (sq_abs _).symm
    rw [this]
    calc |x - s * a| ^ 2 ≤ ((1 + S * a) * Real.exp |x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h4 2
      _ = (1 + S * a) ^ 2 * Real.exp (2 * |x|) := by
        rw [mul_pow, ← Real.exp_nat_mul]; norm_num
  have h6 : 1 ≤ Real.exp (2 * |x|) := Real.one_le_exp (by positivity)
  have h7 : |(x - s * a) ^ 2 - a| ≤ ((1 + S * a) ^ 2 + a) * Real.exp (2 * |x|) := by
    calc |(x - s * a) ^ 2 - a| ≤ (x - s * a) ^ 2 + a := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - s * a)]
      _ ≤ (1 + S * a) ^ 2 * Real.exp (2 * |x|) + a * Real.exp (2 * |x|) := by nlinarith
      _ = _ := by ring
  calc |(x - s * a) ^ 2 - a| * Real.exp (S * |x|)
      ≤ (((1 + S * a) ^ 2 + a) * Real.exp (2 * |x|)) * Real.exp (S * |x|) :=
        mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
    _ = ((1 + S * a) ^ 2 + a) * Real.exp ((S + 2) * |x|) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma hasDerivAt_Q (c : EuclideanSpace ℝ (Fin p)) {q : EuclideanSpace ℝ (Fin p) → ℝ}
    (hq : Measurable q) {W : ℝ} (hW : ∀ z, |q z| ≤ W) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ z, q (z + s • c) ∂(gam p))
      (∫ z, q (z + s0 • c) * inner ℝ c z ∂(gam p)) s0 := by
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0)
  have hfun : (fun s : ℝ => ∫ z, q (z + s • c) ∂(gam p)) =
      fun s => ∫ z, q z * Rsh (s • c) z ∂(gam p) := by
    funext s; exact integral_gam_shift q (s • c)
  have hint : ∫ z, q (z + s0 • c) * inner ℝ c z ∂(gam p) =
      ∫ z, q z * ((inner ℝ c z - s0 * ‖c‖ ^ 2) * Rsh (s0 • c) z) ∂(gam p) := by
    have := integral_shift_poly c q (fun x => x) s0
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  rw [hfun, hint]
  set S : ℝ := |s0| + 1 with hS
  set T : ℝ := S + 2 with hT
  set C : ℝ := 1 + S * ‖c‖ ^ 2 with hC
  have hS0 : 0 ≤ S := by positivity
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun z => q z * Rsh (s • c) z) (gam p) :=
    fun s => (hq.mul (measurable_Rsh _)).aestronglyMeasurable
  have hmeas' : ∀ s : ℝ, AEStronglyMeasurable
      (fun z => q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z)) (gam p) := fun s => by
    have : Measurable fun z => q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z) := by
      refine hq.mul ((by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin p) =>
        inner ℝ c z - s * ‖c‖ ^ 2).mul (measurable_Rsh _))
    exact this.aestronglyMeasurable
  have hFint : Integrable (fun z => q z * Rsh (s0 • c) z) (gam p) := by
    refine ((integrable_Rsh (s0 • c)).const_mul W).mono' (hmeas s0)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Rsh_pos _ _)]
    exact mul_le_mul_of_nonneg_right (hW z) (Rsh_pos _ _).le
  have hbint : Integrable (fun z => W * C * Real.exp (T * |inner ℝ c z|)) (gam p) :=
    (integrable_exp_abs_inner c T).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gam p) (s := Metric.ball s0 1)
    (x₀ := s0) (F := fun s z => q z * Rsh (s • c) z)
    (F' := fun s z => q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z))
    (bound := fun z => W * C * Real.exp (T * |inner ℝ c z|)) (Metric.ball_mem_nhds s0 one_pos)
    (Filter.Eventually.of_forall hmeas) hFint (hmeas' s0) ?_ hbint ?_).2
  · refine Filter.Eventually.of_forall fun z s hs => ?_
    have hsS : |s| ≤ S := by
      have := Metric.mem_ball.1 hs
      rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub s s0
      rw [hS]; linarith [abs_lt.1 ‹|s - s0| < 1›]
    have h1 := real_bd1 (inner ℝ c z) s S (‖c‖ ^ 2) (sq_nonneg _) hsS
    have h2 := Rsh_smul_le c z hsS
    have h3 : Real.exp ((S + 1) * |inner ℝ c z|) ≤ Real.exp (T * |inner ℝ c z|) :=
      Real.exp_le_exp.2 (by rw [hT]; nlinarith [abs_nonneg (inner ℝ c z)])
    calc ‖q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z)‖
        = |q z| * (|inner ℝ c z - s * ‖c‖ ^ 2| * Rsh (s • c) z) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Rsh_pos _ _)]
      _ ≤ W * (|inner ℝ c z - s * ‖c‖ ^ 2| * Real.exp (S * |inner ℝ c z|)) :=
          mul_le_mul (hW z) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) (mul_nonneg (abs_nonneg _) (Rsh_pos _ _).le) hW0
      _ ≤ W * ((1 + S * ‖c‖ ^ 2) * Real.exp ((S + 1) * |inner ℝ c z|)) := by gcongr
      _ ≤ W * C * Real.exp (T * |inner ℝ c z|) := by
          rw [mul_assoc]
          gcongr
  · refine Filter.Eventually.of_forall fun z s hs => ?_
    exact (hasDerivAt_Rs c z s).const_mul (q z) |>.congr_deriv (by ring)

lemma hasDerivAt_Q1 (c : EuclideanSpace ℝ (Fin p)) {q : EuclideanSpace ℝ (Fin p) → ℝ}
    (hq : Measurable q) {W : ℝ} (hW : ∀ z, |q z| ≤ W) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ z, q (z + s • c) * inner ℝ c z ∂(gam p))
      (∫ z, q (z + s0 • c) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ∂(gam p)) s0 := by
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0)
  have hfun : (fun s : ℝ => ∫ z, q (z + s • c) * inner ℝ c z ∂(gam p)) =
      fun s => ∫ z, q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z) ∂(gam p) := by
    funext s
    have := integral_shift_poly c q (fun x => x) s
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  have hint : ∫ z, q (z + s0 • c) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ∂(gam p) =
      ∫ z, q z * (((inner ℝ c z - s0 * ‖c‖ ^ 2) ^ 2 - ‖c‖ ^ 2) * Rsh (s0 • c) z) ∂(gam p) := by
    have := integral_shift_poly c q (fun x => x ^ 2 - ‖c‖ ^ 2) s0
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  rw [hfun, hint]
  set S : ℝ := |s0| + 1 with hS
  set T : ℝ := S + 2 with hT
  set C : ℝ := (1 + S * ‖c‖ ^ 2) ^ 2 + ‖c‖ ^ 2 with hC
  have hS0 : 0 ≤ S := by positivity
  have hmeas' : ∀ s : ℝ, AEStronglyMeasurable
      (fun z => q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z)) (gam p) := fun s => by
    have : Measurable fun z => q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z) := by
      refine hq.mul ((by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin p) =>
        inner ℝ c z - s * ‖c‖ ^ 2).mul (measurable_Rsh _))
    exact this.aestronglyMeasurable
  have hmeas'' : ∀ s : ℝ, AEStronglyMeasurable
      (fun z => q z * (((inner ℝ c z - s * ‖c‖ ^ 2) ^ 2 - ‖c‖ ^ 2) * Rsh (s • c) z)) (gam p) :=
    fun s => by
    have : Measurable fun z => q z * (((inner ℝ c z - s * ‖c‖ ^ 2) ^ 2 - ‖c‖ ^ 2) * Rsh (s • c) z) := by
      refine hq.mul ((by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin p) =>
        (inner ℝ c z - s * ‖c‖ ^ 2) ^ 2 - ‖c‖ ^ 2).mul (measurable_Rsh _))
    exact this.aestronglyMeasurable
  have hbint : Integrable (fun z => W * C * Real.exp (T * |inner ℝ c z|)) (gam p) :=
    (integrable_exp_abs_inner c T).const_mul _
  have hbd1 : ∀ s : ℝ, |s| ≤ S → ∀ z : EuclideanSpace ℝ (Fin p),
      ‖q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z)‖ ≤ W * C * Real.exp (T * |inner ℝ c z|) := by
    intro s hsS z
    have h1 := real_bd1 (inner ℝ c z) s S (‖c‖ ^ 2) (sq_nonneg _) hsS
    have h2 := Rsh_smul_le c z hsS
    have h3 : Real.exp ((S + 1) * |inner ℝ c z|) ≤ Real.exp (T * |inner ℝ c z|) :=
      Real.exp_le_exp.2 (by rw [hT]; nlinarith [abs_nonneg (inner ℝ c z)])
    have hC1 : 1 + S * ‖c‖ ^ 2 ≤ C := by
      rw [hC]; nlinarith [sq_nonneg ‖c‖, mul_nonneg hS0 (sq_nonneg ‖c‖), sq_nonneg (S * ‖c‖ ^ 2)]
    calc ‖q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z)‖
        = |q z| * (|inner ℝ c z - s * ‖c‖ ^ 2| * Rsh (s • c) z) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Rsh_pos _ _)]
      _ ≤ W * (|inner ℝ c z - s * ‖c‖ ^ 2| * Real.exp (S * |inner ℝ c z|)) :=
          mul_le_mul (hW z) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (Rsh_pos _ _).le) hW0
      _ ≤ W * ((1 + S * ‖c‖ ^ 2) * Real.exp ((S + 1) * |inner ℝ c z|)) := by gcongr
      _ ≤ W * (C * Real.exp (T * |inner ℝ c z|)) := by
          gcongr
      _ = W * C * Real.exp (T * |inner ℝ c z|) := by ring
  have hFint : Integrable (fun z => q z * ((inner ℝ c z - s0 * ‖c‖ ^ 2) * Rsh (s0 • c) z)) (gam p) :=
    hbint.mono' (hmeas' s0) (Filter.Eventually.of_forall fun z =>
      hbd1 s0 (by rw [hS]; linarith [abs_nonneg s0]) z)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gam p) (s := Metric.ball s0 1)
    (x₀ := s0) (F := fun s z => q z * ((inner ℝ c z - s * ‖c‖ ^ 2) * Rsh (s • c) z))
    (F' := fun s z => q z * (((inner ℝ c z - s * ‖c‖ ^ 2) ^ 2 - ‖c‖ ^ 2) * Rsh (s • c) z))
    (bound := fun z => W * C * Real.exp (T * |inner ℝ c z|)) (Metric.ball_mem_nhds s0 one_pos)
    (Filter.Eventually.of_forall hmeas') hFint (hmeas'' s0) ?_ hbint ?_).2
  · refine Filter.Eventually.of_forall fun z s hs => ?_
    have hsS : |s| ≤ S := by
      have := Metric.mem_ball.1 hs
      rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub s s0
      rw [hS]; linarith [abs_lt.1 ‹|s - s0| < 1›]
    have h1 := real_bd2 (inner ℝ c z) s S (‖c‖ ^ 2) (sq_nonneg _) hsS
    have h2 := Rsh_smul_le c z hsS
    calc ‖q z * (((inner ℝ c z - s * ‖c‖ ^ 2) ^ 2 - ‖c‖ ^ 2) * Rsh (s • c) z)‖
        = |q z| * (|(inner ℝ c z - s * ‖c‖ ^ 2) ^ 2 - ‖c‖ ^ 2| * Rsh (s • c) z) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Rsh_pos _ _)]
      _ ≤ W * (|(inner ℝ c z - s * ‖c‖ ^ 2) ^ 2 - ‖c‖ ^ 2| * Real.exp (S * |inner ℝ c z|)) :=
          mul_le_mul (hW z) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (Rsh_pos _ _).le) hW0
      _ ≤ W * (C * Real.exp (T * |inner ℝ c z|)) := by gcongr
      _ = W * C * Real.exp (T * |inner ℝ c z|) := by ring
  · refine Filter.Eventually.of_forall fun z s hs => ?_
    exact (hasDerivAt_Rs1 c z s).const_mul (q z)

/-- Taylor remainder along a line for a bounded function that is Lipschitz along `c`. -/
lemma taylor_line_lip (c : EuclideanSpace ℝ (Fin p)) {q : EuclideanSpace ℝ (Fin p) → ℝ}
    (hq : Measurable q) {W : ℝ} (hW : ∀ z, |q z| ≤ W) {L : ℝ}
    (hL : ∀ (z : EuclideanSpace ℝ (Fin p)) (s : ℝ), 0 ≤ s → |q (z + s • c) - q z| ≤ L * s) :
    |∫ z, q (z + c) ∂(gam p) - ∫ z, q z ∂(gam p) - ∫ z, q z * inner ℝ c z ∂(gam p) -
        (∫ z, q z * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ∂(gam p)) / 2| ≤ Real.sqrt 2 * L * ‖c‖ ^ 2 / 6 := by
  have hX2 : Integrable (fun z : EuclideanSpace ℝ (Fin p) => (inner ℝ c z) ^ 2 - ‖c‖ ^ 2) (gam p) := by
    have := integrable_inner_pow c 1
    simp only [mul_one] at this
    exact this.sub (integrable_const _)
  have hqs : ∀ s : ℝ, Integrable (fun z => q (z + s • c) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2)) (gam p) := by
    intro s
    refine hX2.bdd_mul (c := W) ?_ ?_
    · exact (hq.comp (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin p) => z + s • c)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hW _
  have hmain := taylor_two_one_dim (φ := fun s : ℝ => ∫ z, q (z + s • c) ∂(gam p))
    (φ1 := fun s => ∫ z, q (z + s • c) * inner ℝ c z ∂(gam p))
    (φ2 := fun s => ∫ z, q (z + s • c) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ∂(gam p))
    (fun s => hasDerivAt_Q c hq hW s) (fun s => hasDerivAt_Q1 c hq hW s)
    (K := Real.sqrt 2 * L * ‖c‖ ^ 2) (fun s hs => by
      have e : ∫ z, q (z + s • c) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ∂(gam p) -
          ∫ z, q (z + (0 : ℝ) • c) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ∂(gam p) =
          ∫ z, (q (z + s • c) - q z) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ∂(gam p) := by
        simp only [zero_smul, add_zero]
        rw [← integral_sub (hqs s) (by simpa using hqs 0)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [zero_smul, add_zero]; ring
      beta_reduce
      rw [e]
      have hi : Integrable (fun z => (q (z + s • c) - q z) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2)) (gam p) := by
        have := (hqs s).sub (by simpa using hqs 0)
        refine this.congr (Filter.Eventually.of_forall fun z => ?_)
        simp only [Pi.sub_apply, zero_smul, add_zero]; ring
      calc |∫ z, (q (z + s • c) - q z) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ∂(gam p)|
          ≤ ∫ z, |(q (z + s • c) - q z) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2)| ∂(gam p) := by
            have := norm_integral_le_integral_norm (μ := gam p)
              (fun z => (q (z + s • c) - q z) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2))
            simpa only [Real.norm_eq_abs] using this
        _ ≤ ∫ z, L * s * |(inner ℝ c z) ^ 2 - ‖c‖ ^ 2| ∂(gam p) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
              (hX2.abs.const_mul _) (Filter.Eventually.of_forall fun z => ?_)
            show |(q (z + s • c) - q z) * ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2)| ≤
              L * s * |(inner ℝ c z) ^ 2 - ‖c‖ ^ 2|
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hL z s hs.1) (abs_nonneg _)
        _ = L * s * ∫ z, |(inner ℝ c z) ^ 2 - ‖c‖ ^ 2| ∂(gam p) := integral_const_mul _ _
        _ ≤ L * s * (Real.sqrt 2 * ‖c‖ ^ 2) := by
            have hL0 : 0 ≤ L := by
              have := hL 0 1 zero_le_one
              have h0 : 0 ≤ |q ((0 : EuclideanSpace ℝ (Fin p)) + (1 : ℝ) • c) - q 0| := abs_nonneg _
              linarith
            exact mul_le_mul_of_nonneg_left (integral_abs_inner_sq_sub_le c) (mul_nonneg hL0 hs.1)
        _ = Real.sqrt 2 * L * ‖c‖ ^ 2 * s := by ring)
  simpa using hmain

end Line

section SmoothLine

variable {p : ℕ}

lemma continuous_fderiv2_of_contDiff {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fderiv ℝ (fderiv ℝ f)) :=
  (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero

lemma hasDerivAt_line_f {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f)
    (a y : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => f (a + s • y)) (fderiv ℝ f (a + s • y) y) s := by
  have hline : HasDerivAt (fun s : ℝ => a + s • y) y s := by
    simpa using ((hasDerivAt_id s).smul_const y).const_add a
  exact ((hf.differentiable (by norm_num)) (a + s • y)).hasFDerivAt.comp_hasDerivAt s hline

lemma hasDerivAt_line_df {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f)
    (a y : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (a + s • y) y)
      (fderiv ℝ (fderiv ℝ f) (a + s • y) y y) s := by
  have hline : HasDerivAt (fun s : ℝ => a + s • y) y s := by
    simpa using ((hasDerivAt_id s).smul_const y).const_add a
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 := (hd2 (a + s • y)).hasFDerivAt.comp_hasDerivAt s hline
  exact (ContinuousLinearMap.apply ℝ ℝ y).hasFDerivAt.comp_hasDerivAt s h1

lemma hasDerivAt_smooth1 {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f) {M0 M1 : ℝ}
    (h0 : ∀ z, |f z| ≤ M0) (h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ M1)
    (w : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (hw : Measurable w)
    (y : EuclideanSpace ℝ (Fin p)) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ u, f (w u + s • y) ∂(gam p))
      (∫ u, fderiv ℝ f (w u + s0 • y) y ∂(gam p)) s0 := by
  have hfc : Continuous f := hf.continuous
  have hmeasF : ∀ s : ℝ, AEStronglyMeasurable (fun u => f (w u + s • y)) (gam p) := fun s =>
    (hfc.measurable.comp (hw.add_const _)).aestronglyMeasurable
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hmeasF' : ∀ s : ℝ, AEStronglyMeasurable (fun u => fderiv ℝ f (w u + s • y) y) (gam p) := fun s =>
    (((ContinuousLinearMap.apply ℝ ℝ y).continuous.comp hdf).measurable.comp
      (hw.add_const _)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gam p) (s := Set.univ) (x₀ := s0)
    (F := fun s u => f (w u + s • y)) (F' := fun s u => fderiv ℝ f (w u + s • y) y)
    (bound := fun _ => M1 * ‖y‖) Filter.univ_mem (Filter.Eventually.of_forall hmeasF)
    (Integrable.of_bound (hmeasF s0) M0 (Filter.Eventually.of_forall fun u => by
      simpa [Real.norm_eq_abs] using h0 _)) (hmeasF' s0) ?_ (integrable_const _) ?_).2
  · refine Filter.Eventually.of_forall fun u s _ => ?_
    calc ‖fderiv ℝ f (w u + s • y) y‖ ≤ ‖fderiv ℝ f (w u + s • y)‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M1 * ‖y‖ := mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun u s _ => hasDerivAt_line_f hf (w u) y s

lemma hasDerivAt_smooth2 {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f) {M1 M2 : ℝ}
    (h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ M1) (h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M2)
    (w : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (hw : Measurable w)
    (y : EuclideanSpace ℝ (Fin p)) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ u, fderiv ℝ f (w u + s • y) y ∂(gam p))
      (∫ u, fderiv ℝ (fderiv ℝ f) (w u + s0 • y) y y ∂(gam p)) s0 := by
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hdf2 := continuous_fderiv2_of_contDiff hf
  have hmeasF : ∀ s : ℝ, AEStronglyMeasurable (fun u => fderiv ℝ f (w u + s • y) y) (gam p) := fun s =>
    (((ContinuousLinearMap.apply ℝ ℝ y).continuous.comp hdf).measurable.comp
      (hw.add_const _)).aestronglyMeasurable
  have hmeasF' : ∀ s : ℝ, AEStronglyMeasurable (fun u => fderiv ℝ (fderiv ℝ f) (w u + s • y) y y) (gam p) :=
    fun s => (((ContinuousLinearMap.apply ℝ ℝ y).continuous.comp
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ) y).continuous.comp hdf2)).measurable.comp
      (hw.add_const _)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gam p) (s := Set.univ) (x₀ := s0)
    (F := fun s u => fderiv ℝ f (w u + s • y) y) (F' := fun s u => fderiv ℝ (fderiv ℝ f) (w u + s • y) y y)
    (bound := fun _ => M2 * ‖y‖ * ‖y‖) Filter.univ_mem (Filter.Eventually.of_forall hmeasF)
    (Integrable.of_bound (hmeasF s0) (M1 * ‖y‖) (Filter.Eventually.of_forall fun u => by
      calc ‖fderiv ℝ f (w u + s0 • y) y‖ ≤ ‖fderiv ℝ f (w u + s0 • y)‖ * ‖y‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M1 * ‖y‖ := mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _)))
    (hmeasF' s0) ?_ (integrable_const _) ?_).2
  · refine Filter.Eventually.of_forall fun u s _ => ?_
    calc ‖fderiv ℝ (fderiv ℝ f) (w u + s • y) y y‖
        ≤ ‖fderiv ℝ (fderiv ℝ f) (w u + s • y) y‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) (w u + s • y)‖ * ‖y‖) * ‖y‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ M2 * ‖y‖ * ‖y‖ := by
          gcongr
          exact h2 _
  · exact Filter.Eventually.of_forall fun u s _ => hasDerivAt_line_df hf (w u) y s

/-- Taylor remainder along a line for `C²` functions with bounded derivatives, in the
Cameron–Martin form (`q = f ∘ w`); `w (u + s c) = w u + s y`. -/
lemma taylor_line_C2 {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f) {M0 M1 M2 : ℝ}
    (h0 : ∀ z, |f z| ≤ M0) (h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ M1) (h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M2)
    (w : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (hw : Measurable w)
    (c y : EuclideanSpace ℝ (Fin p))
    (hwc : ∀ (u : EuclideanSpace ℝ (Fin p)) (s : ℝ), w (u + s • c) = w u + s • y) :
    |∫ u, f (w (u + c)) ∂(gam p) - ∫ u, f (w u) ∂(gam p) - ∫ u, f (w u) * inner ℝ c u ∂(gam p) -
        (∫ u, f (w u) * ((inner ℝ c u) ^ 2 - ‖c‖ ^ 2) ∂(gam p)) / 2| ≤
      2 * (M2 * ‖y‖ * ‖y‖) * ‖c‖ / 6 := by
  have hdf2 := continuous_fderiv2_of_contDiff hf
  have hfc : Continuous f := hf.continuous
  set q : EuclideanSpace ℝ (Fin p) → ℝ := fun u => f (w u) with hq
  have hqm : Measurable q := hfc.measurable.comp hw
  have hqW : ∀ z, |q z| ≤ M0 := fun z => h0 _
  set W2 : EuclideanSpace ℝ (Fin p) → ℝ := fun u => fderiv ℝ (fderiv ℝ f) (w u) y y with hW2
  have hW2m : Measurable W2 :=
    ((ContinuousLinearMap.apply ℝ ℝ y).continuous.comp
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ) y).continuous.comp hdf2)).measurable.comp hw
  have hW2b : ∀ u, |W2 u| ≤ M2 * ‖y‖ * ‖y‖ := fun u => by
    simp only [hW2]
    calc |fderiv ℝ (fderiv ℝ f) (w u) y y| ≤ ‖fderiv ℝ (fderiv ℝ f) (w u) y y‖ := by
          rw [← Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) (w u) y‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) (w u)‖ * ‖y‖) * ‖y‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ M2 * ‖y‖ * ‖y‖ := by gcongr; exact h2 _
  -- identification of the derivative families
  have hφ : ∀ s : ℝ, ∫ u, q (u + s • c) ∂(gam p) = ∫ u, f (w u + s • y) ∂(gam p) := fun s => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hq, hwc]
  have hD1 : ∀ s : ℝ, ∫ u, q (u + s • c) * inner ℝ c u ∂(gam p) =
      ∫ u, fderiv ℝ f (w u + s • y) y ∂(gam p) := fun s => by
    have hd1 := hasDerivAt_Q c hqm hqW s
    have hd2 := hasDerivAt_smooth1 hf h0 h1 w hw y s
    have hfun : (fun s : ℝ => ∫ u, q (u + s • c) ∂(gam p)) = fun s => ∫ u, f (w u + s • y) ∂(gam p) :=
      funext hφ
    rw [hfun] at hd1
    exact hd1.unique hd2
  have hD2 : ∀ s : ℝ, ∫ u, q (u + s • c) * ((inner ℝ c u) ^ 2 - ‖c‖ ^ 2) ∂(gam p) =
      ∫ u, fderiv ℝ (fderiv ℝ f) (w u + s • y) y y ∂(gam p) := fun s => by
    have hd1 := hasDerivAt_Q1 c hqm hqW s
    have hd2 := hasDerivAt_smooth2 hf h1 h2 w hw y s
    have hfun : (fun s : ℝ => ∫ u, q (u + s • c) * inner ℝ c u ∂(gam p)) =
        fun s => ∫ u, fderiv ℝ f (w u + s • y) y ∂(gam p) := funext hD1
    rw [hfun] at hd1
    exact hd1.unique hd2
  have hmain := taylor_two_one_dim (φ := fun s : ℝ => ∫ u, q (u + s • c) ∂(gam p))
    (φ1 := fun s => ∫ u, q (u + s • c) * inner ℝ c u ∂(gam p))
    (φ2 := fun s => ∫ u, q (u + s • c) * ((inner ℝ c u) ^ 2 - ‖c‖ ^ 2) ∂(gam p))
    (fun s => hasDerivAt_Q c hqm hqW s) (fun s => hasDerivAt_Q1 c hqm hqW s)
    (K := 2 * (M2 * ‖y‖ * ‖y‖) * ‖c‖) (fun s hs => by
      have e : ∀ s : ℝ, ∫ u, q (u + s • c) * ((inner ℝ c u) ^ 2 - ‖c‖ ^ 2) ∂(gam p) =
          ∫ u, W2 (u + s • c) ∂(gam p) := fun s => by
        rw [hD2 s]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hW2, hwc]
      beta_reduce
      rw [e s, e 0]
      have hW20 : ∫ u, W2 (u + (0 : ℝ) • c) ∂(gam p) = ∫ u, W2 u ∂(gam p) := by simp
      rw [hW20]
      have := abs_integral_shift_sub_le_lin hW2m hW2b (s • c)
      refine this.trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      nlinarith [norm_nonneg c, norm_nonneg y, mul_nonneg (norm_nonneg y) (norm_nonneg y)])
  simpa [hq] using hmain

end SmoothLine

end HRS.IID
