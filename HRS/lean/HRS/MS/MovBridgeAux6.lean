import HRS.MS.MovBridgeAux5
import HRS.MS.MovOscAux4

/-!
# MOVA3B2, part 3: the integer endpoint `H^n → Σ^n`, the extension lemma, and `B2`

Namespace `HRS.MS.MovOsc`, helpers `mova3b2_`.
* `mova3b2_Q K m A b`: `|∂_{j₁}⋯∂_{j_k} b| ≤ A (1+‖x‖)^{-m}` for `k ≤ K` (`mova3b2_Q_of_iter`: from
  `‖D^k b‖ (1+‖x‖)^m ≤ A`).  Adjustment w.r.t. the sketch: `b` is assumed smooth of temperate growth
  (`HasTemperateGrowth`, qualitative only; constants depend on the `Q` bounds alone).
* `mova3b2_int_endpoint`: `‖b w‖_{Σ^n} ≤ C A ‖w‖_{H^n}` for Schwartz `w` (ladder induction, no normal ordering);
* `mova3b2_B2_schwartz`: real `0 ≤ s ≤ N`, Schwartz `w`, by `mo_interp_H_osc`;
* `mova3b2_ext_mult` (+ `mova3b2_dense_H`): Schwartz → `{MemSobolev s w}` for any bounded measurable multiplier;
* `mova3b2_B2_pos`, `mova3b2_B2_neg` (duality with `mo_bridge1`), and `mo_bridge2` (all real `s ≤ N`).
-/

noncomputable section

open Filter MeasureTheory Topology
open scoped ContDiff FourierTransform ComplexConjugate

namespace HRS.MS.MovOsc

open HRS HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.MovInterp HRS.Whole

variable {d : ℕ}

local notation "𝓢C" => SchwartzMap (Euc d) ℂ
local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ## The class of decaying smooth multipliers -/

/-- `mova3b2_Q K m A b`: all coordinate partial derivatives `∂_{j₁}⋯∂_{j_k} b`, `k ≤ K`, satisfy
`|·| ≤ A (1+‖x‖)^{-m}`. -/
def mova3b2_Q : ℕ → ℕ → ℝ → (Euc d → ℝ) → Prop
  | 0, m, A, b => ∀ x, |b x| * (1 + ‖x‖) ^ m ≤ A
  | K + 1, m, A, b => (∀ x, |b x| * (1 + ‖x‖) ^ m ≤ A) ∧
      ∀ j : Fin d, mova3b2_Q K m A (mova3b1_Dj j b)

lemma mova3b2_Q_top {K m : ℕ} {A : ℝ} {b : Euc d → ℝ} (h : mova3b2_Q K m A b) (x : Euc d) :
    |b x| * (1 + ‖x‖) ^ m ≤ A := by
  cases K with
  | zero => exact h x
  | succ K => exact h.1 x

lemma mova3b2_Q_mono_K : ∀ {K K' m : ℕ} {A : ℝ} {b : Euc d → ℝ}, K ≤ K' →
    mova3b2_Q K' m A b → mova3b2_Q K m A b := by
  intro K
  induction K with
  | zero => intro K' m A b _ h; exact mova3b2_Q_top h
  | succ K ih =>
    intro K' m A b hK h
    cases K' with
    | zero => omega
    | succ K' => exact ⟨h.1, fun j => ih (by omega) (h.2 j)⟩

lemma mova3b2_Q_mono_m : ∀ {K m m' : ℕ} {A : ℝ} {b : Euc d → ℝ}, m ≤ m' →
    mova3b2_Q K m' A b → mova3b2_Q K m A b := by
  intro K
  induction K with
  | zero =>
    intro m m' A b hm h x
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hm)
      (abs_nonneg _)) (h x)
  | succ K ih =>
    intro m m' A b hm h
    refine ⟨fun x => le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hm) (abs_nonneg _)) (h.1 x),
      fun j => ih hm (h.2 j)⟩

lemma mova3b2_Q_mono_A : ∀ {K m : ℕ} {A A' : ℝ} {b : Euc d → ℝ}, A ≤ A' →
    mova3b2_Q K m A b → mova3b2_Q K m A' b := by
  intro K
  induction K with
  | zero => intro m A A' b hA h x; exact (h x).trans hA
  | succ K ih => intro m A A' b hA h; exact ⟨fun x => (h.1 x).trans hA, fun j => ih hA (h.2 j)⟩

lemma mova3b2_Dj_add (j : Fin d) {u v : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    mova3b1_Dj j (u + v) = mova3b1_Dj j u + mova3b1_Dj j v := by
  funext x
  have h1 : DifferentiableAt ℝ u x := (hu.differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ v x := (hv.differentiable (by simp)) x
  simp only [mova3b1_Dj, Pi.add_apply]
  rw [fderiv_add h1 h2]
  rfl

lemma mova3b2_top_add {m : ℕ} {A A' : ℝ} {b b' : Euc d → ℝ}
    (h : ∀ x, |b x| * (1 + ‖x‖) ^ m ≤ A) (h' : ∀ x, |b' x| * (1 + ‖x‖) ^ m ≤ A') (x : Euc d) :
    |(b + b') x| * (1 + ‖x‖) ^ m ≤ A + A' := by
  calc |(b + b') x| * (1 + ‖x‖) ^ m ≤ (|b x| + |b' x|) * (1 + ‖x‖) ^ m :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)
    _ = |b x| * (1 + ‖x‖) ^ m + |b' x| * (1 + ‖x‖) ^ m := by ring
    _ ≤ A + A' := add_le_add (h x) (h' x)

lemma mova3b2_contDiff_Dj (j : Fin d) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (mova3b1_Dj j u) := by
  unfold mova3b1_Dj
  exact (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma mova3b2_Q_add : ∀ {K m : ℕ} {A A' : ℝ} {b b' : Euc d → ℝ}, ContDiff ℝ ∞ b → ContDiff ℝ ∞ b' →
    mova3b2_Q K m A b → mova3b2_Q K m A' b' → mova3b2_Q K m (A + A') (b + b') := by
  intro K
  induction K with
  | zero => intro m A A' b b' _ _ h h' x; exact mova3b2_top_add h h' x
  | succ K ih =>
    intro m A A' b b' hb hb' h h'
    refine ⟨mova3b2_top_add h.1 h'.1, fun j => ?_⟩
    rw [mova3b2_Dj_add j hb hb']
    exact ih (mova3b2_contDiff_Dj j hb) (mova3b2_contDiff_Dj j hb') (h.2 j) (h'.2 j)

lemma mova3b2_Dj_xmul (j i : Fin d) {b : Euc d → ℝ} (hb : ContDiff ℝ ∞ b) :
    mova3b1_Dj j (fun x => x i * b x) =
      fun x => (if i = j then b x else 0) + x i * mova3b1_Dj j b x := by
  funext x
  have h1 : DifferentiableAt ℝ (fun x : Euc d => x i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt
  have h2 : DifferentiableAt ℝ b x := (hb.differentiable (by simp)) x
  rw [mova3b1_Dj_mul j h1 h2]
  have : mova3b1_Dj j (fun x : Euc d => x i) x = if i = j then 1 else 0 := by
    simp only [mova3b1_Dj]
    have : fderiv ℝ (fun x : Euc d => x i) x = EuclideanSpace.proj (𝕜 := ℝ) i :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).fderiv
    rw [this]
    simp [EuclideanSpace.single_apply]
  rw [this]
  split_ifs <;> simp

lemma mova3b2_Dj_zero (j : Fin d) : mova3b1_Dj j (0 : Euc d → ℝ) = 0 := by
  funext x; simp [mova3b1_Dj]

lemma mova3b2_Q_zero : ∀ {K m : ℕ} {A : ℝ}, 0 ≤ A → mova3b2_Q K m A (0 : Euc d → ℝ) := by
  intro K
  induction K with
  | zero => intro m A hA x; simpa using hA
  | succ K ih =>
    intro m A hA
    refine ⟨fun x => by simpa using hA, fun j => ?_⟩
    rw [mova3b2_Dj_zero]; exact ih hA

lemma mova3b2_abs_coord_le (i : Fin d) (x : Euc d) : |x i| ≤ 1 + ‖x‖ := by
  have := PiLp.norm_apply_le x i
  rw [Real.norm_eq_abs] at this
  linarith

/-- Multiplication by a coordinate loses one power of decay. -/
lemma mova3b2_Q_xmul (i : Fin d) : ∀ {K m : ℕ} {A : ℝ} {b : Euc d → ℝ}, 0 ≤ A → ContDiff ℝ ∞ b →
    mova3b2_Q K (m + 1) A b → mova3b2_Q K m (((K : ℝ) + 1) * A) (fun x => x i * b x) := by
  intro K
  induction K with
  | zero =>
    intro m A b hA hb h x
    have h0 := mova3b2_Q_top h x
    have h1 := mova3b2_abs_coord_le i x
    simp only [Nat.cast_zero, zero_add, one_mul]
    rw [abs_mul]
    calc |x i| * |b x| * (1 + ‖x‖) ^ m ≤ (1 + ‖x‖) * |b x| * (1 + ‖x‖) ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) (by positivity)
      _ = |b x| * (1 + ‖x‖) ^ (m + 1) := by ring
      _ ≤ A := h0
  | succ K ih =>
    intro m A b hA hb h
    have htop : ∀ x, |x i * b x| * (1 + ‖x‖) ^ m ≤ ((((K + 1 : ℕ) : ℝ)) + 1) * A := by
      intro x
      have h0 := mova3b2_Q_top h x
      have h1 := mova3b2_abs_coord_le i x
      rw [abs_mul]
      have : |x i| * |b x| * (1 + ‖x‖) ^ m ≤ A := by
        calc |x i| * |b x| * (1 + ‖x‖) ^ m ≤ (1 + ‖x‖) * |b x| * (1 + ‖x‖) ^ m :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
                (by positivity)
          _ = |b x| * (1 + ‖x‖) ^ (m + 1) := by ring
          _ ≤ A := h0
      have hK : (1 : ℝ) ≤ (((K + 1 : ℕ) : ℝ)) + 1 := by
        have : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      calc _ ≤ A := this
        _ = 1 * A := (one_mul A).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hK hA
    refine ⟨htop, fun j => ?_⟩
    rw [mova3b2_Dj_xmul j i hb]
    have e : (fun x : Euc d => (if i = j then b x else 0) + x i * mova3b1_Dj j b x) =
        (if i = j then b else 0) + (fun x => x i * mova3b1_Dj j b x) := by
      funext x; by_cases hij : i = j <;> simp [hij]
    rw [e]
    have hQb : mova3b2_Q K m A (if i = j then b else 0) := by
      by_cases hij : i = j
      · simp only [hij, if_true]
        exact mova3b2_Q_mono_m (Nat.le_succ m) (mova3b2_Q_mono_K (Nat.le_succ K) h)
      · simp only [hij, if_false]
        exact mova3b2_Q_zero hA
    have hsm : ContDiff ℝ ∞ (if i = j then b else (0 : Euc d → ℝ)) := by
      by_cases hij : i = j
      · simpa [hij] using hb
      · simp [hij]; exact contDiff_const
    have hQd := ih hA (mova3b2_contDiff_Dj j hb) (h.2 j)
    have hsm2 : ContDiff ℝ ∞ (fun x : Euc d => x i * mova3b1_Dj j b x) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.mul (mova3b2_contDiff_Dj j hb)
    have := mova3b2_Q_add hsm hsm2 hQb hQd
    refine mova3b2_Q_mono_A (le_of_eq ?_) this
    push_cast; ring

/-! ## Multiplication of Schwartz functions by temperate multipliers -/

/-- `b • w` for a smooth multiplier `b` of temperate growth. -/
def mova3b2_bsm (b : Euc d → ℝ) : 𝓢R →L[ℝ] 𝓢R := SchwartzMap.smulLeftCLM ℝ b

lemma mova3b2_bsm_apply {b : Euc d → ℝ} (hb : b.HasTemperateGrowth) (w : 𝓢R) (x : Euc d) :
    mova3b2_bsm b w x = b x * w x := by
  simp [mova3b2_bsm, SchwartzMap.smulLeftCLM_apply_apply hb]

lemma mova3b2_tg_fderiv {b : Euc d → ℝ} (hb : b.HasTemperateGrowth) :
    Function.HasTemperateGrowth (fderiv ℝ b) := by
  refine ⟨hb.1.fderiv_right (m := ∞) le_rfl, fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hb.2 (n + 1)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact h x⟩

lemma mova3b2_tg_Dj (j : Fin d) {b : Euc d → ℝ} (hb : b.HasTemperateGrowth) :
    (mova3b1_Dj j b).HasTemperateGrowth :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).hasTemperateGrowth.comp
    (mova3b2_tg_fderiv hb)

lemma mova3b2_tg_G (j : Fin d) {b : Euc d → ℝ} (hb : b.HasTemperateGrowth) :
    (fun x : Euc d => x j * b x + mova3b1_Dj j b x).HasTemperateGrowth :=
  ((mova1_hasTempGrowth_coord j).mul hb).add (mova3b2_tg_Dj j hb)

/-- Leibniz rule for the ladder operator `x_j + ∂_j`. -/
lemma mova3b2_G_bsm (j : Fin d) {b : Euc d → ℝ} (hb : b.HasTemperateGrowth) (w : 𝓢R) :
    mova1_X j (mova3b2_bsm b w) + mova1_D j (mova3b2_bsm b w) =
      mova3b2_bsm (fun x => x j * b x + mova3b1_Dj j b x) w + mova3b2_bsm b (mova1_D j w) := by
  ext x
  have hf : (⇑(mova3b2_bsm b w) : Euc d → ℝ) = fun x => b x * w x :=
    funext (mova3b2_bsm_apply hb w)
  have h1 : DifferentiableAt ℝ b x := (hb.1.differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ w x := w.differentiableAt
  simp only [SchwartzMap.add_apply, mova1_X_apply, mova1_D_apply, hf,
    mova3b2_bsm_apply (mova3b2_tg_G j hb), mova3b2_bsm_apply hb]
  rw [fderiv_fun_mul h1 h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have : mova3b1_Dj j b x = fderiv ℝ b x (EuclideanSpace.single j (1 : ℝ)) := rfl
  rw [this]; ring

/-! ## The word norm is subadditive -/

lemma mova3b2_W_add : ∀ (n : ℕ) (f g : 𝓢R), mova1_W n (f + g) ≤ mova1_W n f + mova1_W n g := by
  intro n
  induction n with
  | zero => intro f g; exact mova1_n2_add f g
  | succ n ih =>
    intro f g
    show mova1_W n (f + g) + ∑ j : Fin d, mova1_W n (mova1_X j (f + g) + mova1_D j (f + g)) ≤
      (mova1_W n f + ∑ j : Fin d, mova1_W n (mova1_X j f + mova1_D j f)) +
        (mova1_W n g + ∑ j : Fin d, mova1_W n (mova1_X j g + mova1_D j g))
    have h1 := ih f g
    have h2 : ∑ j : Fin d, mova1_W n (mova1_X j (f + g) + mova1_D j (f + g)) ≤
        ∑ j : Fin d, (mova1_W n (mova1_X j f + mova1_D j f) +
          mova1_W n (mova1_X j g + mova1_D j g)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have : mova1_X j (f + g) + mova1_D j (f + g) =
          (mova1_X j f + mova1_D j f) + (mova1_X j g + mova1_D j g) := by
        rw [map_add, map_add]; abel
      rw [this]; exact ih _ _
    rw [Finset.sum_add_distrib] at h2
    linarith

/-! ## Sobolev facts for Schwartz functions -/

/-- `‖w‖_{H^r}`. -/
def mova3b2_hn (w : 𝓢R) (r : ℝ) : ℝ := Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r (⇑w))

lemma mova3b2_hn_zero (w : 𝓢R) : mova1_n2 w = mova3b2_hn w 0 := by
  rw [mova1_n2_eq, mova3b2_hn]
  unfold mo_l2 HRS.PDE.ToolboxRd.sobolevNormSq
  congr 1
  have := integral_norm_sq_fourierL2 (w.memLp 2 volume)
  simpa using this.symm

lemma mova3b2_sobNormSq_mono (w : 𝓢R) {r r' : ℝ} (h : r ≤ r') :
    HRS.PDE.ToolboxRd.sobolevNormSq r (⇑w) ≤ HRS.PDE.ToolboxRd.sobolevNormSq r' (⇑w) := by
  rw [mova3b2_sobNormSq_cx, mova3b2_sobNormSq_cx]
  refine integral_mono (mova3b2_int_W _ _) (mova3b2_int_W _ _) fun ξ => ?_
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (mova3b1_W_ge ξ) h)
    (sq_nonneg _)

lemma mova3b2_hn_mono (w : 𝓢R) {r r' : ℝ} (h : r ≤ r') : mova3b2_hn w r ≤ mova3b2_hn w r' :=
  Real.sqrt_le_sqrt (mova3b2_sobNormSq_mono w h)

lemma mova3b2_sobNormSq_D (w : 𝓢R) (j : Fin d) (r : ℝ) :
    HRS.PDE.ToolboxRd.sobolevNormSq r (⇑(mova1_D j w)) ≤
      HRS.PDE.ToolboxRd.sobolevNormSq (r + 1) (⇑w) := by
  rw [mova3b2_sobNormSq_cx, mova3b2_sobNormSq_cx]
  refine integral_mono (mova3b2_int_W _ _) (mova3b2_int_W _ _) fun ξ => ?_
  have hF : (𝓕 (mova3b2_cx (mova1_D j w)) : 𝓢C) ξ =
      (2 * Real.pi * Complex.I * (ξ j : ℂ)) * (𝓕 (mova3b2_cx w) : 𝓢C) ξ :=
    mova1_fourier_D j w ξ
  rw [hF, norm_mul]
  have hW := mova3b1_W_pos ξ
  have h1 : ‖(2 * Real.pi * Complex.I * (ξ j : ℂ))‖ ^ 2 ≤ mova3b1_W ξ := by
    have : ‖(2 * Real.pi * Complex.I * (ξ j : ℂ))‖ = 2 * Real.pi * |ξ j| := by
      simp [abs_of_pos Real.pi_pos]
    rw [this, mul_pow, sq_abs]
    have h2 := PiLp.norm_apply_le ξ j
    rw [Real.norm_eq_abs] at h2
    have h3 : ξ j ^ 2 ≤ ‖ξ‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    unfold mova3b1_W
    nlinarith [Real.pi_pos]
  rw [mul_pow, Real.rpow_add hW, Real.rpow_one]
  calc mova3b1_W ξ ^ r * (‖(2 * Real.pi * Complex.I * (ξ j : ℂ))‖ ^ 2 *
        ‖(𝓕 (mova3b2_cx w) : 𝓢C) ξ‖ ^ 2) ≤ mova3b1_W ξ ^ r * (mova3b1_W ξ *
        ‖(𝓕 (mova3b2_cx w) : 𝓢C) ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
          (Real.rpow_nonneg hW.le _)
    _ = _ := by ring

/-! ## The integer endpoint -/

lemma mova3b2_W_zero_mult {A : ℝ} (hA : 0 ≤ A) {b : Euc d → ℝ} (hb : b.HasTemperateGrowth)
    (hQ : mova3b2_Q 0 0 A b) (w : 𝓢R) :
    mova1_W 0 (mova3b2_bsm b w) ≤ 1 * A * mova3b2_hn w 0 := by
  show mova1_n2 (mova3b2_bsm b w) ≤ 1 * A * mova3b2_hn w 0
  rw [← mova3b2_hn_zero, mova1_n2_eq, mova1_n2_eq]
  unfold mo_l2
  have hab : ∀ x, |b x| ≤ A := fun x => by simpa using hQ x
  have hI1 := ((mova3b2_bsm b w).memLp 2 volume).norm.integrable_sq
  have hI2 := (w.memLp 2 volume).norm.integrable_sq
  have hpt : ∀ x, (mova3b2_bsm b w x) ^ 2 ≤ A ^ 2 * (w x) ^ 2 := by
    intro x
    rw [mova3b2_bsm_apply hb, mul_pow]
    have h1 : b x ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs (b x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hab x) 2
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have : ∫ x, (mova3b2_bsm b w x) ^ 2 ≤ ∫ x, A ^ 2 * (w x) ^ 2 :=
    integral_mono (by simpa using hI1) (by simpa using hI2.const_mul (A ^ 2)) hpt
  rw [integral_const_mul] at this
  calc Real.sqrt (∫ x, (mova3b2_bsm b w x) ^ 2) ≤ Real.sqrt (A ^ 2 * ∫ x, w x ^ 2) :=
        Real.sqrt_le_sqrt this
    _ = 1 * A * Real.sqrt (∫ x, w x ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA]; ring

theorem mova3b2_W_mult (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (b : Euc d → ℝ),
    b.HasTemperateGrowth → mova3b2_Q n n A b → ∀ w : 𝓢R,
      mova1_W n (mova3b2_bsm b w) ≤ C * A * mova3b2_hn w n := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun A hA b hb hQ w => ?_⟩
    simpa using mova3b2_W_zero_mult hA hb hQ w
  | succ n ih =>
    obtain ⟨C, hC, hCb⟩ := ih
    refine ⟨C * (1 + (d : ℝ) * ((n : ℝ) + 3)), by positivity, fun A hA b hb hQ w => ?_⟩
    have hQn : mova3b2_Q n n A b :=
      mova3b2_Q_mono_m (Nat.le_succ n) (mova3b2_Q_mono_K (Nat.le_succ n) hQ)
    have hn1 : mova3b2_hn w (n : ℝ) ≤ mova3b2_hn w ((n + 1 : ℕ) : ℝ) :=
      mova3b2_hn_mono w (by push_cast; linarith)
    have hW0 : 0 ≤ mova3b2_hn w ((n + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
    have T1 : mova1_W n (mova3b2_bsm b w) ≤ C * A * mova3b2_hn w ((n + 1 : ℕ) : ℝ) :=
      (hCb A hA b hb hQn w).trans (mul_le_mul_of_nonneg_left hn1 (mul_nonneg hC hA))
    have T2 : ∀ j : Fin d, mova1_W n (mova1_X j (mova3b2_bsm b w) + mova1_D j (mova3b2_bsm b w)) ≤
        C * A * ((n : ℝ) + 3) * mova3b2_hn w ((n + 1 : ℕ) : ℝ) := by
      intro j
      rw [mova3b2_G_bsm j hb w]
      refine (mova3b2_W_add n _ _).trans ?_
      -- first piece
      have hx : mova3b2_Q n n (((n : ℝ) + 1) * A) (fun x => x j * b x) :=
        mova3b2_Q_xmul j hA hb.1 (mova3b2_Q_mono_K (Nat.le_succ n) hQ)
      have hd : mova3b2_Q n n A (mova3b1_Dj j b) := mova3b2_Q_mono_m (Nat.le_succ n) (hQ.2 j)
      have hsum := mova3b2_Q_add ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.mul hb.1)
        (mova3b2_contDiff_Dj j hb.1) hx hd
      have hb' : mova3b2_Q n n (((n : ℝ) + 1) * A + A)
          (fun x => x j * b x + mova3b1_Dj j b x) := hsum
      have F1 := hCb (((n : ℝ) + 1) * A + A) (by positivity) _ (mova3b2_tg_G j hb) hb' w
      -- second piece
      have F2 := hCb A hA b hb hQn (mova1_D j w)
      have F3 : mova3b2_hn (mova1_D j w) (n : ℝ) ≤ mova3b2_hn w ((n + 1 : ℕ) : ℝ) := by
        refine Real.sqrt_le_sqrt ?_
        refine (mova3b2_sobNormSq_D w j (n : ℝ)).trans (le_of_eq ?_)
        push_cast; rfl
      calc _ ≤ C * (((n : ℝ) + 1) * A + A) * mova3b2_hn w (n : ℝ) +
            C * A * mova3b2_hn (mova1_D j w) (n : ℝ) := add_le_add F1 F2
        _ ≤ C * (((n : ℝ) + 1) * A + A) * mova3b2_hn w ((n + 1 : ℕ) : ℝ) +
            C * A * mova3b2_hn w ((n + 1 : ℕ) : ℝ) := by
            refine add_le_add (mul_le_mul_of_nonneg_left hn1 (by positivity))
              (mul_le_mul_of_nonneg_left F3 (mul_nonneg hC hA))
        _ = _ := by ring
    show mova1_W n (mova3b2_bsm b w) + ∑ j : Fin d,
      mova1_W n (mova1_X j (mova3b2_bsm b w) + mova1_D j (mova3b2_bsm b w)) ≤ _
    calc _ ≤ C * A * mova3b2_hn w ((n + 1 : ℕ) : ℝ) +
          ∑ _j : Fin d, C * A * ((n : ℝ) + 3) * mova3b2_hn w ((n + 1 : ℕ) : ℝ) :=
          add_le_add T1 (Finset.sum_le_sum fun j _ => T2 j)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp; ring

/-- **Integer endpoint of `B2`.**  If `b` is smooth of temperate growth with all coordinate partial
derivatives of order `≤ n` bounded by `A (1+‖x‖)^{-n}`, then for every Schwartz `w`,
`b w ∈ Σ^n` and `‖b w‖_{Σ^n} ≤ C A ‖w‖_{H^n}`, `C = C(d, n)`. -/
theorem mova3b2_int_endpoint (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (b : Euc d → ℝ),
    b.HasTemperateGrowth → mova3b2_Q n n A b → ∀ w : 𝓢R,
      MemOsc (n : ℝ) (fun x => b x * w x) ∧
        oscNorm (n : ℝ) (fun x => b x * w x) ≤
          C * A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ) (⇑w)) := by
  obtain ⟨C1, hC1, h1⟩ := mova3b2_W_mult (d := d) n
  obtain ⟨C2, hC2, h2⟩ := mova1_lower_W (d := d) n
  refine ⟨C2 * C1, mul_nonneg hC2 hC1, fun A hA b hb hQ w => ?_⟩
  have hf : (fun x => b x * w x) = ⇑(mova3b2_bsm b w) := (funext (mova3b2_bsm_apply hb w)).symm
  rw [hf]
  refine ⟨memOsc_schwartz _ _, ?_⟩
  calc oscNorm (n : ℝ) (⇑(mova3b2_bsm b w)) ≤ C2 * mova1_W n (mova3b2_bsm b w) := h2 _
    _ ≤ C2 * (C1 * A * mova3b2_hn w n) :=
        mul_le_mul_of_nonneg_left (h1 A hA b hb hQ w) hC2
    _ = _ := by unfold mova3b2_hn; ring

/-- **`B2` for Schwartz inputs, real index** `0 ≤ s ≤ N`: `‖b w‖_{Σ^s} ≤ C A ‖w‖_{H^s}` for `b` smooth of
temperate growth with `mova3b2_Q N N A b` (all coordinate partial derivatives of order `≤ N` bounded by
`A (1+‖x‖)^{-N}`), by `mo_interp_H_osc` between the integers `⌊s⌋, ⌊s⌋+1`. -/
theorem mova3b2_B2_schwartz (s : ℝ) (hs : 0 ≤ s) (N : ℕ) (hN : s ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (b : Euc d → ℝ), b.HasTemperateGrowth →
      mova3b2_Q N N A b → ∀ w : 𝓢R,
        MemOsc s (fun x => b x * w x) ∧
          oscNorm s (fun x => b x * w x) ≤
            C * A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (⇑w)) := by
  set n0 : ℕ := ⌊s⌋₊ with hn0
  have hn0s : (n0 : ℝ) ≤ s := Nat.floor_le hs
  have hQmono : ∀ {n : ℕ}, n ≤ N → ∀ {A : ℝ} {b : Euc d → ℝ}, mova3b2_Q N N A b →
      mova3b2_Q n n A b := fun hn _ _ h =>
    mova3b2_Q_mono_m hn (mova3b2_Q_mono_K hn h)
  by_cases hint : (n0 : ℝ) = s
  · obtain ⟨C0, hC0, h0⟩ := mova3b2_int_endpoint (d := d) n0
    refine ⟨C0, hC0, fun A hA b hb hQ w => ?_⟩
    have hn0N : n0 ≤ N := by exact_mod_cast hint.le.trans hN
    rw [← hint]
    exact h0 A hA b hb (hQmono hn0N hQ) w
  · have hlt : (n0 : ℝ) < s := lt_of_le_of_ne hn0s hint
    have hn1N : n0 + 1 ≤ N := by
      have : (n0 : ℝ) < N := hlt.trans_le hN
      exact_mod_cast this
    have hs1 : s < (n0 : ℝ) + 1 := Nat.lt_floor_add_one s
    set θ : ℝ := s - n0 with hθ
    have hθ0 : 0 ≤ θ := by linarith
    have hθ1 : θ ≤ 1 := by linarith
    obtain ⟨C0, hC0, h0⟩ := mova3b2_int_endpoint (d := d) n0
    obtain ⟨C1, hC1, h1⟩ := mova3b2_int_endpoint (d := d) (n0 + 1)
    refine ⟨C0 ^ (1 - θ) * C1 ^ θ, mul_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg hC1 _),
      fun A hA b hb hQ w => ?_⟩
    have e0 := fun u : 𝓢R => h0 A hA b hb (hQmono (by omega) hQ) u
    have e1 := fun u : 𝓢R => h1 A hA b hb (hQmono hn1N hQ) u
    have hT := mo_interp_H_osc d (T := fun f x => b x * f x)
      (fun f g c => by
        funext x; simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]; ring)
      (fun f => by
        have := (mova3b2_bsm b f).memLp 2 volume
        have hf : (⇑(mova3b2_bsm b f) : Euc d → ℝ) = fun x => b x * f x :=
          funext (mova3b2_bsm_apply hb f)
        rwa [hf] at this)
      (r0 := (n0 : ℝ)) (r1 := ((n0 + 1 : ℕ) : ℝ)) (s0 := (n0 : ℝ)) (s1 := ((n0 + 1 : ℕ) : ℝ))
      (M0 := C0 * A) (M1 := C1 * A) (mul_nonneg hC0 hA) (mul_nonneg hC1 hA)
      (fun f => ⟨(e0 f).1, by simpa [mul_assoc] using (e0 f).2⟩)
      (fun f => ⟨(e1 f).1, by simpa [mul_assoc] using (e1 f).2⟩)
      (θ := θ) ⟨hθ0, hθ1⟩ w
    have hσ : (1 - θ) * (n0 : ℝ) + θ * ((n0 + 1 : ℕ) : ℝ) = s := by
      rw [hθ]; push_cast; ring
    rw [hσ] at hT
    refine ⟨hT.1, hT.2.trans (le_of_eq ?_)⟩
    rw [Real.mul_rpow hC0 hA, Real.mul_rpow hC1 hA]
    have : A ^ (1 - θ) * A ^ θ = A := by
      rw [← Real.rpow_add' hA (by linarith : (1 - θ) + θ ≠ 0)]; simp
    calc C0 ^ (1 - θ) * A ^ (1 - θ) * (C1 ^ θ * A ^ θ) *
          Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (⇑w))
        = C0 ^ (1 - θ) * C1 ^ θ * (A ^ (1 - θ) * A ^ θ) *
          Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (⇑w)) := by ring
      _ = _ := by rw [this]

/-! ## Density of real Schwartz functions in `H^t` -/

lemma mova3b2_eLpNorm_sq {h : Euc d → ℂ} (hh : MemLp h 2 (volume : Measure (Euc d))) {ε : ℝ}
    (hε : 0 ≤ ε) (hle : eLpNorm h 2 (volume : Measure (Euc d)) ≤ ENNReal.ofReal ε) :
    ∫ ξ, ‖h ξ‖ ^ 2 ≤ ε ^ 2 := by
  rw [hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hle
  have h1 := (ENNReal.ofReal_le_ofReal_iff hε).1 hle
  simp only [ENNReal.toReal_ofNat] at h1
  have h0 : 0 ≤ ∫ ξ, ‖h ξ‖ ^ (2 : ℝ) := integral_nonneg fun ξ => by positivity
  have e : ∫ ξ, ‖h ξ‖ ^ (2 : ℝ) = ∫ ξ, ‖h ξ‖ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp
  rw [e] at h1 h0
  have := pow_le_pow_left₀ (Real.rpow_nonneg h0 _) h1 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0] at this
  simpa using this

lemma mova3b2_dense (w : Euc d → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hw : MemLp w 2 (volume : Measure (Euc d)))
    (hI : Integrable (fun ξ => mova3b1_W ξ ^ t * ‖fourierL2 w ξ‖ ^ 2) volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : 𝓢R, Integrable (fun ξ => mova3b1_W ξ ^ t * ‖fourierL2 (fun x => u x - w x) ξ‖ ^ 2)
        volume ∧ ∫ ξ, mova3b1_W ξ ^ t * ‖fourierL2 (fun x => u x - w x) ξ‖ ^ 2 ≤ ε ^ 2 := by
  set F0 : Euc d → ℂ := fourierL2 w with hF0
  set G : Euc d → ℂ := fun ξ => ((mova3b1_W ξ ^ (t / 2) : ℝ) : ℂ) * F0 ξ with hG
  have hGm : AEStronglyMeasurable G volume :=
    (Complex.continuous_ofReal.comp (mova3b1_W_rpow_cont (t / 2))).aestronglyMeasurable.mul
      (aestronglyMeasurable_fourierL2 hw)
  have hGn : ∀ ξ, ‖G ξ‖ ^ 2 = mova3b1_W ξ ^ t * ‖F0 ξ‖ ^ 2 := by
    intro ξ
    rw [hG]; simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _), mul_pow,
      mova3_rpow_half_sq (mova3b1_W_pos ξ)]
  have hGL : MemLp G 2 (volume : Measure (Euc d)) :=
    (memLp_two_iff_integrable_sq_norm hGm).2 (hI.congr (Eventually.of_forall fun ξ => (hGn ξ).symm))
  obtain ⟨g, hgc, hgs, hgn⟩ := hGL.exist_eLpNorm_sub_le (p := 2) (by norm_num) (by norm_num) hε
  set Χ : 𝓢C := hgc.toSchwartzMap hgs with hΧ
  have hΧg : (⇑Χ : Euc d → ℂ) = g := rfl
  have hgtg : (fun ξ : Euc d => ((mova3b1_W ξ ^ (-(t / 2)) : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (mova3b2_W_rpow_tg (-(t / 2)))
  set Ψ : 𝓢C := SchwartzMap.smulLeftCLM ℂ
    (fun ξ : Euc d => ((mova3b1_W ξ ^ (-(t / 2)) : ℝ) : ℂ)) Χ with hΨ
  have hΨapp : ∀ ξ, Ψ ξ = ((mova3b1_W ξ ^ (-(t / 2)) : ℝ) : ℂ) * g ξ := by
    intro ξ
    rw [hΨ, SchwartzMap.smulLeftCLM_apply_apply hgtg, smul_eq_mul, hΧg]
  set Δ : Euc d → ℂ := fun ξ => Ψ ξ - F0 ξ with hΔ
  have hΔ' : ∀ ξ, ((mova3b1_W ξ ^ (t / 2) : ℝ) : ℂ) * Δ ξ = g ξ - G ξ := by
    intro ξ
    have h1 : ((mova3b1_W ξ ^ (t / 2) : ℝ) : ℂ) * ((mova3b1_W ξ ^ (-(t / 2)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add (mova3b1_W_pos ξ)]
      simp
    simp only [hΔ, hΨapp, hG]
    linear_combination (g ξ) * h1
  have hΔn : ∀ ξ, mova3b1_W ξ ^ t * ‖Δ ξ‖ ^ 2 = ‖g ξ - G ξ‖ ^ 2 := by
    intro ξ
    have := congrArg (fun z : ℂ => ‖z‖ ^ 2) (hΔ' ξ)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _), mul_pow,
      mova3_rpow_half_sq (mova3b1_W_pos ξ)] at this
    exact this
  have hgL : MemLp g 2 (volume : Measure (Euc d)) := Χ.memLp 2 volume
  have hdiffL : MemLp (fun ξ => g ξ - G ξ) 2 (volume : Measure (Euc d)) := hgL.sub hGL
  have hΔI : Integrable (fun ξ => mova3b1_W ξ ^ t * ‖Δ ξ‖ ^ 2) volume :=
    (hdiffL.norm.integrable_sq).congr (Eventually.of_forall fun ξ => (hΔn ξ).symm)
  have hΔle : ∫ ξ, mova3b1_W ξ ^ t * ‖Δ ξ‖ ^ 2 ≤ ε ^ 2 := by
    have h1 : eLpNorm (fun ξ => g ξ - G ξ) 2 (volume : Measure (Euc d)) ≤ ENNReal.ofReal ε := by
      rw [← eLpNorm_neg]
      convert hgn using 2
      funext ξ; simp
    have := mova3b2_eLpNorm_sq hdiffL hε.le h1
    simpa [hΔn] using this
  -- the real Schwartz approximant
  set φ : 𝓢C := 𝓕⁻ Ψ with hφ
  have hφΨ : (𝓕 φ : 𝓢C) = Ψ := FourierTransform.fourier_fourierInv_eq Ψ
  set u : 𝓢R := mova3b2_re φ with hu
  have huL : MemLp (⇑u) 2 (volume : Measure (Euc d)) := u.memLp 2 volume
  have hdL : MemLp (fun x => u x - w x) 2 (volume : Measure (Euc d)) := huL.sub hw
  have hae : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      fourierL2 (fun x => u x - w x) ξ = (Δ ξ + conj (Δ (-ξ))) / 2 := by
    filter_upwards [fourierL2_sub huL hw, mova3b2_fourierL2_eq u, fourierL2_neg hw] with ξ h1 h2 h3
    rw [h1, h2, mova3b2_fourier_re, hφΨ]
    simp only [hΔ, map_sub]
    rw [hF0, h3, Complex.conj_conj]
    ring
  have hbd : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      mova3b1_W ξ ^ t * ‖fourierL2 (fun x => u x - w x) ξ‖ ^ 2 ≤
        (mova3b1_W ξ ^ t * ‖Δ ξ‖ ^ 2 + mova3b1_W (-ξ) ^ t * ‖Δ (-ξ)‖ ^ 2) / 2 := by
    filter_upwards [hae] with ξ h
    rw [h, mova3b1_W_neg]
    have h1 : ‖(Δ ξ + conj (Δ (-ξ))) / 2‖ ^ 2 ≤ (‖Δ ξ‖ ^ 2 + ‖Δ (-ξ)‖ ^ 2) / 2 := by
      rw [norm_div, div_pow]
      have h2 : ‖Δ ξ + conj (Δ (-ξ))‖ ≤ ‖Δ ξ‖ + ‖Δ (-ξ)‖ := by
        simpa using norm_add_le (Δ ξ) (conj (Δ (-ξ)))
      have h3 : ‖Δ ξ + conj (Δ (-ξ))‖ ^ 2 ≤ (‖Δ ξ‖ + ‖Δ (-ξ)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
      norm_num
      nlinarith [sq_nonneg (‖Δ ξ‖ - ‖Δ (-ξ)‖)]
    have h0 : 0 ≤ mova3b1_W ξ ^ t := Real.rpow_nonneg (mova3b1_W_pos ξ).le _
    calc mova3b1_W ξ ^ t * ‖(Δ ξ + conj (Δ (-ξ))) / 2‖ ^ 2 ≤
          mova3b1_W ξ ^ t * ((‖Δ ξ‖ ^ 2 + ‖Δ (-ξ)‖ ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = _ := by ring
  have hΔI' : Integrable (fun ξ : Euc d => mova3b1_W (-ξ) ^ t * ‖Δ (-ξ)‖ ^ 2) volume :=
    hΔI.comp_neg (μ := (volume : Measure (Euc d)))
  have hR : Integrable (fun ξ : Euc d => (mova3b1_W ξ ^ t * ‖Δ ξ‖ ^ 2 +
      mova3b1_W (-ξ) ^ t * ‖Δ (-ξ)‖ ^ 2) / 2) volume := (hΔI.add hΔI').div_const 2
  have hLm : AEStronglyMeasurable
      (fun ξ => mova3b1_W ξ ^ t * ‖fourierL2 (fun x => u x - w x) ξ‖ ^ 2) volume :=
    (mova3b1_W_rpow_cont t).aestronglyMeasurable.mul
      ((aestronglyMeasurable_fourierL2 hdL).norm.pow 2)
  have hLI : Integrable
      (fun ξ => mova3b1_W ξ ^ t * ‖fourierL2 (fun x => u x - w x) ξ‖ ^ 2) volume := by
    refine hR.mono' hLm ?_
    filter_upwards [hbd] with ξ h
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _) (sq_nonneg _))]
    exact h
  refine ⟨u, hLI, ?_⟩
  calc ∫ ξ, mova3b1_W ξ ^ t * ‖fourierL2 (fun x => u x - w x) ξ‖ ^ 2
      ≤ ∫ ξ, (mova3b1_W ξ ^ t * ‖Δ ξ‖ ^ 2 + mova3b1_W (-ξ) ^ t * ‖Δ (-ξ)‖ ^ 2) / 2 :=
        integral_mono_ae hLI hR hbd
    _ = ∫ ξ, mova3b1_W ξ ^ t * ‖Δ ξ‖ ^ 2 := by
        rw [integral_div, integral_add hΔI hΔI']
        have := integral_neg_eq_self (fun ξ : Euc d => mova3b1_W ξ ^ t * ‖Δ ξ‖ ^ 2)
          (volume : Measure (Euc d))
        rw [this]; ring
    _ ≤ ε ^ 2 := hΔle

/-- Minkowski inequality in the weighted `L²` space `L²(W^s dξ)`. -/
lemma mova3b2_minkowski (s : ℝ) {F G : Euc d → ℂ} (hFm : AEStronglyMeasurable F volume)
    (hGm : AEStronglyMeasurable G volume)
    (hF : Integrable (fun ξ => mova3b1_W ξ ^ s * ‖F ξ‖ ^ 2) volume)
    (hG : Integrable (fun ξ => mova3b1_W ξ ^ s * ‖G ξ‖ ^ 2) volume) :
    Integrable (fun ξ => mova3b1_W ξ ^ s * ‖F ξ + G ξ‖ ^ 2) volume ∧
      Real.sqrt (∫ ξ, mova3b1_W ξ ^ s * ‖F ξ + G ξ‖ ^ 2) ≤
        Real.sqrt (∫ ξ, mova3b1_W ξ ^ s * ‖F ξ‖ ^ 2) +
          Real.sqrt (∫ ξ, mova3b1_W ξ ^ s * ‖G ξ‖ ^ 2) := by
  set P : Euc d → ℝ := fun ξ => mova3b1_W ξ ^ (s / 2) * ‖F ξ‖ with hP
  set Q : Euc d → ℝ := fun ξ => mova3b1_W ξ ^ (s / 2) * ‖G ξ‖ with hQ
  have hP0 : ∀ ξ, 0 ≤ P ξ := fun ξ => mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _)
    (norm_nonneg _)
  have hQ0 : ∀ ξ, 0 ≤ Q ξ := fun ξ => mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _)
    (norm_nonneg _)
  have hPm : AEStronglyMeasurable P volume :=
    (mova3b1_W_rpow_cont (s / 2)).aestronglyMeasurable.mul hFm.norm
  have hQm : AEStronglyMeasurable Q volume :=
    (mova3b1_W_rpow_cont (s / 2)).aestronglyMeasurable.mul hGm.norm
  have hPsq : ∀ ξ, P ξ ^ 2 = mova3b1_W ξ ^ s * ‖F ξ‖ ^ 2 := fun ξ => by
    rw [hP]; simp only; rw [mul_pow, mova3_rpow_half_sq (mova3b1_W_pos ξ)]
  have hQsq : ∀ ξ, Q ξ ^ 2 = mova3b1_W ξ ^ s * ‖G ξ‖ ^ 2 := fun ξ => by
    rw [hQ]; simp only; rw [mul_pow, mova3_rpow_half_sq (mova3b1_W_pos ξ)]
  have hP2 : Integrable (fun ξ => P ξ ^ 2) volume := hF.congr (Eventually.of_forall fun ξ => (hPsq ξ).symm)
  have hQ2 : Integrable (fun ξ => Q ξ ^ 2) volume := hG.congr (Eventually.of_forall fun ξ => (hQsq ξ).symm)
  have hPL : MemLp P 2 volume := (memLp_two_iff_integrable_sq hPm).2 hP2
  have hQL : MemLp Q 2 volume := (memLp_two_iff_integrable_sq hQm).2 hQ2
  have hPQ : Integrable (fun ξ => P ξ * Q ξ) volume := by
    have := hPL.integrable_mul hQL
    exact this
  have hCS := mova3b1_CS hP0 hQ0 hPm hQm hP2 hQ2
  have hpt : ∀ ξ, mova3b1_W ξ ^ s * ‖F ξ + G ξ‖ ^ 2 ≤ P ξ ^ 2 + 2 * (P ξ * Q ξ) + Q ξ ^ 2 := by
    intro ξ
    have h1 : ‖F ξ + G ξ‖ ^ 2 ≤ (‖F ξ‖ + ‖G ξ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    have h0 : 0 ≤ mova3b1_W ξ ^ s := Real.rpow_nonneg (mova3b1_W_pos ξ).le _
    calc mova3b1_W ξ ^ s * ‖F ξ + G ξ‖ ^ 2 ≤ mova3b1_W ξ ^ s * (‖F ξ‖ + ‖G ξ‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = (mova3b1_W ξ ^ (s / 2) * ‖F ξ‖ + mova3b1_W ξ ^ (s / 2) * ‖G ξ‖) ^ 2 := by
          rw [← mul_add, mul_pow, mova3_rpow_half_sq (mova3b1_W_pos ξ)]
      _ = _ := by simp only [hP, hQ]; ring
  have hR : Integrable (fun ξ => P ξ ^ 2 + 2 * (P ξ * Q ξ) + Q ξ ^ 2) volume :=
    (hP2.add (hPQ.const_mul 2)).add hQ2
  have hLm : AEStronglyMeasurable (fun ξ => mova3b1_W ξ ^ s * ‖F ξ + G ξ‖ ^ 2) volume :=
    (mova3b1_W_rpow_cont s).aestronglyMeasurable.mul ((hFm.add hGm).norm.pow 2)
  have hL : Integrable (fun ξ => mova3b1_W ξ ^ s * ‖F ξ + G ξ‖ ^ 2) volume := by
    refine hR.mono' hLm (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _) (sq_nonneg _))]
    exact hpt ξ
  refine ⟨hL, ?_⟩
  set X := Real.sqrt (∫ ξ, P ξ ^ 2) with hX
  set Y := Real.sqrt (∫ ξ, Q ξ ^ 2) with hY
  have hXe : ∫ ξ, mova3b1_W ξ ^ s * ‖F ξ‖ ^ 2 = ∫ ξ, P ξ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun ξ => (hPsq ξ).symm)
  have hYe : ∫ ξ, mova3b1_W ξ ^ s * ‖G ξ‖ ^ 2 = ∫ ξ, Q ξ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun ξ => (hQsq ξ).symm)
  rw [hXe, hYe]
  have hint : ∫ ξ, mova3b1_W ξ ^ s * ‖F ξ + G ξ‖ ^ 2 ≤ (X + Y) ^ 2 := by
    calc _ ≤ ∫ ξ, (P ξ ^ 2 + 2 * (P ξ * Q ξ) + Q ξ ^ 2) := integral_mono hL hR hpt
      _ = (∫ ξ, P ξ ^ 2) + 2 * (∫ ξ, P ξ * Q ξ) + ∫ ξ, Q ξ ^ 2 := by
          have i1 : Integrable (fun ξ => P ξ ^ 2 + 2 * (P ξ * Q ξ)) volume :=
            hP2.add (hPQ.const_mul 2)
          have i2 : Integrable (fun ξ => 2 * (P ξ * Q ξ)) volume := hPQ.const_mul 2
          rw [integral_add i1 hQ2, integral_add hP2 i2, integral_const_mul]
      _ ≤ X ^ 2 + 2 * (X * Y) + Y ^ 2 := by
          have hx : X ^ 2 = ∫ ξ, P ξ ^ 2 := Real.sq_sqrt (integral_nonneg fun ξ => sq_nonneg _)
          have hy : Y ^ 2 = ∫ ξ, Q ξ ^ 2 := Real.sq_sqrt (integral_nonneg fun ξ => sq_nonneg _)
          rw [hx, hy]; linarith
      _ = (X + Y) ^ 2 := by ring
  calc Real.sqrt _ ≤ Real.sqrt ((X + Y) ^ 2) := Real.sqrt_le_sqrt hint
    _ = X + Y := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Real Schwartz functions are dense in `H^s` and in `L²` simultaneously. -/
lemma mova3b2_dense_H {w : Euc d → ℝ} {s : ℝ} (hw : HRS.PDE.ToolboxRd.MemSobolev s w) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ u : 𝓢R, Real.sqrt (∫ x, (u x - w x) ^ 2) ≤ ε ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (⇑u)) ≤
        Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) + ε := by
  obtain ⟨hwL, hwI⟩ := (mova3b1_memSobolev_iff s w).1 hw
  set t : ℝ := max s 0 with ht
  have ht0 : 0 ≤ t := le_max_right _ _
  have hst : s ≤ t := le_max_left _ _
  have hIt : Integrable (fun ξ => mova3b1_W ξ ^ t * ‖fourierL2 w ξ‖ ^ 2) volume := by
    by_cases hs : 0 ≤ s
    · rw [ht, max_eq_left hs]; exact hwI
    · rw [ht, max_eq_right (not_le.1 hs).le]
      simpa using integrable_norm_sq_fourierL2 hwL
  obtain ⟨u, hI, hle⟩ := mova3b2_dense w ht0 hwL hIt hε
  have huL : MemLp (⇑u) 2 (volume : Measure (Euc d)) := u.memLp 2 volume
  have hdL : MemLp (fun x => u x - w x) 2 (volume : Measure (Euc d)) := huL.sub hwL
  set Fd : Euc d → ℂ := fourierL2 (fun x => u x - w x) with hFd
  have hFdm : AEStronglyMeasurable Fd volume := aestronglyMeasurable_fourierL2 hdL
  -- the `L²` closeness
  have h1 : ∫ x, (u x - w x) ^ 2 ≤ ε ^ 2 := by
    rw [integral_sq_eq_norm_sq hdL]
    refine (integral_mono (integrable_norm_sq_fourierL2 hdL) hI fun ξ => ?_).trans hle
    have : 1 ≤ mova3b1_W ξ ^ t := Real.one_le_rpow (mova3b1_W_ge ξ) ht0
    nlinarith [sq_nonneg ‖Fd ξ‖]
  -- the `H^s` closeness
  have hIs : Integrable (fun ξ => mova3b1_W ξ ^ s * ‖Fd ξ‖ ^ 2) volume := by
    refine hI.mono' ((mova3b1_W_rpow_cont s).aestronglyMeasurable.mul (hFdm.norm.pow 2))
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (mova3b1_W_ge ξ) hst) (sq_nonneg _)
  have h2 : ∫ ξ, mova3b1_W ξ ^ s * ‖Fd ξ‖ ^ 2 ≤ ε ^ 2 := by
    refine (integral_mono hIs hI fun ξ => ?_).trans hle
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (mova3b1_W_ge ξ) hst) (sq_nonneg _)
  -- Minkowski
  have hMk := mova3b2_minkowski s (aestronglyMeasurable_fourierL2 hwL) hFdm hwI hIs
  have hFu : ∀ᵐ ξ ∂(volume : Measure (Euc d)), fourierL2 (⇑u) ξ = fourierL2 w ξ + Fd ξ := by
    filter_upwards [fourierL2_sub huL hwL] with ξ h
    rw [hFd, h]; ring
  have hEq : HRS.PDE.ToolboxRd.sobolevNormSq s (⇑u) =
      ∫ ξ, mova3b1_W ξ ^ s * ‖fourierL2 w ξ + Fd ξ‖ ^ 2 := by
    rw [mova3b1_sobolevNormSq_eq]
    refine integral_congr_ae ?_
    filter_upwards [hFu] with ξ h
    rw [h]
  refine ⟨u, ?_, ?_⟩
  · calc Real.sqrt (∫ x, (u x - w x) ^ 2) ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt h1
      _ = ε := Real.sqrt_sq hε.le
  · rw [hEq]
    refine hMk.2.trans ?_
    have hw' : HRS.PDE.ToolboxRd.sobolevNormSq s w = ∫ ξ, mova3b1_W ξ ^ s * ‖fourierL2 w ξ‖ ^ 2 := rfl
    rw [hw']
    have : Real.sqrt (∫ ξ, mova3b1_W ξ ^ s * ‖Fd ξ‖ ^ 2) ≤ ε := by
      calc _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt h2
        _ = ε := Real.sqrt_sq hε.le
    linarith

lemma mova3b2_pair_le {u v : Euc d → ℝ} (hu : MemLp u 2 (volume : Measure (Euc d)))
    (hv : MemLp v 2 (volume : Measure (Euc d))) :
    |∫ x, u x * v x| ≤ Real.sqrt (∫ x, u x ^ 2) * Real.sqrt (∫ x, v x ^ 2) := by
  have hP2 : Integrable (fun x => |u x| ^ 2) volume := by
    simpa [sq_abs] using hu.integrable_sq
  have hQ2 : Integrable (fun x => |v x| ^ 2) volume := by
    simpa [sq_abs] using hv.integrable_sq
  have hCS := mova3b1_CS (P := fun x => |u x|) (Q := fun x => |v x|) (fun x => abs_nonneg _)
    (fun x => abs_nonneg _) hu.aestronglyMeasurable.norm hv.aestronglyMeasurable.norm hP2 hQ2
  simp only [sq_abs] at hCS
  calc |∫ x, u x * v x| ≤ ∫ x, |u x * v x| := abs_integral_le_integral_abs
    _ = ∫ x, |u x| * |v x| := by simp only [abs_mul]
    _ ≤ _ := hCS

lemma mova3b2_mulL2 {a : Euc d → ℝ} (ha : Measurable a) {A0 : ℝ} (hab : ∀ x, |a x| ≤ A0)
    {u : Euc d → ℝ} (hu : MemLp u 2 (volume : Measure (Euc d))) :
    MemLp (fun x => a x * u x) 2 (volume : Measure (Euc d)) := by
  have hA0 : 0 ≤ A0 := (abs_nonneg _).trans (hab 0)
  refine (hu.norm.const_mul A0).of_le (ha.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hA0]
  exact mul_le_mul_of_nonneg_right (hab x) (abs_nonneg _)

/-- Pairing bound for the multiplied Schwartz approximant. -/
lemma mova3b2_ext_pair {a : Euc d → ℝ} (ha : Measurable a) {A0 : ℝ} (hab : ∀ x, |a x| ≤ A0)
    {s K : ℝ} (hK : 0 ≤ K)
    (h : ∀ φ : 𝓢R, MemOsc s (fun x => a x * φ x) ∧
      oscNorm s (fun x => a x * φ x) ≤
        K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (⇑φ)))
    {w : Euc d → ℝ} (hw : HRS.PDE.ToolboxRd.MemSobolev s w) {g : Euc d → ℝ}
    (hgL : MemLp g 2 (volume : Measure (Euc d))) (hgO : MemOsc (-s) g)
    (hg : oscNorm (-s) g ≤ 1) :
    |∫ x, a x * w x * g x| ≤ K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) := by
  have hA0 : 0 ≤ A0 := (abs_nonneg _).trans (hab 0)
  have hwL : MemLp w 2 (volume : Measure (Euc d)) := hw.1
  set X : ℝ := Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) with hX
  set G2 : ℝ := Real.sqrt (∫ x, g x ^ 2) with hG2
  have hG20 : 0 ≤ G2 := Real.sqrt_nonneg _
  refine le_of_forall_pos_le_add fun η hη => ?_
  set ε : ℝ := η / (K + A0 * G2 + 1) with hε
  have hden : 0 < K + A0 * G2 + 1 := by positivity
  have hεpos : 0 < ε := div_pos hη hden
  obtain ⟨u, hu1, hu2⟩ := mova3b2_dense_H hw hεpos
  have huL : MemLp (⇑u) 2 (volume : Measure (Euc d)) := u.memLp 2 volume
  have hau : MemLp (fun x => a x * u x) 2 (volume : Measure (Euc d)) := mova3b2_mulL2 ha hab huL
  have hawu : MemLp (fun x => a x * (w x - u x)) 2 (volume : Measure (Euc d)) :=
    mova3b2_mulL2 ha hab (hwL.sub huL)
  have i1 : Integrable (fun x => a x * u x * g x) volume := hau.integrable_mul hgL
  have i2 : Integrable (fun x => a x * (w x - u x) * g x) volume := hawu.integrable_mul hgL
  have hsplit : ∫ x, a x * w x * g x = (∫ x, a x * u x * g x) + ∫ x, a x * (w x - u x) * g x := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have b1 : |∫ x, a x * u x * g x| ≤ K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (⇑u)) := by
    have hu' : MemOsc (- -s) (fun x => a x * u x) := by rw [neg_neg]; exact (h u).1
    have hh := mo_dual_le (-s) hu' hgO
    rw [neg_neg] at hh
    refine hh.trans ?_
    calc oscNorm s (fun x => a x * u x) * oscNorm (-s) g ≤
          (K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (⇑u))) * 1 :=
          mul_le_mul (h u).2 hg (Real.sqrt_nonneg _) (mul_nonneg hK (Real.sqrt_nonneg _))
      _ = _ := mul_one _
  have b2 : |∫ x, a x * (w x - u x) * g x| ≤ A0 * ε * G2 := by
    refine (mova3b2_pair_le hawu hgL).trans ?_
    have hI : Integrable (fun x => A0 ^ 2 * (u x - w x) ^ 2) volume :=
      (huL.sub hwL).integrable_sq.const_mul _
    have hsq : ∫ x, (a x * (w x - u x)) ^ 2 ≤ A0 ^ 2 * ∫ x, (u x - w x) ^ 2 := by
      rw [← integral_const_mul]
      refine integral_mono hawu.integrable_sq hI fun x => ?_
      have e1 : (u x - w x) ^ 2 = (w x - u x) ^ 2 := by ring
      have e2 : a x ^ 2 ≤ A0 ^ 2 := by
        rw [← sq_abs (a x)]; exact pow_le_pow_left₀ (abs_nonneg _) (hab x) 2
      show (a x * (w x - u x)) ^ 2 ≤ A0 ^ 2 * (u x - w x) ^ 2
      rw [mul_pow, e1]
      exact mul_le_mul_of_nonneg_right e2 (sq_nonneg _)
    have hsq' : Real.sqrt (∫ x, (a x * (w x - u x)) ^ 2) ≤ A0 * ε := by
      calc _ ≤ Real.sqrt (A0 ^ 2 * ∫ x, (u x - w x) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = A0 * Real.sqrt (∫ x, (u x - w x) ^ 2) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0]
        _ ≤ A0 * ε := mul_le_mul_of_nonneg_left hu1 hA0
    exact mul_le_mul_of_nonneg_right hsq' hG20
  calc |∫ x, a x * w x * g x| ≤ |∫ x, a x * u x * g x| + |∫ x, a x * (w x - u x) * g x| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ K * (X + ε) + A0 * ε * G2 := add_le_add (b1.trans (mul_le_mul_of_nonneg_left hu2 hK)) b2
    _ = K * X + ε * (K + A0 * G2) := by ring
    _ ≤ K * X + η := by
        have h1 : ε * (K + A0 * G2 + 1) = η := by rw [hε]; field_simp
        nlinarith [hεpos]

/-- **Extension lemma (Schwartz → `H^s`).**  If a bounded measurable multiplier `a` satisfies
`‖a φ‖_{Σ^s} ≤ K ‖φ‖_{H^s}` for all real Schwartz `φ`, then the same holds for every `w ∈ H^s`
(`MemSobolev s w`), and in particular `a w ∈ Σ^s`.  Proof by duality with finite Hermite sums
(`mo_memOsc_neg_of_dual_bdd`) and the density of Schwartz functions (`mova3b2_dense_H`). -/
theorem mova3b2_ext_mult {a : Euc d → ℝ} (ha : Measurable a) {A0 : ℝ} (hab : ∀ x, |a x| ≤ A0)
    {s K : ℝ} (hK : 0 ≤ K)
    (h : ∀ φ : 𝓢R, MemOsc s (fun x => a x * φ x) ∧
      oscNorm s (fun x => a x * φ x) ≤
        K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (⇑φ)))
    {w : Euc d → ℝ} (hw : HRS.PDE.ToolboxRd.MemSobolev s w) :
    MemOsc s (fun x => a x * w x) ∧
      oscNorm s (fun x => a x * w x) ≤
        K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) := by
  have hf : MemLp (fun x => a x * w x) 2 (volume : Measure (Euc d)) :=
    mova3b2_mulL2 ha hab hw.1
  have hM : ∀ t ∈ mo_dualSet (-s) (fun x => a x * w x),
      t ≤ K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) := by
    rintro t ⟨S, c, hg, rfl⟩
    exact mova3b2_ext_pair ha hab hK h hw (mova2_hsum_memLp S c) (mo_hsum_memOsc (-s) S c) hg
  have key := mo_memOsc_neg_of_dual_bdd (-s) hf hM
  simpa only [neg_neg] using key


/-! ## `B2` for `H^s` inputs, all real `s ≤ N` -/

lemma mova3b2_Q_abs {K m : ℕ} {A : ℝ} {b : Euc d → ℝ} (h : mova3b2_Q K m A b) (x : Euc d) :
    |b x| ≤ A := by
  have h1 := mova3b2_Q_top h x
  have h2 : 1 ≤ (1 + ‖x‖) ^ m := one_le_pow₀ (by linarith [norm_nonneg x])
  calc |b x| = |b x| * 1 := (mul_one _).symm
    _ ≤ |b x| * (1 + ‖x‖) ^ m := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ ≤ A := h1

lemma mova3b2_Q_iter : ∀ {K m : ℕ} {A : ℝ} {b : Euc d → ℝ}, mova3b2_Q K m A b →
    ∀ (j : Fin d) (i : ℕ), i ≤ K → ∀ x, |(mova3b1_Dj j)^[i] b x| ≤ A := by
  intro K
  induction K with
  | zero =>
    intro m A b h j i hi x
    have : i = 0 := by omega
    subst this
    simpa using mova3b2_Q_abs h x
  | succ K ih =>
    intro m A b h j i hi x
    cases i with
    | zero => simpa using mova3b2_Q_abs h x
    | succ i =>
      rw [Function.iterate_succ_apply]
      exact ih (h.2 j) j i (by omega) x

/-- **`B2`, nonnegative index, `H^s` inputs**: for `0 ≤ s ≤ N`,
`‖a w‖_{Σ^s} ≤ C A ‖w‖_{H^s}` for every `w` with `MemSobolev s w`. -/
theorem mova3b2_B2_pos (s : ℝ) (hs : 0 ≤ s) (N : ℕ) (hN : s ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (b : Euc d → ℝ), b.HasTemperateGrowth →
      mova3b2_Q N N A b → ∀ w : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev s w →
        MemOsc s (fun x => b x * w x) ∧
          oscNorm s (fun x => b x * w x) ≤
            C * A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) := by
  obtain ⟨C, hC, hCb⟩ := mova3b2_B2_schwartz (d := d) s hs N hN
  refine ⟨C, hC, fun A hA b hb hQ w hw => ?_⟩
  exact mova3b2_ext_mult (a := b) hb.1.continuous.measurable (A0 := A) (fun x => mova3b2_Q_abs hQ x)
    (mul_nonneg hC hA) (fun φ => hCb A hA b hb hQ φ) hw

/-- Sobolev duality `|⟨w, v⟩| ≤ ‖w‖_{H^s} ‖v‖_{H^{-s}}`. -/
lemma mova3b2_sob_pair {w v : Euc d → ℝ} {s : ℝ} (hw : HRS.PDE.ToolboxRd.MemSobolev s w)
    (hv : HRS.PDE.ToolboxRd.MemSobolev (-s) v) :
    |∫ x, w x * v x| ≤ Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) *
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (-s) v) := by
  obtain ⟨hwL, hwI⟩ := (mova3b1_memSobolev_iff s w).1 hw
  obtain ⟨hvL, hvI⟩ := (mova3b1_memSobolev_iff (-s) v).1 hv
  set P : Euc d → ℝ := fun ξ => mova3b1_W ξ ^ (s / 2) * ‖fourierL2 w ξ‖ with hP
  set Q : Euc d → ℝ := fun ξ => mova3b1_W ξ ^ (-s / 2) * ‖fourierL2 v ξ‖ with hQ
  have hP0 : ∀ ξ, 0 ≤ P ξ := fun ξ => mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _)
    (norm_nonneg _)
  have hQ0 : ∀ ξ, 0 ≤ Q ξ := fun ξ => mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _)
    (norm_nonneg _)
  have hPm : AEStronglyMeasurable P volume :=
    (mova3b1_W_rpow_cont (s / 2)).aestronglyMeasurable.mul
      (aestronglyMeasurable_fourierL2 hwL).norm
  have hQm : AEStronglyMeasurable Q volume :=
    (mova3b1_W_rpow_cont (-s / 2)).aestronglyMeasurable.mul
      (aestronglyMeasurable_fourierL2 hvL).norm
  have hPsq : ∀ ξ, P ξ ^ 2 = mova3b1_W ξ ^ s * ‖fourierL2 w ξ‖ ^ 2 := fun ξ => by
    rw [hP]; simp only; rw [mul_pow, mova3_rpow_half_sq (mova3b1_W_pos ξ)]
  have hQsq : ∀ ξ, Q ξ ^ 2 = mova3b1_W ξ ^ (-s) * ‖fourierL2 v ξ‖ ^ 2 := fun ξ => by
    rw [hQ]; simp only; rw [mul_pow, mova3_rpow_half_sq (mova3b1_W_pos ξ)]
  have hP2 : Integrable (fun ξ => P ξ ^ 2) volume :=
    hwI.congr (Eventually.of_forall fun ξ => (hPsq ξ).symm)
  have hQ2 : Integrable (fun ξ => Q ξ ^ 2) volume :=
    hvI.congr (Eventually.of_forall fun ξ => (hQsq ξ).symm)
  have hCS := mova3b1_CS hP0 hQ0 hPm hQm hP2 hQ2
  have hPQ : ∀ ξ, P ξ * Q ξ = ‖fourierL2 w ξ‖ * ‖fourierL2 v ξ‖ := by
    intro ξ
    have hW := mova3b1_W_pos ξ
    have : mova3b1_W ξ ^ (s / 2) * mova3b1_W ξ ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add hW, show s / 2 + -s / 2 = 0 by ring, Real.rpow_zero]
    calc P ξ * Q ξ = (mova3b1_W ξ ^ (s / 2) * mova3b1_W ξ ^ (-s / 2)) *
          (‖fourierL2 w ξ‖ * ‖fourierL2 v ξ‖) := by simp only [hP, hQ]; ring
      _ = _ := by rw [this, one_mul]
  have hint : Integrable (fun ξ => ‖fourierL2 w ξ * conj (fourierL2 v ξ)‖) volume := by
    have := (integrable_fourierL2_mul_conj hwL hvL).norm
    exact this
  calc |∫ x, w x * v x| = |(∫ ξ, fourierL2 w ξ * conj (fourierL2 v ξ)).re| := by
        rw [integral_mul_eq_re_fourierL2 hwL hvL]
    _ ≤ ‖∫ ξ, fourierL2 w ξ * conj (fourierL2 v ξ)‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ ξ, ‖fourierL2 w ξ * conj (fourierL2 v ξ)‖ := norm_integral_le_integral_norm _
    _ = ∫ ξ, P ξ * Q ξ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        show ‖fourierL2 w ξ * conj (fourierL2 v ξ)‖ = P ξ * Q ξ
        rw [hPQ, norm_mul, Complex.norm_conj]
    _ ≤ Real.sqrt (∫ ξ, P ξ ^ 2) * Real.sqrt (∫ ξ, Q ξ ^ 2) := hCS
    _ = _ := by
        rw [mova3b1_sobolevNormSq_eq, mova3b1_sobolevNormSq_eq]
        congr 2
        · exact integral_congr_ae (Eventually.of_forall hPsq)
        · exact integral_congr_ae (Eventually.of_forall hQsq)

/-- **`B2`, nonpositive index** (duality with `B1`): for `s ≤ 0` and `b` smooth of temperate growth
with all coordinate partial derivatives of order `≤ ⌈-s⌉` bounded by `A`, `‖b w‖_{Σ^s} ≤ C A ‖w‖_{H^s}`
for every `w` with `MemSobolev s w`. -/
theorem mova3b2_B2_neg (s : ℝ) (hs : s ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (b : Euc d → ℝ), b.HasTemperateGrowth →
      mova3b2_Q ⌈-s⌉₊ 0 A b → ∀ w : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev s w →
        MemOsc s (fun x => b x * w x) ∧
          oscNorm s (fun x => b x * w x) ≤
            C * A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) := by
  obtain ⟨C, hC, hB1⟩ := mo_bridge1 (d := d) (-s) (by linarith) ⌈-s⌉₊ (Nat.le_ceil _)
  refine ⟨C, hC, fun A hA b hb hQ w hw => ?_⟩
  have hbm : Measurable b := hb.1.continuous.measurable
  have hbA : ∀ x, |b x| ≤ A := fun x => mova3b2_Q_abs hQ x
  have hf : MemLp (fun x => b x * w x) 2 (volume : Measure (Euc d)) :=
    mova3b2_mulL2 hbm hbA hw.1
  set X : ℝ := Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hM : ∀ t ∈ mo_dualSet (-s) (fun x => b x * w x), t ≤ C * A * X := by
    rintro t ⟨S, c, hg, rfl⟩
    have hmem : mo_hsum S c ∈ mo_Hspan d := mova3_comb_mem S c
    have hB := hB1 b A hbA (hb.1.of_le (by exact_mod_cast le_top))
      (fun j i hi x => mova3b2_Q_iter hQ j i hi x) (mo_hsum S c) hmem
    have hpair := mova3b2_sob_pair hw hB.1
    have hsw : ∫ x, b x * w x * mo_hsum S c x = ∫ x, w x * (b x * mo_hsum S c x) :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    show |∫ x, b x * w x * mo_hsum S c x| ≤ C * A * X
    rw [hsw]
    refine hpair.trans ?_
    calc X * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (-s) (fun x => b x * mo_hsum S c x))
        ≤ X * (C * A * oscNorm (-s) (mo_hsum S c)) := mul_le_mul_of_nonneg_left hB.2 hX0
      _ ≤ X * (C * A * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (mul_nonneg hC hA)) hX0
      _ = _ := by ring
  have key := mo_memOsc_neg_of_dual_bdd (-s) hf hM
  simpa only [neg_neg] using key

/-- **`B2`, all real `s ≤ N`.** `C = C(d, s, N)`; `b` smooth of temperate growth with all coordinate
partial derivatives of order `≤ max N ⌈-s⌉` bounded by `A (1+‖x‖)^{-N}` (`mova3b2_Q`, i.e.
`|D^γ b| ≤ A ⟨x⟩^{-N}` for `|γ| ≤ max N ⌈-s⌉`). Conclusion for every `w ∈ H^s`:
`b w ∈ Σ^s`, `‖b w‖_{Σ^s} ≤ C A ‖w‖_{H^s}`. -/
theorem mo_bridge2 (s : ℝ) (N : ℕ) (hN : s ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (b : Euc d → ℝ), b.HasTemperateGrowth →
      mova3b2_Q (max N ⌈-s⌉₊) N A b → ∀ w : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev s w →
        MemOsc s (fun x => b x * w x) ∧
          oscNorm s (fun x => b x * w x) ≤
            C * A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s w) := by
  rcases le_or_gt 0 s with hs | hs
  · obtain ⟨C, hC, h⟩ := mova3b2_B2_pos (d := d) s hs N hN
    exact ⟨C, hC, fun A hA b hb hQ w hw =>
      h A hA b hb (mova3b2_Q_mono_K (le_max_left _ _) hQ) w hw⟩
  · obtain ⟨C, hC, h⟩ := mova3b2_B2_neg (d := d) s hs.le
    exact ⟨C, hC, fun A hA b hb hQ w hw =>
      h A hA b hb (mova3b2_Q_mono_m (Nat.zero_le N) (mova3b2_Q_mono_K (le_max_right _ _) hQ)) w hw⟩

/-- Criterion for `mova3b2_Q`: `‖D^k b(x)‖ ≤ A (1+‖x‖)^{-m}` for `k ≤ K` (Fréchet derivatives). -/
lemma mova3b2_Q_of_iter : ∀ {K m : ℕ} {A : ℝ} {b : Euc d → ℝ}, ContDiff ℝ ∞ b →
    (∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k b x‖ * (1 + ‖x‖) ^ m ≤ A) → mova3b2_Q K m A b := by
  intro K
  induction K with
  | zero =>
    intro m A b hb h x
    have := h 0 le_rfl x
    rwa [norm_iteratedFDeriv_zero] at this
  | succ K ih =>
    intro m A b hb h
    refine ⟨fun x => ?_, fun j => ?_⟩
    · have := h 0 (Nat.zero_le _) x
      rwa [norm_iteratedFDeriv_zero] at this
    · refine ih (mova3b2_contDiff_Dj j hb) (fun k hk x => ?_)
      have hdf : ContDiff ℝ ∞ (fderiv ℝ b) := hb.fderiv_right (m := ∞) le_rfl
      have e : mova3b1_Dj j b =
          (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)) ∘ fderiv ℝ b :=
        rfl
      have h1 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d))
        hdf.contDiffAt (x := x) (n := k) (by first | simp | exact_mod_cast le_top | exact (by norm_cast; exact le_top))
      have h2 : ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
        simp only [ContinuousLinearMap.apply_apply, one_mul]
        refine (L.le_opNorm _).trans ?_
        simp
      rw [e]
      have h3 : ‖iteratedFDeriv ℝ k (fderiv ℝ b) x‖ = ‖iteratedFDeriv ℝ (k + 1) b x‖ :=
        norm_iteratedFDeriv_fderiv
      calc ‖iteratedFDeriv ℝ k ((ContinuousLinearMap.apply ℝ ℝ
            (EuclideanSpace.single j (1 : ℝ) : Euc d)) ∘ fderiv ℝ b) x‖ * (1 + ‖x‖) ^ m
          ≤ (‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)‖ *
              ‖iteratedFDeriv ℝ k (fderiv ℝ b) x‖) * (1 + ‖x‖) ^ m :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (1 * ‖iteratedFDeriv ℝ (k + 1) b x‖) * (1 + ‖x‖) ^ m := by
            rw [h3]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
              (by positivity)
        _ ≤ A := by rw [one_mul]; exact h (k + 1) (by omega) x


end HRS.MS.MovOsc
