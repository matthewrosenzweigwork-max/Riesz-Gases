import HRS.Whole.MovtrAux4

/-!
# Packet MPRGEN, stage 2: the cancellation-convention convolution operator and its derivatives

For a kernel `κ : ℝ^d → ℝ` with `|κ(z)| ≤ σ|z|^{-s-1}` (`0 ≤ s < d`) and `g : ℝ^d → F` (`F` Banach) put
`rgT κ g (x) = ∫ κ(z) • (g(x-z) - 1_{|z| ≤ 1/4} g(x)) dz` (the cancellation convention of `convGradConvW`,
after `y = x - z`).  If `g` is `C^{m+2}` with `|D^l g(y)| ≤ a_l (1+|y|)^{-(d+1)}`, then `rgT κ g` is `C^m` and
`‖D^l (rgT κ g)(x)‖ ≤ σ (I_s a_{l+1} + 4^{s+1} W a_l)` (`l ≤ m`).  Proof: differentiation under the integral
sign, `D (rgT κ g) = rgT κ (D g)` (with `F` replaced by `ℝ^d →L F`), by induction on `m`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.RdGen
open HRS HRS.Whole

variable {d : ℕ}

/-- `g(x - z) - 1_{|z|≤1/4} g(x)`. -/
def rgR {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Euc d → F) (x z : Euc d) : F :=
  if ‖z‖ ≤ 1 / 4 then g (x - z) - g x else g (x - z)

/-- The convolution `∫ κ(z) • (g(x-z) - 1_{|z|≤1/4} g(x)) dz`. -/
def rgT {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (κ : Euc d → ℝ) (g : Euc d → F)
    (x : Euc d) : F :=
  ∫ z, κ z • rgR g x z

/-- The kernel hypothesis: `κ` measurable, `|κ(z)| ≤ σ |z|^{-s-1}`. -/
structure RgKer (d : ℕ) (s σ : ℝ) (κ : Euc d → ℝ) : Prop where
  sigma_nonneg : 0 ≤ σ
  meas : Measurable κ
  bound : ∀ z : Euc d, z ≠ 0 → |κ z| ≤ σ * ‖z‖ ^ (-s - 1)

/-- `∫_{|z| ≤ 1/4} |z|^{-s} dz`. -/
def rgNear (d : ℕ) (s : ℝ) : ℝ := ∫ z in Metric.closedBall (0 : Euc d) (1 / 4), ‖z‖ ^ (-s)

/-- `∫ (1+|y|)^{-(d+1)} dy`. -/
def rgW (d : ℕ) : ℝ := ∫ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1))

/-- The decay class: `C^n` with `‖D^l g(y)‖ ≤ a_l (1+|y|)^{-(d+1)}` for `l ≤ n`. -/
def RgDecay {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) (a : ℕ → ℝ)
    (g : Euc d → F) : Prop :=
  ContDiff ℝ n g ∧ ∀ l, l ≤ n → ∀ y : Euc d, ‖iteratedFDeriv ℝ l g y‖ ≤ a l * (1 + ‖y‖) ^ (-((d : ℝ) + 1))

/-- The integrable majorant. -/
def rgMaj (d : ℕ) (s σ b0 b1 : ℝ) (x z : Euc d) : ℝ :=
  σ * (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (fun z => b1 * ‖z‖ ^ (-s)) z +
    4 ^ (s + 1) * b0 * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1)))

section Basic
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma rg_pow_far {s : ℝ} (hs0 : 0 ≤ s) {z : Euc d} (hz : 1 / 4 < ‖z‖) :
    ‖z‖ ^ (-s - 1) ≤ 4 ^ (s + 1) := by
  have h5 : ((1 / 4 : ℝ)) ^ (-s - 1) = 4 ^ (s + 1) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_sub', neg_neg]
    ring_nf
  rw [← h5]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hz.le (by linarith)

lemma rg_norm_le {s σ : ℝ} (hs0 : 0 ≤ s) {κ : Euc d → ℝ} (hκ : RgKer d s σ κ) {g : Euc d → F}
    (hg : Differentiable ℝ g) {b0 b1 : ℝ} (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (h0 : ∀ y, ‖g y‖ ≤ b0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ b1) (x z : Euc d) (hz : z ≠ 0) :
    ‖κ z • rgR g x z‖ ≤ rgMaj d s σ b0 b1 x z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hσ := hκ.sigma_nonneg
  have hD := hκ.bound z hz
  rw [norm_smul, Real.norm_eq_abs]
  unfold rgR rgMaj
  by_cases hB : ‖z‖ ≤ 1 / 4
  · have hmem : z ∈ Metric.closedBall (0 : Euc d) (1 / 4) := by simpa using hB
    rw [Set.indicator_of_mem hmem]
    simp only [hB, ite_true]
    have hmv : ‖g (x - z) - g x‖ ≤ b1 * ‖z‖ := by
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := g) (C := b1) (s := Set.univ)
        (x := x) (y := x - z) (fun y _ => hg y) (fun y _ => h1 y) convex_univ (Set.mem_univ _)
        (Set.mem_univ _)
      simpa using this
    have e : ‖z‖ ^ (-s - 1) * ‖z‖ = ‖z‖ ^ (-s) := by
      rw [← Real.rpow_add_one hzpos.ne']; congr 1; ring
    calc |κ z| * ‖g (x - z) - g x‖
        ≤ (σ * ‖z‖ ^ (-s - 1)) * (b1 * ‖z‖) :=
          mul_le_mul hD hmv (norm_nonneg _) (mul_nonneg hσ (Real.rpow_nonneg hzpos.le _))
      _ = σ * (b1 * (‖z‖ ^ (-s - 1) * ‖z‖)) := by ring
      _ = σ * (b1 * ‖z‖ ^ (-s)) := by rw [e]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hσ
        have : 0 ≤ 4 ^ (s + 1) * b0 * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1)) := by positivity
        linarith
  · have hnmem : z ∉ Metric.closedBall (0 : Euc d) (1 / 4) := by simpa using hB
    rw [Set.indicator_of_notMem hnmem]
    simp only [hB, ite_false]
    push Not at hB
    have h4 := rg_pow_far (d := d) hs0 hB
    calc |κ z| * ‖g (x - z)‖
        ≤ (σ * 4 ^ (s + 1)) * (b0 * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1))) := by
          apply mul_le_mul _ (h0 (x - z)) (norm_nonneg _) (by positivity)
          exact hD.trans (mul_le_mul_of_nonneg_left h4 hσ)
      _ = σ * (4 ^ (s + 1) * b0 * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1))) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hσ
        have : 0 ≤ b1 * ‖z‖ ^ (-s) := mul_nonneg hb1 (Real.rpow_nonneg hzpos.le _)
        linarith

lemma rg_near_integrable (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.closedBall (0 : Euc d) (1 / 4)) := by
  have hdim : 1 ≤ Module.finrank ℝ (Euc d) := by simpa using hd
  have h1 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.ball 0 (1 / 2)) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) hdim (C := 1) (α := s) (r := 1 / 2)
      (by simpa using hsd) ?_ ?_
    · refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun z _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), one_mul]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  refine h1.mono_set ?_
  intro z hz
  simp only [Metric.mem_closedBall, dist_zero_right] at hz
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

lemma rg_W_integrable (hd : 1 ≤ d) :
    Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) := by
  apply integrable_one_add_norm
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  linarith

lemma rg_maj_integrable (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) (σ b0 b1 : ℝ) (x : Euc d) :
    Integrable (rgMaj d s σ b0 b1 x) := by
  have h2 : Integrable (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
      (fun z => b1 * ‖z‖ ^ (-s))) := by
    rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact (rg_near_integrable hd hsd).const_mul b1
  have h3 : Integrable (fun z : Euc d => (1 + ‖x - z‖) ^ (-((d : ℝ) + 1))) :=
    (rg_W_integrable hd).comp_sub_left x
  unfold rgMaj
  exact (h2.add (h3.const_mul _)).const_mul _

lemma rg_integral_maj (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) (σ b0 b1 : ℝ) (x : Euc d) :
    ∫ z, rgMaj d s σ b0 b1 x z = σ * (b1 * rgNear d s + 4 ^ (s + 1) * b0 * rgW d) := by
  have h2 : Integrable (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
      (fun z => b1 * ‖z‖ ^ (-s))) := by
    rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact (rg_near_integrable hd hsd).const_mul b1
  have h3 : Integrable (fun z : Euc d => (1 + ‖x - z‖) ^ (-((d : ℝ) + 1))) :=
    (rg_W_integrable hd).comp_sub_left x
  unfold rgMaj
  rw [integral_const_mul, integral_add h2 (h3.const_mul _), integral_indicator
    Metric.isClosed_closedBall.measurableSet, integral_const_mul, integral_const_mul]
  have : ∫ z : Euc d, (1 + ‖x - z‖) ^ (-((d : ℝ) + 1)) = rgW d := by
    unfold rgW
    exact integral_sub_left_eq_self (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) volume x
  rw [this]
  unfold rgNear
  ring


lemma rg_rgR_eq (g : Euc d → F) (x z : Euc d) :
    rgR g x z = g (x - z) - Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (fun _ => g x) z := by
  unfold rgR
  by_cases h : ‖z‖ ≤ 1 / 4
  · have : z ∈ Metric.closedBall (0 : Euc d) (1 / 4) := by simpa using h
    rw [if_pos h, Set.indicator_of_mem this]
  · have : z ∉ Metric.closedBall (0 : Euc d) (1 / 4) := by simpa using h
    rw [if_neg h, Set.indicator_of_notMem this, sub_zero]

lemma rg_aesm {κ : Euc d → ℝ} (hκm : Measurable κ) {g : Euc d → F} (hg : Continuous g) (x : Euc d) :
    AEStronglyMeasurable (fun z => κ z • rgR g x z) volume := by
  have : (fun z => κ z • rgR g x z) = fun z => κ z •
      (g (x - z) - Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (fun _ => g x) z) := by
    funext z; rw [rg_rgR_eq]
  rw [this]
  refine hκm.aestronglyMeasurable.smul ?_
  refine AEStronglyMeasurable.sub ?_ ?_
  · exact (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact (aestronglyMeasurable_const).indicator Metric.isClosed_closedBall.measurableSet

lemma rg_integrable (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {g : Euc d → F} (hg : Differentiable ℝ g) {b0 b1 : ℝ} (hb0 : 0 ≤ b0)
    (hb1 : 0 ≤ b1) (h0 : ∀ y, ‖g y‖ ≤ b0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ b1) (x : Euc d) :
    Integrable (fun z => κ z • rgR g x z) := by
  refine Integrable.mono' (rg_maj_integrable hd hsd σ b0 b1 x)
    (rg_aesm hκ.meas hg.continuous x) ?_
  filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
  exact rg_norm_le hs0 hκ hg hb0 hb1 h0 h1 x z hz

lemma rg_norm_T_le (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {g : Euc d → F} (hg : Differentiable ℝ g) {b0 b1 : ℝ} (hb0 : 0 ≤ b0)
    (hb1 : 0 ≤ b1) (h0 : ∀ y, ‖g y‖ ≤ b0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ b1) (x : Euc d) :
    ‖rgT κ g x‖ ≤ σ * (b1 * rgNear d s + 4 ^ (s + 1) * b0 * rgW d) := by
  unfold rgT
  rw [← rg_integral_maj hd hsd σ b0 b1 x]
  refine norm_integral_le_of_norm_le (rg_maj_integrable hd hsd σ b0 b1 x) ?_
  filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
  exact rg_norm_le hs0 hκ hg hb0 hb1 h0 h1 x z hz

lemma rg_peetre {x x0 : Euc d} (z : Euc d) (h : ‖x - x0‖ < 1) :
    (1 + ‖x - z‖) ^ (-((d : ℝ) + 1)) ≤ 2 ^ ((d : ℝ) + 1) * (1 + ‖x0 - z‖) ^ (-((d : ℝ) + 1)) := by
  have hA : 0 < 1 + ‖x - z‖ := by positivity
  have hB : 0 < 1 + ‖x0 - z‖ := by positivity
  have h1 : ‖x0 - z‖ ≤ ‖x0 - x‖ + ‖x - z‖ := by
    calc ‖x0 - z‖ = ‖(x0 - x) + (x - z)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖x0 - x‖ < 1 := by rw [norm_sub_rev]; exact h
  have hle : (1 + ‖x0 - z‖) / 2 ≤ 1 + ‖x - z‖ := by linarith [norm_nonneg (x - z)]
  have hp : -((d : ℝ) + 1) ≤ 0 := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  calc (1 + ‖x - z‖) ^ (-((d : ℝ) + 1)) ≤ ((1 + ‖x0 - z‖) / 2) ^ (-((d : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle hp
    _ = 2 ^ ((d : ℝ) + 1) * (1 + ‖x0 - z‖) ^ (-((d : ℝ) + 1)) := by
        have h6 : ((2 : ℝ)⁻¹) ^ (-((d : ℝ) + 1)) = 2 ^ ((d : ℝ) + 1) := by
          rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
        rw [div_eq_mul_inv, Real.mul_rpow hB.le (by norm_num), h6, mul_comm]


lemma rg_hasFDerivAt_rgR (f : Euc d → F) (hf : Differentiable ℝ f) (x z : Euc d) :
    HasFDerivAt (fun x' => rgR f x' z) (rgR (fderiv ℝ f) x z) x := by
  have h1 : HasFDerivAt (fun x' : Euc d => f (x' - z)) (fderiv ℝ f (x - z)) x := by
    have := (hf (x - z)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  unfold rgR
  by_cases h : ‖z‖ ≤ 1 / 4
  · simp only [h, ite_true]
    exact h1.sub (hf x).hasFDerivAt
  · simp only [h, ite_false]
    exact h1

variable {Fb : Type*} [NormedAddCommGroup Fb] [NormedSpace ℝ Fb] [CompleteSpace Fb]

/-- Differentiation under the integral sign: `D (rgT κ f) = rgT κ (D f)`. -/
lemma rg_hasFDerivAt (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {f : Euc d → Fb} (hf : ContDiff ℝ 2 f) {a0 a1 a2 : ℝ}
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (h0 : ∀ y, ‖f y‖ ≤ a0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ y, ‖fderiv ℝ f y‖ ≤ a1 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ a2) (x₀ : Euc d) :
    HasFDerivAt (rgT κ f) (rgT κ (fderiv ℝ f) x₀) x₀ := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hf1d : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable (by norm_num)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have h1' : ∀ y, ‖fderiv ℝ f y‖ ≤ a1 := fun y =>
    (h1 y).trans (by calc a1 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ a1 * 1 :=
                          mul_le_mul_of_nonneg_left (hw y) ha1
                      _ = a1 := mul_one _)
  have hmeas : ∀ x, AEStronglyMeasurable (fun z => κ z • rgR f x z) volume :=
    fun x => rg_aesm hκ.meas hfd.continuous x
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x₀ 1)
    (F := fun x z => κ z • rgR f x z) (F' := fun x z => κ z • rgR (fderiv ℝ f) x z)
    (bound := rgMaj d s σ (a1 * 2 ^ ((d : ℝ) + 1)) a2 x₀) (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall hmeas) (rg_integrable hd hs0 hsd hκ hfd ha0 ha1 h0 h1' x₀)
    (rg_aesm hκ.meas hf1d.continuous x₀) ?_ (rg_maj_integrable hd hsd σ _ a2 x₀) ?_
  · filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz x hx
    have hxn : ‖x - x₀‖ < 1 := by
      have := Metric.mem_ball.1 hx
      rwa [dist_eq_norm] at this
    have := rg_norm_le hs0 hκ hf1d ha1 ha2 h1 h2 x z hz
    refine this.trans ?_
    unfold rgMaj
    apply mul_le_mul_of_nonneg_left _ hκ.sigma_nonneg
    refine add_le_add_right ?_ _
    have hp := rg_peetre (d := d) z hxn
    have h4 : (0 : ℝ) ≤ 4 ^ (s + 1) * a1 := by positivity
    calc 4 ^ (s + 1) * a1 * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1))
        ≤ 4 ^ (s + 1) * a1 * (2 ^ ((d : ℝ) + 1) * (1 + ‖x₀ - z‖) ^ (-((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hp h4
      _ = 4 ^ (s + 1) * (a1 * 2 ^ ((d : ℝ) + 1)) * (1 + ‖x₀ - z‖) ^ (-((d : ℝ) + 1)) := by ring
  · refine Eventually.of_forall fun z x _ => ?_
    exact (rg_hasFDerivAt_rgR f hfd x z).const_smul (κ z)

end Basic


section Induction
universe u

lemma rg_decay_parts {Fb : Type*} [NormedAddCommGroup Fb] [NormedSpace ℝ Fb] {n : ℕ} (hn : 2 ≤ n)
    {a : ℕ → ℝ} (ha : ∀ l, 0 ≤ a l) {f : Euc d → Fb} (h : RgDecay n a f) :
    ContDiff ℝ 2 f ∧ (∀ y, ‖f y‖ ≤ a 0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ y, ‖fderiv ℝ f y‖ ≤ a 1 * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ a 2) := by
  obtain ⟨hc, hb⟩ := h
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨hc.of_le (by exact_mod_cast hn), fun y => ?_, fun y => ?_, fun y => ?_⟩
  · have := hb 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero] at this
  · have := hb 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  · have := hb 2 hn y
    have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := y) (n := 1)
    rw [norm_iteratedFDeriv_one] at e
    rw [e]
    exact this.trans (by calc a 2 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ a 2 * 1 :=
                                mul_le_mul_of_nonneg_left (hw y) (ha 2)
                            _ = a 2 := mul_one _)


lemma rg_hasFDerivAt_decay (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {Fb : Type u} [NormedAddCommGroup Fb] [NormedSpace ℝ Fb] [CompleteSpace Fb]
    {n : ℕ} (hn : 2 ≤ n) {a : ℕ → ℝ} (ha : ∀ l, 0 ≤ a l) {f : Euc d → Fb} (h : RgDecay n a f)
    (x : Euc d) : HasFDerivAt (rgT κ f) (rgT κ (fderiv ℝ f) x) x := by
  obtain ⟨h2, h0, h1, h2'⟩ := rg_decay_parts hn ha h
  exact rg_hasFDerivAt hd hs0 hsd hκ h2 (ha 0) (ha 1) (ha 2) h0 h1 h2' x

lemma rg_bound0 (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {Fb : Type u} [NormedAddCommGroup Fb] [NormedSpace ℝ Fb]
    {n : ℕ} (hn : 2 ≤ n) {a : ℕ → ℝ} (ha : ∀ l, 0 ≤ a l) {f : Euc d → Fb} (h : RgDecay n a f)
    (x : Euc d) : ‖rgT κ f x‖ ≤ σ * (a 1 * rgNear d s + 4 ^ (s + 1) * a 0 * rgW d) := by
  obtain ⟨h2, h0, h1, h2'⟩ := rg_decay_parts hn ha h
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have h1' : ∀ y, ‖fderiv ℝ f y‖ ≤ a 1 := fun y =>
    (h1 y).trans (by calc a 1 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ a 1 * 1 :=
                          mul_le_mul_of_nonneg_left (hw y) (ha 1)
                      _ = a 1 := mul_one _)
  exact rg_norm_T_le hd hs0 hsd hκ (h2.differentiable (by norm_num)) (ha 0) (ha 1) h0 h1' x

/-- **Smoothness and bounds of the cancellation-convention convolution.**  If `f` is `C^{m+2}` with
`‖D^l f(y)‖ ≤ a_l (1+|y|)^{-(d+1)}` (`l ≤ m+2`), then `rgT κ f` is `C^m` and
`‖D^l (rgT κ f)(x)‖ ≤ σ (a_{l+1} I_s + 4^{s+1} a_l W)` for `l ≤ m`. -/
theorem rg_Tdiff (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) : ∀ (m : ℕ) {Fb : Type u} [NormedAddCommGroup Fb] [NormedSpace ℝ Fb]
      [CompleteSpace Fb] (a : ℕ → ℝ), (∀ l, 0 ≤ a l) → ∀ f : Euc d → Fb, RgDecay (m + 2) a f →
      ContDiff ℝ m (rgT κ f) ∧ ∀ l, l ≤ m → ∀ x : Euc d,
        ‖iteratedFDeriv ℝ l (rgT κ f) x‖ ≤
          σ * (a (l + 1) * rgNear d s + 4 ^ (s + 1) * a l * rgW d) := by
  intro m
  induction m with
  | zero =>
    intro Fb _ _ _ a ha f h
    refine ⟨?_, fun l hl x => ?_⟩
    · have hdiff : Differentiable ℝ (rgT κ f) := fun x =>
        (rg_hasFDerivAt_decay hd hs0 hsd hκ (by omega) ha h x).differentiableAt
      exact contDiff_zero.2 hdiff.continuous
    · have : l = 0 := by omega
      subst this
      rw [norm_iteratedFDeriv_zero]
      exact rg_bound0 hd hs0 hsd hκ (by omega) ha h x
  | succ m ih =>
    intro Fb _ _ _ a ha f h
    have hd1 : ∀ x, HasFDerivAt (rgT κ f) (rgT κ (fderiv ℝ f) x) x := fun x =>
      rg_hasFDerivAt_decay hd hs0 hsd hκ (by omega) ha h x
    have hfd : fderiv ℝ (rgT κ f) = rgT κ (fderiv ℝ f) := by
      funext x; exact (hd1 x).fderiv
    have hdf : RgDecay (m + 2) (fun l => a (l + 1)) (fderiv ℝ f) := by
      obtain ⟨hc, hb⟩ := h
      refine ⟨hc.fderiv_right (m := (m + 2 : ℕ)) (by push_cast; ring_nf; exact le_rfl), fun l hl y => ?_⟩
      have := hb (l + 1) (by omega) y
      rwa [← norm_iteratedFDeriv_fderiv] at this
    obtain ⟨hc, hb⟩ := ih (fun l => a (l + 1)) (fun l => ha (l + 1)) (fderiv ℝ f) hdf
    refine ⟨?_, fun l hl x => ?_⟩
    · push_cast
      refine contDiff_succ_iff_fderiv.2 ⟨fun x => (hd1 x).differentiableAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · rw [hfd]; exact hc
    · rcases l with _ | l
      · rw [norm_iteratedFDeriv_zero]
        exact rg_bound0 hd hs0 hsd hκ (by omega) ha h x
      · rw [← norm_iteratedFDeriv_fderiv, hfd]
        exact hb l (by omega) x

end Induction


section Kernel

lemma rg_sigma_nonneg {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ movtr_sigma s := by
  unfold movtr_sigma; split_ifs <;> linarith

/-- The `k`-th component of `∇g` is an admissible kernel. -/
lemma rgKerComp_ok {s : ℝ} (hs0 : 0 ≤ s) (k : Fin d) :
    RgKer d s (movtr_sigma s) (fun z => (rieszKernelGrad d s z) k) := by
  refine ⟨rg_sigma_nonneg hs0, ?_, fun z hz => ?_⟩
  · exact ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).continuous.measurable).comp
      (movtr_rieszKernelGrad_measurable (d := d) s)
  · calc |(rieszKernelGrad d s z) k| = ‖(rieszKernelGrad d s z) k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖rieszKernelGrad d s z‖ := PiLp.norm_apply_le _ k
      _ = _ := movtr_rieszKernelGrad_norm s hs0 hz

/-- The norm of `∇g` is an admissible kernel. -/
lemma rgKerNorm_ok {s : ℝ} (hs0 : 0 ≤ s) :
    RgKer d s (movtr_sigma s) (fun z => ‖rieszKernelGrad d s z‖) := by
  refine ⟨rg_sigma_nonneg hs0, ?_, fun z hz => ?_⟩
  · exact (movtr_rieszKernelGrad_measurable s).norm
  · rw [abs_norm, movtr_rieszKernelGrad_norm s hs0 hz]

lemma rg_movtr_R_eq (ρ : Euc d → ℝ) (x z : Euc d) : movtr_R ρ x z = rgR ρ x z := by
  unfold movtr_R rgR; rfl

/-- The components of `convGradConvW (∇g) ρ` are `rgT` of the component kernels. -/
lemma rg_force_comp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : Differentiable ℝ ρ) {a0 a1 : ℝ} (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1)
    (h0 : ∀ y, ‖ρ y‖ ≤ a0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ a1) (x : Euc d) (k : Fin d) :
    (convGradConvW (rieszKernelGrad d s) ρ x) k =
      rgT (fun z => (rieszKernelGrad d s z) k) ρ x := by
  rw [movtr_force_eq]
  have hint : Integrable (fun z => movtr_R ρ x z • rieszKernelGrad d s z) := by
    refine Integrable.mono' (rg_maj_integrable hd hsd (movtr_sigma s) a0 a1 x) ?_ ?_
    · exact ((movtr_R_measurable hρ.continuous x).smul
        (movtr_rieszKernelGrad_measurable s)).aestronglyMeasurable
    · filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
      have := rg_norm_le hs0 (rgKerNorm_ok (d := d) hs0) hρ ha0 ha1 h0 h1 x z hz
      refine le_trans (le_of_eq ?_) this
      rw [norm_smul, norm_smul, rg_movtr_R_eq, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, mul_comm]
  have key : (∫ z, movtr_R ρ x z • rieszKernelGrad d s z) k =
      ∫ z, (movtr_R ρ x z • rieszKernelGrad d s z) k :=
    (ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ) hint).symm
  rw [key]
  unfold rgT
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [PiLp.smul_apply, smul_eq_mul, rg_movtr_R_eq]
  ring

end Kernel

end HRS.MP.RdGen
