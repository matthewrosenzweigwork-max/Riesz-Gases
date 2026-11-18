import HRS.MC.CepE2Aux4

/-!
# Packet CEPE2, auxiliary 5: the Moreau envelope, its gradient and its convergence
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE2

open HRS.MC.CepE1

variable {N : ℕ}

/-- A function with a quadratic Taylor remainder has that gradient. -/
theorem cepe2_hasGradientAt_of_quad {f : Ch N → ℝ} {g z : Ch N} {C : ℝ} (hC : 0 < C)
    (h : ∀ z' : Ch N, |f z' - f z - inner ℝ g (z' - z)| ≤ C * ‖z' - z‖ ^ 2) :
    HasGradientAt f g z := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  have hball : Metric.ball (0 : Ch N) (c / C) ∈ 𝓝 (0 : Ch N) := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with w hw
  have hw' : ‖w‖ < c / C := by simpa using hw
  have h1 := h (z + w)
  simp only [add_sub_cancel_left, InnerProductSpace.toDual_apply_apply] at h1 ⊢
  rw [Real.norm_eq_abs]
  calc |f (z + w) - f z - inner ℝ g w| ≤ C * ‖w‖ ^ 2 := h1
    _ = (C * ‖w‖) * ‖w‖ := by ring
    _ ≤ c * ‖w‖ := by
        gcongr
        rw [lt_div_iff₀ hC] at hw'
        linarith

/-- The Moreau envelope. -/
def cepe2_env {a : ℝ} (ha : 0 < a) (n : ℝ) (z : Ch N) : ℝ :=
  if 0 < n then cep_chamberPot a N (cepe2_J ha n z) + (n / 2) * ‖z - cepe2_J ha n z‖ ^ 2 else 0

theorem cepe2_env_eq {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    cepe2_env ha n z = cep_chamberPot a N (cepe2_J ha n z) + (n / 2) * ‖z - cepe2_J ha n z‖ ^ 2 := by
  simp [cepe2_env, hn]

theorem cepe2_env_min {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) (z : Ch N) {y : Ch N}
    (hy : y ∈ cep_Alcove N) :
    cepe2_env ha n z ≤ cep_chamberPot a N y + (n / 2) * ‖z - y‖ ^ 2 := by
  obtain ⟨hA, hF⟩ := cepe2_J_spec ha hn z
  set x := cepe2_J ha n z
  rw [cepe2_env_eq ha hn]
  have hc := cepe2_convex ha.le hy hA
  rw [← hF, inner_smul_left] at hc
  simp only [conj_trivial] at hc
  have e : z - y = (z - x) - (y - x) := by abel
  have e2 : ‖z - y‖ ^ 2 = ‖z - x‖ ^ 2 - 2 * inner ℝ (z - x) (y - x) + ‖y - x‖ ^ 2 := by
    rw [e, norm_sub_sq_real]
  have : 0 ≤ (n / 2) * ‖y - x‖ ^ 2 := by positivity
  nlinarith

theorem cepe2_env_le {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) {z : Ch N} (hz : z ∈ cep_Alcove N) :
    cepe2_env ha n z ≤ cep_chamberPot a N z := by
  have := cepe2_env_min ha hn z hz
  simpa using this

theorem cepe2_env_lower {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) {z : Ch N} (hz : z ∈ cep_Alcove N) :
    cep_chamberPot a N z - ‖cepe1_pairGrad (cepe1_h1 a N) z‖ ^ 2 / (2 * n) ≤ cepe2_env ha n z := by
  obtain ⟨hA, hF⟩ := cepe2_J_spec ha hn z
  set x := cepe2_J ha n z
  rw [cepe2_env_eq ha hn]
  have hc := cepe2_convex ha.le hA hz
  set g := cepe1_pairGrad (cepe1_h1 a N) z with hg
  have h1 : -(‖g‖ * ‖x - z‖) ≤ inner ℝ g (x - z) := by
    have := abs_real_inner_le_norm g (x - z)
    linarith [neg_abs_le (inner ℝ g (x - z))]
  have e : ‖z - x‖ = ‖x - z‖ := norm_sub_rev _ _
  rw [e]
  have h2 : (n / 2) * ‖x - z‖ ^ 2 - ‖g‖ * ‖x - z‖ ≥ -(‖g‖ ^ 2 / (2 * n)) := by
    have : 0 ≤ (n / 2) * (‖x - z‖ - ‖g‖ / n) ^ 2 := by positivity
    have e3 : (n / 2) * (‖x - z‖ - ‖g‖ / n) ^ 2 =
        (n / 2) * ‖x - z‖ ^ 2 - ‖g‖ * ‖x - z‖ + ‖g‖ ^ 2 / (2 * n) := by
      field_simp
      ring
    linarith
  linarith

theorem cepe2_env_tendsto {a : ℝ} (ha : 0 < a) {z : Ch N} (hz : z ∈ cep_Alcove N) :
    Tendsto (fun n : ℕ => cepe2_env ha (n : ℝ) z) atTop (𝓝 (cep_chamberPot a N z)) := by
  set g := cepe1_pairGrad (cepe1_h1 a N) z
  have hlow : Tendsto (fun n : ℕ => cep_chamberPot a N z - ‖g‖ ^ 2 / (2 * (n : ℝ))) atTop
      (𝓝 (cep_chamberPot a N z)) := by
    have h : Tendsto (fun n : ℕ => ‖g‖ ^ 2 / (2 * (n : ℝ))) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
      exact tendsto_const_nhds.div_atTop this
    simpa using (tendsto_const_nhds (x := cep_chamberPot a N z)).sub h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact cepe2_env_lower ha (by exact_mod_cast hn) hz
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact cepe2_env_le ha (by exact_mod_cast hn) hz

theorem cepe2_env_hasGradient {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    HasGradientAt (cepe2_env ha n) (n • (z - cepe2_J ha n z)) z := by
  refine cepe2_hasGradientAt_of_quad (C := 3 * n / 2) (by positivity) fun z' => ?_
  obtain ⟨hA, hF⟩ := cepe2_J_spec ha hn z
  obtain ⟨hA', hF'⟩ := cepe2_J_spec ha hn z'
  set x := cepe2_J ha n z
  set x' := cepe2_J ha n z'
  have hup := cepe2_env_min ha hn z' hA
  have hdn := cepe2_env_min ha hn z hA'
  have hz : cepe2_env ha n z = cep_chamberPot a N x + (n / 2) * ‖z - x‖ ^ 2 := cepe2_env_eq ha hn z
  have hz' : cepe2_env ha n z' = cep_chamberPot a N x' + (n / 2) * ‖z' - x'‖ ^ 2 := cepe2_env_eq ha hn z'
  have hlip := cepe2_lip ha hn z z'
  have hlip' : ‖(z' - x') - (z - x)‖ ≤ ‖z' - z‖ := by
    rw [norm_sub_rev, norm_sub_rev z' z]; exact hlip
  -- upper bound
  have u1 : ‖z' - x‖ ^ 2 = ‖z - x‖ ^ 2 + 2 * inner ℝ (z - x) (z' - z) + ‖z' - z‖ ^ 2 := by
    have : z' - x = (z - x) + (z' - z) := by abel
    rw [this, norm_add_sq_real]
  have U : cepe2_env ha n z' - cepe2_env ha n z ≤ inner ℝ (n • (z - x)) (z' - z) + (n / 2) * ‖z' - z‖ ^ 2 := by
    rw [real_inner_smul_left]
    nlinarith
  -- lower bound
  have u2 : ‖z - x'‖ ^ 2 = ‖z' - x'‖ ^ 2 + 2 * inner ℝ (z' - x') (z - z') + ‖z - z'‖ ^ 2 := by
    have : z - x' = (z' - x') + (z - z') := by abel
    rw [this, norm_add_sq_real]
  have L1 : cepe2_env ha n z - cepe2_env ha n z' ≤ n * inner ℝ (z' - x') (z - z') + (n / 2) * ‖z - z'‖ ^ 2 := by
    nlinarith
  have hcs : |inner ℝ ((z' - x') - (z - x)) (z' - z)| ≤ ‖z' - z‖ ^ 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_right hlip' (norm_nonneg _)
  have e1 : inner ℝ (z' - x') (z - z') = -inner ℝ (z' - x') (z' - z) := by
    rw [← inner_neg_right, neg_sub]
  have e2 : inner ℝ (z' - x') (z' - z) = inner ℝ (z - x) (z' - z) + inner ℝ ((z' - x') - (z - x)) (z' - z) := by
    rw [← inner_add_left]; congr 1; abel
  have e3 : ‖z - z'‖ = ‖z' - z‖ := norm_sub_rev _ _
  rw [e1, e2, e3] at L1
  rw [real_inner_smul_left] at U ⊢
  rw [abs_le]
  have := neg_abs_le (inner ℝ ((z' - x') - (z - x)) (z' - z))
  have := le_abs_self (inner ℝ ((z' - x') - (z - x)) (z' - z))
  constructor <;> nlinarith [norm_nonneg (z' - z)]

end HRS.MC.CepE2
