import HRS.MC.CepH3B1

/-!
# Packet CEPH3, part B2: Moreau representation `Φn n z = Φ(J z) + (n/2)‖z - J z‖² + c n`, `c n → 0`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepH3

open HRS HRS.MC.Cepa

variable {N : ℕ} {J : ℝ → Ch N → Ch N}

/-- The Moreau envelope computed through the resolvent. -/
def h3b_M (J : ℝ → Ch N → Ch N) (n : ℝ) (z : Ch N) : ℝ :=
  cep_chamberPot 1 N (J n z) + n / 2 * ‖z - J n z‖ ^ 2

/-- The resolvent point minimises `Φ y + (n/2)‖z - y‖²` over the alcove (strongly). -/
lemma h3b_minprop (hJ : cep_Yosida 1 N J) {n : ℝ} (hn : 0 < n) (z : Ch N) {y : Ch N}
    (hy : y ∈ cep_Alcove N) :
    h3b_M J n z + n / 2 * ‖y - J n z‖ ^ 2 ≤ cep_chamberPot 1 N y + n / 2 * ‖z - y‖ ^ 2 := by
  have h1 := h3a_tangent_pot (hJ.mem n z hn) hy
  rw [h3b_force hJ hn z, real_inner_smul_left] at h1
  have h2 : ‖z - y‖ ^ 2 = ‖z - J n z‖ ^ 2 - 2 * ⟪z - J n z, y - J n z⟫ + ‖y - J n z‖ ^ 2 := by
    have : z - y = (z - J n z) - (y - J n z) := by abel
    rw [this, norm_sub_sq_real]
  unfold h3b_M
  rw [h2]
  nlinarith

lemma h3b_M_hasGradientAt (hJ : cep_Yosida 1 N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    HasGradientAt (h3b_M J n) (n • (z - J n z)) z := by
  refine h3b_hasGradientAt_of_quad (C := n) fun z' => ?_
  have hJz := hJ.mem n z hn
  have hJz' := hJ.mem n z' hn
  have hup := h3b_minprop hJ hn z' hJz
  have hlow := h3b_minprop hJ hn z hJz'
  have hnonexp := h3b_J_nonexp hJ hn z z'
  set a := J n z with ha
  set b := J n z' with hb
  have e1 : ‖z' - a‖ ^ 2 = ‖z - a‖ ^ 2 + 2 * ⟪z - a, z' - z⟫ + ‖z' - z‖ ^ 2 := by
    have : z' - a = (z - a) + (z' - z) := by abel
    rw [this, norm_add_sq_real]
  have e2 : ‖z' - b‖ ^ 2 = ‖z - b‖ ^ 2 + 2 * ⟪z' - z, z - b⟫ + ‖z' - z‖ ^ 2 := by
    have : z' - b = (z - b) + (z' - z) := by abel
    rw [this, norm_add_sq_real, real_inner_comm (z' - z) (z - b)]
  have hinner : ⟪n • (z - a), z' - z⟫ = n * ⟪z - a, z' - z⟫ := real_inner_smul_left _ _ _
  have hM : h3b_M J n z = cep_chamberPot 1 N a + n / 2 * ‖z - a‖ ^ 2 := rfl
  have hM' : h3b_M J n z' = cep_chamberPot 1 N b + n / 2 * ‖z' - b‖ ^ 2 := rfl
  have hq1 : 0 ≤ n / 2 * ‖a - b‖ ^ 2 := by positivity
  have hq2 : 0 ≤ n / 2 * ‖b - a‖ ^ 2 := by positivity
  have e1' : n / 2 * ‖z' - a‖ ^ 2 = n / 2 * ‖z - a‖ ^ 2 + n * ⟪z - a, z' - z⟫ + n / 2 * ‖z' - z‖ ^ 2 := by
    rw [e1]; ring
  have e2' : n / 2 * ‖z' - b‖ ^ 2 = n / 2 * ‖z - b‖ ^ 2 + n * ⟪z' - z, z - b⟫ + n / 2 * ‖z' - z‖ ^ 2 := by
    rw [e2]; ring
  have hU : h3b_M J n z' ≤ h3b_M J n z + n * ⟪z - a, z' - z⟫ + n / 2 * ‖z' - z‖ ^ 2 := by
    rw [hM]; linarith
  have hcross : -(‖z' - z‖ * ‖z' - z‖) ≤ ⟪z' - z, a - b⟫ := by
    have h3 : -(‖z' - z‖ * ‖a - b‖) ≤ ⟪z' - z, a - b⟫ := by
      have := neg_le_of_abs_le (abs_real_inner_le_norm (z' - z) (a - b)); linarith
    have h2 : ‖a - b‖ ≤ ‖z' - z‖ := by rw [norm_sub_rev z' z]; exact hnonexp
    nlinarith [norm_nonneg (z' - z), norm_nonneg (a - b)]
  have hz : z - b = (z - a) + (a - b) := by abel
  have e3 : ⟪z' - z, z - b⟫ = ⟪z' - z, z - a⟫ + ⟪z' - z, a - b⟫ := by
    rw [hz, inner_add_right]
  have hcomm : ⟪z' - z, z - a⟫ = ⟪z - a, z' - z⟫ := real_inner_comm _ _
  have hL : h3b_M J n z + n * ⟪z - a, z' - z⟫ - n * ‖z' - z‖ ^ 2 ≤ h3b_M J n z' := by
    have hlow' : h3b_M J n z ≤ cep_chamberPot 1 N b + n / 2 * ‖z - b‖ ^ 2 := by linarith
    have hn1 : n * (-(‖z' - z‖ * ‖z' - z‖)) ≤ n * ⟪z' - z, a - b⟫ :=
      mul_le_mul_of_nonneg_left hcross hn.le
    have e4 : n * ⟪z' - z, z - b⟫ = n * ⟪z - a, z' - z⟫ + n * ⟪z' - z, a - b⟫ := by
      rw [e3, hcomm]; ring
    have hn2 : n * (‖z' - z‖ * ‖z' - z‖) = n * ‖z' - z‖ ^ 2 := by ring
    have hn3 : 0 ≤ n * ‖z' - z‖ ^ 2 := by positivity
    rw [hM']
    linarith
  have hn3 : 0 ≤ n * ‖z' - z‖ ^ 2 := by positivity
  have hn4 : n / 2 * ‖z' - z‖ ^ 2 = (n * ‖z' - z‖ ^ 2) / 2 := by ring
  rw [hinner, abs_le]
  constructor
  · linarith
  · linarith

variable {Φn : ℝ → Ch N → ℝ}

/-- The envelope equals the resolvent expression up to a constant. -/
lemma h3b_Phin_eq (hJ : cep_Yosida 1 N J)
    (hΦ : ∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z) {n : ℝ} (hn : 0 < n)
    (w z : Ch N) :
    Φn n z = h3b_M J n z + (Φn n w - h3b_M J n w) := by
  have hd : ∀ x, HasFDerivAt (fun y => Φn n y - h3b_M J n y) (0 : Ch N →L[ℝ] ℝ) x := by
    intro x
    have h1 : HasFDerivAt (Φn n) (InnerProductSpace.toDual ℝ (Ch N) (n • (x - J n x))) x := hΦ n x hn
    have h2 : HasFDerivAt (h3b_M J n) (InnerProductSpace.toDual ℝ (Ch N) (n • (x - J n x))) x :=
      h3b_M_hasGradientAt hJ hn x
    have h := h1.sub h2
    rwa [sub_self] at h
  have hc := is_const_of_fderiv_eq_zero (f := fun y => Φn n y - h3b_M J n y)
    (fun x => (hd x).differentiableAt) (fun x => (hd x).fderiv) z w
  linarith

lemma h3b_M_le (hJ : cep_Yosida 1 N J) {n : ℝ} (hn : 0 < n) {w : Ch N} (hw : w ∈ cep_Alcove N) :
    h3b_M J n w ≤ cep_chamberPot 1 N w := by
  have := h3b_minprop hJ hn w hw
  simp at this
  nlinarith [sq_nonneg ‖w - J n w‖, this]

lemma h3b_M_ge (hJ : cep_Yosida 1 N J) {n : ℝ} (hn : 0 < n) {w : Ch N} (hw : w ∈ cep_Alcove N) :
    cep_chamberPot 1 N w - ‖h3a_gam w‖ ^ 2 / (2 * n) ≤ h3b_M J n w := by
  have h1 := h3a_tangent_pot hw (hJ.mem n w hn)
  have h2 : -(‖h3a_gam w‖ * ‖J n w - w‖) ≤ ⟪h3a_gam w, J n w - w⟫ := by
    have := neg_le_of_abs_le (abs_real_inner_le_norm (h3a_gam w) (J n w - w)); linarith
  have h3 : ‖J n w - w‖ = ‖w - J n w‖ := norm_sub_rev _ _
  unfold h3b_M
  set r := ‖w - J n w‖
  set B := ‖h3a_gam w‖
  have h4 : B ^ 2 / (2 * n) ≥ B * r - n / 2 * r ^ 2 := by
    rw [ge_iff_le, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (B - n * r)]
  rw [h3] at h2
  linarith

lemma h3b_M_tendsto (hJ : cep_Yosida 1 N J) {w : Ch N} (hw : w ∈ cep_Alcove N) :
    Tendsto (fun n : ℕ => h3b_M J (n : ℝ) w) atTop (𝓝 (cep_chamberPot 1 N w)) := by
  have hlow : Tendsto (fun n : ℕ => cep_chamberPot 1 N w - ‖h3a_gam w‖ ^ 2 / (2 * (n : ℝ))) atTop
      (𝓝 (cep_chamberPot 1 N w)) := by
    have : Tendsto (fun n : ℕ => ‖h3a_gam w‖ ^ 2 / (2 * (n : ℝ))) atTop (𝓝 0) := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (show (0:ℝ) < 2 by norm_num)
      exact (tendsto_const_nhds (x := ‖h3a_gam w‖ ^ 2)).div_atTop h
    simpa using (tendsto_const_nhds (x := cep_chamberPot 1 N w)).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact h3b_M_ge hJ (by exact_mod_cast hn) hw
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact h3b_M_le hJ (by exact_mod_cast hn) hw

/-- The constant of the Moreau representation tends to `0`. -/
lemma h3b_c_tendsto (hJ : cep_Yosida 1 N J)
    (hΦlim : ∀ z, z ∈ cep_Alcove N → Tendsto (fun n : ℕ => Φn n z) atTop (𝓝 (cep_chamberPot 1 N z)))
    {w : Ch N} (hw : w ∈ cep_Alcove N) :
    Tendsto (fun n : ℕ => Φn n w - h3b_M J (n : ℝ) w) atTop (𝓝 0) := by
  simpa using (hΦlim w hw).sub (h3b_M_tendsto hJ hw)

/-- Quadratic lower bound for the envelope. -/
lemma h3b_Phin_lower (hJ : cep_Yosida 1 N J)
    (hΦ : ∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z) {n : ℝ} (hn : 0 < n)
    (w z : Ch N) :
    -((N : ℝ) * Real.log 2) + (Φn n w - h3b_M J n w) + n / 2 * Metric.infDist z (cep_Alcove N) ^ 2
      ≤ Φn n z := by
  rw [h3b_Phin_eq hJ hΦ hn w z]
  have h1 := h3a_pot_lower (hJ.mem n z hn)
  have h2 : Metric.infDist z (cep_Alcove N) ≤ ‖z - J n z‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (hJ.mem n z hn)
  have h3 : Metric.infDist z (cep_Alcove N) ^ 2 ≤ ‖z - J n z‖ ^ 2 :=
    pow_le_pow_left₀ Metric.infDist_nonneg h2 2
  unfold h3b_M
  nlinarith

end HRS.MC.CepH3
