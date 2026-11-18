import HRS.MS.SA16Y5Dc1
import HRS.MS.SA16ZE10
import HRS.MS.CzElemAux1
import HRS.MS.LpDissLimit

/-!
# S.A.16 (SA16Y5) Lc1: the commutator `[Λ^θ, μ]` is bounded on `L^p` for `0 < θ < 1`

`sa16y5_lamComm_bound`: for `μ ∈ C_b²` with `sa16z_Cb 2 Λ μ` and `w ∈ C_c^∞`:
`‖lamComm d θ μ w‖_p ≤ K Λ ‖w‖_p`, `K = ‖k0‖_{L^1}`, `k0(z) = |z|^{1-d-θ} 1_{|z| ≤ 1} + 2 |z|^{-d-θ} 1_{|z| > 1}`
(the kernel `(μ(x) - μ(x-z)) |z|^{-d-θ}` is dominated by `Λ k0`, which is integrable exactly when `0 < θ < 1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section Lc1
variable {d : ℕ}

/-- the dominating kernel -/
def sa16y5_k0 (d : ℕ) (θ : ℝ) (z : Euc d) : ℝ :=
  if ‖z‖ ≤ 1 then ‖z‖ ^ (-((d : ℝ) + θ - 1)) else 2 * ‖z‖ ^ (-((d : ℝ) + θ))

lemma sa16y5_k0_nonneg (θ : ℝ) (z : Euc d) : 0 ≤ sa16y5_k0 d θ z := by
  unfold sa16y5_k0
  split_ifs
  · exact Real.rpow_nonneg (norm_nonneg _) _
  · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)

lemma sa16y5_k0_meas (θ : ℝ) : Measurable (sa16y5_k0 d θ) := by
  unfold sa16y5_k0
  refine Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ ?_
  · exact measurable_norm.pow_const _
  · exact (measurable_norm.pow_const _).const_mul _

lemma sa16y5_k0_fin (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∫⁻ z, ENNReal.ofReal (sa16y5_k0 d θ z) ≠ ⊤ := by
  have h1 := HRS.S16Frac.s16frac_integrableOn_ball_rpow (d := d) hd (α := (d : ℝ) + θ - 1) (by linarith) 2
  have h2 := HRS.CZ.Pv.pvapi_integrableOn_tail_rpow (d := d) hd (s := (d : ℝ) + θ) (by linarith)
  have hf1 : ∫⁻ z in ball (0 : Euc d) 2, ‖‖z‖ ^ (-((d : ℝ) + θ - 1))‖ₑ < ⊤ := h1.2
  have hf2 : ∫⁻ z in {z : Euc d | 1 < ‖z‖}, ‖‖z‖ ^ (-((d : ℝ) + θ))‖ₑ < ⊤ := h2.2
  have hS : MeasurableSet {z : Euc d | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hle : ∀ z : Euc d, ENNReal.ofReal (sa16y5_k0 d θ z) ≤
      (ball (0 : Euc d)  2).indicator (fun z => ‖‖z‖ ^ (-((d : ℝ) + θ - 1))‖ₑ) z +
        2 * {z : Euc d | 1 < ‖z‖}.indicator (fun z => ‖‖z‖ ^ (-((d : ℝ) + θ))‖ₑ) z := by
    intro z
    unfold sa16y5_k0
    by_cases hz : ‖z‖ ≤ 1
    · have hz2 : z ∈ ball (0 : Euc d) 2 := by
        simp only [mem_ball, dist_zero_right]; linarith
      rw [if_pos hz, indicator_of_mem hz2, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact le_self_add
    · have hz1 : z ∈ {z : Euc d | 1 < ‖z‖} := not_le.1 hz
      rw [if_neg hz, indicator_of_mem hz1, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ENNReal.ofReal_mul (by norm_num)]
      simp
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_add_left, lintegral_const_mul' _ _ (by simp), lintegral_indicator measurableSet_ball,
    lintegral_indicator hS]
  · exact ENNReal.add_ne_top.2 ⟨hf1.ne, ENNReal.mul_ne_top (by simp) hf2.ne⟩
  · exact (measurable_norm.pow_const _).enorm.indicator measurableSet_ball

lemma sa16y5_comm_pt {θ : ℝ} (hθ0 : 0 < θ) {μ : Euc d → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hb : ∀ y, |μ y| ≤ Λ) (hL : ∀ a b, |μ a - μ b| ≤ Λ * ‖a - b‖) (x z : Euc d) (w : Euc d → ℝ) :
    ‖(μ x - μ (x - z)) * w (x - z) / ‖z‖ ^ ((d : ℝ) + θ)‖ₑ ≤
      ENNReal.ofReal (Λ * sa16y5_k0 d θ z) * ‖w (x - z)‖ₑ := by
  by_cases hz0 : z = 0
  · subst hz0; simp
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hE : 0 < ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_pos_of_pos hn _
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (mul_nonneg hΛ (sa16y5_k0_nonneg θ z))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [abs_div, abs_mul, abs_of_pos hE, div_le_iff₀ hE]
  have hw := abs_nonneg (w (x - z))
  have hD := abs_nonneg (μ x - μ (x - z))
  unfold sa16y5_k0
  split_ifs with h1
  · have h2 : |μ x - μ (x - z)| ≤ Λ * ‖z‖ := by
      have := hL x (x - z); simpa using this
    have h3 : ‖z‖ ^ (-((d : ℝ) + θ - 1)) * ‖z‖ ^ ((d : ℝ) + θ) = ‖z‖ := by
      rw [← Real.rpow_add hn]; simp
    calc |μ x - μ (x - z)| * |w (x - z)| ≤ (Λ * ‖z‖) * |w (x - z)| := mul_le_mul_of_nonneg_right h2 hw
      _ = Λ * ‖z‖ ^ (-((d : ℝ) + θ - 1)) * |w (x - z)| * ‖z‖ ^ ((d : ℝ) + θ) := by
          have : Λ * ‖z‖ ^ (-((d : ℝ) + θ - 1)) * |w (x - z)| * ‖z‖ ^ ((d : ℝ) + θ) =
              Λ * |w (x - z)| * (‖z‖ ^ (-((d : ℝ) + θ - 1)) * ‖z‖ ^ ((d : ℝ) + θ)) := by ring
          rw [this, h3]; ring
  · have h2 : |μ x - μ (x - z)| ≤ 2 * Λ := by
      calc |μ x - μ (x - z)| ≤ |μ x| + |μ (x - z)| := abs_sub _ _
        _ ≤ Λ + Λ := add_le_add (hb x) (hb _)
        _ = 2 * Λ := by ring
    have h3 : 2 * ‖z‖ ^ (-((d : ℝ) + θ)) * ‖z‖ ^ ((d : ℝ) + θ) = 2 := by
      rw [mul_assoc, ← Real.rpow_add hn]; simp
    calc |μ x - μ (x - z)| * |w (x - z)| ≤ (2 * Λ) * |w (x - z)| := mul_le_mul_of_nonneg_right h2 hw
      _ = Λ * (2 * ‖z‖ ^ (-((d : ℝ) + θ))) * |w (x - z)| * ‖z‖ ^ ((d : ℝ) + θ) := by
          have : Λ * (2 * ‖z‖ ^ (-((d : ℝ) + θ))) * |w (x - z)| * ‖z‖ ^ ((d : ℝ) + θ) =
              Λ * |w (x - z)| * (2 * ‖z‖ ^ (-((d : ℝ) + θ)) * ‖z‖ ^ ((d : ℝ) + θ)) := by ring
          rw [this, h3]; ring

theorem sa16y5_lamComm_bound (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {p : ℝ} (hp : 1 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ : Euc d → ℝ} {Λ : ℝ}, 0 ≤ Λ → ContDiff ℝ ∞ μ → sa16z_Cb 2 Λ μ →
      ∀ {w : Euc d → ℝ}, IsCcInfty w →
      eLpNorm (fun x => lamComm d θ μ w x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * Λ) * eLpNorm w (ENNReal.ofReal p) volume := by
  have hθ2 : θ < 2 := by linarith
  refine ⟨(∫⁻ z, ENNReal.ofReal (sa16y5_k0 d θ z)).toReal, ENNReal.toReal_nonneg,
    fun {μ Λ} hΛ hμs hCb {w} hw => ?_⟩
  have hCb1 : sa16z_Cb 1 Λ μ := sa16z_Cb_mono (by omega) hCb
  have hb : ∀ y, |μ y| ≤ Λ := fun y => sa16z_Cb_abs (sa16z_Cb_mono (by omega) hCb) y
  have hL : ∀ a b, |μ a - μ b| ≤ Λ * ‖a - b‖ := by
    intro a b
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := μ) (s := univ) (C := Λ)
      (fun x _ => hμs.differentiable (by simp) x) (fun x _ => sa16z_Cb_fderiv hCb1 x) convex_univ
      (mem_univ b) (mem_univ a)
    simpa [Real.norm_eq_abs] using this
  have hmem : HRS.MemCb 2 μ := sa16z_memCb hμs hCb
  set W : 𝓢(Euc d, ℝ) := sa16z_schw hw with hW
  have hWc : ⇑W = w := rfl
  have hpt : ∀ x, ‖lamComm d θ μ w x‖ₑ ≤ ∫⁻ z, ENNReal.ofReal (Λ * sa16y5_k0 d θ z) * ‖w (x - z)‖ₑ := by
    intro x
    have ht := HRS.CZ.Pv.lamComm_kernel_tendsto hd hθ0 hθ2 hmem W x
    refine le_of_tendsto ht.enorm (Eventually.of_forall fun ε => ?_)
    have hS : MeasurableSet {z : Euc d | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
    refine (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans ?_)
    refine lintegral_mono fun z => ?_
    exact sa16y5_comm_pt hθ0 hΛ hb hL x z w
  have hWm : Measurable w := hw.1.continuous.measurable
  have hFm : AEStronglyMeasurable (fun x => lamComm d θ μ w x) volume := by
    have hμw : IsCcInfty (fun y => μ y * w y) := ⟨hμs.mul hw.1, hw.2.mul_left⟩
    have h1 := sa16bd_fracLap_aesm hd hθ0 hθ2 (sa16z_schw hμw)
    have h2 := sa16bd_fracLap_aesm hd hθ0 hθ2 W
    exact h1.sub (hμs.continuous.aestronglyMeasurable.mul h2)
  have hk : Measurable (fun z : Euc d => Λ * sa16y5_k0 d θ z) := (sa16y5_k0_meas θ).const_mul _
  have hy := HRS.CZ.ElemA.elema_young hk hWm hFm hp hpt
  refine hy.trans (le_of_eq ?_)
  have e : ∫⁻ z, ENNReal.ofReal (Λ * sa16y5_k0 d θ z) = ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (sa16y5_k0 d θ z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun z => ENNReal.ofReal_mul hΛ
  rw [e, ENNReal.ofReal_mul (ENNReal.toReal_nonneg), ENNReal.ofReal_toReal (sa16y5_k0_fin hd hθ0 hθ1)]
  ring

end Lc1

end HRS.Whole.AppendixA.Phase2SA16R
