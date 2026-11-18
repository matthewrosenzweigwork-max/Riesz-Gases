import HRS.MS.SA16U3K7c
import HRS.MS.CzHlsAux1

/-!
# S.A.16 K7, part (d): the `θ = 1` bound (worker SA16U3)

`F = A + B` with `A = ∫ kA W(x-·)` (Young, kernel `sa16u3_m` in `L^1`, independent of `δ`) and
`B = ∑_i ∂_iμ (T_δ^i W - T_1^i W)` (uniform CZ bound `pvasm_Lp_ae_pv`, `|∂_iμ| ≤ ‖Dμ‖_∞`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.Pvk HRS.CZ.PvAsm HRS.CZ.ElemA HRS.CZ.Hls Phase2SA16

section K7d
variable {d : ℕ}

lemma sa16u3_eLp_mul_le {f g : Euc d → ℝ} {c p : ℝ} (hc : 0 ≤ c) (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (h : ∀ x, |f x| ≤ c) :
    eLpNorm (fun x => f x * g x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal c * eLpNorm g (ENNReal.ofReal p) volume := by
  have h1 : eLpNorm (fun x => f x * g x) (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => c * ‖g x‖) (ENNReal.ofReal p) volume :=
    eLpNorm_mono_real (hf.mul hg) (fun x => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _))
  have h2 : (fun x => c * ‖g x‖) = c • (fun x => ‖g x‖) := by
    funext x; simp
  have h3 : eLpNorm (fun x => c * ‖g x‖) (ENNReal.ofReal p) volume =
      ENNReal.ofReal c * eLpNorm g (ENNReal.ofReal p) volume := by
    rw [h2, eLpNorm_const_smul, eLpNorm_norm g hg, Real.enorm_of_nonneg hc]
  exact h1.trans h3.le

lemma sa16u3_grad_cont {μ : Euc d → ℝ} (hμ : ContDiff ℝ 2 μ) (i : Fin d) :
    Continuous (fun x => gradient μ x i) := by
  have h1 : Continuous (fun x : Euc d => fderiv ℝ μ x) := hμ.continuous_fderiv (by norm_num)
  exact (EuclideanSpace.proj i).continuous.comp
    ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h1)

lemma sa16u3_grad_le {μ : Euc d → ℝ} {B1 : ℝ} (h1 : ∀ y, ‖fderiv ℝ μ y‖ ≤ B1) (x : Euc d)
    (i : Fin d) : |gradient μ x i| ≤ B1 := by
  calc |gradient μ x i| = ‖gradient μ x i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖gradient μ x‖ := PiLp.norm_apply_le _ i
    _ = ‖fderiv ℝ μ x‖ := by unfold gradient; exact LinearIsometryEquiv.norm_map _ _
    _ ≤ B1 := h1 x

/-- the two constants in `∫ sa16u3_m` -/
def sa16u3_I1 (d : ℕ) : ℝ := ∫ z : Euc d, (closedBall (0 : Euc d) 1).indicator
  (fun z => ‖z‖ ^ (2 - ((d : ℝ) + 1))) z

def sa16u3_J1 (d : ℕ) : ℝ := ∫ z : Euc d, {z : Euc d | 1 < ‖z‖}.indicator
  (fun z => ‖z‖ ^ (-((d : ℝ) + 1))) z

lemma sa16u3_I1_nonneg : 0 ≤ sa16u3_I1 d :=
  integral_nonneg fun z => Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) z

lemma sa16u3_J1_nonneg : 0 ≤ sa16u3_J1 d :=
  integral_nonneg fun z => Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) z

lemma sa16u3_m_integral (hd : 1 ≤ d) (B0 B2 : ℝ) :
    ∫ z, sa16u3_m d B0 B2 z = B2 / 2 * sa16u3_I1 d + 2 * B0 * sa16u3_J1 d := by
  obtain ⟨I0, hI0, hI⟩ := sa16s_moment (d := d) hd (θ := 1) (by norm_num)
  have h1 := (hI 1 one_pos).1
  have h2 : Integrable ({z : Euc d | 1 < ‖z‖}.indicator (fun z => ‖z‖ ^ (-((d : ℝ) + 1)))) := by
    rw [integrable_indicator_iff (measurableSet_lt measurable_const measurable_norm)]
    exact pvapi_integrableOn_rpow_outside hd (s := (d : ℝ) + 1) (by linarith) one_pos
  unfold sa16u3_m sa16u3_I1 sa16u3_J1
  rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]

end K7d

/-- K7 at `θ = 1` -/
theorem sa16u3_k7_one (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ μ : Euc d → ℝ, MemCb 2 μ →
      ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (fun x => jumpCut d 1 δ (fun y => μ y * W y) x - μ x * jumpCut d 1 δ W x)
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * cbNorm 2 μ) * eLpNorm W (ENNReal.ofReal p) volume := by
  have hp1 : 1 < p := by linarith
  have hp1' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  obtain ⟨C1, hC1, hP⟩ := pvasm_Lp_ae_pv hd hp1
  set I1 := sa16u3_I1 d with hI1
  set J1 := sa16u3_J1 d with hJ1
  have hI1n : 0 ≤ I1 := sa16u3_I1_nonneg
  have hJ1n : 0 ≤ J1 := sa16u3_J1_nonneg
  refine ⟨I1 / 2 + 2 * J1 + 2 * d * C1 + 1, by positivity, fun δ hδ μ hμ W => ?_⟩
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hcb, -, h0, h1, h2⟩ := elema_cb2_data hμ
  have hWp : MemLp W (ENNReal.ofReal p) volume := W.memLp _ _
  -- the pieces
  set A : Euc d → ℝ := fun x => ∫ z, sa16u3_kA d μ δ x z * W (x - z) with hA
  set Φ : Fin d → Euc d → ℝ := fun i x =>
    pvTrunc d 1 (fun v : Euc d => v i) W δ x - pvTrunc d 1 (fun v : Euc d => v i) W 1 x with hΦ
  set B : Euc d → ℝ := fun x => ∑ i : Fin d, gradient μ x i * Φ i x with hB
  have hF : ∀ x, jumpCut d 1 δ (fun y => μ y * W y) x - μ x * jumpCut d 1 δ W x = A x + B x := by
    intro x
    rw [sa16u3_k7_repr hd one_pos hδ.1 hμ W x]
    exact sa16u3_F_decomp hd hμ2 hB0 hB2 h0 h2 hδ.1 hδ.2 W hp1 x
  have hTm : ∀ (i : Fin d) (ε : ℝ), AEStronglyMeasurable
      (fun x => pvTrunc d 1 (fun v : Euc d => v i) W ε x) volume := by
    intro i ε
    have : (fun x => pvTrunc d 1 (fun v : Euc d => v i) W ε x) =
        fun x => ∫ z, pvkKtr (pvasmK d i) ε z * W (x - z) := funext fun x => pvasm_trunc_eq i W ε x
    rw [this]
    exact hlsg_aesm_conv (pvasm_Ktr_meas hd i ε) W.continuous.aestronglyMeasurable
  have hΦm : ∀ i, AEStronglyMeasurable (Φ i) volume := fun i => (hTm i δ).sub (hTm i 1)
  have hBm : AEStronglyMeasurable B volume := by
    have : B = ∑ i : Fin d, fun x => gradient μ x i * Φ i x := by
      funext x; simp [hB, Finset.sum_apply]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun i _ =>
      (sa16u3_grad_cont hμ2 i).aestronglyMeasurable.mul (hΦm i)
  have hFm : AEStronglyMeasurable (fun x => jumpCut d 1 δ (fun y => μ y * W y) x -
      μ x * jumpCut d 1 δ W x) volume := by
    have := sa16u3_k7_aesm (θ := 1) (δ := δ) hμ2.continuous W
    refine this.congr (Eventually.of_forall fun x => ?_)
    exact (sa16u3_k7_repr hd one_pos hδ.1 hμ W x).symm
  have hAm : AEStronglyMeasurable A volume := by
    have : A = fun x => (jumpCut d 1 δ (fun y => μ y * W y) x - μ x * jumpCut d 1 δ W x) - B x :=
      funext fun x => by rw [hF x]; ring
    rw [this]
    exact hFm.sub hBm
  -- bound for A
  have hmi := sa16u3_m_int hd B0 B2
  have hAn : eLpNorm A (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (B2 / 2 * I1 + 2 * B0 * J1) * eLpNorm W (ENNReal.ofReal p) volume := by
    have hJ : ∫⁻ z, ENNReal.ofReal (sa16u3_m d B0 B2 z) =
        ENNReal.ofReal (B2 / 2 * I1 + 2 * B0 * J1) := by
      rw [← sa16u3_m_integral hd B0 B2]
      exact (ofReal_integral_eq_lintegral_ofReal hmi
        (Eventually.of_forall (sa16u3_m_nonneg hB0 hB2))).symm
    have key := elema_young (sa16u3_m_meas (d := d) B0 B2) W.continuous.measurable hAm hp1.le
      (fun x => by
        refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
        rw [enorm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (sa16u3_kA_le hμ2 hB0 hB2 h0 h2 hδ.1 x z))
    rw [hJ] at key
    exact key
  -- bound for B
  have hΦn : ∀ i, eLpNorm (Φ i) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2 * C1) * eLpNorm W (ENNReal.ofReal p) volume := by
    intro i
    have e1 := ((hP i W hWp).1 δ hδ.1)
    have e2 := ((hP i W hWp).1 1 one_pos)
    calc eLpNorm (Φ i) (ENNReal.ofReal p) volume
        ≤ eLpNorm (fun x => pvTrunc d 1 (fun v : Euc d => v i) W δ x) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => pvTrunc d 1 (fun v : Euc d => v i) W 1 x) (ENNReal.ofReal p) volume :=
          eLpNorm_sub_le hp1'
      _ ≤ ENNReal.ofReal C1 * eLpNorm W (ENNReal.ofReal p) volume +
          ENNReal.ofReal C1 * eLpNorm W (ENNReal.ofReal p) volume := add_le_add e1 e2
      _ = ENNReal.ofReal (2 * C1) * eLpNorm W (ENNReal.ofReal p) volume := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, ← two_mul,
            mul_assoc]
  have hBn : eLpNorm B (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (d * (B1 * (2 * C1))) * eLpNorm W (ENNReal.ofReal p) volume := by
    have hsum : B = ∑ i : Fin d, fun x => gradient μ x i * Φ i x := by
      funext x; simp [hB, Finset.sum_apply]
    rw [hsum]
    refine (eLpNorm_sum_le hp1').trans ?_
    have hterm : ∀ i : Fin d, eLpNorm (fun x => gradient μ x i * Φ i x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (B1 * (2 * C1)) * eLpNorm W (ENNReal.ofReal p) volume := fun i =>
      (sa16u3_eLp_mul_le hB1 (sa16u3_grad_cont hμ2 i).aestronglyMeasurable (hΦm i)
        (fun x => sa16u3_grad_le h1 x i)).trans (by
          rw [ENNReal.ofReal_mul hB1, mul_assoc]
          exact mul_le_mul_right (hΦn i) _)
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg d), ← mul_assoc]
    simp
  have hfun : (fun x => jumpCut d 1 δ (fun y => μ y * W y) x - μ x * jumpCut d 1 δ W x) =
      fun x => A x + B x := funext hF
  rw [hfun]
  calc eLpNorm (fun x => A x + B x) (ENNReal.ofReal p) volume
      ≤ eLpNorm A (ENNReal.ofReal p) volume + eLpNorm B (ENNReal.ofReal p) volume :=
        eLpNorm_add_le hp1'
    _ ≤ ENNReal.ofReal (B2 / 2 * I1 + 2 * B0 * J1) * eLpNorm W (ENNReal.ofReal p) volume +
        ENNReal.ofReal (d * (B1 * (2 * C1))) * eLpNorm W (ENNReal.ofReal p) volume :=
        add_le_add hAn hBn
    _ = ENNReal.ofReal (B2 / 2 * I1 + 2 * B0 * J1 + d * (B1 * (2 * C1))) *
          eLpNorm W (ENNReal.ofReal p) volume := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((I1 / 2 + 2 * J1 + 2 * d * C1 + 1) * cbNorm 2 μ) *
          eLpNorm W (ENNReal.ofReal p) volume := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        rw [hcb]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith [mul_nonneg hI1n hB0, mul_nonneg hI1n hB1, mul_nonneg hI1n hB2,
          mul_nonneg hJ1n hB0, mul_nonneg hJ1n hB1, mul_nonneg hJ1n hB2,
          mul_nonneg (mul_nonneg hd0 hC1) hB0, mul_nonneg (mul_nonneg hd0 hC1) hB1,
          mul_nonneg (mul_nonneg hd0 hC1) hB2]

end HRS.Whole.AppendixA.Phase2SA16Cutoff
