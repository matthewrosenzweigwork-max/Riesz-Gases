import HRS.MS.SA16Y3Iw1
import HRS.MS.SA16Y3Op1

/-!
# S.A.16 (SA16Y3) Iw2: `L^q` bound of the iso dual `∑_i ∂_i (μ Q^i ψ)` (packet P7/P8, iso case)

`sa16y3_dual_pt`: `∑_i ∂_i (μ · Q^i ψ) = ∑_j ((∂_j μ) Q^j ψ + μ Q^j (∂_j ψ))` (product rule and `sa16y3_Q_deriv`).
`sa16y3_dual_Lp`: for `1 < q`, `‖∑_i ∂_i (μ Q^i ψ)‖_{L^q} ≤ (2 ∑_j C_j) Λ S_2^q(ψ)` when `sa16z_Cb 1 Λ μ`,
with the constants `C_j` of `sa16y3_Q_jet` at exponent `q` (`c = 1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Iw2
variable {d : ℕ} {s : ℝ}

lemma sa16y3_partial_one (ψ : Euc d → ℝ) (i : Fin d) (x : Euc d) :
    partialDeriv (fun _ : Fin 1 => i) ψ x = sa16z_dm ψ i x := by
  unfold partialDeriv sa16z_dm
  rw [iteratedFDeriv_one_apply]

lemma sa16y3_partial_empty (ψ : Euc d → ℝ) (κ : Fin 0 → Fin d) : partialDeriv κ ψ = ψ := by
  funext x
  unfold partialDeriv
  rw [iteratedFDeriv_zero_apply]

lemma sa16y3_dual_pt (hs0 : 0 ≤ s) (hsd : s < d) {μ ψ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ)
    (hψ : IsCcInfty ψ) (x : Euc d) :
    sa16y3_dualIW s μ ψ x = ∑ j : Fin d, (fderiv ℝ μ x (sa16z_e j) * sa16y3_Q s j ψ x +
      μ x * sa16y3_Q s j (sa16z_dm ψ j) x) := by
  unfold sa16y3_dualIW
  refine Finset.sum_congr rfl fun j _ => ?_
  have hQ : ContDiff ℝ ∞ (sa16y3_Q s j ψ) := sa16y3_Q_smooth hs0 hsd hψ j
  rw [show (fun y => μ y * sa16y3_Q s j ψ y) = μ * sa16y3_Q s j ψ from rfl,
    fderiv_mul (hμ.differentiable (by simp) x) (hQ.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [sa16y3_Q_deriv hs0 hsd hψ j j x]
  ring

lemma sa16y3_Q_one (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {q : ℝ} (hq : 1 < q)
    (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ψ : Euc d → ℝ}, IsCcInfty ψ → ∀ {r : ℕ} (κ : Fin r → Fin d),
      eLpNorm (sa16y3_Q s i (partialDeriv κ ψ)) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal C * sa16z_S q ψ (r + 1) := by
  obtain ⟨C, hC0, hC⟩ := sa16y3_Q_jet (s := s) hd hs0 hsd hθ1 hq i
  refine ⟨C, hC0, fun {ψ} hψ {r} κ => ?_⟩
  have h := hC (c := fun _ : Euc d => (1 : ℝ)) (φ := ψ) contDiff_const hψ (Bc := 1) (Lc := 0)
    zero_le_one le_rfl (fun y => by simp) (fun y => by simp) κ
  simpa using h

lemma sa16y3_eLp_const_norm {q c : ℝ} (hc : 0 ≤ c) (f : Euc d → ℝ) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => c * ‖f x‖) (ENNReal.ofReal q) volume =
      ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal q) volume := by
  have h : (fun x => c * ‖f x‖) = c • (fun x => ‖f x‖) := by
    funext x; simp [smul_eq_mul]
  rw [h, eLpNorm_const_smul, eLpNorm_norm f hf, Real.enorm_eq_ofReal hc]

lemma sa16y3_eLp_mul_le {q Λ C : ℝ} {S : ENNReal} (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) {a f : Euc d → ℝ}
    (ha : Continuous a) (hf : Continuous f) (hab : ∀ x, ‖a x‖ ≤ Λ)
    (hQ : eLpNorm f (ENNReal.ofReal q) volume ≤ ENNReal.ofReal C * S) :
    eLpNorm (fun x => a x * f x) (ENNReal.ofReal q) volume ≤ ENNReal.ofReal (Λ * C) * S := by
  have hm : AEStronglyMeasurable (fun x => a x * f x) volume := (ha.mul hf).aestronglyMeasurable
  calc eLpNorm (fun x => a x * f x) (ENNReal.ofReal q) volume
      ≤ eLpNorm (fun x => Λ * ‖f x‖) (ENNReal.ofReal q) volume :=
        eLpNorm_mono_real hm (fun x => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hab x) (norm_nonneg _))
    _ = ENNReal.ofReal Λ * eLpNorm f (ENNReal.ofReal q) volume :=
        sa16y3_eLp_const_norm hΛ f hf.aestronglyMeasurable
    _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal C * S) := mul_le_mul' le_rfl hQ
    _ = ENNReal.ofReal (Λ * C) * S := by rw [ENNReal.ofReal_mul hΛ, mul_assoc]

theorem sa16y3_dual_Lp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ ψ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty ψ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb 1 Λ μ →
      eLpNorm (sa16y3_dualIW s μ ψ) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (C * Λ) * sa16z_S q ψ 2 := by
  choose Ci hCi0 hCi using fun i : Fin d => sa16y3_Q_one hd hs0 hsd hθ1 hq i
  refine ⟨2 * ∑ i : Fin d, Ci i, mul_nonneg zero_le_two (Finset.sum_nonneg fun i _ => hCi0 i), ?_⟩
  intro μ ψ hμ hψ Λ hΛ hCb
  have hb0 : sa16z_Cb 0 Λ μ := sa16z_Cb_mono (Nat.zero_le _) hCb
  have hab : ∀ x, |μ x| ≤ Λ := sa16z_Cb_abs hb0
  have hfd : ∀ x, ‖fderiv ℝ μ x‖ ≤ Λ := sa16z_Cb_fderiv hCb
  have hdm : ∀ i : Fin d, IsCcInfty (sa16z_dm ψ i) := fun i => sa16s_cc_fderiv hψ (sa16z_e i)
  have hQc : ∀ i : Fin d, Continuous (sa16y3_Q s i ψ) :=
    fun i => (sa16y3_Q_smooth hs0 hsd hψ i).continuous
  have hQdc : ∀ i : Fin d, Continuous (sa16y3_Q s i (sa16z_dm ψ i)) :=
    fun i => (sa16y3_Q_smooth hs0 hsd (hdm i) i).continuous
  have hMc : ∀ i : Fin d, Continuous (fun x => fderiv ℝ μ x (sa16z_e i)) :=
    fun i => (hμ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hen : ∀ j : Fin d, ‖sa16z_e j‖ = 1 := fun j => by simp [sa16z_e]
  have hAb : ∀ j : Fin d, ∀ x, ‖fderiv ℝ μ x (sa16z_e j)‖ ≤ Λ := fun j x =>
    ((fderiv ℝ μ x).le_opNorm _).trans (by rw [hen j, mul_one]; exact hfd x)
  have hBb : ∀ x, ‖μ x‖ ≤ Λ := fun x => by rw [Real.norm_eq_abs]; exact hab x
  have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq.le
  have hterm : ∀ j : Fin d,
      eLpNorm (fun x => fderiv ℝ μ x (sa16z_e j) * sa16y3_Q s j ψ x +
        μ x * sa16y3_Q s j (sa16z_dm ψ j) x) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (2 * Λ * Ci j) * sa16z_S q ψ 2 := by
    intro j
    have hQ0 : eLpNorm (sa16y3_Q s j ψ) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (Ci j) * sa16z_S q ψ 2 := by
      have h0 := hCi j hψ (r := 0) (fun i => Fin.elim0 i)
      rw [sa16y3_partial_empty] at h0
      exact h0.trans (mul_le_mul' le_rfl (sa16z_S_mono ψ (by norm_num)))
    have hQ1 : eLpNorm (sa16y3_Q s j (sa16z_dm ψ j)) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (Ci j) * sa16z_S q ψ 2 := by
      have h1 := hCi j hψ (r := 1) (fun _ => j)
      have hfun : partialDeriv (fun _ : Fin 1 => j) ψ = sa16z_dm ψ j :=
        funext fun x => sa16y3_partial_one ψ j x
      rw [hfun] at h1
      exact h1
    have hA := sa16y3_eLp_mul_le (q := q) hΛ (hCi0 j) (hMc j) (hQc j) (hAb j) hQ0
    have hB := sa16y3_eLp_mul_le (q := q) hΛ (hCi0 j) hμ.continuous (hQdc j) hBb hQ1
    have hmA : AEStronglyMeasurable (fun x => fderiv ℝ μ x (sa16z_e j) * sa16y3_Q s j ψ x) volume :=
      ((hMc j).mul (hQc j)).aestronglyMeasurable
    have hmB : AEStronglyMeasurable (fun x => μ x * sa16y3_Q s j (sa16z_dm ψ j) x) volume :=
      (hμ.continuous.mul (hQdc j)).aestronglyMeasurable
    calc eLpNorm (fun x => fderiv ℝ μ x (sa16z_e j) * sa16y3_Q s j ψ x +
          μ x * sa16y3_Q s j (sa16z_dm ψ j) x) (ENNReal.ofReal q) volume
        ≤ eLpNorm (fun x => fderiv ℝ μ x (sa16z_e j) * sa16y3_Q s j ψ x) (ENNReal.ofReal q) volume +
            eLpNorm (fun x => μ x * sa16y3_Q s j (sa16z_dm ψ j) x) (ENNReal.ofReal q) volume :=
          eLpNorm_add_le hq1
      _ ≤ ENNReal.ofReal (Λ * Ci j) * sa16z_S q ψ 2 + ENNReal.ofReal (Λ * Ci j) * sa16z_S q ψ 2 :=
          add_le_add hA hB
      _ = ENNReal.ofReal (2 * Λ * Ci j) * sa16z_S q ψ 2 := by
          rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hΛ (hCi0 j)) (mul_nonneg hΛ (hCi0 j))]
          congr 2
          ring
  have hfun : sa16y3_dualIW s μ ψ = fun x => ∑ j : Fin d, (fderiv ℝ μ x (sa16z_e j) *
      sa16y3_Q s j ψ x + μ x * sa16y3_Q s j (sa16z_dm ψ j) x) :=
    funext fun x => sa16y3_dual_pt hs0 hsd hμ hψ x
  have hsumf : (fun x => ∑ j : Fin d, (fderiv ℝ μ x (sa16z_e j) * sa16y3_Q s j ψ x +
      μ x * sa16y3_Q s j (sa16z_dm ψ j) x)) =
      ∑ j : Fin d, (fun x => fderiv ℝ μ x (sa16z_e j) * sa16y3_Q s j ψ x +
        μ x * sa16y3_Q s j (sa16z_dm ψ j) x) :=
    funext fun x => by simp [Finset.sum_apply]
  rw [hfun, hsumf]
  calc eLpNorm (∑ j : Fin d, (fun x => fderiv ℝ μ x (sa16z_e j) * sa16y3_Q s j ψ x +
        μ x * sa16y3_Q s j (sa16z_dm ψ j) x)) (ENNReal.ofReal q) volume
      ≤ ∑ j : Fin d, eLpNorm (fun x => fderiv ℝ μ x (sa16z_e j) * sa16y3_Q s j ψ x +
          μ x * sa16y3_Q s j (sa16z_dm ψ j) x) (ENNReal.ofReal q) volume :=
        eLpNorm_sum_le hq1
    _ ≤ ∑ j : Fin d, ENNReal.ofReal (2 * Λ * Ci j) * sa16z_S q ψ 2 :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (∑ j : Fin d, ENNReal.ofReal (2 * Λ * Ci j)) * sa16z_S q ψ 2 := by
        rw [Finset.sum_mul]
    _ = ENNReal.ofReal (∑ j : Fin d, 2 * Λ * Ci j) * sa16z_S q ψ 2 := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_nonneg zero_le_two hΛ) (hCi0 j))]
    _ = ENNReal.ofReal ((2 * ∑ i : Fin d, Ci i) * Λ) * sa16z_S q ψ 2 := by
        congr 2
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

end Iw2

end HRS.Whole.AppendixA.Phase2SA16R
