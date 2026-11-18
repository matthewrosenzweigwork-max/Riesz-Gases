import HRS.MS.SA16SEn3

/-!
# S.A.16 (SA16S) En4: the regularized diffusion and transport identities (packet P7, step 5)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section En4
variable {d : ℕ} {ι : Type*} [Fintype ι]

lemma sa16sy_T_cc {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) :
    IsCcInfty (fun x => ∑ a, W a x ^ 2) := by
  have h : (fun x => ∑ a, W a x ^ 2) = ∑ a : ι, fun x => W a x ^ 2 := by
    funext x; simp [Finset.sum_apply]
  rw [h]
  exact (ccSub d).sum_mem (fun a _ => (⟨(hW a).1.pow 2, (hW a).2.comp_left (g := fun t => t ^ 2) (by simp)⟩ :
    IsCcInfty (fun x => W a x ^ 2)))

lemma sa16sy_theta_cc {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) {p η : ℝ} (hη : 0 < η) (hp : 0 < p) :
    IsCcInfty (fun x => sa16sy_s W η x ^ (p / 2) - η ^ p) := by
  have hT := sa16sy_T_cc hW
  refine ⟨(sa16sy_rpow_smooth hW hη (p / 2)).sub contDiff_const, ?_⟩
  have := hT.2.comp_left (g := fun t : ℝ => (t + η ^ 2) ^ (p / 2) - η ^ p) (by
    simp only [zero_add]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    push_cast
    rw [show (2 : ℝ) * (p / 2) = p by ring]
    simp)
  exact this

lemma sa16sy_dir_cont {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) (a : ι) (e : Euc d) :
    IsCcInfty (fun y => fderiv ℝ (W a) y e) := sa16s_cc_fderiv (hW a) e

/-- the derivative of `A_a = s^r W_a` -/
lemma sa16sy_A_fderiv {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) {η : ℝ} (hη : 0 < η) (r : ℝ)
    (a : ι) (x e : Euc d) :
    fderiv ℝ (fun y => sa16sy_s W η y ^ r * W a y) x e =
      (r * sa16sy_s W η x ^ (r - 1) * (2 * ∑ b, W b x * fderiv ℝ (W b) x e)) * W a x +
        sa16sy_s W η x ^ r * fderiv ℝ (W a) x e := by
  have h1 : HasFDerivAt (fun y => sa16sy_s W η y ^ r)
      ((r * sa16sy_s W η x ^ (r - 1)) • ∑ b, (2 * W b x) • fderiv ℝ (W b) x) x := by
    have h1 := (sa16sy_s_hasFDerivAt hW η x)
    exact (Real.hasDerivAt_rpow_const (Or.inl (sa16sy_s_pos W hη x).ne') : HasDerivAt (fun t : ℝ => t ^ r)
      (r * sa16sy_s W η x ^ (r - 1)) (sa16sy_s W η x)).comp_hasFDerivAt x h1
  have h2 := h1.mul ((hW a).1.differentiable (by simp) x).hasFDerivAt
  have h3 : HasFDerivAt (fun y => sa16sy_s W η y ^ r * W a y) _ x := h2
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.sum_apply]
  have : ∑ b, 2 * W b x * (fderiv ℝ (W b) x) e = 2 * ∑ b, W b x * (fderiv ℝ (W b) x) e := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  ring

lemma sa16sy_diff_eta {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) {p : ℝ} (hp : 2 ≤ p) {η : ℝ}
    (hη : 0 < η) (e : Euc d) :
    ∑ a, ∫ x, sa16sy_s W η x ^ (p / 2 - 1) * W a x *
      fderiv ℝ (fun y => fderiv ℝ (W a) y e) x e ≤ 0 := by
  set r : ℝ := p / 2 - 1 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hA : ∀ a, ContDiff ℝ ∞ (fun x => sa16sy_s W η x ^ r * W a x) :=
    fun a => (sa16sy_rpow_smooth hW hη r).mul (hW a).1
  have hstep : ∀ a, ∫ x, sa16sy_s W η x ^ r * W a x * fderiv ℝ (fun y => fderiv ℝ (W a) y e) x e =
      -∫ x, fderiv ℝ (fun y => sa16sy_s W η y ^ r * W a y) x e * fderiv ℝ (W a) x e := by
    intro a
    have := sa16sw_ibp (hA a) (sa16sy_dir_cont hW a e) e
    linarith
  simp_rw [hstep]
  rw [Finset.sum_neg_distrib, neg_nonpos]
  have hint : ∀ a, Integrable (fun x => fderiv ℝ (fun y => sa16sy_s W η y ^ r * W a y) x e *
      fderiv ℝ (W a) x e) := by
    intro a
    have hc : Continuous (fun x => fderiv ℝ (fun y => sa16sy_s W η y ^ r * W a y) x e) :=
      ((hA a).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.mul (sa16sy_dir_cont hW a e).1.continuous).integrable_of_hasCompactSupport
      (sa16sy_dir_cont hW a e).2.mul_left
  rw [← integral_finsetSum _ (fun a _ => hint a)]
  refine integral_nonneg fun x => ?_
  simp only [sa16sy_A_fderiv hW hη r _ x e]
  set s := sa16sy_s W η x with hs
  have hspos : 0 < s := sa16sy_s_pos W hη x
  set S1 := ∑ b, W b x * fderiv ℝ (W b) x e with hS1
  have e1 : ∑ a, ((r * s ^ (r - 1) * (2 * S1)) * W a x + s ^ r * fderiv ℝ (W a) x e) *
      fderiv ℝ (W a) x e = 2 * r * s ^ (r - 1) * S1 ^ 2 + s ^ r * ∑ a, (fderiv ℝ (W a) x e) ^ 2 := by
    have : ∀ a, ((r * s ^ (r - 1) * (2 * S1)) * W a x + s ^ r * fderiv ℝ (W a) x e) * fderiv ℝ (W a) x e =
        (r * s ^ (r - 1) * (2 * S1)) * (W a x * fderiv ℝ (W a) x e) + s ^ r * (fderiv ℝ (W a) x e) ^ 2 :=
      fun a => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← hS1, Finset.mul_sum]
    rw [← Finset.mul_sum]
    ring
  rw [e1]
  have h1 : 0 ≤ s ^ (r - 1) := Real.rpow_nonneg hspos.le _
  have h2 : 0 ≤ s ^ r := Real.rpow_nonneg hspos.le _
  have h3 : 0 ≤ ∑ a, (fderiv ℝ (W a) x e) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have : 0 ≤ 2 * r * s ^ (r - 1) * S1 ^ 2 := by positivity
  exact add_nonneg this (mul_nonneg h2 h3)

end En4

end HRS.Whole.AppendixA.Phase2SA16R
