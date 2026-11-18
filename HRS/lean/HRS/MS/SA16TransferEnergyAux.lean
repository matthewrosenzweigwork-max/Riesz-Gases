import HRS.MS.SA16TransferDefs
import HRS.MS.SA16EvolE5

/-!
# S.A.16 energy transfer: auxiliary calculus for a smooth norm (used by T4, T5)

Basic facts on `IsSmoothNorm`, Jensen for `N`, and a uniform one-step energy estimate on compact sets.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA

section Aux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {p : ℝ} {N : X → ℝ}

lemma sa16x_N_zero (hN : IsSmoothNorm p N) : N 0 = 0 := (hN.zero 0).2 rfl

lemma sa16x_N_neg (hN : IsSmoothNorm p N) (x : X) : N (-x) = N x := by
  have := hN.smul (-1) x
  simpa using this

lemma sa16x_N_sub_le (hN : IsSmoothNorm p N) (x y : X) : N (x - y) ≤ N x + N y := by
  rw [sub_eq_add_neg]
  exact (hN.add x (-y)).trans (by rw [sa16x_N_neg hN])

/-- `N` is Lipschitz for the ambient norm -/
lemma sa16x_N_lip (hN : IsSmoothNorm p N) : ∃ C : ℝ, 0 < C ∧ ∀ x y, |N x - N y| ≤ C * ‖x - y‖ := by
  obtain ⟨c, C, hc, hC, h⟩ := hN.equivalent
  refine ⟨C, hC, fun x y => ?_⟩
  have h1 : N x - N y ≤ N (x - y) := by
    have := hN.add (x - y) y
    simp only [sub_add_cancel] at this
    linarith
  have h2 : N y - N x ≤ N (y - x) := by
    have := hN.add (y - x) x
    simp only [sub_add_cancel] at this
    linarith
  have h3 : N (y - x) = N (x - y) := by rw [← neg_sub, sa16x_N_neg hN]
  rw [abs_le]
  constructor
  · have := (h (x - y)).2
    linarith
  · have := (h (x - y)).2
    linarith

lemma sa16x_N_cont (hN : IsSmoothNorm p N) : Continuous N := by
  obtain ⟨C, hC, h⟩ := sa16x_N_lip hN
  refine LipschitzWith.continuous (K := ⟨C, hC.le⟩) (LipschitzWith.of_dist_le_mul fun x y => ?_)
  rw [Real.dist_eq, dist_eq_norm]
  exact h x y

lemma sa16x_N_convex (hN : IsSmoothNorm p N) : ConvexOn ℝ (Set.univ : Set X) N := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1 := hN.add (a • x) (b • y)
  rw [hN.smul, hN.smul, abs_of_nonneg ha, abs_of_nonneg hb] at h1
  simpa using h1

lemma sa16x_N_comp_int (hN : IsSmoothNorm p N) {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → X} (hf : Integrable f μ) : Integrable (fun x => N (f x)) μ := by
  obtain ⟨C, hC, hl⟩ := sa16x_N_lip hN
  refine Integrable.mono' (g := fun x => C * ‖f x‖) (hf.norm.const_mul C)
    ((sa16x_N_cont hN).comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  refine Eventually.of_forall fun x => ?_
  have := hl (f x) 0
  rw [sa16x_N_zero hN, sub_zero, sub_zero] at this
  rw [Real.norm_eq_abs]
  exact this

/-- Jensen's inequality for the smooth norm `N` -/
lemma sa16x_N_integral_le [CompleteSpace X] (hN : IsSmoothNorm p N) {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → X} (hf : Integrable f μ) :
    N (∫ x, f x ∂μ) ≤ ∫ x, N (f x) ∂μ := by
  have hint : Integrable (fun x => N (f x)) μ := sa16x_N_comp_int hN hf
  by_cases h0 : μ = 0
  · subst h0
    simp [sa16x_N_zero hN]
  · have : NeZero μ := ⟨h0⟩
    have hJ := (sa16x_N_convex hN).map_average_le (sa16x_N_cont hN).continuousOn isClosed_univ
      (Eventually.of_forall fun _ => mem_univ _) hf hint
    have hm : 0 < μ.real univ := by
      have : μ univ ≠ 0 := by simpa using h0
      exact ENNReal.toReal_pos this (measure_ne_top _ _)
    rw [average_eq, average_eq] at hJ
    have e1 : ∫ x, f x ∂μ = μ.real univ • ((μ.real univ)⁻¹ • ∫ x, f x ∂μ) := by
      rw [smul_smul, mul_inv_cancel₀ hm.ne', one_smul]
    have e2 : ∫ x, N (f x) ∂μ = μ.real univ * ((μ.real univ)⁻¹ * ∫ x, N (f x) ∂μ) := by
      rw [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
    rw [e1, hN.smul, abs_of_pos hm]
    conv_rhs => rw [e2]
    simp only [smul_eq_mul] at hJ ⊢
    exact mul_le_mul_of_nonneg_left hJ hm.le

/-- uniform nearness of a continuous map around a compact set -/
lemma sa16x_unif_near {Y : Type*} [NormedAddCommGroup Y] {F : X → Y} (hF : Continuous F)
    {Q : Set X} (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Q, ∀ z : X, ‖z‖ ≤ ρ → ‖F (x + z) - F x‖ < ε := by
  have hopen : IsOpen {q : X × X | ‖F (q.1 + q.2) - F q.1‖ < ε} :=
    isOpen_lt (by fun_prop) continuous_const
  obtain ⟨u, v, hu, hv, hQu, h0v, huv⟩ := generalized_tube_lemma hQ isCompact_singleton
    (n := {q : X × X | ‖F (q.1 + q.2) - F q.1‖ < ε}) hopen (by
      intro q hq
      obtain ⟨h1, h2⟩ := hq
      have : q.2 = 0 := h2
      simpa [this, hε] using hε)
  have h0 : (0 : X) ∈ v := h0v rfl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hv 0 h0
  refine ⟨r / 2, by positivity, fun x hx z hz => ?_⟩
  have : (x, z) ∈ u ×ˢ v := ⟨hQu hx, hball (by
    rw [Metric.mem_ball, dist_zero_right]; linarith)⟩
  exact huv this

lemma sa16x_root_aux {p a y e : ℝ} (hp : 1 ≤ p) (ha : 0 < a) (hy : 0 ≤ y) (he : 0 ≤ e)
    (hyp : y ^ p ≤ a ^ p + e) : p * a ^ (p - 1) * (y - a) ≤ e := by
  by_cases hya : y ≤ a
  · have : 0 ≤ p * a ^ (p - 1) := by positivity
    nlinarith
  · push Not at hya
    have hs0 : 0 ≤ (y - a) / a := by
      have : 0 ≤ y - a := by linarith
      positivity
    have hy' : y = a * (1 + (y - a) / a) := by field_simp; ring
    have hyp2 : a ^ p * (1 + p * ((y - a) / a)) ≤ y ^ p := by
      conv_rhs => rw [hy', Real.mul_rpow ha.le (by linarith)]
      exact mul_le_mul_of_nonneg_left (one_add_mul_self_le_rpow_one_add (by linarith) hp)
        (by positivity)
    have hpa : a ^ p * (p * ((y - a) / a)) = p * a ^ (p - 1) * (y - a) := by
      rw [Real.rpow_sub_one ha.ne']
      field_simp
    nlinarith

lemma sa16x_step_small (hN : IsSmoothNorm p N) {c C K C₁ h η L : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hcC : ∀ x, c * ‖x‖ ≤ N x ∧ N x ≤ C * ‖x‖) (hK : 0 ≤ K) (hh : 0 < h)
    (hL0 : 0 ≤ L) (hL : C * K / c - C₁ ≤ L) {x z : X} (hz : ‖z‖ ≤ K * h * ‖x‖) (hsmall : N x ≤ η) :
    N (x + z) ≤ N x * (1 + C₁ * h) + η * L * h := by
  have hnx0 := hN.nonneg x
  have hNz : N z ≤ C * ‖z‖ := (hcC z).2
  have hx' : ‖x‖ ≤ N x / c := by rw [le_div_iff₀ hc]; linarith [(hcC x).1]
  have h1 : N (x + z) ≤ N x + N z := hN.add x z
  have h2 : C * ‖z‖ ≤ C * (K * h * (N x / c)) :=
    mul_le_mul_of_nonneg_left (hz.trans (mul_le_mul_of_nonneg_left hx' (by positivity))) hC.le
  have h3 : C * (K * h * (N x / c)) = N x * h * (C * K / c) := by
    field_simp
  have h6 : N x * h * (C * K / c) = N x * (C₁ * h) + N x * h * (C * K / c - C₁) := by ring
  have h7 : N x * h * (C * K / c - C₁) ≤ N x * h * L :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h8 : N x * h * L ≤ η * L * h := by
    have : N x * (h * L) ≤ η * (h * L) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    linarith
  linarith

lemma sa16x_step_large {p y nx C₁ h e P : ℝ} (hp : 1 ≤ p) (hnx : 0 < nx) (hC1h : -(1 / 2 : ℝ) ≤ C₁ * h)
    (hy : 0 ≤ y) (he : 0 ≤ e) (hyp : y ^ p ≤ nx ^ p + h * (p * C₁ * nx ^ p) + e)
    (hP : 0 < P) (hPa : P ≤ p * (nx * (1 + C₁ * h)) ^ (p - 1)) :
    y ≤ nx * (1 + C₁ * h) + e / P := by
  have ha0 : 0 < nx * (1 + C₁ * h) := by
    have : 0 < 1 + C₁ * h := by linarith
    positivity
  have hbern : nx ^ p * (1 + p * (C₁ * h)) ≤ (nx * (1 + C₁ * h)) ^ p := by
    rw [Real.mul_rpow hnx.le (by linarith)]
    exact mul_le_mul_of_nonneg_left (one_add_mul_self_le_rpow_one_add (by linarith) hp)
      (by positivity)
  have h1 : nx ^ p * (1 + p * (C₁ * h)) = nx ^ p + h * (p * C₁ * nx ^ p) := by ring
  have hkey := sa16x_root_aux hp ha0 hy he (hyp.trans (by linarith))
  have h2 : P * (y - nx * (1 + C₁ * h)) ≤ e := by
    by_cases hya : y ≤ nx * (1 + C₁ * h)
    · have : P * (y - nx * (1 + C₁ * h)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hP.le (by linarith)
      linarith
    · push Not at hya
      exact (mul_le_mul_of_nonneg_right hPa (by linarith)).trans hkey
  have : y - nx * (1 + C₁ * h) ≤ e / P := by
    rw [le_div_iff₀ hP]; linarith
  linarith

/-- Taylor expansion of `N ^ p` with uniformly small remainder near a compact set -/
lemma sa16x_taylor (hN : IsSmoothNorm p N) {Q : Set X} {ε ρ : ℝ} (hρ : 0 < ρ)
    (hρF : ∀ x ∈ Q, ∀ z : X, ‖z‖ ≤ ρ →
      ‖fderiv ℝ (fun y => (N y) ^ p) (x + z) - fderiv ℝ (fun y => (N y) ^ p) x‖ < ε)
    {x : X} (hx : x ∈ Q) {z : X} (hz : ‖z‖ ≤ ρ) :
    (N (x + z)) ^ p ≤ (N x) ^ p + fderiv ℝ (fun y => (N y) ^ p) x z + ε * ‖z‖ := by
  set G : X → ℝ := fun y => (N y) ^ p with hG
  have hGd : Differentiable ℝ G := hN.differentiable
  have hmv : ‖(G (x + z) - fderiv ℝ G x (x + z)) - (G x - fderiv ℝ G x x)‖ ≤ ε * ‖x + z - x‖ := by
    refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fun y => G y - fderiv ℝ G x y) (s := Metric.closedBall x ρ) (fun y _ => ?_)
      (fun y hy => ?_) (convex_closedBall x ρ) (Metric.mem_closedBall_self hρ.le) ?_
    · exact (hGd y).sub (fderiv ℝ G x).differentiableAt
    · have hd : HasFDerivAt (fun y => G y - fderiv ℝ G x y)
          (fderiv ℝ G y - fderiv ℝ G x) y :=
        (hGd y).hasFDerivAt.sub (fderiv ℝ G x).hasFDerivAt
      rw [hd.fderiv]
      have := hρF x hx (y - x) (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy)
      simpa using this.le
    · rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using hz
  have h1 : (G (x + z) - fderiv ℝ G x (x + z)) - (G x - fderiv ℝ G x x) ≤ ε * ‖z‖ :=
    calc _ ≤ ‖(G (x + z) - fderiv ℝ G x (x + z)) - (G x - fderiv ℝ G x x)‖ := by
          rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ ε * ‖x + z - x‖ := hmv
      _ = ε * ‖z‖ := by rw [add_sub_cancel_left]
  rw [map_add] at h1
  show G (x + z) ≤ G x + fderiv ℝ G x z + ε * ‖z‖
  linarith

/-- the one-step energy estimate, uniform on a compact set -/
lemma sa16x_step (hN : IsSmoothNorm p N) (hp : 2 ≤ p) (K C₁ : ℝ) (hK : 0 ≤ K)
    {Q : Set X} (hQ : IsCompact Q) {θ : ℝ} (hθ : 0 < θ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ x ∈ Q, ∀ z : X, ‖z‖ ≤ K * h * ‖x‖ →
      fderiv ℝ (fun y => (N y)^p) x z ≤ h * (p * C₁ * (N x)^p) →
      N (x + z) ≤ N x * (1 + C₁ * h) + θ * h := by
  obtain ⟨c, C, hc, hC, hcC⟩ := hN.equivalent
  obtain ⟨R₀, hR₀⟩ := hQ.isBounded.exists_norm_le
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  obtain ⟨R, hR0, hRb⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ Q, ‖x‖ ≤ R :=
    ⟨max R₀ 0, le_max_right _ _, fun x hx => (hR₀ x hx).trans (le_max_left _ _)⟩
  obtain ⟨L, hL1, hL⟩ : ∃ L : ℝ, 1 ≤ L ∧ C * K / c - C₁ ≤ L := by
    refine ⟨C * K / c + |C₁| + 1, ?_, ?_⟩
    · have : 0 ≤ C * K / c := by positivity
      have := abs_nonneg C₁
      linarith
    · have := neg_abs_le C₁
      linarith
  obtain ⟨η, hη0, hηL⟩ : ∃ η : ℝ, 0 < η ∧ η * L = θ / 2 :=
    ⟨θ / (2 * L), by positivity, by field_simp⟩
  obtain ⟨P, hP0, hP⟩ : ∃ P : ℝ, 0 < P ∧ P = p * (η / 2) ^ (p - 1) :=
    ⟨_, by positivity, rfl⟩
  have hKR : 0 < K * R + 1 := by positivity
  obtain ⟨ε, hε0, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε = θ * P / (2 * (K * R + 1)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨ρ, hρ, hρF⟩ := sa16x_unif_near hN.cont_deriv hQ hε0
  refine ⟨min (1 / (2 * (|C₁| + 1))) (ρ / (K * R + 1)), by positivity,
    fun h hh hh0 x hx z hz hdz => ?_⟩
  have hhA : h ≤ 1 / (2 * (|C₁| + 1)) := hh0.trans (min_le_left _ _)
  have hhB : h ≤ ρ / (K * R + 1) := hh0.trans (min_le_right _ _)
  have hxR := hRb x hx
  have hnx0 := hN.nonneg x
  have hzR : ‖z‖ ≤ ρ := by
    have h1 : K * h * ‖x‖ ≤ K * h * R := mul_le_mul_of_nonneg_left hxR (by positivity)
    have h2 : h * (K * R + 1) ≤ ρ := by
      rwa [le_div_iff₀ hKR] at hhB
    nlinarith
  by_cases hsmall : N x < η
  · have := sa16x_step_small hN hc hC hcC hK hh (by linarith) hL hz hsmall.le
    have h9 : η * L * h = θ / 2 * h := by rw [hηL]
    nlinarith [mul_pos hθ hh]
  · push Not at hsmall
    have hnxpos : 0 < N x := lt_of_lt_of_le hη0 hsmall
    have hC1h : -(1 / 2 : ℝ) ≤ C₁ * h := by
      have h1 : |C₁| * h ≤ 1 / 2 := by
        calc |C₁| * h ≤ |C₁| * (1 / (2 * (|C₁| + 1))) :=
              mul_le_mul_of_nonneg_left hhA (abs_nonneg _)
          _ ≤ 1 / 2 := by
              rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith
      have h2 : -|C₁| * h ≤ C₁ * h := mul_le_mul_of_nonneg_right (neg_abs_le C₁) hh.le
      linarith
    have hT := sa16x_taylor hN hρ (fun x hx z hz => hρF x hx z hz) hx hzR
    have hε1 : ε * ‖z‖ ≤ ε * (K * h * R) :=
      mul_le_mul_of_nonneg_left (hz.trans (mul_le_mul_of_nonneg_left hxR (by positivity))) hε0.le
    have hyp : (N (x + z)) ^ p ≤ (N x) ^ p + h * (p * C₁ * (N x) ^ p) + ε * (K * h * R) := by
      linarith
    have ha_pos : η / 2 ≤ N x * (1 + C₁ * h) := by
      calc η / 2 ≤ N x / 2 := by linarith
        _ = N x * (1 / 2) := by ring
        _ ≤ N x * (1 + C₁ * h) := mul_le_mul_of_nonneg_left (by linarith) hnx0
    have hPa : P ≤ p * (N x * (1 + C₁ * h)) ^ (p - 1) := by
      rw [hP]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ha_pos (by linarith))
        hp0.le
    have := sa16x_step_large hp1 hnxpos hC1h (hN.nonneg _) (by positivity) hyp hP0 hPa
    have h2 : ε * (K * h * R) / P ≤ θ * h / 2 := by
      rw [div_le_iff₀ hP0, hε]
      have : K * R / (K * R + 1) ≤ 1 := by rw [div_le_one hKR]; linarith
      calc θ * P / (2 * (K * R + 1)) * (K * h * R)
          = θ * P * h / 2 * (K * R / (K * R + 1)) := by field_simp
        _ ≤ θ * P * h / 2 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
        _ = θ * h / 2 * P := by ring
    nlinarith [mul_pos hθ hh]

end Aux

end HRS.Whole.AppendixA.Phase2SA16Transfer
