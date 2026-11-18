import HRS.Sections.ScrnAux10
import HRS.Sections.ScrnAux3

/-!
# Packet SCRN, part 11: Riemann-sum comparison of the covariance matrices

For `φ_a ∈ C_c^∞`, times `t_a ≥ 0` and `b_N, b ∈ [b₋,b₊]`:
`|Re ℓ^d ∑_{k≠0} G^{ac}_{b_N}(ℓk) - (mesoCovMatrix b)_{ac}| ≤ C(ℓ + |b_N - b|)` with `C` independent of the times
(`scrn_cov_compare`): local Lipschitz bound of `G` away from `0` (`scrnk_lip`), `scrn_riemann`, and the
`b`-Lipschitz bound `scrnk_b_lip`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate SchwartzMap

namespace HRS

variable {d : ℕ}

lemma scrn_fourier_diff {φ : Euc d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Differentiable ℝ (𝓕 (scrnPhiC φ)) := by
  set f : 𝓢(Euc d, ℂ) := (hasCompactSupport_scrnPhiC hc).toSchwartzMap (contDiff_scrnPhiC hφ) with hf
  set g : 𝓢(Euc d, ℂ) := 𝓕 f with hg
  have hcoe : ⇑g = 𝓕 (scrnPhiC φ) := by
    rw [hg, SchwartzMap.fourier_coe]
    rfl
  rw [← hcoe]
  exact g.differentiable

lemma scrn_rpow_half {y x : ℝ} (N : ℕ) (hy : 0 ≤ y) (hx : (1 + y) / 2 ≤ x) :
    x ^ (-(N : ℝ)) ≤ 2 ^ N * (1 + y) ^ (-(N : ℝ)) := by
  have h0 : 0 < (1 + y) / 2 := by positivity
  calc x ^ (-(N : ℝ)) ≤ ((1 + y) / 2) ^ (-(N : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos h0 hx (by simp)
    _ = 2 ^ N * (1 + y) ^ (-(N : ℝ)) := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          Real.rpow_natCast]
        field_simp

/-- Local Lipschitz bound of a differentiable function with decaying derivative. -/
lemma scrn_F_lip {F : Euc d → ℂ} (hF : Differentiable ℝ F) {A : ℝ} {N : ℕ}
    (hD : ∀ ξ, ‖fderiv ℝ F ξ‖ ≤ A * (1 + ‖ξ‖) ^ (-(N : ℝ))) (hA : 0 ≤ A) {ξ η : Euc d}
    (hξη : ‖ξ - η‖ ≤ ‖η‖ / 2) :
    ‖F ξ - F η‖ ≤ A * 2 ^ N * (1 + ‖η‖) ^ (-(N : ℝ)) * ‖ξ - η‖ := by
  have hs : ∀ ζ ∈ Metric.closedBall η (‖η‖ / 2), ‖fderiv ℝ F ζ‖ ≤ A * 2 ^ N * (1 + ‖η‖) ^ (-(N : ℝ)) := by
    intro ζ hζ
    have h1 : ‖ζ - η‖ ≤ ‖η‖ / 2 := by simpa [dist_eq_norm] using hζ
    have h2 : ‖η‖ / 2 ≤ ‖ζ‖ := by
      have := norm_sub_norm_le η ζ
      rw [norm_sub_rev] at this
      linarith [norm_nonneg η]
    have h3 : (1 + ‖η‖) / 2 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg η]
    calc ‖fderiv ℝ F ζ‖ ≤ A * (1 + ‖ζ‖) ^ (-(N : ℝ)) := hD ζ
      _ ≤ A * (2 ^ N * (1 + ‖η‖) ^ (-(N : ℝ))) :=
          mul_le_mul_of_nonneg_left (scrn_rpow_half N (norm_nonneg η) h3) hA
      _ = _ := by ring
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := F)
    (s := Metric.closedBall η (‖η‖ / 2)) (fun x _ => hF x) hs (convex_closedBall _ _)
    (x := η) (y := ξ) (Metric.mem_closedBall_self (by positivity))
    (by simpa [dist_eq_norm] using hξη)
  exact this


lemma scrn_decay_div {y : ℝ} (hy : 0 < y) {N L : ℝ} (hN : L + 1 ≤ N) :
    (1 + y) ^ (-N) ≤ (1 + y) ^ (-L) / y := by
  have h1 : 1 ≤ 1 + y := by linarith
  have h0 : 0 < 1 + y := by linarith
  have e : (1 + y) ^ (-N) = (1 + y) ^ (-L) * (1 + y) ^ (-(N - L)) := by
    rw [← Real.rpow_add h0]; congr 1; ring
  have h2 : (1 + y) ^ (-(N - L)) ≤ (1 + y) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have h3 : (1 + y) ^ (-(1 : ℝ)) ≤ 1 / y := by
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ hy (by linarith)
  have h4 : 0 ≤ (1 + y) ^ (-L) := Real.rpow_nonneg h0.le _
  rw [e, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (h2.trans h3) h4

lemma scrn_decay_mono {y : ℝ} (hy : 0 ≤ y) {N L : ℝ} (hN : L ≤ N) : (1 + y) ^ (-N) ≤ (1 + y) ^ (-L) :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

lemma scrn_rpow_mul_self {x : ℝ} (hx : 0 < x) (N : ℕ) :
    x ^ (-(N : ℝ)) * x ^ (-(N : ℝ)) = x ^ (-((2 * N : ℕ) : ℝ)) := by
  rw [← Real.rpow_add hx]; congr 1; push_cast; ring

/-- Local Lipschitz bound for the radial kernel in `ξ`. -/
lemma scrnKab_lip {c q b : ℝ} (hc : 0 < c) (hb : 0 < b) (hq : 0 ≤ q) {τ₁ τ₂ : ℝ} (h1 : 0 ≤ τ₁)
    (h2 : 0 ≤ τ₂) {ξ η : Euc d} (hη : 0 < ‖η‖) (hξη : ‖ξ - η‖ ≤ ‖η‖ / 2) :
    |scrnk c q b τ₁ τ₂ (2 * Real.pi * ‖ξ‖) - scrnk c q b τ₁ τ₂ (2 * Real.pi * ‖η‖)| ≤
      2 * (q / 4 + (2 + |2 - q|)) * ‖ξ - η‖ / ‖η‖ := by
  set B := q / 4 + (2 + |2 - q|) with hB
  have hB0 : 0 ≤ B := by positivity
  have hpi := Real.pi_pos
  have hdiff : |‖ξ‖ - ‖η‖| ≤ ‖ξ - η‖ := abs_norm_sub_norm_le ξ η
  have hξn : ‖η‖ / 2 ≤ ‖ξ‖ := by
    have := norm_sub_norm_le η ξ
    rw [norm_sub_rev] at this
    linarith
  have hρη : 0 < 2 * Real.pi * ‖η‖ := by positivity
  have hρξ : 0 < 2 * Real.pi * ‖ξ‖ := by
    have : 0 < ‖ξ‖ := by linarith
    positivity
  have hrd : |2 * Real.pi * ‖ξ‖ - 2 * Real.pi * ‖η‖| ≤ 2 * Real.pi * ‖ξ - η‖ := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left hdiff (by positivity)
  rcases le_total (2 * Real.pi * ‖ξ‖) (2 * Real.pi * ‖η‖) with hle | hle
  · have h := scrnk_lip hc hb hq h1 h2 hρξ hle
    rw [abs_sub_comm]
    refine h.trans ?_
    have hmin : Real.pi * ‖η‖ ≤ 2 * Real.pi * ‖ξ‖ := by nlinarith
    have hm0 : 0 < Real.pi * ‖η‖ := by positivity
    calc B * |2 * Real.pi * ‖η‖ - 2 * Real.pi * ‖ξ‖| / (2 * Real.pi * ‖ξ‖)
        ≤ B * (2 * Real.pi * ‖ξ - η‖) / (Real.pi * ‖η‖) := by
          rw [abs_sub_comm]
          have : B * |2 * Real.pi * ‖ξ‖ - 2 * Real.pi * ‖η‖| ≤ B * (2 * Real.pi * ‖ξ - η‖) :=
            mul_le_mul_of_nonneg_left hrd hB0
          calc B * |2 * Real.pi * ‖ξ‖ - 2 * Real.pi * ‖η‖| / (2 * Real.pi * ‖ξ‖)
              ≤ B * (2 * Real.pi * ‖ξ - η‖) / (2 * Real.pi * ‖ξ‖) :=
                div_le_div_of_nonneg_right this hρξ.le
            _ ≤ B * (2 * Real.pi * ‖ξ - η‖) / (Real.pi * ‖η‖) :=
                div_le_div_of_nonneg_left (by positivity) hm0 hmin
      _ = 2 * B * ‖ξ - η‖ / ‖η‖ := by field_simp
  · have h := scrnk_lip hc hb hq h1 h2 hρη hle
    refine h.trans ?_
    calc B * |2 * Real.pi * ‖ξ‖ - 2 * Real.pi * ‖η‖| / (2 * Real.pi * ‖η‖)
        ≤ B * (2 * Real.pi * ‖ξ - η‖) / (2 * Real.pi * ‖η‖) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrd hB0) hρη.le
      _ = B * ‖ξ - η‖ / ‖η‖ := by field_simp
      _ ≤ 2 * B * ‖ξ - η‖ / ‖η‖ := by
          have : 0 ≤ B * ‖ξ - η‖ / ‖η‖ := by positivity
          have e : 2 * B * ‖ξ - η‖ / ‖η‖ = 2 * (B * ‖ξ - η‖ / ‖η‖) := by ring
          rw [e]; linarith


/-- Hypotheses (H1), (H2) of `scrn_riemann` for the covariance integrand, uniformly in `b > 0` and the times. -/
theorem scrn_G_hyp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {p : ℕ}
    (φ : Fin p → Euc d → ℝ) (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (b : ℝ), 0 < b → ∀ (t : Fin p → ℝ), (∀ a, 0 ≤ t a) → ∀ a c : Fin p,
      Measurable (scrnGab d s b t φ a c) ∧
      (∀ ξ, ‖scrnGab d s b t φ a c ξ‖ ≤ A * (1 + ‖ξ‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ ξ, ‖𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ)‖ ≤
        A * (1 + ‖ξ‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ ξ η : Euc d, 0 < ‖η‖ → ‖ξ - η‖ ≤ ‖η‖ / 2 →
        ‖scrnGab d s b t φ a c ξ - scrnGab d s b t φ a c η‖ ≤
          A * ‖ξ - η‖ * (1 + ‖η‖) ^ (-((d : ℝ) + 1)) / ‖η‖) := by
  classical
  set Nn : ℕ := d + 2 with hNn
  have hc : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  set q : ℝ := (d : ℝ) - s with hq
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  set B : ℝ := q / 4 + (2 + |2 - q|) with hB
  have hB0 : 0 ≤ B := by positivity
  have hex : ∀ a : Fin p, ∃ Aa : ℝ, 0 ≤ Aa ∧ ∀ ξ : Euc d,
      ‖𝓕 (scrnPhiC (φ a)) ξ‖ ≤ Aa * (1 + ‖ξ‖) ^ (-(Nn : ℝ)) ∧
      ‖fderiv ℝ (𝓕 (scrnPhiC (φ a))) ξ‖ ≤ Aa * (1 + ‖ξ‖) ^ (-(Nn : ℝ)) :=
    fun a => scrn_fourier_bound (hφ a).1 (hφ a).2 Nn
  choose Aa hAa0 hAa using hex
  set A0 : ℝ := ∑ a, Aa a with hA0
  have hA00 : 0 ≤ A0 := Finset.sum_nonneg fun a _ => hAa0 a
  have hAle : ∀ a, Aa a ≤ A0 := fun a =>
    Finset.single_le_sum (f := Aa) (fun a _ => hAa0 a) (Finset.mem_univ a)
  have hF0 : ∀ a ξ, ‖𝓕 (scrnPhiC (φ a)) ξ‖ ≤ A0 * (1 + ‖ξ‖) ^ (-(Nn : ℝ)) := fun a ξ =>
    ((hAa a ξ).1).trans (mul_le_mul_of_nonneg_right (hAle a) (Real.rpow_nonneg (by positivity) _))
  have hF1 : ∀ a ξ, ‖fderiv ℝ (𝓕 (scrnPhiC (φ a))) ξ‖ ≤ A0 * (1 + ‖ξ‖) ^ (-(Nn : ℝ)) := fun a ξ =>
    ((hAa a ξ).2).trans (mul_le_mul_of_nonneg_right (hAle a) (Real.rpow_nonneg (by positivity) _))
  have hFd : ∀ a, Differentiable ℝ (𝓕 (scrnPhiC (φ a))) := fun a =>
    scrn_fourier_diff (hφ a).1 (hφ a).2
  set L : ℝ := (d : ℝ) + 1 with hL
  have h2N : L + 1 ≤ ((2 * Nn : ℕ) : ℝ) := by
    simp only [hL, hNn]; push_cast; linarith
  refine ⟨A0 ^ 2 * (2 * 4 ^ Nn + 2 * B), by positivity, fun b hb t ht a c => ?_⟩
  have hK0 : ∀ ξ : Euc d, 0 ≤ scrnKab d s b t a c ξ ∧ scrnKab d s b t a c ξ ≤ 1 := by
    intro ξ
    unfold scrnKab
    have hρ : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
    exact ⟨scrnk_nonneg' hc hb hρ, scrnk_le_one' hc hb hρ (abs_nonneg _) (add_nonneg (ht a) (ht c))⟩
  have hFm : ∀ a, Continuous (𝓕 (scrnPhiC (φ a))) := fun a => (hFd a).continuous
  have hmeas : Measurable (scrnGab d s b t φ a c) := by
    unfold scrnGab scrnKab
    refine ((hFm a).measurable.mul (Complex.continuous_conj.measurable.comp (hFm c).measurable)).mul ?_
    exact Complex.measurable_ofReal.comp ((measurable_scrnk _ _ _ _ _).comp
      (measurable_const.mul measurable_norm))
  have hP : ∀ ξ : Euc d, ‖𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ)‖ ≤
      A0 ^ 2 * (1 + ‖ξ‖) ^ (-((2 * Nn : ℕ) : ℝ)) := by
    intro ξ
    rw [norm_mul, Complex.norm_conj]
    calc ‖𝓕 (scrnPhiC (φ a)) ξ‖ * ‖𝓕 (scrnPhiC (φ c)) ξ‖
        ≤ (A0 * (1 + ‖ξ‖) ^ (-(Nn : ℝ))) * (A0 * (1 + ‖ξ‖) ^ (-(Nn : ℝ))) :=
          mul_le_mul (hF0 a ξ) (hF0 c ξ) (norm_nonneg _) (by
            have := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖ξ‖) (-(Nn : ℝ))
            positivity)
      _ = A0 ^ 2 * (1 + ‖ξ‖) ^ (-((2 * Nn : ℕ) : ℝ)) := by
          rw [← scrn_rpow_mul_self (by positivity : (0:ℝ) < 1 + ‖ξ‖) Nn]; ring
  have hAge : A0 ^ 2 ≤ A0 ^ 2 * (2 * 4 ^ Nn + 2 * B) := by
    have h4 : (1:ℝ) ≤ 4 ^ Nn := one_le_pow₀ (by norm_num)
    nlinarith [sq_nonneg A0]
  refine ⟨hmeas, fun ξ => ?_, fun ξ => ?_, fun ξ η hη hξη => ?_⟩
  · unfold scrnGab
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 ξ).1]
    calc ‖𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ)‖ * scrnKab d s b t a c ξ
        ≤ ‖𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hK0 ξ).2 (norm_nonneg _)
      _ ≤ A0 ^ 2 * (1 + ‖ξ‖) ^ (-((2 * Nn : ℕ) : ℝ)) := by rw [mul_one]; exact hP ξ
      _ ≤ A0 ^ 2 * (1 + ‖ξ‖) ^ (-L) :=
          mul_le_mul_of_nonneg_left (scrn_decay_mono (norm_nonneg ξ) (by linarith)) (sq_nonneg A0)
      _ ≤ (A0 ^ 2 * (2 * 4 ^ Nn + 2 * B)) * (1 + ‖ξ‖) ^ (-L) := by
          have : (0:ℝ) ≤ (1 + ‖ξ‖) ^ (-L) := Real.rpow_nonneg (by positivity) _
          have h4 : (1:ℝ) ≤ 4 ^ Nn := one_le_pow₀ (by norm_num)
          nlinarith [mul_nonneg (sq_nonneg A0) this]
  · calc ‖𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ)‖
        ≤ A0 ^ 2 * (1 + ‖ξ‖) ^ (-((2 * Nn : ℕ) : ℝ)) := hP ξ
      _ ≤ A0 ^ 2 * (1 + ‖ξ‖) ^ (-L) :=
          mul_le_mul_of_nonneg_left (scrn_decay_mono (norm_nonneg ξ) (by linarith)) (sq_nonneg A0)
      _ ≤ (A0 ^ 2 * (2 * 4 ^ Nn + 2 * B)) * (1 + ‖ξ‖) ^ (-L) :=
          mul_le_mul_of_nonneg_right hAge (Real.rpow_nonneg (by positivity) _)
  · set δ : ℝ := ‖ξ - η‖ with hδ
    have hδ0 : 0 ≤ δ := norm_nonneg _
    set u : ℝ := (1 + ‖η‖) ^ (-(Nn : ℝ)) with hu
    have hu0 : 0 ≤ u := Real.rpow_nonneg (by positivity) _
    have hξn : ‖η‖ / 2 ≤ ‖ξ‖ := by
      have := norm_sub_norm_le η ξ
      rw [norm_sub_rev] at this
      linarith
    have hhalf : (1 + ‖η‖) / 2 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg η]
    have hFlip : ∀ a, ‖𝓕 (scrnPhiC (φ a)) ξ - 𝓕 (scrnPhiC (φ a)) η‖ ≤ A0 * 2 ^ Nn * u * δ := fun a =>
      scrn_F_lip (hFd a) (hF1 a) hA00 hξη
    have hFξ : ∀ a, ‖𝓕 (scrnPhiC (φ a)) ξ‖ ≤ A0 * (2 ^ Nn * u) := fun a =>
      (hF0 a ξ).trans (mul_le_mul_of_nonneg_left (scrn_rpow_half Nn (norm_nonneg η) hhalf) hA00)
    have hFη : ∀ a, ‖𝓕 (scrnPhiC (φ a)) η‖ ≤ A0 * u := fun a => hF0 a η
    set Pξ : ℂ := 𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ) with hPξ
    set Pη : ℂ := 𝓕 (scrnPhiC (φ a)) η * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) η) with hPη
    have hPdiff : ‖Pξ - Pη‖ ≤ 2 * A0 ^ 2 * 4 ^ Nn * (u * u) * δ := by
      have e : Pξ - Pη = (𝓕 (scrnPhiC (φ a)) ξ - 𝓕 (scrnPhiC (φ a)) η) *
          (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ) +
          𝓕 (scrnPhiC (φ a)) η * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ - 𝓕 (scrnPhiC (φ c)) η) := by
        simp only [hPξ, hPη, map_sub]; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      have h1 : ‖𝓕 (scrnPhiC (φ a)) ξ - 𝓕 (scrnPhiC (φ a)) η‖ * ‖𝓕 (scrnPhiC (φ c)) ξ‖ ≤
          (A0 * 2 ^ Nn * u * δ) * (A0 * (2 ^ Nn * u)) :=
        mul_le_mul (hFlip a) (hFξ c) (norm_nonneg _) (by positivity)
      have h2 : ‖𝓕 (scrnPhiC (φ a)) η‖ * ‖𝓕 (scrnPhiC (φ c)) ξ - 𝓕 (scrnPhiC (φ c)) η‖ ≤
          (A0 * u) * (A0 * 2 ^ Nn * u * δ) :=
        mul_le_mul (hFη a) (hFlip c) (norm_nonneg _) (by positivity)
      have h3 : (2 : ℝ) ^ Nn ≤ 4 ^ Nn := pow_le_pow_left₀ (by norm_num) (by norm_num) Nn
      have h4 : (2 : ℝ) ^ Nn * 2 ^ Nn = 4 ^ Nn := by rw [← mul_pow]; norm_num
      have h5 : 0 ≤ A0 ^ 2 * (u * u) * δ := by positivity
      have h6 : (0 : ℝ) ≤ 2 ^ Nn := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h3 h5]
    have hKdiff : |scrnKab d s b t a c ξ - scrnKab d s b t a c η| ≤ 2 * B * δ / ‖η‖ := by
      unfold scrnKab
      exact scrnKab_lip hc hb hq0 (abs_nonneg _) (add_nonneg (ht a) (ht c)) hη hξη
    have hPη' : ‖Pη‖ ≤ A0 ^ 2 * (u * u) := by
      simp only [hPη]
      rw [norm_mul, Complex.norm_conj]
      calc ‖𝓕 (scrnPhiC (φ a)) η‖ * ‖𝓕 (scrnPhiC (φ c)) η‖ ≤ (A0 * u) * (A0 * u) :=
            mul_le_mul (hFη a) (hFη c) (norm_nonneg _) (by positivity)
        _ = A0 ^ 2 * (u * u) := by ring
    have hGe : scrnGab d s b t φ a c ξ - scrnGab d s b t φ a c η =
        (Pξ - Pη) * ((scrnKab d s b t a c ξ : ℝ) : ℂ) +
          Pη * (((scrnKab d s b t a c ξ - scrnKab d s b t a c η : ℝ)) : ℂ) := by
      unfold scrnGab
      simp only [hPξ, hPη]
      push_cast; ring
    rw [hGe]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hK0 ξ).1]
    have hKξ : scrnKab d s b t a c ξ ≤ 1 := (hK0 ξ).2
    have t1 : ‖Pξ - Pη‖ * scrnKab d s b t a c ξ ≤ 2 * A0 ^ 2 * 4 ^ Nn * (u * u) * δ := by
      calc _ ≤ ‖Pξ - Pη‖ * 1 := mul_le_mul_of_nonneg_left hKξ (norm_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hPdiff
    have t2 : ‖Pη‖ * |scrnKab d s b t a c ξ - scrnKab d s b t a c η| ≤
        A0 ^ 2 * (u * u) * (2 * B * δ / ‖η‖) :=
      mul_le_mul hPη' hKdiff (abs_nonneg _) (by positivity)
    have huu : u * u = (1 + ‖η‖) ^ (-((2 * Nn : ℕ) : ℝ)) := by
      rw [hu]; exact scrn_rpow_mul_self (by positivity) Nn
    have hdd := scrn_decay_div hη (N := ((2 * Nn : ℕ) : ℝ)) (L := L) h2N
    have hdm := scrn_decay_mono (norm_nonneg η) (N := ((2 * Nn : ℕ) : ℝ)) (L := L) (by linarith)
    rw [← huu] at hdd hdm
    have hpos : 0 < ‖η‖ := hη
    calc ‖Pξ - Pη‖ * scrnKab d s b t a c ξ +
          ‖Pη‖ * |scrnKab d s b t a c ξ - scrnKab d s b t a c η|
        ≤ 2 * A0 ^ 2 * 4 ^ Nn * (u * u) * δ + A0 ^ 2 * (u * u) * (2 * B * δ / ‖η‖) := add_le_add t1 t2
      _ ≤ 2 * A0 ^ 2 * 4 ^ Nn * ((1 + ‖η‖) ^ (-L) / ‖η‖) * δ +
          A0 ^ 2 * (1 + ‖η‖) ^ (-L) * (2 * B * δ / ‖η‖) := by
          have a1 : 2 * A0 ^ 2 * 4 ^ Nn * (u * u) * δ ≤
              2 * A0 ^ 2 * 4 ^ Nn * ((1 + ‖η‖) ^ (-L) / ‖η‖) * δ := by gcongr
          have a2 : A0 ^ 2 * (u * u) * (2 * B * δ / ‖η‖) ≤
              A0 ^ 2 * (1 + ‖η‖) ^ (-L) * (2 * B * δ / ‖η‖) := by
            have : 0 ≤ 2 * B * δ / ‖η‖ := by positivity
            gcongr
          linarith
      _ = (A0 ^ 2 * (2 * 4 ^ Nn + 2 * B)) * ‖ξ - η‖ * (1 + ‖η‖) ^ (-L) / ‖η‖ := by
          rw [hδ]; field_simp


/-- Comparison of the lattice-sum covariance with the limiting one: `≤ C (ℓ + |b_N - b|)`, uniformly in
the times. -/
theorem scrn_cov_compare (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {p : ℕ}
    (φ : Fin p → Euc d → ℝ) (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a))
    {bm : ℝ} (hbm : 0 < bm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : Fin p → ℝ), (∀ a, 0 ≤ t a) → ∀ (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 →
      ∀ bN b : ℝ, bm ≤ bN → bm ≤ b → ∀ a c : Fin p,
        |(∑' k : Lattice d, if k = 0 then (0 : ℂ) else
            ((ℓ ^ d : ℝ) : ℂ) * scrnGab d s bN t φ a c (ℓ • Lattice.toEuc k)).re -
          mesoCovMatrix d s b t φ a c| ≤ C * (ℓ + |bN - b|) := by
  have hd0 : 0 < d := by omega
  obtain ⟨A, hA0, hG⟩ := scrn_G_hyp hd hs0 hsd φ hφ
  obtain ⟨CR, hCR0, hR⟩ := scrn_riemann hd (L := (d : ℝ) + 1) (by linarith)
  have hLint : Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ (-((d : ℝ) + 1))) := by
    refine integrable_one_add_norm (E := Euc d) ?_
    simp
  set J : ℝ := ∫ ξ : Euc d, (1 + ‖ξ‖) ^ (-((d : ℝ) + 1)) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun ξ => Real.rpow_nonneg (by positivity) _
  refine ⟨CR * A + 2 / bm * (A * J), by positivity, fun t ht ℓ hℓ hℓ1 bN b hbN hb a c => ?_⟩
  obtain ⟨hmN, h1N, hPb, h2N⟩ := hG bN (hbm.trans_le hbN) t ht a c
  obtain ⟨hmb, h1b, -, h2b⟩ := hG b (hbm.trans_le hb) t ht a c
  rw [meso_entry_eq]
  set S : ℂ := ∑' k : Lattice d, if k = 0 then (0 : ℂ) else
    ((ℓ ^ d : ℝ) : ℂ) * scrnGab d s bN t φ a c (ℓ • Lattice.toEuc k) with hS
  have hRie := hR A hA0 _ hmN h1N h2N ℓ hℓ hℓ1
  have hint : ∀ b' : ℝ, 0 < b' → Integrable (scrnGab d s b' t φ a c) := by
    intro b' hb'
    obtain ⟨hm', h1', -, -⟩ := hG b' hb' t ht a c
    exact Integrable.mono' (hLint.const_mul A) hm'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => h1' ξ)
  have hdiff : ‖(∫ ξ : Euc d, scrnGab d s bN t φ a c ξ) - ∫ ξ : Euc d, scrnGab d s b t φ a c ξ‖ ≤
      2 / bm * (A * J) * |bN - b| := by
    rw [← integral_sub (hint bN (hbm.trans_le hbN)) (hint b (hbm.trans_le hb))]
    have hbd : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ‖scrnGab d s bN t φ a c ξ - scrnGab d s b t φ a c ξ‖ ≤
        (2 / bm * |bN - b|) * (A * (1 + ‖ξ‖) ^ (-((d : ℝ) + 1))) := by
      haveI : Nontrivial (Euc d) := by
        haveI : NeZero d := ⟨by omega⟩
        infer_instance
      have hne : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ξ ≠ 0 := by
        rw [ae_iff]; simp
      filter_upwards [hne] with ξ hξ
      have hξn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have hρ : 0 < 2 * Real.pi * ‖ξ‖ := by positivity
      have hcr : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
      have hk : |scrnKab d s bN t a c ξ - scrnKab d s b t a c ξ| ≤ 2 / bm * |bN - b| := by
        unfold scrnKab
        rcases le_total bN b with hle | hle
        · have := scrnk_b_lip (q := (d : ℝ) - s) hcr hρ (τ₁ := |t a - t c|) (τ₂ := t a + t c)
            (abs_nonneg _) (add_nonneg (ht a) (ht c)) (hbm.trans_le hbN) hle
          rw [abs_sub_comm]
          refine this.trans ?_
          rw [abs_sub_comm]
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (by norm_num) hbm hbN) (abs_nonneg _)
        · have := scrnk_b_lip (q := (d : ℝ) - s) hcr hρ (τ₁ := |t a - t c|) (τ₂ := t a + t c)
            (abs_nonneg _) (add_nonneg (ht a) (ht c)) (hbm.trans_le hb) hle
          refine this.trans ?_
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (by norm_num) hbm hb) (abs_nonneg _)
      unfold scrnGab
      rw [← mul_sub, norm_mul]
      have : ((scrnKab d s bN t a c ξ : ℝ) : ℂ) - ((scrnKab d s b t a c ξ : ℝ) : ℂ) =
          (((scrnKab d s bN t a c ξ - scrnKab d s b t a c ξ : ℝ)) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
      calc _ ≤ ‖𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ)‖ *
            (2 / bm * |bN - b|) := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
        _ ≤ (A * (1 + ‖ξ‖) ^ (-((d : ℝ) + 1))) * (2 / bm * |bN - b|) :=
            mul_le_mul_of_nonneg_right (hPb ξ) (by positivity)
        _ = _ := by ring
    refine (norm_integral_le_of_norm_le ((hLint.const_mul A).const_mul (2 / bm * |bN - b|)) hbd).trans ?_
    rw [integral_const_mul, integral_const_mul]
    have : ∫ ξ : Euc d, (1 + ‖ξ‖) ^ (-((d : ℝ) + 1)) = J := rfl
    rw [this]
    nlinarith [abs_nonneg (bN - b)]
  have hre : |S.re - (∫ ξ : Euc d, scrnGab d s b t φ a c ξ).re| ≤
      ‖S - ∫ ξ : Euc d, scrnGab d s b t φ a c ξ‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  calc |S.re - (∫ ξ : Euc d, scrnGab d s b t φ a c ξ).re|
      ≤ ‖S - ∫ ξ : Euc d, scrnGab d s b t φ a c ξ‖ := hre
    _ ≤ ‖S - ∫ ξ : Euc d, scrnGab d s bN t φ a c ξ‖ +
        ‖(∫ ξ : Euc d, scrnGab d s bN t φ a c ξ) - ∫ ξ : Euc d, scrnGab d s b t φ a c ξ‖ := by
        have : S - ∫ ξ : Euc d, scrnGab d s b t φ a c ξ =
            (S - ∫ ξ : Euc d, scrnGab d s bN t φ a c ξ) +
              ((∫ ξ : Euc d, scrnGab d s bN t φ a c ξ) - ∫ ξ : Euc d, scrnGab d s b t φ a c ξ) := by ring
        rw [this]; exact norm_add_le _ _
    _ ≤ CR * A * ℓ + 2 / bm * (A * J) * |bN - b| := add_le_add hRie hdiff
    _ ≤ (CR * A + 2 / bm * (A * J)) * (ℓ + |bN - b|) := by
        have h1 : 0 ≤ CR * A := by positivity
        have h2 : 0 ≤ 2 / bm * (A * J) := by positivity
        nlinarith [abs_nonneg (bN - b)]

end HRS
