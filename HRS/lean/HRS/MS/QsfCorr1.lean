import HRS.MS.QsfIbp6
import HRS.Whole.MovtrAux5

/-!
# S4.5 packet B1, part 1: the one-body integration by parts against the smoothed kernel

`s45_obi_eps`: for `ρ ∈ C¹` with Gaussian bounds on `ρ, ∇ρ`, a `C¹` field `v` with bounded `v, Dv`, and `ε ∈ (0,1]`,
`∫ ρ(y) ⟨v(x) - v(y), ∇g_ε(x-y)⟩ dy = ∫ g_ε(x-y) (⟨∇ρ(y), v(x)-v(y)⟩ - ρ(y) div v(y)) dy`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- Integrability of `k(x-y) h(y)` for `|k| ≤ K₁ (2|z|^{-sp} + |z| + 1)` and `|h| ≤ K₂ e^{-c|y|²}`. -/
theorem s45_LI (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c)
    {k h : Euc d → ℝ} (hk : AEStronglyMeasurable k volume) (hh : Continuous h) {K1 K2 : ℝ}
    (hK1 : 0 ≤ K1) (hkB : ∀ z, z ≠ 0 → |k z| ≤ K1 * (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1))
    (hK2 : 0 ≤ K2) (hbd : ∀ y, |h y| ≤ K2 * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    Integrable (fun y => k (x - y) * h y) := by
  have h1 := movtr_integrable_of_gauss_bound (c := c) hc (k := k)
    (B := fun z => K1 * (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1)) hk
    (by filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz; exact hkB z hz)
    (by
      have := (movtr_majorant_integrable hd hs0 hsd (c := c / 2) (by positivity)).const_mul K1
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [mul_assoc])
    hK2 hh (x' := x) (R := ‖x‖) le_rfl hbd
  have h2 := h1.comp_sub_left x
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp

theorem s45_hasFDerivAt_G (s : ℝ) {ε : ℝ} (hε : ε ≠ 0) (x y : Euc d) :
    HasFDerivAt (fun y => movtr_gEps d s ε (x - y))
      ((innerSL ℝ (s45_F s ε (x - y))).comp (-(ContinuousLinearMap.id ℝ (Euc d)))) y :=
  (s45_hasFDerivAt_gEps s hε (x - y)).comp y ((hasFDerivAt_id y).const_sub x)

theorem s45_fderiv_G1 (s : ℝ) {ε : ℝ} (hε : ε ≠ 0) (x y e : Euc d) :
    fderiv ℝ (fun y => movtr_gEps d s ε (x - y)) y e = -⟪s45_F s ε (x - y), e⟫ := by
  rw [(s45_hasFDerivAt_G s hε x y).fderiv]
  simp

/-- The vector field `W_x(y) = v(x) - v(y)` and the functions `f_b = ρ W_b`. -/
theorem s45_hasFDerivAt_f {ρ : Euc d → ℝ} (hρ : Differentiable ℝ ρ) {v : Euc d → Euc d}
    (hv : Differentiable ℝ v) (x y : Euc d) (b : Fin d) :
    HasFDerivAt (fun y => ρ y * (v x b - v y b))
      (ρ y • (-((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).comp (fderiv ℝ v y))) +
        (v x b - v y b) • fderiv ℝ ρ y) y := by
  have h1 : HasFDerivAt (fun y => v x b - v y b)
      (-((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).comp (fderiv ℝ v y))) y := by
    have := (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).hasFDerivAt.comp y (hv y).hasFDerivAt
    exact (this.const_sub (v x b))
  exact (hρ y).hasFDerivAt.mul h1

theorem s45_inner_eq_sum (u w : Euc d) : ⟪u, w⟫ = ∑ b : Fin d, u b * w b := by
  simp [PiLp.inner_apply, mul_comm]

/-- **One-body integration by parts against the smoothed kernel.** -/
theorem s45_obi_eps (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) {v : Euc d → Euc d}
    (hv : ContDiff ℝ 1 v) {Bv Dv : ℝ} (hBv : ∀ x, ‖v x‖ ≤ Bv) (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv)
    (x : Euc d) :
    ∫ y, ρ y * ⟪v x - v y, s45_F s ε (x - y)⟫ =
      ∫ y, movtr_gEps d s ε (x - y) * (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y) := by
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  have hDv0 : 0 ≤ Dv := (norm_nonneg _).trans (hDv 0)
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hε0 : ε ≠ 0 := hε.ne'
  have hσ := s45_sigma_nonneg hs0
  set κ : ℝ := movtr_sigma s * ε ^ (-s - 1) with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg hσ (Real.rpow_nonneg hε.le _)
  set G : Euc d → ℝ := fun y => movtr_gEps d s ε (x - y) with hG
  have hGd : Differentiable ℝ G := fun y => (s45_hasFDerivAt_G s hε0 x y).differentiableAt
  have hGm : AEStronglyMeasurable (fun z => movtr_gEps d s ε z) volume :=
    (movtr_gEps_measurable s ε).aestronglyMeasurable
  have hGB : ∀ z : Euc d, z ≠ 0 → |movtr_gEps d s ε z| ≤ 1 * (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) :=
    fun z hz => by rw [one_mul]; exact movtr_gEps_abs_le hs0 hε.le hε1 hz
  have hW : ∀ y b, |v x b - v y b| ≤ 2 * Bv := by
    intro y b
    calc |v x b - v y b| ≤ |v x b| + |v y b| := abs_sub _ _
      _ ≤ Bv + Bv := add_le_add ((s45_abs_coord_le _ _).trans (hBv _))
          ((s45_abs_coord_le _ _).trans (hBv _))
      _ = 2 * Bv := by ring
  have hFG : ∀ (y : Euc d) (b : Fin d), |fderiv ℝ G y (EuclideanSpace.single b 1)| ≤ κ := by
    intro y b
    rw [hG, s45_fderiv_G1 s hε0, abs_neg]
    calc |⟪s45_F s ε (x - y), EuclideanSpace.single b (1 : ℝ)⟫|
        ≤ ‖s45_F s ε (x - y)‖ * ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ := abs_real_inner_le_norm _ _
      _ ≤ κ * 1 := mul_le_mul (s45_F_norm_le hs0 hε _) (movtr_norm_single b) (norm_nonneg _) hκ0
      _ = κ := mul_one _
  have hFGc : ∀ b : Fin d, Continuous fun y => fderiv ℝ G y (EuclideanSpace.single b 1) := by
    intro b
    have : (fun y => fderiv ℝ G y (EuclideanSpace.single b 1)) =
        fun y => -⟪s45_F s ε (x - y), EuclideanSpace.single b (1 : ℝ)⟫ := by
      funext y; rw [hG, s45_fderiv_G1 s hε0]
    rw [this]
    exact ((s45_continuous_F hε0).comp (continuous_const.sub continuous_id)).inner continuous_const |>.neg
  -- per-coordinate identity with integrability
  have key : ∀ b : Fin d,
      Integrable (fun y => ρ y * (v x b - v y b) * fderiv ℝ G y (EuclideanSpace.single b 1)) ∧
      Integrable (fun y => fderiv ℝ (fun y => ρ y * (v x b - v y b)) y (EuclideanSpace.single b 1) * G y) ∧
      ∫ y, ρ y * (v x b - v y b) * fderiv ℝ G y (EuclideanSpace.single b 1) =
        -∫ y, fderiv ℝ (fun y => ρ y * (v x b - v y b)) y (EuclideanSpace.single b 1) * G y := by
    intro b
    have hfd : Differentiable ℝ (fun y => ρ y * (v x b - v y b)) := fun y =>
      (s45_hasFDerivAt_f hρd hvd x y b).differentiableAt
    have hfc : Continuous (fun y => ρ y * (v x b - v y b)) := hfd.continuous
    have hfbd : ∀ y, |ρ y * (v x b - v y b)| ≤ (C * (2 * Bv)) * Real.exp (-c * ‖y‖ ^ 2) := by
      intro y
      rw [abs_mul]
      calc |ρ y| * |v x b - v y b| ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (2 * Bv) :=
            mul_le_mul (h0 y) (hW y b) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hdfbd : ∀ y, |fderiv ℝ (fun y => ρ y * (v x b - v y b)) y (EuclideanSpace.single b 1)| ≤
        (C * 2 * Bv + C * Dv) * Real.exp (-c * ‖y‖ ^ 2) := by
      intro y
      rw [(s45_hasFDerivAt_f hρd hvd x y b).fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
      have hn : ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ ≤ 1 := movtr_norm_single b
      have e1 : |fderiv ℝ ρ y (EuclideanSpace.single b 1)| ≤ C * Real.exp (-c * ‖y‖ ^ 2) := by
        calc |fderiv ℝ ρ y (EuclideanSpace.single b 1)| = ‖fderiv ℝ ρ y (EuclideanSpace.single b 1)‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ ρ y‖ * ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖fderiv ℝ ρ y‖ * 1 := by gcongr
          _ ≤ C * Real.exp (-c * ‖y‖ ^ 2) := by rw [mul_one]; exact h1 y
      have e2 : |(fderiv ℝ v y (EuclideanSpace.single b 1)) b| ≤ Dv := by
        refine (s45_abs_coord_le _ _).trans ?_
        calc ‖fderiv ℝ v y (EuclideanSpace.single b (1 : ℝ))‖
            ≤ ‖fderiv ℝ v y‖ * ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ Dv * 1 := mul_le_mul (hDv y) hn (norm_nonneg _) hDv0
          _ = Dv := mul_one _
      calc _ ≤ |ρ y * -(fderiv ℝ v y (EuclideanSpace.single b 1)) b| +
            |(v x b - v y b) * fderiv ℝ ρ y (EuclideanSpace.single b 1)| := abs_add_le _ _
        _ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * Dv + (2 * Bv) * (C * Real.exp (-c * ‖y‖ ^ 2)) := by
            refine add_le_add ?_ ?_
            · rw [abs_mul, abs_neg]
              exact mul_le_mul (h0 y) e2 (abs_nonneg _) (by positivity)
            · rw [abs_mul]
              exact mul_le_mul (hW y b) e1 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hfC1 : ContDiff ℝ 1 (fun y => ρ y * (v x b - v y b)) := by
      refine hρ.mul (contDiff_const.sub ?_)
      exact (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).contDiff.comp hv
    have hdfc : Continuous (fun y => fderiv ℝ (fun y => ρ y * (v x b - v y b)) y (EuclideanSpace.single b 1)) :=
      (hfC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hI1 : Integrable (fun y => fderiv ℝ (fun y => ρ y * (v x b - v y b)) y
        (EuclideanSpace.single b 1) * G y) := by
      have := s45_LI hd hs0 hsd hc (k := fun z => movtr_gEps d s ε z) (h := fun y => fderiv ℝ
        (fun y => ρ y * (v x b - v y b)) y (EuclideanSpace.single b 1)) hGm hdfc zero_le_one hGB
        (by positivity) hdfbd x
      exact this.congr (Filter.Eventually.of_forall fun y => by simp [hG, mul_comm])
    have hI3 : Integrable (fun y => ρ y * (v x b - v y b) * G y) := by
      have := s45_LI hd hs0 hsd hc (k := fun z => movtr_gEps d s ε z) (h := fun y => ρ y * (v x b - v y b))
        hGm hfc zero_le_one hGB (by positivity) hfbd x
      exact this.congr (Filter.Eventually.of_forall fun y => by simp [hG, mul_comm])
    have hfint : Integrable (fun y => ρ y * (v x b - v y b)) := by
      have := s45_LI hd hs0 hsd hc (k := fun _ => 1) (h := fun y => ρ y * (v x b - v y b))
        aestronglyMeasurable_const hfc zero_le_one
        (fun z _ => by
          simp only [abs_one, one_mul]
          have : (0 : ℝ) ≤ 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ := by
            have := Real.rpow_nonneg (norm_nonneg z) (-movtr_sp s); positivity
          linarith)
        (by positivity) hfbd x
      exact this.congr (Filter.Eventually.of_forall fun y => by simp)
    have hI2 : Integrable (fun y => ρ y * (v x b - v y b) * fderiv ℝ G y (EuclideanSpace.single b 1)) := by
      exact hfint.mul_bdd (hFGc b).aestronglyMeasurable (c := κ)
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hFG y b)
    refine ⟨hI2, hI1, ?_⟩
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
      (f := fun y => ρ y * (v x b - v y b)) (g := G) (v := EuclideanSpace.single b 1)
      hI1 hI2 hI3 (fun y _ => hfd y) (fun y _ => hGd y)
  -- sum over coordinates
  have hA : ∀ y, ∑ b : Fin d, ρ y * (v x b - v y b) * fderiv ℝ G y (EuclideanSpace.single b 1) =
      -(ρ y * ⟪v x - v y, s45_F s ε (x - y)⟫) := by
    intro y
    rw [s45_inner_eq_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hG, s45_fderiv_G1 s hε0]
    simp [EuclideanSpace.inner_single_right]
    ring
  have hB : ∀ y, ∑ b : Fin d, fderiv ℝ (fun y => ρ y * (v x b - v y b)) y (EuclideanSpace.single b 1) * G y =
      G y * (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y) := by
    intro y
    have e : ∀ b : Fin d, fderiv ℝ (fun y => ρ y * (v x b - v y b)) y (EuclideanSpace.single b 1) =
        (v x b - v y b) * gradient ρ y b - ρ y * (fderiv ℝ v y (EuclideanSpace.single b 1)) b := by
      intro b
      rw [(s45_hasFDerivAt_f hρd hvd x y b).fderiv, movtr_gradient_apply]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
      simp; ring
    simp_rw [e]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, s45_inner_eq_sum, mul_comm (G y)]
    congr 2
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp only [PiLp.sub_apply]; ring
    · unfold s45_div; rw [Finset.mul_sum]
  have hint1 : ∀ b ∈ (Finset.univ : Finset (Fin d)), Integrable (fun y => ρ y * (v x b - v y b) *
      fderiv ℝ G y (EuclideanSpace.single b 1)) := fun b _ => (key b).1
  have hint2 : ∀ b ∈ (Finset.univ : Finset (Fin d)), Integrable (fun y => fderiv ℝ
      (fun y => ρ y * (v x b - v y b)) y (EuclideanSpace.single b 1) * G y) := fun b _ => (key b).2.1
  have hfin : ∫ y, (∑ b : Fin d, ρ y * (v x b - v y b) * fderiv ℝ G y (EuclideanSpace.single b 1)) =
      -∫ y, ∑ b : Fin d, fderiv ℝ (fun y => ρ y * (v x b - v y b)) y (EuclideanSpace.single b 1) * G y := by
    rw [integral_finsetSum _ hint1, integral_finsetSum _ hint2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => (key b).2.2
  simp_rw [hA, hB] at hfin
  rw [integral_neg] at hfin
  have := neg_inj.1 hfin
  exact this

theorem s45_F_cont_eps (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    Continuous fun ε : ℝ => s45_F s ε z := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold s45_F
  refine Continuous.smul (f := fun ε : ℝ => -(movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)))
    (g := fun _ => z) ?_ continuous_const
  refine (continuous_const.mul ?_).neg
  have hb : Continuous fun ε : ℝ => ‖z‖ ^ 2 + ε ^ 2 := by fun_prop
  exact hb.rpow_const fun ε => Or.inl (by positivity)

theorem s45_u_le_B {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {z : Euc d} (hz : z ≠ 0) :
    (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2) ≤ 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1 := by
  by_cases hs : s = 0
  · subst hs
    simp only [neg_zero, zero_div, Real.rpow_zero]
    have := Real.rpow_nonneg (norm_nonneg z) (-movtr_sp 0)
    linarith [norm_nonneg z]
  · have h := movtr_gEps_abs_le hs0 hε hε1 hz
    have e : movtr_gEps d s ε z = (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2) := by
      unfold movtr_gEps; simp only [hs, ite_false]
    rw [e] at h
    exact (le_abs_self _).trans h

theorem s45_norm_gradient (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _

/-- Dominated convergence along `ε → 0+`. -/
theorem s45_dct_eps {L : ℝ → Euc d → ℝ} {L0 : Euc d → ℝ} {bd : Euc d → ℝ}
    (hm : ∀ ε, 0 < ε → Continuous (L ε))
    (hb : ∀ ε, 0 < ε → ε ≤ 1 → ∀ᵐ y : Euc d ∂volume, |L ε y| ≤ bd y) (hi : Integrable bd)
    (hl : ∀ᵐ y : Euc d ∂volume, Tendsto (fun ε => L ε y) (𝓝[>] 0) (𝓝 (L0 y))) :
    Tendsto (fun ε => ∫ y, L ε y) (𝓝[>] (0 : ℝ)) (𝓝 (∫ y, L0 y)) :=
  tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
    (l := 𝓝[>] (0 : ℝ)) (F := fun ε y => L ε y) (f := L0) bd
    (by filter_upwards [self_mem_nhdsWithin] with ε hε
        exact (hm ε hε).aestronglyMeasurable)
    (by filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
        filter_upwards [hb ε hε.1 hε.2] with y hy
        rw [Real.norm_eq_abs]; exact hy)
    hi hl

/-- **One-body integration by parts against the true kernel** (the limit `ε → 0` of `s45_obi_eps`). -/
theorem s45_obi (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) {v : Euc d → Euc d}
    (hv : ContDiff ℝ 1 v) {Bv Dv : ℝ} (hBv : ∀ x, ‖v x‖ ≤ Bv) (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv)
    (x : Euc d) :
    ∫ y, ρ y * ⟪v x - v y, rieszKernelGrad d s (x - y)⟫ =
      ∫ y, rieszKernel d s (x - y) * (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y) := by
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  have hDv0 : 0 ≤ Dv := (norm_nonneg _).trans (hDv 0)
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hσ := s45_sigma_nonneg hs0
  have hρc := hρ.continuous
  have hvc := hv.continuous
  have hgρ : Continuous (gradient ρ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hρ.continuous_fderiv one_ne_zero)
  have hdiv := s45_continuous_div hv
  have hne : ∀ᵐ y : Euc d ∂volume, x - y ≠ 0 := by
    have := movtr_ae_ne_zero (d := d) hd
    have h2 := ((volume : Measure (Euc d)).measurePreserving_sub_left x).quasiMeasurePreserving.ae this
    filter_upwards [h2] with y hy
    simpa using hy
  have hGc : ∀ ε, 0 < ε → Continuous fun y => movtr_gEps d s ε (x - y) := fun ε hε =>
    (show Differentiable ℝ (fun y => movtr_gEps d s ε (x - y)) from
      fun y => (s45_hasFDerivAt_G s hε.ne' x y).differentiableAt).continuous
  have hBm : Measurable (fun z : Euc d => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) :=
    (((measurable_norm.pow_const _).const_mul 2).add measurable_norm).add_const 1
  -- the two sides
  have hL := s45_dct_eps (L := fun ε y => ρ y * ⟪v x - v y, s45_F s ε (x - y)⟫)
    (L0 := fun y => ρ y * ⟪v x - v y, rieszKernelGrad d s (x - y)⟫)
    (bd := fun y => (movtr_sigma s * Dv * (2 * ‖x - y‖ ^ (-movtr_sp s) + ‖x - y‖ + 1)) *
      (C * Real.exp (-c * ‖y‖ ^ 2)))
    (fun ε hε => hρc.mul ((continuous_const.sub hvc).inner
      ((s45_continuous_F hε.ne').comp (continuous_const.sub continuous_id))))
    (fun ε hε hε1 => by
      filter_upwards [hne] with y hy
      have hlip : ‖v x - v y‖ ≤ Dv * ‖x - y‖ := by
        have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := v) (fun z _ => hvd z)
          (fun z _ => hDv z) (mem_univ y) (mem_univ x)
        exact this
      have h2 := s45_pair_inner_le hs0 hε (x - y) (v x - v y) hDv0 hlip
      rw [real_inner_comm] at h2
      have h3 := s45_u_le_B hs0 hε.le hε1 hy
      rw [abs_mul]
      calc |ρ y| * |⟪v x - v y, s45_F s ε (x - y)⟫|
          ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (movtr_sigma s * Dv * (2 * ‖x - y‖ ^ (-movtr_sp s) + ‖x - y‖ + 1)) :=
            mul_le_mul (h0 y) (h2.trans (mul_le_mul_of_nonneg_left h3 (mul_nonneg hσ hDv0)))
              (abs_nonneg _) (by positivity)
        _ = _ := by ring)
    (by
      have := s45_LI hd hs0 hsd hc (k := fun z => movtr_sigma s * Dv * (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1))
        (h := fun y => C * Real.exp (-c * ‖y‖ ^ 2))
        (hBm.const_mul (movtr_sigma s * Dv)).aestronglyMeasurable (by fun_prop) (K1 := movtr_sigma s * Dv) (K2 := C)
        (mul_nonneg hσ hDv0) (fun z _ => by
          rw [abs_of_nonneg (by have := Real.rpow_nonneg (norm_nonneg z) (-movtr_sp s); positivity)])
        hC (fun y => by rw [abs_of_nonneg (by positivity)]) x
      exact this)
    (by
      filter_upwards [hne] with y hy
      have h1 : Continuous fun ε : ℝ => ρ y * ⟪v x - v y, s45_F s ε (x - y)⟫ :=
        continuous_const.mul (continuous_const.inner (s45_F_cont_eps s hy))
      have h2 := (h1.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      rwa [s45_F_zero hy] at h2)
  have hR := s45_dct_eps (L := fun ε y => movtr_gEps d s ε (x - y) *
      (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y))
    (L0 := fun y => rieszKernel d s (x - y) * (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y))
    (bd := fun y => (1 * (2 * ‖x - y‖ ^ (-movtr_sp s) + ‖x - y‖ + 1)) *
      ((C * (2 * Bv) + C * (d * Dv)) * Real.exp (-c * ‖y‖ ^ 2)))
    (fun ε hε => (hGc ε hε).mul ((hgρ.inner (continuous_const.sub hvc)).sub (hρc.mul hdiv)))
    (fun ε hε hε1 => by
      filter_upwards [hne] with y hy
      have h2 := movtr_gEps_abs_le hs0 hε.le hε1 hy
      have h3 : |⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y| ≤
          (C * (2 * Bv) + C * (d * Dv)) * Real.exp (-c * ‖y‖ ^ 2) := by
        have e1 : |⟪gradient ρ y, v x - v y⟫| ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (2 * Bv) := by
          calc |⟪gradient ρ y, v x - v y⟫| ≤ ‖gradient ρ y‖ * ‖v x - v y‖ := abs_real_inner_le_norm _ _
            _ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (2 * Bv) := by
                refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
                · rw [s45_norm_gradient]; exact h1 y
                · calc ‖v x - v y‖ ≤ ‖v x‖ + ‖v y‖ := norm_sub_le _ _
                    _ ≤ Bv + Bv := add_le_add (hBv _) (hBv _)
                    _ = 2 * Bv := by ring
        have e2 : |ρ y * s45_div v y| ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (d * Dv) := by
          rw [abs_mul]
          exact mul_le_mul (h0 y) (s45_div_le hDv y) (abs_nonneg _) (by positivity)
        calc |⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y|
            ≤ |⟪gradient ρ y, v x - v y⟫| + |ρ y * s45_div v y| := abs_sub _ _
          _ ≤ _ := by nlinarith [e1, e2]
      rw [abs_mul]
      calc |movtr_gEps d s ε (x - y)| * |⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y|
          ≤ (1 * (2 * ‖x - y‖ ^ (-movtr_sp s) + ‖x - y‖ + 1)) *
              ((C * (2 * Bv) + C * (d * Dv)) * Real.exp (-c * ‖y‖ ^ 2)) :=
            mul_le_mul (by rw [one_mul]; exact h2) h3 (abs_nonneg _)
              (by have := Real.rpow_nonneg (norm_nonneg (x - y)) (-movtr_sp s); positivity))
    (by
      have := s45_LI hd hs0 hsd hc (k := fun z => 1 * (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1))
        (h := fun y => (C * (2 * Bv) + C * (d * Dv)) * Real.exp (-c * ‖y‖ ^ 2))
        (hBm.const_mul 1).aestronglyMeasurable (by fun_prop) (K1 := 1) (K2 := C * (2 * Bv) + C * (d * Dv))
        zero_le_one (fun z _ => by
          rw [abs_of_nonneg (by have := Real.rpow_nonneg (norm_nonneg z) (-movtr_sp s); positivity)])
        (by positivity) (fun y => by rw [abs_of_nonneg (by positivity)]) x
      exact this)
    (by
      filter_upwards [hne] with y hy
      have h1 : Continuous fun ε : ℝ => movtr_gEps d s ε (x - y) *
          (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y) :=
        (movtr_gEps_cont_eps s hy).mul continuous_const
      have h2 := (h1.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [movtr_gEps_zero] using h2)
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ y, movtr_gEps d s ε (x - y) *
      (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y)) =
      ∫ y, ρ y * ⟪v x - v y, s45_F s ε (x - y)⟫ := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact (s45_obi_eps hd hs0 hsd hε.1 hε.2 hc hC hρ h0 h1 hv hBv hDv x).symm
  exact tendsto_nhds_unique hL (hR.congr' heq)

end S45

end
