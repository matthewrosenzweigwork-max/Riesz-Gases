import HRS.MS.MovAdjAux14

/-!
# S6.7 (packet P4, part 1): product rule for the one-body generator and bounds for the cut-off

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67_kolmL_mul`: `kolmL (χu) = χ kolmL u + u kolmL χ + 2⟨∇χ,∇u⟩` for `C²` functions;
* `s67_cut_kolmL_bound`: `|kolmL q B (hsCut n)| ≤ K` uniformly in `n` for `‖B‖ ≤ Mb` (the drift grows linearly, the derivatives of the
  cut-off decay like `1/(n+1)` and are supported in `‖y‖ ≤ 2(n+1)`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63

variable {d : ℕ}

theorem s67_kolmL_mul {q : ℝ} {B : Euc d → Euc d} {χ u : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hu : ContDiff ℝ 2 u) (y : Euc d) :
    kolmL q B (fun z => χ z * u z) y =
      χ y * kolmL q B u y + u y * kolmL q B χ y + 2 * inner ℝ (gradient χ y) (gradient u y) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hdχ : DifferentiableAt ℝ χ y := hχ.differentiable (by norm_num) y
  have hdu : DifferentiableAt ℝ u y := hu.differentiable (by norm_num) y
  have hfd : ∀ z, fderiv ℝ (fun w => χ w * u w) z = χ z • fderiv ℝ u z + u z • fderiv ℝ χ z := fun z =>
    fderiv_fun_mul (hχ.differentiable (by norm_num) z) (hu.differentiable (by norm_num) z)
  have hdfu : DifferentiableAt ℝ (fderiv ℝ u) y :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero y
  have hdfχ : DifferentiableAt ℝ (fderiv ℝ χ) y :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero y
  -- the second derivative
  have h2 : ∀ e : Euc d, fderiv ℝ (fderiv ℝ (fun w => χ w * u w)) y e e =
      χ y * fderiv ℝ (fderiv ℝ u) y e e + u y * fderiv ℝ (fderiv ℝ χ) y e e +
        2 * (fderiv ℝ χ y e * fderiv ℝ u y e) := by
    intro e
    have hfun : fderiv ℝ (fun w => χ w * u w) = fun z => χ z • fderiv ℝ u z + u z • fderiv ℝ χ z :=
      funext hfd
    rw [hfun]
    have h1 : HasFDerivAt (fun z => χ z • fderiv ℝ u z + u z • fderiv ℝ χ z)
        (χ y • fderiv ℝ (fderiv ℝ u) y + (fderiv ℝ χ y).smulRight (fderiv ℝ u y) +
          (u y • fderiv ℝ (fderiv ℝ χ) y + (fderiv ℝ u y).smulRight (fderiv ℝ χ y))) y :=
      (hdχ.hasFDerivAt.smul hdfu.hasFDerivAt).add (hdu.hasFDerivAt.smul hdfχ.hasFDerivAt)
    rw [h1.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  unfold kolmL
  rw [kl_laplacian_eq, kl_laplacian_eq (h := u), kl_laplacian_eq (h := χ)]
  simp_rw [h2]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hg : ∀ (h : Euc d → ℝ) (v : Euc d), inner ℝ v (gradient h y) = fderiv ℝ h y v := fun h v =>
    kl_inner_gradient h y v
  rw [hg (fun w => χ w * u w), hg u, hg χ, hfd y]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hin : inner ℝ (gradient χ y) (gradient u y) =
      ∑ i : Fin d, fderiv ℝ χ y (EuclideanSpace.single i 1) * fderiv ℝ u y (EuclideanSpace.single i 1) := by
    rw [s67_inner_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [mnc_gradient_apply]
  rw [hin]
  ring

/-! ### The cut-off -/

theorem s67_cut_zero_far (n : ℕ) {y : Euc d} (hy : 2 * ((n : ℝ) + 1) < ‖y‖) :
    hsCut n =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
  have hopen : IsOpen {z : Euc d | 2 * ((n : ℝ) + 1) < ‖z‖} := isOpen_lt continuous_const continuous_norm
  filter_upwards [hopen.mem_nhds hy] with z hz
  have hz' : 2 * ((n : ℝ) + 1) < ‖z‖ := hz
  unfold hsCut
  refine (hsChi d).zero_of_le_dist ?_
  show (2 : ℝ) ≤ dist (((n : ℝ) + 1)⁻¹ • z) 0
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ hn]
  linarith

theorem s67_cut_one_near (n : ℕ) {y : Euc d} (hy : ‖y‖ < (n : ℝ) + 1) :
    hsCut n =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
  have hopen : IsOpen {z : Euc d | ‖z‖ < (n : ℝ) + 1} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hy] with z hz
  exact hs_cut_eq_one n (le_of_lt hz)

theorem s67_cut_grad_zero_far (n : ℕ) {y : Euc d} (hy : 2 * ((n : ℝ) + 1) < ‖y‖) :
    gradient (hsCut n) y = 0 := by
  have h := (s67_cut_zero_far n hy).fderiv_eq (𝕜 := ℝ)
  unfold gradient
  rw [h]
  simp

theorem s67_cut_grad_bound :
    ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ (n : ℕ) (y : Euc d), ‖gradient (hsCut n) y‖ ≤ c₁ * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨c, hc0, hc⟩ := hs_cut_deriv (d := d) 1 le_rfl
  refine ⟨c, hc0, fun n y => ?_⟩
  rw [s67_grad_norm, ← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := hsCut n) (x := y)]
  exact hc n y

theorem s67_cut_kolmL_zero_near {q : ℝ} {B : Euc d → Euc d} (n : ℕ) {y : Euc d} (hy : ‖y‖ < (n : ℝ) + 1) :
    kolmL q B (hsCut n) y = 0 := by
  have h := s67_cut_one_near n hy
  have hg : gradient (hsCut n) y = 0 := by
    unfold gradient
    rw [h.fderiv_eq (𝕜 := ℝ)]
    simp
  have hl : Laplacian.laplacian (hsCut n) y = 0 := by
    have := (InnerProductSpace.laplacian_congr_nhds h).self_of_nhds
    rw [this]
    simp
  unfold kolmL
  rw [hg, hl]
  simp

theorem s67_cut_kolmL_bound {q Mb : ℝ} {B : Euc d → Euc d} (hB : ∀ y, ‖B y‖ ≤ Mb) :
    ∃ K : ℝ, ∀ (n : ℕ) (y : Euc d), |kolmL q B (hsCut n) y| ≤ K := by
  obtain ⟨c₁, hc₁0, hc₁⟩ := s67_cut_grad_bound (d := d)
  obtain ⟨c₂, hc₂0, hc₂⟩ := hs_cut_deriv (d := d) 2 (by norm_num)
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (hB 0)
  refine ⟨d * c₂ + (2 * |q| * c₁ + Mb * c₁), fun n y => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  -- the Laplacian
  have hlap : |Laplacian.laplacian (hsCut n) y| ≤ d * c₂ := by
    have := s67_lap_bound (u := hsCut (d := d) n) (B := c₂ * ((n : ℝ) + 1)⁻¹) (fun x => hc₂ n x) y
    refine this.trans ?_
    have : c₂ * ((n : ℝ) + 1)⁻¹ ≤ c₂ := mul_le_of_le_one_right hc₂0 hn1
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d)
  -- the drift term
  have hdr : |inner ℝ (-q • y + B y) (gradient (hsCut n) y)| ≤ 2 * |q| * c₁ + Mb * c₁ := by
    by_cases hy : ‖y‖ ≤ 2 * ((n : ℝ) + 1)
    · refine (abs_real_inner_le_norm _ _).trans ?_
      have h1 : ‖-q • y + B y‖ ≤ |q| * (2 * ((n : ℝ) + 1)) + Mb := by
        refine (norm_add_le _ _).trans (add_le_add ?_ (hB y))
        rw [norm_smul, norm_neg, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      have h2 := hc₁ n y
      calc ‖-q • y + B y‖ * ‖gradient (hsCut n) y‖
          ≤ (|q| * (2 * ((n : ℝ) + 1)) + Mb) * (c₁ * ((n : ℝ) + 1)⁻¹) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = 2 * |q| * c₁ + Mb * c₁ * ((n : ℝ) + 1)⁻¹ := by field_simp
        _ ≤ 2 * |q| * c₁ + Mb * c₁ := by
            have : Mb * c₁ * ((n : ℝ) + 1)⁻¹ ≤ Mb * c₁ := mul_le_of_le_one_right (by positivity) hn1
            linarith
    · push Not at hy
      rw [s67_cut_grad_zero_far n hy]
      simp only [inner_zero_right, abs_zero]
      positivity
  unfold kolmL
  exact (abs_add_le _ _).trans (add_le_add hlap hdr)

end HRS.MS.MovAdj
