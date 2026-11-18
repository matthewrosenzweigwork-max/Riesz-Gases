import HRS.Energy.Commutator.EnergyCoulomb

/-!
# Heat-kernel estimates on the torus (packet CM-S3, helpers for `stress_rough`)

Gaussian (image-sum) estimates for the periodic heat kernel `Θ_u(x) = 1 + Ψ(x,u)`, `u = 4π²t`,
and its gradient: `‖y‖ |∇Θ_u| ≲ Θ_{2u}`, `|∇Θ_u| ≲ u^{-1/2} Θ_{2u}`, `‖y‖ Θ_u ≲ √u Θ_{2u}`,
`Θ_u ≤ (u'/u)^{d/2} Θ_{u'}` (`u ≤ u'`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux

namespace HRS.Commutator.HeatAux

variable {d : ℕ}

/-! ### Scalar Gaussian inequalities -/

theorem abs_mul_exp_half_le (x : ℝ) : |x| * Real.exp (-(x ^ 2 / 2)) ≤ 1 := by
  have h1 := Real.add_one_le_exp (x ^ 2 / 2)
  have h2 : |x| ≤ x ^ 2 / 2 + 1 := by
    nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  have h3 : 0 < Real.exp (x ^ 2 / 2) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one h3]
  linarith

theorem sq_mul_exp_half_le (x : ℝ) : x ^ 2 * Real.exp (-(x ^ 2 / 2)) ≤ 2 := by
  have h1 := Real.add_one_le_exp (x ^ 2 / 2)
  have h3 : 0 < Real.exp (x ^ 2 / 2) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ h3]
  linarith

/-- `r e^{-π²r²/u} ≤ (√u/π) e^{-π²r²/(2u)}`. -/
theorem r_exp_le {u : ℝ} (hu : 0 < u) (r : ℝ) (hr : 0 ≤ r) :
    r * Real.exp (-(Real.pi ^ 2 * r ^ 2 / u)) ≤
      Real.sqrt u / Real.pi * Real.exp (-(Real.pi ^ 2 * r ^ 2 / (2 * u))) := by
  set x : ℝ := Real.pi * r / Real.sqrt u with hx
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx2 : x ^ 2 = Real.pi ^ 2 * r ^ 2 / u := by
    rw [hx, div_pow, mul_pow, Real.sq_sqrt hu.le]
  have hr' : r = Real.sqrt u / Real.pi * x := by
    rw [hx]; field_simp
  have e1 : Real.exp (-(Real.pi ^ 2 * r ^ 2 / u)) = Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add, hx2]; congr 1; ring
  have e2 : Real.exp (-(Real.pi ^ 2 * r ^ 2 / (2 * u))) = Real.exp (-(x ^ 2 / 2)) := by
    congr 1; rw [hx2]; ring
  rw [e1, e2]
  have hxa : |x| * Real.exp (-(x ^ 2 / 2)) ≤ 1 := abs_mul_exp_half_le x
  have hxr : 0 ≤ x := by rw [hx]; positivity
  rw [abs_of_nonneg hxr] at hxa
  calc r * (Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)))
      = Real.sqrt u / Real.pi * (x * Real.exp (-(x ^ 2 / 2))) * Real.exp (-(x ^ 2 / 2)) := by
        rw [hr']; ring
    _ ≤ Real.sqrt u / Real.pi * 1 * Real.exp (-(x ^ 2 / 2)) := by
        gcongr
    _ = _ := by ring

/-- `r² e^{-π²r²/u} ≤ (2u/π²) e^{-π²r²/(2u)}`. -/
theorem r2_exp_le {u : ℝ} (hu : 0 < u) (r : ℝ) :
    r ^ 2 * Real.exp (-(Real.pi ^ 2 * r ^ 2 / u)) ≤
      2 * u / Real.pi ^ 2 * Real.exp (-(Real.pi ^ 2 * r ^ 2 / (2 * u))) := by
  set x : ℝ := Real.pi * r / Real.sqrt u with hx
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx2 : x ^ 2 = Real.pi ^ 2 * r ^ 2 / u := by
    rw [hx, div_pow, mul_pow, Real.sq_sqrt hu.le]
  have hr2 : r ^ 2 = u / Real.pi ^ 2 * x ^ 2 := by
    rw [hx2]; field_simp
  have e1 : Real.exp (-(Real.pi ^ 2 * r ^ 2 / u)) = Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add, hx2]; congr 1; ring
  have e2 : Real.exp (-(Real.pi ^ 2 * r ^ 2 / (2 * u))) = Real.exp (-(x ^ 2 / 2)) := by
    congr 1; rw [hx2]; ring
  rw [e1, e2]
  have hxa := sq_mul_exp_half_le x
  calc r ^ 2 * (Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)))
      = u / Real.pi ^ 2 * (x ^ 2 * Real.exp (-(x ^ 2 / 2))) * Real.exp (-(x ^ 2 / 2)) := by
        rw [hr2]; ring
    _ ≤ u / Real.pi ^ 2 * 2 * Real.exp (-(x ^ 2 / 2)) := by gcongr
    _ = _ := by ring


/-! ### Image sums -/

/-- The Gaussian term `e^{-π² |y-m|²/u}`. -/
def gw (y : Fin d → ℝ) (m : Lattice d) (u : ℝ) : ℝ := Real.exp (-(Real.pi ^ 2 * wsq y m / u))

theorem gw_pos (y : Fin d → ℝ) (m : Lattice d) (u : ℝ) : 0 < gw y m u := Real.exp_pos _

theorem summable_gw (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) : Summable fun m : Lattice d => gw y m u :=
  SliceAux.summable_theta_terms y hu |>.congr fun m => by
    unfold gw wsq
    rw [mul_div_assoc, Finset.sum_div]

/-- Heat kernel as an image sum. -/
theorem one_add_psiFn_eq (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    1 + psiFn (boxPt y) u = Real.sqrt (Real.pi / u) ^ d * ∑' m : Lattice d, gw y m u := by
  rw [← HRS.psi_eq _ hu, theta_images_wsq y hu]
  rfl

theorem gw_sq_eq (y : Fin d → ℝ) (m : Lattice d) (u : ℝ) :
    gw y m u = Real.exp (-(Real.pi ^ 2 * (Real.sqrt (wsq y m)) ^ 2 / u)) := by
  unfold gw; rw [Real.sq_sqrt (wsq_nonneg y m)]

/-- `r_m g_m(u) ≤ (√u/π) g_m(2u)` -/
theorem rgw_le (y : Fin d → ℝ) (m : Lattice d) {u : ℝ} (hu : 0 < u) :
    Real.sqrt (wsq y m) * gw y m u ≤ Real.sqrt u / Real.pi * gw y m (2 * u) := by
  have := r_exp_le hu (Real.sqrt (wsq y m)) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (wsq_nonneg y m)] at this
  unfold gw
  exact this

theorem r2gw_le (y : Fin d → ℝ) (m : Lattice d) {u : ℝ} (hu : 0 < u) :
    wsq y m * gw y m u ≤ 2 * u / Real.pi ^ 2 * gw y m (2 * u) := by
  have := r2_exp_le hu (Real.sqrt (wsq y m))
  rw [Real.sq_sqrt (wsq_nonneg y m)] at this
  unfold gw
  exact this

theorem gw_mono (y : Fin d → ℝ) (m : Lattice d) {u u' : ℝ} (hu : 0 < u) (huu' : u ≤ u') :
    gw y m u ≤ gw y m u' := by
  unfold gw
  refine Real.exp_le_exp.mpr ?_
  have h0 : 0 ≤ Real.pi ^ 2 * wsq y m := mul_nonneg (sq_nonneg _) (wsq_nonneg y m)
  have : Real.pi ^ 2 * wsq y m / u' ≤ Real.pi ^ 2 * wsq y m / u :=
    div_le_div_of_nonneg_left h0 hu huu'
  linarith

/-- Monotonicity of the heat kernel in time up to a polynomial factor. -/
theorem one_add_psiFn_le (y : Fin d → ℝ) {u u' : ℝ} (hu : 0 < u) (huu' : u ≤ u') :
    1 + psiFn (boxPt y) u ≤ (u' / u) ^ ((d : ℝ) / 2) * (1 + psiFn (boxPt y) u') := by
  have hu' : 0 < u' := lt_of_lt_of_le hu huu'
  rw [one_add_psiFn_eq y hu, one_add_psiFn_eq y hu']
  have hc : Real.sqrt (Real.pi / u) ^ d = (u' / u) ^ ((d : ℝ) / 2) * Real.sqrt (Real.pi / u') ^ d := by
    have h1 : Real.sqrt (Real.pi / u) = Real.sqrt (u' / u) * Real.sqrt (Real.pi / u') := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1; field_simp
    rw [h1, mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 2; ring
  rw [hc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Summable.tsum_le_tsum (fun m => gw_mono y m hu huu') (summable_gw y hu) (summable_gw y hu')


theorem summable_rgw (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    Summable fun m : Lattice d => Real.sqrt (wsq y m) * gw y m u := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (Real.sqrt_nonneg _) (gw_pos y m u).le)
    (fun m => rgw_le y m hu) ?_
  exact (summable_gw y (by positivity : 0 < 2 * u)).mul_left _

theorem summable_wsqgw (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    Summable fun m : Lattice d => wsq y m * gw y m u := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (wsq_nonneg y m) (gw_pos y m u).le)
    (fun m => r2gw_le y m hu) ?_
  exact (summable_gw y (by positivity : 0 < 2 * u)).mul_left _

/-- `ρ Θ_u ≲ √u Θ_{2u}` (image sums). -/
theorem rho_sum_le (y : Fin d → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ m, ρ ≤ Real.sqrt (wsq y m)) {u : ℝ}
    (hu : 0 < u) :
    ρ * ∑' m : Lattice d, gw y m u ≤ Real.sqrt u / Real.pi * ∑' m : Lattice d, gw y m (2 * u) := by
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun m => ?_) ((summable_gw y hu).mul_left ρ)
    ((summable_gw y (by positivity : 0 < 2 * u)).mul_left _)
  calc ρ * gw y m u ≤ Real.sqrt (wsq y m) * gw y m u :=
        mul_le_mul_of_nonneg_right (hρ m) (gw_pos y m u).le
    _ ≤ _ := rgw_le y m hu

theorem abs_psiG_le (j : Fin d) (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    |psiG j (boxPt y) u| ≤
      Real.sqrt (Real.pi / u) ^ d * (2 * Real.pi ^ 2 / u) *
        ∑' m : Lattice d, Real.sqrt (wsq y m) * gw y m u := by
  rw [psiG_images j y hu, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ Real.sqrt (Real.pi / u) ^ d * (2 * Real.pi ^ 2 / u))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsum := summable_rgw y hu
  have h1 : Summable fun m : Lattice d => (((m j : ℤ) : ℝ) - y j) * gw y m u := by
    refine Summable.of_norm_bounded hsum fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gw_pos y m u)]
    refine mul_le_mul_of_nonneg_right ?_ (gw_pos y m u).le
    refine Real.abs_le_sqrt ?_
    unfold wsq
    exact Finset.single_le_sum (f := fun i => (((m i : ℤ) : ℝ) - y i) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  calc |∑' m : Lattice d, (((m j : ℤ) : ℝ) - y j) * Real.exp (-(Real.pi ^ 2 * wsq y m / u))|
      = |∑' m : Lattice d, (((m j : ℤ) : ℝ) - y j) * gw y m u| := rfl
    _ ≤ ∑' m : Lattice d, |(((m j : ℤ) : ℝ) - y j) * gw y m u| := by
        have := norm_tsum_le_tsum_norm (f := fun m : Lattice d => (((m j : ℤ) : ℝ) - y j) * gw y m u)
          h1.norm
        simpa using this
    _ ≤ ∑' m : Lattice d, Real.sqrt (wsq y m) * gw y m u := by
        refine Summable.tsum_le_tsum (fun m => ?_) h1.norm hsum
        rw [abs_mul, abs_of_pos (gw_pos y m u)]
        refine mul_le_mul_of_nonneg_right ?_ (gw_pos y m u).le
        refine Real.abs_le_sqrt ?_
        unfold wsq
        exact Finset.single_le_sum (f := fun i => (((m i : ℤ) : ℝ) - y i) ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ j)


theorem sqrt_pi_div_eq (u : ℝ) (hu : 0 < u) :
    Real.sqrt (Real.pi / u) ^ d = Real.sqrt 2 ^ d * Real.sqrt (Real.pi / (2 * u)) ^ d := by
  rw [← mul_pow]
  congr 1
  rw [← Real.sqrt_mul (by norm_num)]
  congr 1; field_simp

/-- (T1) `ρ Θ_u ≤ (√u/π) 2^{d/2} Θ_{2u}`. -/
theorem rho_theta_le (y : Fin d → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ m, ρ ≤ Real.sqrt (wsq y m)) {u : ℝ}
    (hu : 0 < u) :
    ρ * (1 + psiFn (boxPt y) u) ≤
      Real.sqrt u / Real.pi * Real.sqrt 2 ^ d * (1 + psiFn (boxPt y) (2 * u)) := by
  rw [one_add_psiFn_eq y hu, one_add_psiFn_eq y (by positivity : 0 < 2 * u), sqrt_pi_div_eq u hu]
  have := rho_sum_le y hρ0 hρ hu
  have hc : 0 ≤ Real.sqrt 2 ^ d * Real.sqrt (Real.pi / (2 * u)) ^ d := by positivity
  calc ρ * (Real.sqrt 2 ^ d * Real.sqrt (Real.pi / (2 * u)) ^ d * ∑' m : Lattice d, gw y m u)
      = (Real.sqrt 2 ^ d * Real.sqrt (Real.pi / (2 * u)) ^ d) * (ρ * ∑' m : Lattice d, gw y m u) := by ring
    _ ≤ (Real.sqrt 2 ^ d * Real.sqrt (Real.pi / (2 * u)) ^ d) *
          (Real.sqrt u / Real.pi * ∑' m : Lattice d, gw y m (2 * u)) :=
        mul_le_mul_of_nonneg_left this hc
    _ = _ := by ring

/-- (T2) `|∂_j Θ_u| ≤ 2π u^{-1/2} 2^{d/2} Θ_{2u}`. -/
theorem abs_psiG_le_theta (j : Fin d) (y : Fin d → ℝ) {u : ℝ} (hu : 0 < u) :
    |psiG j (boxPt y) u| ≤
      2 * Real.pi / Real.sqrt u * Real.sqrt 2 ^ d * (1 + psiFn (boxPt y) (2 * u)) := by
  refine (abs_psiG_le j y hu).trans ?_
  have hS1 : ∑' m : Lattice d, Real.sqrt (wsq y m) * gw y m u ≤
      Real.sqrt u / Real.pi * ∑' m : Lattice d, gw y m (2 * u) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun m => rgw_le y m hu) (summable_rgw y hu)
      ((summable_gw y (by positivity : 0 < 2 * u)).mul_left _)
  have hc : 0 ≤ Real.sqrt (Real.pi / u) ^ d * (2 * Real.pi ^ 2 / u) := by positivity
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hpi : 0 < Real.pi := Real.pi_pos
  have e : (2 * Real.pi ^ 2 / u) * (Real.sqrt u / Real.pi) = 2 * Real.pi / Real.sqrt u := by
    have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
    field_simp
    nlinarith [hsq]
  calc Real.sqrt (Real.pi / u) ^ d * (2 * Real.pi ^ 2 / u) *
        ∑' m : Lattice d, Real.sqrt (wsq y m) * gw y m u
      ≤ Real.sqrt (Real.pi / u) ^ d * (2 * Real.pi ^ 2 / u) *
        (Real.sqrt u / Real.pi * ∑' m : Lattice d, gw y m (2 * u)) :=
        mul_le_mul_of_nonneg_left hS1 hc
    _ = 2 * Real.pi / Real.sqrt u * (Real.sqrt (Real.pi / u) ^ d * ∑' m : Lattice d, gw y m (2 * u)) := by
        rw [← e]; ring
    _ = _ := by
        rw [one_add_psiFn_eq y (by positivity : 0 < 2 * u), sqrt_pi_div_eq u hu]; ring

/-- (T3) `ρ |∂_j Θ_u| ≤ 4 · 2^{d/2} Θ_{2u}`. -/
theorem rho_abs_psiG_le_theta (j : Fin d) (y : Fin d → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ m, ρ ≤ Real.sqrt (wsq y m)) {u : ℝ} (hu : 0 < u) :
    ρ * |psiG j (boxPt y) u| ≤ 4 * Real.sqrt 2 ^ d * (1 + psiFn (boxPt y) (2 * u)) := by
  have h1 := mul_le_mul_of_nonneg_left (abs_psiG_le j y hu) hρ0
  refine h1.trans ?_
  have hS : ρ * ∑' m : Lattice d, Real.sqrt (wsq y m) * gw y m u ≤
      2 * u / Real.pi ^ 2 * ∑' m : Lattice d, gw y m (2 * u) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun m => ?_) ((summable_rgw y hu).mul_left ρ)
      ((summable_gw y (by positivity : 0 < 2 * u)).mul_left _)
    calc ρ * (Real.sqrt (wsq y m) * gw y m u) ≤ Real.sqrt (wsq y m) * (Real.sqrt (wsq y m) * gw y m u) :=
          mul_le_mul_of_nonneg_right (hρ m) (mul_nonneg (Real.sqrt_nonneg _) (gw_pos y m u).le)
      _ = wsq y m * gw y m u := by
          rw [← mul_assoc, Real.mul_self_sqrt (wsq_nonneg y m)]
      _ ≤ _ := r2gw_le y m hu
  have hc : 0 ≤ Real.sqrt (Real.pi / u) ^ d * (2 * Real.pi ^ 2 / u) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  calc ρ * (Real.sqrt (Real.pi / u) ^ d * (2 * Real.pi ^ 2 / u) *
        ∑' m : Lattice d, Real.sqrt (wsq y m) * gw y m u)
      = (Real.sqrt (Real.pi / u) ^ d * (2 * Real.pi ^ 2 / u)) *
        (ρ * ∑' m : Lattice d, Real.sqrt (wsq y m) * gw y m u) := by ring
    _ ≤ (Real.sqrt (Real.pi / u) ^ d * (2 * Real.pi ^ 2 / u)) *
        (2 * u / Real.pi ^ 2 * ∑' m : Lattice d, gw y m (2 * u)) :=
        mul_le_mul_of_nonneg_left hS hc
    _ = 4 * (Real.sqrt (Real.pi / u) ^ d * ∑' m : Lattice d, gw y m (2 * u)) := by
        field_simp; ring
    _ = _ := by
        rw [one_add_psiFn_eq y (by positivity : 0 < 2 * u), sqrt_pi_div_eq u hu]; ring


/-! ### Torus-point versions -/

theorem tdist_le_sqrt_wsq (z : Torus d) (m : Lattice d) :
    KernelGrad.tdist z 0 ≤ Real.sqrt (wsq (fun i => KernelGrad.centeredRep z i) m) := by
  rw [KernelGrad.tdist_zero_right]
  have h := SliceAux.norm_sub_toEuc_ge_of_box (fun i => KernelGrad.abs_centeredRep_le z i) m
  refine h.trans (le_of_eq ?_)
  rw [EuclideanSpace.norm_eq]
  unfold wsq
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, Lattice.toEuc]
  ring

theorem tdist_theta_le (z : Torus d) {u : ℝ} (hu : 0 < u) :
    KernelGrad.tdist z 0 * (1 + psiFn z u) ≤
      Real.sqrt u / Real.pi * Real.sqrt 2 ^ d * (1 + psiFn z (2 * u)) := by
  have := rho_theta_le (fun i => KernelGrad.centeredRep z i) (KernelGrad.tdist_nonneg z 0) (tdist_le_sqrt_wsq z) hu
  rwa [EnergyAux.boxPt_centeredRep] at this

theorem abs_psiG_theta (j : Fin d) (z : Torus d) {u : ℝ} (hu : 0 < u) :
    |psiG j z u| ≤ 2 * Real.pi / Real.sqrt u * Real.sqrt 2 ^ d * (1 + psiFn z (2 * u)) := by
  have := abs_psiG_le_theta j (fun i => KernelGrad.centeredRep z i) hu
  rwa [EnergyAux.boxPt_centeredRep] at this

theorem tdist_abs_psiG_theta (j : Fin d) (z : Torus d) {u : ℝ} (hu : 0 < u) :
    KernelGrad.tdist z 0 * |psiG j z u| ≤ 4 * Real.sqrt 2 ^ d * (1 + psiFn z (2 * u)) := by
  have := rho_abs_psiG_le_theta j (fun i => KernelGrad.centeredRep z i) (KernelGrad.tdist_nonneg z 0)
    (tdist_le_sqrt_wsq z) hu
  rwa [EnergyAux.boxPt_centeredRep] at this

theorem theta_mono (z : Torus d) {u u' : ℝ} (hu : 0 < u) (huu' : u ≤ u') :
    1 + psiFn z u ≤ (u' / u) ^ ((d : ℝ) / 2) * (1 + psiFn z u') := by
  have := one_add_psiFn_le (fun i => KernelGrad.centeredRep z i) hu huu'
  rwa [EnergyAux.boxPt_centeredRep] at this

theorem abs_psiFn_le_exp (d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : Torus d) (u : ℝ), 1 ≤ u → |psiFn x u| ≤ K * Real.exp (-u) := by
  set G := ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) with hG
  have hG0 : 0 ≤ G := tsum_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨Real.exp 1 * G, by positivity, fun x u h1 => ?_⟩
  have hb : ∀ k : Lattice d, ‖if k = 0 then 0 else Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x‖
      ≤ Real.exp (-u) * Real.exp 1 * Real.exp (-1 * Lattice.enorm k ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp only [hk, ite_true, norm_zero]; positivity
    · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hm := one_le_enorm k hk
      calc Real.exp (-u * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
          ≤ Real.exp (-u * Lattice.enorm k ^ 2) * 1 := by gcongr; exact abs_cosMode_le k x
        _ = Real.exp (-u * Lattice.enorm k ^ 2) := mul_one _
        _ ≤ Real.exp (-u + 1 + -1 * Lattice.enorm k ^ 2) := by
            apply Real.exp_le_exp.mpr
            nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (show (1:ℝ) ≤ Lattice.enorm k ^ 2 by nlinarith))]
        _ = _ := by rw [Real.exp_add, Real.exp_add]
  have hsum := ((summable_gauss_lattice d 1 one_pos).mul_left
    (Real.exp (-u) * Real.exp 1)).hasSum
  have h2 := tsum_of_norm_bounded hsum hb
  rw [tsum_mul_left, ← hG] at h2
  have h3 : |psiFn x u| ≤ Real.exp (-u) * Real.exp 1 * G := by
    rw [← Real.norm_eq_abs]; exact h2
  calc |psiFn x u| ≤ Real.exp (-u) * Real.exp 1 * G := h3
    _ = _ := by ring

theorem small_time_bound {l : ℝ} (hl : 0 ≤ l) {z : Torus d} (hz : z ≠ 0) {S K : ℝ}
    (hS : 1 / (4 * Real.pi ^ 2) ≤ S) (hK0 : 0 ≤ K)
    (hK : ∀ (x : Torus d) (u : ℝ), 1 ≤ u → |psiFn x u| ≤ K * Real.exp (-u)) :
    ∫ s in Ioc (0 : ℝ) S, Real.exp (-l * s) * (1 + psiFn z (4 * Real.pi ^ 2 * s)) ≤
      S + sliceG d l z + K / (4 * Real.pi ^ 2) := by
  have hc0 : 0 < 4 * Real.pi ^ 2 := by positivity
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hI := SliceAux.integrableOn_slice_psi hl hz
  have hI1 : IntegrableOn (fun s : ℝ => Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s)) (Ioc 0 S) :=
    hI.mono_set Ioc_subset_Ioi_self
  have hI2 : IntegrableOn (fun s : ℝ => Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s)) (Ioi S) :=
    hI.mono_set (Ioi_subset_Ioi hS0.le)
  have hE : IntegrableOn (fun s : ℝ => Real.exp (-l * s)) (Ioc 0 S) :=
    (Continuous.integrableOn_Ioc (by fun_prop))
  have hsplit : sliceG d l z = (∫ s in Ioc (0 : ℝ) S, Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s)) +
      ∫ s in Ioi S, Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s) := by
    unfold sliceG
    rw [← Ioc_union_Ioi_eq_Ioi hS0.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hI1 hI2]
  have h1 : ∫ s in Ioc (0 : ℝ) S, Real.exp (-l * s) * (1 + psiFn z (4 * Real.pi ^ 2 * s)) =
      (∫ s in Ioc (0 : ℝ) S, Real.exp (-l * s)) +
        ∫ s in Ioc (0 : ℝ) S, Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s) := by
    rw [← integral_add hE hI1]
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    beta_reduce; ring
  have h2 : (∫ s in Ioc (0 : ℝ) S, Real.exp (-l * s)) ≤ S := by
    calc (∫ s in Ioc (0 : ℝ) S, Real.exp (-l * s)) ≤ ∫ s in Ioc (0 : ℝ) S, (1 : ℝ) := by
          refine setIntegral_mono_on hE (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc fun s hs => ?_
          have : 0 < s := hs.1
          rw [Real.exp_le_one_iff]; nlinarith
      _ = S := by simp [hS0.le]
  have h3 : -(∫ s in Ioi S, Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s)) ≤ K / (4 * Real.pi ^ 2) := by
    have hE2 : IntegrableOn (fun s : ℝ => K * Real.exp (-(4 * Real.pi ^ 2 * s))) (Ioi S) := by
      have := integrableOn_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) S
      have h2 : IntegrableOn (fun s : ℝ => K * Real.exp (-(4 * Real.pi ^ 2) * s)) (Ioi S) :=
        this.const_mul K
      refine h2.congr_fun (fun s _ => ?_) measurableSet_Ioi
      simp [neg_mul]
    have hle : ∀ s ∈ Ioi S, -(Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s)) ≤
        K * Real.exp (-(4 * Real.pi ^ 2 * s)) := by
      intro s hs
      have hs' : S < s := hs
      have h1u : 1 ≤ 4 * Real.pi ^ 2 * s := by
        have : 1 / (4 * Real.pi ^ 2) < s := lt_of_le_of_lt hS hs'
        rw [div_lt_iff₀ hc0] at this; linarith
      have hp := hK z _ h1u
      have hel : Real.exp (-l * s) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      calc -(Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s))
          ≤ |Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s)| := neg_le_abs _
        _ = Real.exp (-l * s) * |psiFn z (4 * Real.pi ^ 2 * s)| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ 1 * (K * Real.exp (-(4 * Real.pi ^ 2 * s))) := by
            exact mul_le_mul hel hp (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc -(∫ s in Ioi S, Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s))
        = ∫ s in Ioi S, -(Real.exp (-l * s) * psiFn z (4 * Real.pi ^ 2 * s)) := (integral_neg _).symm
      _ ≤ ∫ s in Ioi S, K * Real.exp (-(4 * Real.pi ^ 2 * s)) :=
          setIntegral_mono_on hI2.neg hE2 measurableSet_Ioi hle
      _ ≤ K / (4 * Real.pi ^ 2) := by
          rw [integral_const_mul]
          have := integral_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) S
          simp only [neg_mul] at this ⊢
          rw [this]
          have hpos : 0 ≤ Real.exp (-(4 * Real.pi ^ 2 * S)) := (Real.exp_pos _).le
          have hle1 : Real.exp (-(4 * Real.pi ^ 2 * S)) ≤ 1 := by
            rw [Real.exp_le_one_iff]; nlinarith
          have : -Real.exp (-(4 * Real.pi ^ 2 * S)) / -(4 * Real.pi ^ 2) =
              Real.exp (-(4 * Real.pi ^ 2 * S)) / (4 * Real.pi ^ 2) := by
            rw [neg_div_neg_eq]
          rw [this]
          calc K * (Real.exp (-(4 * Real.pi ^ 2 * S)) / (4 * Real.pi ^ 2))
              ≤ K * (1 / (4 * Real.pi ^ 2)) := by gcongr
            _ = _ := by ring
  rw [h1]
  have := hsplit
  linarith


theorem integrableOn_exp_abs_psiG {l : ℝ} (hl : 0 ≤ l) (j : Fin d) {z : Torus d} (hz : z ≠ 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t) * |psiG j z (4 * Real.pi ^ 2 * t)|) (Ioi 0) := by
  have hc0 : 0 < 4 * Real.pi ^ 2 := by positivity
  obtain ⟨xe, rfl, hxe⟩ := KernelGrad.exists_mk_box z
  obtain ⟨M, hM0, hM⟩ := psiG_bound j xe hxe (SliceAux.mk_ne_zero_ne_zero hz)
  have hE : IntegrableOn (fun t : ℝ => M * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) (0 : ℝ)
    have h2 : IntegrableOn (fun t : ℝ => M * Real.exp (-(4 * Real.pi ^ 2) * t)) (Ioi 0) :=
      this.const_mul M
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [neg_mul]
  refine Integrable.mono' hE ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul ?_
    refine ContinuousOn.abs ?_
    refine (psiG_continuousOn j _).comp (continuousOn_const.mul continuousOn_id) fun t ht => ?_
    have : (0 : ℝ) < t := ht
    show 0 < 4 * Real.pi ^ 2 * t
    positivity
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
    have hel : Real.exp (-l * t) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    have := hM (4 * Real.pi ^ 2 * t) (by positivity)
    calc Real.exp (-l * t) * |psiG j (Torus.mk xe) (4 * Real.pi ^ 2 * t)|
        ≤ 1 * (M * Real.exp (-(4 * Real.pi ^ 2 * t))) := mul_le_mul hel this (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

theorem bdd_theta {z : Torus d} (hz : z ≠ 0) : ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 0 < u → 1 + psiFn z u ≤ B := by
  obtain ⟨M, hM0, hM⟩ := psi_bound z hz
  refine ⟨1 + M, by positivity, fun u hu => ?_⟩
  have := hM u hu
  have h2 : psiFn z u ≤ M * Real.exp (-u) := (le_abs_self _).trans this
  have h3 : Real.exp (-u) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  nlinarith


theorem small_time_scaled {l : ℝ} (hl : 0 ≤ l) {z : Torus d} (hz : z ≠ 0) {T K : ℝ}
    (hT : 1 / (4 * Real.pi ^ 2) ≤ T) (hK0 : 0 ≤ K)
    (hK : ∀ (x : Torus d) (u : ℝ), 1 ≤ u → |psiFn x u| ≤ K * Real.exp (-u)) :
    ∫ t in Ioc (0 : ℝ) T, Real.exp (-l * t) * (1 + psiFn z (2 * (4 * Real.pi ^ 2) * t)) ≤
      Real.exp (l * T) * (T + sliceG d l z / 2 + K / (2 * (4 * Real.pi ^ 2))) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hc0 : 0 < 4 * Real.pi ^ 2 := by positivity
  -- change of variables s = 2 t
  have hcv : ∫ t in Ioc (0 : ℝ) T, Real.exp (-l * t) * (1 + psiFn z (2 * (4 * Real.pi ^ 2) * t)) =
      (1 / 2) * ∫ s in Ioc (0 : ℝ) (2 * T), Real.exp (-l * (s / 2)) * (1 + psiFn z (4 * Real.pi ^ 2 * s)) := by
    have h := intervalIntegral.integral_comp_mul_left
      (fun s : ℝ => Real.exp (-l * (s / 2)) * (1 + psiFn z (4 * Real.pi ^ 2 * s))) (c := 2) (a := 0) (b := T)
      (by norm_num)
    rw [intervalIntegral.integral_of_le hT0.le, intervalIntegral.integral_of_le (by linarith)] at h
    simp only [mul_zero, smul_eq_mul] at h
    have e : ∀ t : ℝ, Real.exp (-l * (2 * t / 2)) * (1 + psiFn z (4 * Real.pi ^ 2 * (2 * t))) =
        Real.exp (-l * t) * (1 + psiFn z (2 * (4 * Real.pi ^ 2) * t)) := fun t => by
      congr 3 <;> ring
    simp only [e] at h
    rw [h]; ring
  rw [hcv]
  have hle : ∫ s in Ioc (0 : ℝ) (2 * T), Real.exp (-l * (s / 2)) * (1 + psiFn z (4 * Real.pi ^ 2 * s)) ≤
      Real.exp (l * T) * ∫ s in Ioc (0 : ℝ) (2 * T), Real.exp (-l * s) * (1 + psiFn z (4 * Real.pi ^ 2 * s)) := by
    rw [← integral_const_mul]
    have hint : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f (Ioc 0 (2 * T)) := fun f hf =>
      hf.integrableOn_Ioc
    obtain ⟨B, hB0, hB⟩ := bdd_theta hz
    have hbd : IntegrableOn (fun s : ℝ => Real.exp (-l * (s / 2)) * (1 + psiFn z (4 * Real.pi ^ 2 * s)))
        (Ioc 0 (2 * T)) := by
      refine Integrable.mono' (g := fun s : ℝ => B) (integrableOn_const measure_Ioc_lt_top.ne) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
        refine (by fun_prop : Continuous fun s : ℝ => Real.exp (-l * (s / 2))).continuousOn.mul ?_
        refine continuousOn_const.add ?_
        refine (psi_continuousOn z).comp (continuousOn_const.mul continuousOn_id) fun s hs => ?_
        have : (0 : ℝ) < s := hs.1
        show 0 < 4 * Real.pi ^ 2 * s
        positivity
      · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
        have hs0 : (0 : ℝ) < s := hs.1
        have h1 : 0 ≤ 1 + psiFn z (4 * Real.pi ^ 2 * s) := EnergyAux.one_add_psiFn_nonneg' z (by positivity)
        have h2 : Real.exp (-l * (s / 2)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h1)]
        calc Real.exp (-l * (s / 2)) * (1 + psiFn z (4 * Real.pi ^ 2 * s))
            ≤ 1 * B := mul_le_mul h2 (hB _ (by positivity)) h1 zero_le_one
          _ = B := one_mul _
    have hbd2 : IntegrableOn (fun s : ℝ => Real.exp (l * T) * (Real.exp (-l * s) * (1 + psiFn z (4 * Real.pi ^ 2 * s))))
        (Ioc 0 (2 * T)) := by
      refine Integrable.mono' (g := fun s : ℝ => Real.exp (l * T) * B) (integrableOn_const measure_Ioc_lt_top.ne) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
        refine continuousOn_const.mul ((by fun_prop : Continuous fun s : ℝ => Real.exp (-l * s)).continuousOn.mul ?_)
        refine continuousOn_const.add ?_
        refine (psi_continuousOn z).comp (continuousOn_const.mul continuousOn_id) fun s hs => ?_
        have : (0 : ℝ) < s := hs.1
        show 0 < 4 * Real.pi ^ 2 * s
        positivity
      · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
        have hs0 : (0 : ℝ) < s := hs.1
        have h1 : 0 ≤ 1 + psiFn z (4 * Real.pi ^ 2 * s) := EnergyAux.one_add_psiFn_nonneg' z (by positivity)
        have h2 : Real.exp (-l * s) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
        have h3 := hB _ (by positivity : 0 < 4 * Real.pi ^ 2 * s)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le h1))]
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        calc Real.exp (-l * s) * (1 + psiFn z (4 * Real.pi ^ 2 * s)) ≤ 1 * B :=
              mul_le_mul h2 h3 h1 zero_le_one
          _ = B := one_mul _
    refine setIntegral_mono_on hbd hbd2 measurableSet_Ioc fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs.1
    have hs1 : s ≤ 2 * T := hs.2
    have h1 : 0 ≤ 1 + psiFn z (4 * Real.pi ^ 2 * s) := EnergyAux.one_add_psiFn_nonneg' z (by positivity)
    have : Real.exp (-l * (s / 2)) ≤ Real.exp (l * T) * Real.exp (-l * s) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
    calc Real.exp (-l * (s / 2)) * (1 + psiFn z (4 * Real.pi ^ 2 * s))
        ≤ (Real.exp (l * T) * Real.exp (-l * s)) * (1 + psiFn z (4 * Real.pi ^ 2 * s)) :=
          mul_le_mul_of_nonneg_right this h1
      _ = _ := by ring
  have hsm := small_time_bound hl hz (S := 2 * T) (K := K) (by linarith) hK0 hK
  have hexp : 0 ≤ Real.exp (l * T) := (Real.exp_pos _).le
  calc 1 / 2 * ∫ s in Ioc (0 : ℝ) (2 * T), Real.exp (-l * (s / 2)) * (1 + psiFn z (4 * Real.pi ^ 2 * s))
      ≤ 1 / 2 * (Real.exp (l * T) * ∫ s in Ioc (0 : ℝ) (2 * T), Real.exp (-l * s) * (1 + psiFn z (4 * Real.pi ^ 2 * s))) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ ≤ 1 / 2 * (Real.exp (l * T) * (2 * T + sliceG d l z + K / (4 * Real.pi ^ 2))) := by
        gcongr
    _ = _ := by field_simp


theorem tdist_abs_sgc_le {l : ℝ} (hl : 0 ≤ l) {z : Torus d} (hz : z ≠ 0) (j : Fin d) {K M1 : ℝ}
    (hK0 : 0 ≤ K) (hM10 : 0 ≤ M1) (hK : ∀ (x : Torus d) (u : ℝ), 1 ≤ u → |psiFn x u| ≤ K * Real.exp (-u))
    (hM1 : ∀ (x : Torus d) (u : ℝ), 1 ≤ u → |psiG j x u| ≤ M1 * Real.exp (-u)) :
    KernelGrad.tdist z 0 * |SliceAux.sgc j l z| ≤
      4 * Real.sqrt 2 ^ d * (Real.exp (l * (1 / (4 * Real.pi ^ 2))) *
        (1 / (4 * Real.pi ^ 2) + sliceG d l z / 2 + K / (2 * (4 * Real.pi ^ 2)))) +
      d * M1 / (4 * Real.pi ^ 2) := by
  have hc0 : 0 < 4 * Real.pi ^ 2 := by positivity
  set T : ℝ := 1 / (4 * Real.pi ^ 2) with hT
  have hT0 : 0 < T := by positivity
  have hI := integrableOn_exp_abs_psiG hl j hz
  have hd0 : KernelGrad.tdist z 0 ≤ d := SliceAux.tdist_le_dim z
  have ht0 : 0 ≤ KernelGrad.tdist z 0 := KernelGrad.tdist_nonneg z 0
  -- step 1,2
  have h1 : KernelGrad.tdist z 0 * |SliceAux.sgc j l z| ≤
      ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * (KernelGrad.tdist z 0 * |psiG j z (4 * Real.pi ^ 2 * t)|) := by
    calc KernelGrad.tdist z 0 * |SliceAux.sgc j l z|
        ≤ KernelGrad.tdist z 0 * ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * |psiG j z (4 * Real.pi ^ 2 * t)| :=
          mul_le_mul_of_nonneg_left (SliceAux.abs_sgc_le j z) ht0
      _ = _ := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only []; ring
  refine h1.trans ?_
  have hsplit := Ioc_union_Ioi_eq_Ioi hT0.le
  have hI' : IntegrableOn (fun t : ℝ => Real.exp (-l * t) * (KernelGrad.tdist z 0 * |psiG j z (4 * Real.pi ^ 2 * t)|))
      (Ioi 0) := by
    have h2 : IntegrableOn (fun t : ℝ => KernelGrad.tdist z 0 * (Real.exp (-l * t) *
        |psiG j z (4 * Real.pi ^ 2 * t)|)) (Ioi 0) := hI.const_mul (KernelGrad.tdist z 0)
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
    beta_reduce; ring
  rw [← hsplit, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hI'.mono_set Ioc_subset_Ioi_self) (hI'.mono_set (Ioi_subset_Ioi hT0.le))]
  have hA : ∫ t in Ioc (0 : ℝ) T, Real.exp (-l * t) * (KernelGrad.tdist z 0 * |psiG j z (4 * Real.pi ^ 2 * t)|) ≤
      4 * Real.sqrt 2 ^ d * (Real.exp (l * T) * (T + sliceG d l z / 2 + K / (2 * (4 * Real.pi ^ 2)))) := by
    have hsm := small_time_scaled hl hz (T := T) (K := K) le_rfl hK0 hK
    have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-l * t) * (1 + psiFn z (2 * (4 * Real.pi ^ 2) * t)))
        (Ioc 0 T) := by
      obtain ⟨B, hB0, hB⟩ := bdd_theta hz
      refine Integrable.mono' (g := fun s : ℝ => B) (integrableOn_const measure_Ioc_lt_top.ne) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
        refine (by fun_prop : Continuous fun s : ℝ => Real.exp (-l * s)).continuousOn.mul ?_
        refine continuousOn_const.add ?_
        refine (psi_continuousOn z).comp (continuousOn_const.mul continuousOn_id) fun s hs => ?_
        have : (0 : ℝ) < s := hs.1
        show 0 < 2 * (4 * Real.pi ^ 2) * s
        positivity
      · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
        have hs0 : (0 : ℝ) < s := hs.1
        have h1 : 0 ≤ 1 + psiFn z (2 * (4 * Real.pi ^ 2) * s) :=
          EnergyAux.one_add_psiFn_nonneg' z (by positivity)
        have h2 : Real.exp (-l * s) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h1)]
        calc Real.exp (-l * s) * (1 + psiFn z (2 * (4 * Real.pi ^ 2) * s))
            ≤ 1 * B := mul_le_mul h2 (hB _ (by positivity)) h1 zero_le_one
          _ = B := one_mul _
    calc ∫ t in Ioc (0 : ℝ) T, Real.exp (-l * t) * (KernelGrad.tdist z 0 * |psiG j z (4 * Real.pi ^ 2 * t)|)
        ≤ ∫ t in Ioc (0 : ℝ) T, 4 * Real.sqrt 2 ^ d *
            (Real.exp (-l * t) * (1 + psiFn z (2 * (4 * Real.pi ^ 2) * t))) := by
          refine setIntegral_mono_on (hI'.mono_set Ioc_subset_Ioi_self) (hint2.const_mul _)
            measurableSet_Ioc fun t ht => ?_
          have ht0' : (0 : ℝ) < t := ht.1
          have := tdist_abs_psiG_theta j z (u := 4 * Real.pi ^ 2 * t) (by positivity)
          have e : 2 * (4 * Real.pi ^ 2 * t) = 2 * (4 * Real.pi ^ 2) * t := by ring
          rw [e] at this
          calc Real.exp (-l * t) * (KernelGrad.tdist z 0 * |psiG j z (4 * Real.pi ^ 2 * t)|)
              ≤ Real.exp (-l * t) * (4 * Real.sqrt 2 ^ d * (1 + psiFn z (2 * (4 * Real.pi ^ 2) * t))) :=
                mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
            _ = _ := by ring
      _ = 4 * Real.sqrt 2 ^ d * ∫ t in Ioc (0 : ℝ) T, Real.exp (-l * t) * (1 + psiFn z (2 * (4 * Real.pi ^ 2) * t)) :=
          integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsm (by positivity)
  have hB : ∫ t in Ioi T, Real.exp (-l * t) * (KernelGrad.tdist z 0 * |psiG j z (4 * Real.pi ^ 2 * t)|) ≤
      d * M1 / (4 * Real.pi ^ 2) := by
    have hE : IntegrableOn (fun t : ℝ => d * M1 * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi T) := by
      have := integrableOn_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) T
      have h2 : IntegrableOn (fun t : ℝ => d * M1 * Real.exp (-(4 * Real.pi ^ 2) * t)) (Ioi T) :=
        this.const_mul (d * M1)
      refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp [neg_mul]
    calc ∫ t in Ioi T, Real.exp (-l * t) * (KernelGrad.tdist z 0 * |psiG j z (4 * Real.pi ^ 2 * t)|)
        ≤ ∫ t in Ioi T, d * M1 * Real.exp (-(4 * Real.pi ^ 2 * t)) := by
          refine setIntegral_mono_on (hI'.mono_set (Ioi_subset_Ioi hT0.le)) hE measurableSet_Ioi fun t ht => ?_
          have ht' : T < t := ht
          have h1u : 1 ≤ 4 * Real.pi ^ 2 * t := by
            have : 1 / (4 * Real.pi ^ 2) < t := ht'
            rw [div_lt_iff₀ hc0] at this; linarith
          have hel : Real.exp (-l * t) ≤ 1 := by
            rw [Real.exp_le_one_iff]; nlinarith
          have hp := hM1 z _ h1u
          calc Real.exp (-l * t) * (KernelGrad.tdist z 0 * |psiG j z (4 * Real.pi ^ 2 * t)|)
              ≤ 1 * (d * (M1 * Real.exp (-(4 * Real.pi ^ 2 * t)))) := by
                refine mul_le_mul hel ?_ (mul_nonneg ht0 (abs_nonneg _)) zero_le_one
                exact mul_le_mul hd0 hp (abs_nonneg _) (Nat.cast_nonneg d)
            _ = _ := by ring
      _ ≤ d * M1 / (4 * Real.pi ^ 2) := by
          rw [integral_const_mul]
          have := integral_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) T
          simp only [neg_mul] at this ⊢
          rw [this]
          have hle1 : Real.exp (-(4 * Real.pi ^ 2 * T)) ≤ 1 := by
            rw [Real.exp_le_one_iff]; nlinarith
          have : -Real.exp (-(4 * Real.pi ^ 2 * T)) / -(4 * Real.pi ^ 2) =
              Real.exp (-(4 * Real.pi ^ 2 * T)) / (4 * Real.pi ^ 2) := by
            rw [neg_div_neg_eq]
          rw [this]
          have hdM : 0 ≤ (d : ℝ) * M1 := mul_nonneg (Nat.cast_nonneg d) hM10
          calc (d : ℝ) * M1 * (Real.exp (-(4 * Real.pi ^ 2 * T)) / (4 * Real.pi ^ 2))
              ≤ (d : ℝ) * M1 * (1 / (4 * Real.pi ^ 2)) := by gcongr
            _ = _ := by ring
  linarith


/-- (K1) Domination of the commutator force: `|z| ‖∇𝒢_l(z)‖ ≤ A 𝒢_l(z) + B`. -/
theorem tdist_grad_le (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z : Torus d, z ≠ 0 →
      KernelGrad.tdist z 0 * ‖sliceGrad d l z‖ ≤ A * sliceG d l z + B := by
  have hc0 : 0 < 4 * Real.pi ^ 2 := by positivity
  obtain ⟨K, hK0, hK⟩ := abs_psiFn_le_exp d
  have hMj : ∀ j : Fin d, ∃ M : ℝ, 0 ≤ M ∧ ∀ (x : Torus d) (u : ℝ), 1 ≤ u → |psiG j x u| ≤ M * Real.exp (-u) :=
    fun j => psiG_large_bound j
  choose M1 hM10 hM1 using hMj
  set T : ℝ := 1 / (4 * Real.pi ^ 2) with hT
  set c1 : ℝ := 4 * Real.sqrt 2 ^ d with hc1
  have hc1p : 0 ≤ c1 := by positivity
  have hexp : 0 < Real.exp (l * T) := Real.exp_pos _
  refine ⟨d * (c1 * (Real.exp (l * T) * (1 / 2))),
    d * (c1 * (Real.exp (l * T) * (T + K / (2 * (4 * Real.pi ^ 2))))) + ∑ j : Fin d, d * M1 j / (4 * Real.pi ^ 2),
    by positivity, by
      have : 0 ≤ ∑ j : Fin d, (d : ℝ) * M1 j / (4 * Real.pi ^ 2) :=
        Finset.sum_nonneg fun j _ => by have := hM10 j; positivity
      positivity, fun z hz => ?_⟩
  have hnorm : ‖sliceGrad d l z‖ ≤ ∑ j : Fin d, |SliceAux.sgc j l z| := by
    rw [sliceGrad_eq hl hz]
    exact (HRS.KernelAux.norm_toLp_le_sum _).trans (le_of_eq rfl)
  have ht0 : 0 ≤ KernelGrad.tdist z 0 := KernelGrad.tdist_nonneg z 0
  calc KernelGrad.tdist z 0 * ‖sliceGrad d l z‖
      ≤ KernelGrad.tdist z 0 * ∑ j : Fin d, |SliceAux.sgc j l z| := mul_le_mul_of_nonneg_left hnorm ht0
    _ = ∑ j : Fin d, KernelGrad.tdist z 0 * |SliceAux.sgc j l z| := Finset.mul_sum _ _ _
    _ ≤ ∑ j : Fin d, (c1 * (Real.exp (l * T) * (T + sliceG d l z / 2 + K / (2 * (4 * Real.pi ^ 2)))) +
          d * M1 j / (4 * Real.pi ^ 2)) :=
        Finset.sum_le_sum fun j _ => tdist_abs_sgc_le hl hz j hK0 (hM10 j) hK (hM1 j)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


end HRS.Commutator.HeatAux
