import HRS.MS.R26T8AP22i

/-!
# S8.2 local Newton layer, packet T8A.P22 (part j): the Newton integral of the leading source
`r26t8a_p22_cfun` is the annular commutator `2 <∇chi, ∇L> + L Δchi`. `r26t8a_p22_identity`: for `0 < |z| < 1`,
`∫ K(z-w) chi(w) g(w) dw = L_B(z) + 2 nu ∫ K(z-w) c(w) dw`, `g = -(s/2) |w|^(-s) B(ω,ω)`
(dominated convergence for `phi_eps` and the Poisson representation `r26t8a_p22_poisson_repr`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N HRS.MD.DOMProof

namespace HRS.MS.R26T8A

variable {d : ℕ}

def r26t8a_p22_cfun (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (chi : Euc d → ℝ) (w : Euc d) : ℝ :=
  2 * inner ℝ (gradient chi w) (gradient (s82n_leadingInverse nu B) w) +
    s82n_leadingInverse nu B w * Laplacian.laplacian chi w

set_option maxHeartbeats 3200000 in
theorem r26t8a_p22_identity (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) {z : Euc d} (hz : z ≠ 0) (hz1 : ‖z‖ < 1)
    (hcint : Integrable (fun w => newtonKernel d nu (z - w) * r26t8a_p22_cfun nu B chi w)) :
    ∫ w, newtonKernel d nu (z - w) * chi w *
        (-(s82n_critS d / 2) * ‖w‖ ^ (-s82n_critS d) * B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w)) =
      s82n_leadingInverse nu B z + 2 * nu * ∫ w, newtonKernel d nu (z - w) * r26t8a_p22_cfun nu B chi w := by
  obtain ⟨Cd, hCd0, hCd⟩ := r26t8a_p22_lap_phi_bound hd nu hnu hchi
  set L := s82n_leadingInverse nu B with hL
  set s' : ℝ := r26t8a_p22_sp d with hs'
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs'0 : 0 < s' := by simp only [hs', r26t8a_p22_sp]; positivity
  have hs'd : s' < d := by simp only [hs', r26t8a_p22_sp]; linarith
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set F : ℕ → Euc d → ℝ := fun n w => newtonKernel d nu (z - w) *
    Laplacian.laplacian (r26t8a_p22_phi nu B chi (ε n)) w with hF
  set bnd : Euc d → ℝ := fun w => Cd * ‖B‖ * (|newtonKernel d nu (z - w)| *
    (closedBall (0 : Euc d) 2).indicator (fun w => ‖w‖ ^ (-s')) w) with hbnd
  have hbint : Integrable bnd :=
    (r26t8a_p07_major hd nu hs'0 hs'd hz).const_mul (Cd * ‖B‖)
  have hFm : ∀ n, AEStronglyMeasurable (F n) volume := fun n =>
    (((r26t8a_K_measurable nu).comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      (HRS.Parx.continuous_laplacian (r26t8a_p22_phi_contDiff nu B hchi (hε0 n))).aestronglyMeasurable
  have hFb : ∀ n, ∀ᵐ w : Euc d ∂volume, ‖F n w‖ ≤ bnd w := by
    intro n
    filter_upwards [r26t8a_ae_ne_zero hd] with w hw
    simp only [hF, hbnd, norm_mul, Real.norm_eq_abs]
    by_cases hw2 : ‖w‖ ≤ 2
    · rw [Set.indicator_of_mem (by simpa using hw2)]
      have := hCd B hB (ε n) (hε0 n) w hw hw2
      calc |newtonKernel d nu (z - w)| * |Laplacian.laplacian (r26t8a_p22_phi nu B chi (ε n)) w|
          ≤ |newtonKernel d nu (z - w)| * (Cd * ‖B‖ * ‖w‖ ^ (-s')) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = _ := by ring
    · rw [r26t8a_p22_lap_phi_zero hchi nu B (ε n) (not_le.1 hw2), abs_zero, mul_zero, Set.indicator_of_notMem (by simpa using hw2)]
      have : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
      positivity
  -- pointwise limit
  set M : Euc d → ℝ := fun x => chi x * L x with hM
  set f : Euc d → ℝ := fun w => newtonKernel d nu (z - w) * Laplacian.laplacian M w with hf
  have heq : ∀ y : Euc d, 0 < ‖y‖ → ∀ n, 2 * ε n < ‖y‖ → r26t8a_p22_phi nu B chi (ε n) =ᶠ[𝓝 y] M := by
    intro y hy n hn
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hn] with x hx
    have h1 : r26t8a_p22_theta chi (ε n) x = 1 := by
      unfold r26t8a_p22_theta
      rw [hchi.2.2.2.2 _ (by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg (hε0 n).le, le_inv_mul_iff₀ (hε0 n)]; linarith)]
      ring
    simp only [r26t8a_p22_phi, hM, h1, one_mul]
    rfl
  have hFlim : ∀ᵐ w : Euc d ∂volume, Tendsto (fun n => F n w) atTop (𝓝 (f w)) := by
    filter_upwards [r26t8a_ae_ne_zero hd] with w hw
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hev : ∀ᶠ n in atTop, ε n < ‖w‖ / 2 := hεt.eventually (gt_mem_nhds (by positivity))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [hF, hf]
    rw [(InnerProductSpace.laplacian_congr_nhds (heq w hwn n (by linarith))).eq_of_nhds]
  -- the limit is integrable and has the integral -M z / (2 nu)
  have hfm : AEStronglyMeasurable f volume := aestronglyMeasurable_of_tendsto_ae atTop hFm hFlim
  have hfb : ∀ᵐ w : Euc d ∂volume, ‖f w‖ ≤ bnd w := by
    filter_upwards [ae_all_iff.2 hFb, hFlim] with w h1 h2
    exact le_of_tendsto (h2.norm) (Eventually.of_forall h1)
  have hfi : Integrable f := Integrable.mono' hbint hfm hfb
  have hlim := tendsto_integral_of_dominated_convergence bnd hFm hbint hFb hFlim
  have hconst : ∀ᶠ n in atTop, ∫ w, F n w = -(M z) / (2 * nu) := by
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hev : ∀ᶠ n in atTop, ε n < ‖z‖ / 2 := hεt.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hev] with n hn
    have h := r26t8a_p22_poisson_repr hd nu hnu (r26t8a_p22_phi_contDiff nu B hchi (hε0 n))
      (r26t8a_p22_phi_cs nu B hchi (ε n)) z
    have hz' : r26t8a_p22_phi nu B chi (ε n) z = M z := (heq z hz0 n (by linarith)).eq_of_nhds
    simp only [hF]
    rw [h, hz']
  have hint : ∫ w, f w = -(M z) / (2 * nu) :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconst.mono fun n hn => hn.symm))
  have hMz : M z = L z := by simp only [hM, hchi.2.2.2.1 z hz1.le, one_mul]
  -- algebra on the integrand
  have hpt : ∀ᵐ w : Euc d ∂volume, newtonKernel d nu (z - w) * chi w *
      (-(s82n_critS d / 2) * ‖w‖ ^ (-s82n_critS d) * B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w)) =
      (-(2 * nu)) * (f w - newtonKernel d nu (z - w) * r26t8a_p22_cfun nu B chi w) := by
    filter_upwards [r26t8a_ae_ne_zero hd] with w hw
    have hL2 : ContDiffAt ℝ 2 L w := by
      have h : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) L w := contDiffAt_infty.1 (r26t8a_p22_L_contDiffAt nu B hw) 2
      exact_mod_cast h
    have hlapM : Laplacian.laplacian M w = chi w * Laplacian.laplacian L w + r26t8a_p22_cfun nu B chi w := by
      have := domp_lap_mul (r26t8a_p22_chi_c2 hchi).contDiffAt hL2
      simp only [hM, r26t8a_p22_cfun]
      rw [this]; ring
    have hlapL := s82n_leading_laplacian hd nu hnu B hB w hw
    have hΔL : Laplacian.laplacian L w = (-(-(s82n_critS d / 2) * ‖w‖ ^ (-s82n_critS d) *
        B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w))) / (2 * nu) := by
      rw [eq_div_iff (by positivity : (2 * nu) ≠ 0)]
      linarith [hlapL]
    simp only [hf]
    rw [hlapM, hΔL]
    field_simp
    ring
  have hKg : Integrable (fun w => newtonKernel d nu (z - w) * chi w *
      (-(s82n_critS d / 2) * ‖w‖ ^ (-s82n_critS d) * B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w))) :=
    (((hfi.sub hcint).const_mul (-(2 * nu)))).congr (hpt.mono fun w hw => hw.symm)
  rw [integral_congr_ae hpt, integral_const_mul, integral_sub hfi hcint, hint, hMz]
  field_simp
  ring

end HRS.MS.R26T8A
