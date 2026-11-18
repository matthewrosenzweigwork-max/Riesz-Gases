import HRS.MS.MovForceAux3
import HRS.MS.SuppU2Aux6
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# MOV-B2 (1): kernel split `g = g_loc + g_far` (S6.1, step 3)

Namespace `HRS.MS.MovForce`, helper prefix `movb2_`, output prefix `mv1_`.

`g = rieszKernel d s` (`|z|^{-s}` or `-log|z|`), `θ` a smooth cutoff (`θ = 1` on the closed unit ball,
`θ = 0` outside the open ball of radius `2`), `g_loc = θ g`, `g_far = (1 - θ) g`.

* `mv1_gloc_integrable`: `g_loc ∈ L¹` (and `‖z‖ g_loc ∈ L¹`);
* `mv1_gfar_smooth`: `g_far ∈ C^∞`;
* `mv1_gfar_bound`: for `j ≥ 1`, `‖D^j g_far (z)‖ ≤ C (1+‖z‖)^{-s-j}`, valid for `s = 0` too (the bound is
  obtained from the homogeneity bounds `u2_iter_bound` for the homogeneous kernels `κ_i = ∂_i g` of degree `-(s+1)`);
* the decomposition `g = g_loc + g_far` and the pointwise majorants `|g_loc|, |g_far| ≤ |g|`.

Statement adjustment: the weight is `(1+‖z‖)` instead of `⟨z⟩ = (1+‖z‖²)^{1/2}` (the two are equivalent up to
the constant `√2`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovForce

open HRS.Whole

variable {d : ℕ}

/-! ### The cutoff -/

/-- The bump function: `1` on `closedBall 0 1`, supported in `ball 0 2`. -/
def movb2_bump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff `θ`. -/
def movb2_theta (d : ℕ) (z : Euc d) : ℝ := movb2_bump d z

/-- `g_loc = θ g`. -/
def movb2_gloc (d : ℕ) (s : ℝ) (z : Euc d) : ℝ := movb2_theta d z * rieszKernel d s z

/-- `g_far = (1 - θ) g`. -/
def movb2_gfar (d : ℕ) (s : ℝ) (z : Euc d) : ℝ := (1 - movb2_theta d z) * rieszKernel d s z

lemma movb2_theta_smooth : ContDiff ℝ ∞ (movb2_theta d) := (movb2_bump d).contDiff

lemma movb2_theta_nonneg (z : Euc d) : 0 ≤ movb2_theta d z := (movb2_bump d).nonneg

lemma movb2_theta_le_one (z : Euc d) : movb2_theta d z ≤ 1 := (movb2_bump d).le_one

lemma movb2_theta_one {z : Euc d} (hz : ‖z‖ ≤ 1) : movb2_theta d z = 1 :=
  (movb2_bump d).one_of_mem_closedBall (by simpa [movb2_bump] using hz)

lemma movb2_theta_zero {z : Euc d} (hz : 2 ≤ ‖z‖) : movb2_theta d z = 0 :=
  (movb2_bump d).zero_of_le_dist (by simpa [movb2_bump, dist_eq_norm] using hz)

lemma movb2_gloc_add_gfar (s : ℝ) (z : Euc d) :
    movb2_gloc d s z + movb2_gfar d s z = rieszKernel d s z := by
  unfold movb2_gloc movb2_gfar; ring

lemma movb2_abs_gloc_le (s : ℝ) (z : Euc d) : |movb2_gloc d s z| ≤ |rieszKernel d s z| := by
  unfold movb2_gloc
  rw [abs_mul, abs_of_nonneg (movb2_theta_nonneg z)]
  exact mul_le_of_le_one_left (abs_nonneg _) (movb2_theta_le_one z)

lemma movb2_abs_gfar_le (s : ℝ) (z : Euc d) : |movb2_gfar d s z| ≤ |rieszKernel d s z| := by
  unfold movb2_gfar
  rw [abs_mul, abs_of_nonneg (by linarith [movb2_theta_le_one z] : (0:ℝ) ≤ 1 - movb2_theta d z)]
  exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [movb2_theta_nonneg z])

lemma movb2_gloc_eq_zero {s : ℝ} {z : Euc d} (hz : 2 ≤ ‖z‖) : movb2_gloc d s z = 0 := by
  simp [movb2_gloc, movb2_theta_zero hz]

lemma movb2_gfar_eq_zero {s : ℝ} {z : Euc d} (hz : ‖z‖ ≤ 1) : movb2_gfar d s z = 0 := by
  simp [movb2_gfar, movb2_theta_one hz]

lemma movb2_gfar_eq_g {s : ℝ} {z : Euc d} (hz : 2 ≤ ‖z‖) :
    movb2_gfar d s z = rieszKernel d s z := by
  simp [movb2_gfar, movb2_theta_zero hz]

/-! ### Smoothness -/

lemma movb2_g_contDiffAt (s : ℝ) {z : Euc d} (hz : z ≠ 0) : ContDiffAt ℝ ∞ (rieszKernel d s) z := by
  have hn : ContDiffAt ℝ ∞ (fun y : Euc d => ‖y‖) z := contDiffAt_norm ℝ hz
  have hn0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  by_cases hs : s = 0
  · have : ContDiffAt ℝ ∞ (fun y : Euc d => -Real.log ‖y‖) z := (hn.log hn0).neg
    convert this using 1
    funext y; simp [rieszKernel, hs]
  · have : ContDiffAt ℝ ∞ (fun y : Euc d => ‖y‖ ^ (-s)) z := hn.rpow_const_of_ne hn0
    convert this using 1
    funext y; simp [rieszKernel, hs]

theorem mv1_gfar_smooth (s : ℝ) : ContDiff ℝ ∞ (movb2_gfar d s) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : Euc d) one_pos] with y hy
    exact movb2_gfar_eq_zero (by have := mem_ball_zero_iff.mp hy; exact this.le)
  · exact ((contDiffAt_const.sub movb2_theta_smooth.contDiffAt).mul (movb2_g_contDiffAt s hz))

/-! ### Iterated derivatives of finite sums `∑ f_i • c_i` -/

lemma movb2_norm_iter_sum {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (c : ι → H) {f : ι → Euc d → ℝ} {N : ℕ∞ω} {x : Euc d} (hf : ∀ i, ContDiffAt ℝ N (f i) x) (k : ℕ)
    (hk : (k : ℕ∞ω) ≤ N) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ i, f i y • c i) x‖ ≤ ∑ i, ‖c i‖ * ‖iteratedFDeriv ℝ k (f i) x‖ := by
  have hs := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (f := fun i y => f i y • c i) (u := Finset.univ)
    (n := k) (x := x) (fun i _ => (((hf i).smul contDiffAt_const).of_le hk))
  rw [hs]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  set L : ℝ →L[ℝ] H := (ContinuousLinearMap.id ℝ ℝ).smulRight (c i) with hL
  have hLn : ‖L‖ ≤ ‖c i‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun t => ?_
    simp [hL, norm_smul, mul_comm]
  have hfun : (fun y => f i y • c i) = L ∘ f i := by
    funext y; simp [hL]
  rw [hfun]
  exact (L.norm_iteratedFDeriv_comp_left (hf i) hk).trans
    (mul_le_mul_of_nonneg_right hLn (norm_nonneg _))

/-! ### The homogeneous kernels `κ_i = ∂_i g` -/

/-- `κ_i(z) = -σ ‖z‖^{-s-2} z_i = ∂_i g (z)` for `z ≠ 0`; homogeneous of degree `-(s+1)`. -/
def movb2_kappa (d : ℕ) (s : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  -(movtr_sigma s * ‖z‖ ^ (-s - 2)) * z i

lemma movb2_kappa_smooth (s : ℝ) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (movb2_kappa d s i) z := by
  have hn : ContDiffAt ℝ ∞ (fun y : Euc d => ‖y‖) z := contDiffAt_norm ℝ hz
  have hn0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have h1 : ContDiffAt ℝ ∞ (fun y : Euc d => ‖y‖ ^ (-s - 2)) z := hn.rpow_const_of_ne hn0
  have h2 : ContDiffAt ℝ ∞ (fun y : Euc d => y i) z :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.contDiffAt
  exact ((contDiffAt_const.mul h1).neg).mul h2

lemma movb2_kappa_hom (s : ℝ) (i : Fin d) {t : ℝ} (ht : 0 < t) {z : Euc d} :
    movb2_kappa d s i (t • z) = t ^ (-(s + 1)) * movb2_kappa d s i z := by
  unfold movb2_kappa
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, Real.mul_rpow ht.le (norm_nonneg _)]
  have : t ^ (-(s + 1)) = t ^ (-s - 2) * t := by
    rw [← Real.rpow_add_one ht.ne']; congr 1; ring
  rw [this]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma movb2_fderiv_g (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    fderiv ℝ (rieszKernel d s) z = ∑ i, movb2_kappa d s i z • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
  ext e
  have h1 : fderiv ℝ (rieszKernel d s) z e = inner ℝ (rieszKernelGrad d s z) e := by
    unfold rieszKernelGrad gradient
    rw [InnerProductSpace.toDual_symm_apply]
  rw [h1, movtr_rieszKernelGrad_eq s hz, real_inner_smul_left]
  simp [movb2_kappa, PiLp.inner_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma movb2_norm_proj_le (i : Fin d) : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simpa using PiLp.norm_apply_le x i

/-- Far-region bound: `‖D^j g‖ ≤ C ‖z‖^{-s-j}` for `‖z‖ ≥ 3`, `j ≥ 1`, for the far kernel. -/
lemma movb2_gfar_far (s : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Euc d, 3 ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ j (movb2_gfar d s) z‖ ≤ C * ‖z‖ ^ (-s - j) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have hb : ∀ i : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Euc d, z ≠ 0 →
      ‖iteratedFDeriv ℝ n (movb2_kappa d s i) z‖ ≤ C * ‖z‖ ^ (-(s + 1) - (n : ℝ)) :=
    fun i => u2_iter_bound (movb2_kappa d s i) (s + 1) (fun z hz => movb2_kappa_smooth s i hz)
      (fun t ht z _ => by simpa using movb2_kappa_hom s i (z := z) ht) n
  choose C hC0 hC using hb
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hU : IsOpen {y : Euc d | 2 < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hev : fderiv ℝ (movb2_gfar d s) =ᶠ[𝓝 z]
      fun y => ∑ i, movb2_kappa d s i y • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
    filter_upwards [hU.mem_nhds (show 2 < ‖z‖ by linarith)] with y hy
    have hy' : y ≠ 0 := norm_pos_iff.mp (by have : (2:ℝ) < ‖y‖ := hy; linarith)
    have : movb2_gfar d s =ᶠ[𝓝 y] rieszKernel d s := by
      filter_upwards [hU.mem_nhds hy] with w hw
      exact movb2_gfar_eq_g (le_of_lt hw)
    rw [this.fderiv_eq]
    exact movb2_fderiv_g s hy'
  have h1 : ‖iteratedFDeriv ℝ (n + 1) (movb2_gfar d s) z‖ =
      ‖iteratedFDeriv ℝ n (fderiv ℝ (movb2_gfar d s)) z‖ := by
    rw [norm_iteratedFDeriv_fderiv]
  rw [h1, (hev.iteratedFDeriv ℝ n).self_of_nhds]
  refine (movb2_norm_iter_sum (fun i => (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ))
    (f := fun i y => movb2_kappa d s i y) (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) (x := z)
    (fun i => movb2_kappa_smooth s i hz0) n (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have hexp : (-(s + 1) - (n : ℝ)) = -s - ((n + 1 : ℕ) : ℝ) := by
    push_cast; ring
  have := hC i z hz0
  rw [hexp] at this
  calc ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ n (movb2_kappa d s i) z‖
      ≤ 1 * (C i * ‖z‖ ^ (-s - ((n + 1 : ℕ) : ℝ))) :=
        mul_le_mul (movb2_norm_proj_le i) this (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **`mv1_gfar_bound`** (step 3): for `j ≥ 1` (valid for `s = 0` as well),
`‖D^j g_far (z)‖ ≤ C (1+‖z‖)^{-s-j}`. -/
theorem mv1_gfar_bound {s : ℝ} (hs0 : 0 ≤ s) (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Euc d,
      ‖iteratedFDeriv ℝ j (movb2_gfar d s) z‖ ≤ C * (1 + ‖z‖) ^ (-s - j) := by
  obtain ⟨Cf, hCf0, hCf⟩ := movb2_gfar_far (d := d) s j hj
  have hcont : Continuous fun z : Euc d => ‖iteratedFDeriv ℝ j (movb2_gfar d s) z‖ :=
    ((mv1_gfar_smooth (d := d) s).continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc d) 3).exists_bound_of_continuousOn hcont.continuousOn
  set p : ℝ := s + j with hp
  have hp0 : 0 ≤ p := by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨max (max M 0 * 4 ^ p) (Cf * (4 / 3) ^ p), le_max_of_le_left (mul_nonneg hM0 (by positivity)),
    fun z => ?_⟩
  have hnp : -s - (j : ℝ) = -p := by rw [hp]; ring
  rw [hnp]
  have hpos : 0 < 1 + ‖z‖ := by positivity
  by_cases hz : ‖z‖ ≤ 3
  · have h1 : ‖iteratedFDeriv ℝ j (movb2_gfar d s) z‖ ≤ max M 0 := by
      have := hM z (by simpa using hz)
      simp only [norm_norm] at this
      exact this.trans (le_max_left _ _)
    have h2 : (4 : ℝ) ^ (-p) ≤ (1 + ‖z‖) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
    have h3 : (4 : ℝ) ^ p * (4 : ℝ) ^ (-p) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    calc ‖iteratedFDeriv ℝ j (movb2_gfar d s) z‖ ≤ max M 0 * ((4 : ℝ) ^ p * (4 : ℝ) ^ (-p)) := by
          rw [h3, mul_one]; exact h1
      _ ≤ max M 0 * ((4 : ℝ) ^ p * (1 + ‖z‖) ^ (-p)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hM0
      _ = (max M 0 * 4 ^ p) * (1 + ‖z‖) ^ (-p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · push Not at hz
    have h1 := hCf z hz.le
    rw [hnp] at h1
    have hz0 : 0 < ‖z‖ := by linarith
    have h2 : ((3 / 4 : ℝ) * (1 + ‖z‖)) ≤ ‖z‖ := by linarith
    have h3 : ‖z‖ ^ (-p) ≤ ((3 / 4 : ℝ) * (1 + ‖z‖)) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
    have h4 : ((3 / 4 : ℝ) * (1 + ‖z‖)) ^ (-p) = (4 / 3 : ℝ) ^ p * (1 + ‖z‖) ^ (-p) := by
      rw [Real.mul_rpow (by norm_num) hpos.le, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3 / 4)]
      congr 1
      rw [← Real.inv_rpow (by norm_num), inv_div]
    calc ‖iteratedFDeriv ℝ j (movb2_gfar d s) z‖ ≤ Cf * ‖z‖ ^ (-p) := h1
      _ ≤ Cf * ((4 / 3 : ℝ) ^ p * (1 + ‖z‖) ^ (-p)) := by
          rw [← h4]; exact mul_le_mul_of_nonneg_left h3 hCf0
      _ = (Cf * (4 / 3) ^ p) * (1 + ‖z‖) ^ (-p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ### Integrability of the local kernel -/

lemma movb2_g_aesm (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    AEStronglyMeasurable (rieszKernel d s) volume :=
  (mv1_g_data (d := d) hd hs0 hsd (c := 1) one_pos).1

lemma movb2_gloc_aesm (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    AEStronglyMeasurable (movb2_gloc d s) volume :=
  (movb2_theta_smooth.continuous.aestronglyMeasurable).mul (movb2_g_aesm hd hs0 hsd)

lemma movb2_gfar_aesm (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    AEStronglyMeasurable (movb2_gfar d s) volume :=
  (((continuous_const.sub movb2_theta_smooth.continuous)).aestronglyMeasurable).mul
    (movb2_g_aesm hd hs0 hsd)

/-- **`mv1_gloc_integrable`** (step 3): `g_loc ∈ L¹` (and `‖z‖ g_loc ∈ L¹`). -/
theorem mv1_gloc_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (movb2_gloc d s) volume ∧ Integrable (fun z => ‖z‖ * movb2_gloc d s z) volume := by
  obtain ⟨hk, hB, hBint⟩ := mv1_g_data (d := d) hd hs0 hsd (c := 1) one_pos
  have hm := movb2_gloc_aesm hd hs0 hsd
  have h1 : Integrable (movb2_gloc d s) volume := by
    refine Integrable.mono' (hBint.const_mul (Real.exp 2)) hm ?_
    filter_upwards [hB] with z hz
    by_cases h2 : 2 ≤ ‖z‖
    · rw [movb2_gloc_eq_zero h2]
      simp only [norm_zero]
      positivity
    · push Not at h2
      have hg : ‖movb2_gloc d s z‖ ≤ 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1 := by
        rw [Real.norm_eq_abs]; exact (movb2_abs_gloc_le s z).trans hz
      have hb0 : 0 ≤ 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1 := (norm_nonneg _).trans hg
      have he : 1 ≤ Real.exp 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith [norm_nonneg z]
      calc ‖movb2_gloc d s z‖ ≤ (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * 1 := by rw [mul_one]; exact hg
        _ ≤ (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * (Real.exp 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left he hb0
        _ = _ := by ring
  refine ⟨h1, ?_⟩
  refine Integrable.mono' (h1.norm.const_mul 2) (continuous_norm.aestronglyMeasurable.mul hm) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [norm_mul, norm_norm]
  by_cases h2 : 2 ≤ ‖z‖
  · rw [movb2_gloc_eq_zero h2]; simp
  · push Not at h2
    exact mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)

end HRS.MS.MovForce

end
