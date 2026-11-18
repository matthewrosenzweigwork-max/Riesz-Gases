import HRS.MC.CepN5b
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Packet N5, helper 1: the smooth scale function

Pure calculus.  `n5_S θ lam δ` is a global `C²` function that agrees with the scale function
`cep_scale θ lam` on `[δ, ∞)` (the singularity of `u^{-θ}` at `0` is removed by the smooth clamp `n5_m`),
with `S' = u^{-θ} e^{-λu}` and `S'' = S'(-θ/u - λ)` on `(δ, ∞)`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace HRS.MC.CepN5

open HRS.MC.CepN5b (cep_scale)

/-- The scale density `u^{-θ} e^{-λu}`. -/
def n5_psi (θ lam u : ℝ) : ℝ := u ^ (-θ) * Real.exp (-(lam * u))

/-- Smooth clamp: `m x ≥ δ/2` everywhere and `m x = x` for `x ≥ δ`. -/
def n5_m (δ x : ℝ) : ℝ := δ / 2 + (x - δ / 2) * Real.smoothTransition ((x - δ / 2) / (δ / 2))

theorem n5_m_contDiff (δ : ℝ) (n : ℕ∞) : ContDiff ℝ n (n5_m δ) := by
  unfold n5_m
  have h1 : ContDiff ℝ n (fun x : ℝ => x - δ / 2) := contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ n (fun x : ℝ => (x - δ / 2) / (δ / 2)) := h1.div_const _
  exact contDiff_const.add (h1.mul (Real.smoothTransition.contDiff.comp h2))

theorem n5_m_ge {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : δ / 2 ≤ n5_m δ x := by
  unfold n5_m
  by_cases h : x ≤ δ / 2
  · have : Real.smoothTransition ((x - δ / 2) / (δ / 2)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    rw [this]; simp
  · push Not at h
    have := Real.smoothTransition.nonneg ((x - δ / 2) / (δ / 2))
    nlinarith

theorem n5_m_of_ge {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : δ ≤ x) : n5_m δ x = x := by
  unfold n5_m
  have : Real.smoothTransition ((x - δ / 2) / (δ / 2)) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ (by linarith)]; linarith
  rw [this]; ring

/-- The `C¹` extension of the scale density. -/
def n5_g (θ lam δ x : ℝ) : ℝ := n5_psi θ lam (n5_m δ x)

theorem n5_psi_contDiffAt (θ lam : ℝ) {u : ℝ} (hu : u ≠ 0) (n : ℕ∞) :
    ContDiffAt ℝ n (n5_psi θ lam) u := by
  unfold n5_psi
  refine ContDiffAt.mul (Real.contDiffAt_rpow_const_of_ne hu) ?_
  exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg).contDiffAt

theorem n5_g_contDiff {δ : ℝ} (hδ : 0 < δ) (θ lam : ℝ) (n : ℕ∞) : ContDiff ℝ n (n5_g θ lam δ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hm := n5_m_ge hδ x
  exact (n5_psi_contDiffAt θ lam (by linarith : n5_m δ x ≠ 0) n).comp x (n5_m_contDiff δ n).contDiffAt

theorem n5_psi_nonneg (θ lam : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ n5_psi θ lam u :=
  mul_nonneg (Real.rpow_nonneg hu _) (Real.exp_pos _).le

theorem n5_g_nonneg {δ : ℝ} (hδ : 0 < δ) (θ lam x : ℝ) : 0 ≤ n5_g θ lam δ x :=
  n5_psi_nonneg θ lam (by linarith [n5_m_ge hδ x])

theorem n5_g_of_ge {δ : ℝ} (hδ : 0 < δ) (θ lam : ℝ) {x : ℝ} (hx : δ ≤ x) :
    n5_g θ lam δ x = n5_psi θ lam x := by
  unfold n5_g; rw [n5_m_of_ge hδ hx]

/-- The global `C²` scale function, equal to `cep_scale` on `[δ, ∞)`. -/
def n5_S (θ lam δ x : ℝ) : ℝ := cep_scale θ lam δ + ∫ u in δ..x, n5_g θ lam δ u

theorem n5_S_hasDerivAt {δ : ℝ} (hδ : 0 < δ) (θ lam x : ℝ) :
    HasDerivAt (n5_S θ lam δ) (n5_g θ lam δ x) x := by
  have h := ((n5_g_contDiff hδ θ lam 0).continuous.integral_hasStrictDerivAt δ x).hasDerivAt
  exact h.const_add _

theorem n5_S_deriv {δ : ℝ} (hδ : 0 < δ) (θ lam : ℝ) :
    deriv (n5_S θ lam δ) = n5_g θ lam δ := funext fun x => (n5_S_hasDerivAt hδ θ lam x).deriv

theorem n5_S_contDiff {δ : ℝ} (hδ : 0 < δ) (θ lam : ℝ) : ContDiff ℝ 2 (n5_S θ lam δ) := by
  have h : ContDiff ℝ (1 + 1 : WithTop ℕ∞) (n5_S θ lam δ) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x => (n5_S_hasDerivAt hδ θ lam x).differentiableAt, by simp, ?_⟩
    rw [n5_S_deriv hδ]
    exact n5_g_contDiff hδ θ lam 1
  rwa [show (1 + 1 : WithTop ℕ∞) = 2 by norm_num] at h

theorem n5_S_eq {δ : ℝ} (hδ : 0 < δ) {θ lam : ℝ} (hθ : θ < 1) (hlam : 0 ≤ lam) {x : ℝ} (hx : δ ≤ x) :
    n5_S θ lam δ x = cep_scale θ lam x := by
  unfold n5_S
  have h1 := HRS.MC.CepN5b.n5b_intInt hθ hlam hδ.le
  have h2 := HRS.MC.CepN5b.n5b_intInt hθ hlam (hδ.le.trans hx)
  have h3 : ∫ u in δ..x, n5_g θ lam δ u = ∫ u in δ..x, (fun u : ℝ => u ^ (-θ) * Real.exp (-(lam * u))) u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hx] at hu
    exact n5_g_of_ge hδ θ lam hu.1
  rw [h3, ← intervalIntegral.integral_interval_sub_left h2 h1]
  unfold cep_scale; ring

theorem n5_S_deriv_gt {δ : ℝ} (hδ : 0 < δ) (θ lam : ℝ) {x : ℝ} (hx : δ < x) :
    deriv (n5_S θ lam δ) x = n5_psi θ lam x := by
  rw [n5_S_deriv hδ]; exact n5_g_of_ge hδ θ lam hx.le

theorem n5_psi_hasDerivAt (θ lam : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (n5_psi θ lam) (n5_psi θ lam x * (-θ / x - lam)) x := by
  unfold n5_psi
  have h1 : HasDerivAt (fun u : ℝ => u ^ (-θ)) ((-θ) * x ^ (-θ - 1)) x := Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (-(lam * u))) (Real.exp (-(lam * x)) * (-lam)) x := by
    have := ((hasDerivAt_id x).const_mul lam).neg.exp
    simpa using this
  convert h1.mul h2 using 1
  rw [Real.rpow_sub_one hx.ne']
  field_simp
  ring

theorem n5_S_deriv2_gt {δ : ℝ} (hδ : 0 < δ) (θ lam : ℝ) {x : ℝ} (hx : δ < x) :
    deriv (deriv (n5_S θ lam δ)) x = n5_psi θ lam x * (-θ / x - lam) := by
  have hev : deriv (n5_S θ lam δ) =ᶠ[𝓝 x] n5_psi θ lam := by
    filter_upwards [lt_mem_nhds hx] with y hy using n5_S_deriv_gt hδ θ lam hy
  rw [hev.deriv_eq]
  exact (n5_psi_hasDerivAt θ lam (by linarith)).deriv

/-- The generator inequality: `L S = S'(b - κ/x - C) ≤ 0` whenever `b ≤ κ/x + C`, for
`θ = 2κ/σ²`, `λ = 2C/σ²`. -/
theorem n5_drift_le {δ : ℝ} (hδ : 0 < δ) {κ C σ : ℝ} (hσ : 0 < σ) {x b : ℝ} (hx : δ < x)
    (hb : b ≤ κ / x + C) :
    deriv (n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ) x * b +
      σ ^ 2 / 2 * deriv (deriv (n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ)) x ≤ 0 := by
  rw [n5_S_deriv_gt hδ _ _ hx, n5_S_deriv2_gt hδ _ _ hx]
  have hψ : 0 ≤ n5_psi (2 * κ / σ ^ 2) (2 * C / σ ^ 2) x := n5_psi_nonneg _ _ (by linarith)
  have hx0 : 0 < x := by linarith
  have e : σ ^ 2 / 2 * (-(2 * κ / σ ^ 2) / x - 2 * C / σ ^ 2) = -(κ / x) - C := by
    field_simp
  have : n5_psi (2 * κ / σ ^ 2) (2 * C / σ ^ 2) x * b +
      σ ^ 2 / 2 * (n5_psi (2 * κ / σ ^ 2) (2 * C / σ ^ 2) x * (-(2 * κ / σ ^ 2) / x - 2 * C / σ ^ 2)) =
      n5_psi (2 * κ / σ ^ 2) (2 * C / σ ^ 2) x * (b - κ / x - C) := by
    rw [← mul_assoc, mul_comm (σ ^ 2 / 2), mul_assoc, e]; ring
  rw [this]
  exact mul_nonpos_of_nonneg_of_nonpos hψ (by linarith)

theorem n5_scale_nonneg {θ lam : ℝ} (hθ : θ < 1) (hlam : 0 ≤ lam) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ cep_scale θ lam z := by
  unfold cep_scale
  refine intervalIntegral.integral_nonneg hz fun u hu => ?_
  exact n5_psi_nonneg θ lam hu.1

theorem n5_scale_mono {θ lam : ℝ} (hθ : θ < 1) (hlam : 0 ≤ lam) {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    cep_scale θ lam y ≤ cep_scale θ lam z := by
  have h1 := HRS.MC.CepN5b.n5b_intInt hθ hlam hy
  have h2 := HRS.MC.CepN5b.n5b_intInt hθ hlam (hy.trans hyz)
  have : cep_scale θ lam z - cep_scale θ lam y = ∫ u in y..z, (fun u : ℝ => u ^ (-θ) * Real.exp (-(lam * u))) u :=
    intervalIntegral.integral_interval_sub_left h2 h1
  have h3 : 0 ≤ ∫ u in y..z, (fun u : ℝ => u ^ (-θ) * Real.exp (-(lam * u))) u :=
    intervalIntegral.integral_nonneg hyz fun u hu => n5_psi_nonneg θ lam (hy.trans hu.1)
  linarith

theorem n5_scale_pos {θ lam : ℝ} (hθ : θ < 1) (hlam : 0 ≤ lam) {z : ℝ} (hz : 0 < z) :
    0 < cep_scale θ lam z := by
  have h := HRS.MC.CepN5b.n5b_S_ge hθ hlam hz.le
  have hp : (0 : ℝ) < -θ + 1 := by linarith
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (div_pos (Real.rpow_pos_of_pos hz _) hp)) h

end HRS.MC.CepN5
