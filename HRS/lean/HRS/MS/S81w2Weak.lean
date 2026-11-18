import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import HRS.Whole.Basic

/-!
# S8.1 (worker S81W2): weak identification of `L²(μ)`-limits of gradients

`s81w2_weak_ident`: for a smooth positive density `ρ` (`μ = ρ dx` a probability measure), `C¹` functions `F_L → h` in `L²(μ)`
whose partial derivatives `∂_i F_L → G_i` in `L²(μ)`, with `h ∈ C¹`, `∂_i h ∈ L²(μ)`: `G_i = ∂_i h` `μ`-a.e.
(integration by parts against `ψ ρ`, `ψ ∈ C_c^∞`, and the fundamental lemma of the calculus of variations).
This is the "closed gradient" step of the physical gradient/current identification of the Pro paper (Lemma 2.1).
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators ContDiff

namespace HRS.Whole.S81W2

open HRS HRS.Whole

variable {d : ℕ}

theorem s81w2_mu_integral {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (u : Euc d → ℝ) :
    ∫ x, u x ∂(withDensityReal ρ) = ∫ x, ρ x * u x := by
  unfold withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (ρ x)) (ENNReal.measurable_ofReal.comp hρ.measurable)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hpos x).le]

theorem s81w2_mu_integrable {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    {u : Euc d → ℝ} (hu : Integrable u (withDensityReal ρ)) : Integrable (fun x => ρ x * u x) := by
  unfold withDensityReal at hu
  rw [integrable_withDensity_iff_integrable_smul' (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ.measurable)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at hu
  refine hu.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hpos x).le]

/-- Convergence in `L²(μ)` gives convergence of pairings with a fixed `L²` function. -/
theorem s81w2_tendsto_pair {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : ℕ → α → ℝ)
    (hf : ∀ L, MemLp (f L) 2 μ) {u : α → ℝ} (hu : MemLp u 2 μ) {w : α → ℝ} (hw : MemLp w 2 μ)
    (h : Tendsto (fun L => (hf L).toLp (f L)) atTop (𝓝 (hu.toLp u))) :
    Tendsto (fun L => ∫ x, f L x * w x ∂μ) atTop (𝓝 (∫ x, u x * w x ∂μ)) := by
  have h1 := h.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hw.toLp w))
  have hinner : ∀ (a b : α → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ),
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x ∂μ := by
    intro a b ha hb
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  simp only [hinner] at h1
  exact h1

theorem s81w2_ibp_mu {ρ : Euc d → ℝ} (hρs : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (v : Euc d) :
    ∫ x, fderiv ℝ u x v * ψ x ∂(withDensityReal ρ) =
      -∫ x, u x * (fderiv ℝ (fun y => ψ y * ρ y) x v / ρ x) ∂(withDensityReal ρ) := by
  have hρc := hρs.continuous
  set g : Euc d → ℝ := fun y => ψ y * ρ y with hg
  have hgs : ContDiff ℝ ∞ g := hψ.mul hρs
  have hgc : HasCompactSupport g := hψc.mul_right
  rw [s81w2_mu_integral hρc hpos, s81w2_mu_integral hρc hpos]
  have hcongr1 : ∀ x, ρ x * (fderiv ℝ u x v * ψ x) = fderiv ℝ u x v * g x := fun x => by
    simp only [hg]; ring
  have hcongr2 : ∀ x, ρ x * (u x * (fderiv ℝ g x v / ρ x)) = u x * fderiv ℝ g x v := fun x => by
    field_simp [(hpos x).ne']
  simp_rw [hcongr1, hcongr2]
  have hDu : Continuous fun x => fderiv ℝ u x v :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDg : Continuous fun x => fderiv ℝ g x v :=
    (hgs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDgc : HasCompactSupport fun x => fderiv ℝ g x v := hgc.fderiv_apply ℝ v
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := u) (g := g)
    (v := v)
    (hDu.mul hgs.continuous |>.integrable_of_hasCompactSupport hgc.mul_left)
    ((hu.continuous.mul hDg).integrable_of_hasCompactSupport hDgc.mul_left)
    ((hu.continuous.mul hgs.continuous).integrable_of_hasCompactSupport hgc.mul_left)
    (fun x _ => hu.differentiable (by norm_num) x) (fun x _ => hgs.differentiable (by simp) x)
  linarith

theorem s81w2_weak_ident {ρ : Euc d → ℝ} (hρs : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (withDensityReal ρ)]
    (F : ℕ → Euc d → ℝ) (hF : ∀ L, ContDiff ℝ 1 (F L)) (hFm : ∀ L, MemLp (F L) 2 (withDensityReal ρ))
    {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) (hhm : MemLp h 2 (withDensityReal ρ))
    (v : Euc d) (hDm : ∀ L, MemLp (fun x => fderiv ℝ (F L) x v) 2 (withDensityReal ρ))
    {G : Euc d → ℝ} (hGm : MemLp G 2 (withDensityReal ρ))
    (hDhm : MemLp (fun x => fderiv ℝ h x v) 2 (withDensityReal ρ))
    (hconvF : Tendsto (fun L => (hFm L).toLp (F L)) atTop (𝓝 (hhm.toLp h)))
    (hconvD : Tendsto (fun L => (hDm L).toLp (fun x => fderiv ℝ (F L) x v)) atTop
      (𝓝 (hGm.toLp G))) :
    G =ᵐ[withDensityReal ρ] fun x => fderiv ℝ h x v := by
  set μ := withDensityReal ρ with hμ
  have hρc := hρs.continuous
  have key : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, (G x - fderiv ℝ h x v) * ψ x ∂μ = 0 := by
    intro ψ hψ hψc
    set g : Euc d → ℝ := fun y => ψ y * ρ y with hg
    have hgs : ContDiff ℝ ∞ g := hψ.mul hρs
    have hgc : HasCompactSupport g := hψc.mul_right
    set Θ : Euc d → ℝ := fun x => fderiv ℝ g x v / ρ x with hΘ
    have hΘc : Continuous Θ :=
      ((hgs.continuous_fderiv (by simp)).clm_apply continuous_const).div hρc (fun x => (hpos x).ne')
    have hΘs : HasCompactSupport Θ := by
      have h1 : HasCompactSupport fun x => fderiv ℝ g x v := hgc.fderiv_apply ℝ v
      refine h1.mono' ?_
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp only [hΘ, h0, zero_div]
    have hΘm : MemLp Θ 2 μ := hΘc.memLp_of_hasCompactSupport hΘs
    have hψm : MemLp ψ 2 μ := hψ.continuous.memLp_of_hasCompactSupport hψc
    have a1 : ∀ L, ∫ x, fderiv ℝ (F L) x v * ψ x ∂μ = -∫ x, F L x * Θ x ∂μ := fun L =>
      s81w2_ibp_mu hρs hpos (hF L) hψ hψc v
    have a2 := s81w2_tendsto_pair (fun L x => fderiv ℝ (F L) x v) hDm hGm hψm hconvD
    have a3 := s81w2_tendsto_pair F hFm hhm hΘm hconvF
    have a4 : ∫ x, G x * ψ x ∂μ = -∫ x, h x * Θ x ∂μ := by
      have a5 : Tendsto (fun L => ∫ x, fderiv ℝ (F L) x v * ψ x ∂μ) atTop
          (𝓝 (-∫ x, h x * Θ x ∂μ)) := by
        simp only [a1]
        exact a3.neg
      exact tendsto_nhds_unique a2 a5
    have a6 : ∫ x, fderiv ℝ h x v * ψ x ∂μ = -∫ x, h x * Θ x ∂μ :=
      s81w2_ibp_mu hρs hpos hh hψ hψc v
    have i1 : Integrable (fun x => G x * ψ x) μ := hGm.integrable_mul hψm
    have i2 : Integrable (fun x => fderiv ℝ h x v * ψ x) μ := hDhm.integrable_mul hψm
    have : ∫ x, (G x - fderiv ℝ h x v) * ψ x ∂μ =
        ∫ x, G x * ψ x ∂μ - ∫ x, fderiv ℝ h x v * ψ x ∂μ := by
      rw [← integral_sub i1 i2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [this, a4, a6]; ring
  -- fundamental lemma
  set u : Euc d → ℝ := fun x => G x - fderiv ℝ h x v with hu
  have hum : MemLp u 2 μ := hGm.sub hDhm
  have hw : Integrable (fun x => ρ x * u x) := s81w2_mu_integrable hρc hpos (hum.integrable (by norm_num))
  have hae : ∀ᵐ x, ρ x * u x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hw.locallyIntegrable ?_
    intro ψ hψ hψc
    have := key ψ hψ hψc
    rw [s81w2_mu_integral hρc hpos] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hu, smul_eq_mul]
    ring
  have hae2 : ∀ᵐ x, u x = 0 := by
    filter_upwards [hae] with x hx
    exact (mul_eq_zero.1 hx).resolve_left (hpos x).ne'
  have hae3 : ∀ᵐ x ∂μ, u x = 0 :=
    (withDensity_absolutelyContinuous volume _).ae_le hae2
  filter_upwards [hae3] with x hx
  exact sub_eq_zero.1 hx

end HRS.Whole.S81W2
