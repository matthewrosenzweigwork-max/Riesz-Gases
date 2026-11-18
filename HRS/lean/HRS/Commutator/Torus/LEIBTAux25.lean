import HRS.Commutator.Torus.LEIBTAux24

/-!
# LEIB-T helpers, part 25: one step (`M` fixed) of the transference inequality
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The constant `κ_p = (2d+1)^{d/p}`. -/
def leibt_kappa (d : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ := ENNReal.ofReal (((2 * d + 1 : ℝ)) ^ d) ^ (p⁻¹).toReal

lemma leibt_Lam_N'_le {η : ℝ} (hη : 0 < η) (M : ℕ) {N N' : ℝ} (hN : N = ((M : ℝ) + 1 / 2) / η)
    (hN' : N' = ((((2 * d * M + d : ℕ)) : ℝ) + 1 / 2) / η) (p : ℝ≥0∞) :
    leibt_Lam d N' p ≤ leibt_kappa d p * leibt_Lam d N p := by
  have hN0 : 0 < N := by rw [hN]; positivity
  have hle : N' ≤ (2 * d + 1 : ℝ) * N := by
    rw [hN, hN', ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hη.le
    push_cast
    nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hc : (1 : ℝ) ≤ 2 * d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hN'0 : 0 < N' := by rw [hN']; positivity
  exact (leibt_Lam_mono hN'0 hle p).trans (leibt_Lam_scale hN0 hc p)

lemma leibt_Lam_prod (r p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q) (h : p⁻¹ + q⁻¹ = r⁻¹) (hr : r ≠ 0)
    (N : ℝ) : leibt_Lam d N p * leibt_Lam d N q = leibt_Lam d N r :=
  leibt_Lam_mul p q r (by intro h0; rw [h0] at hp; simp at hp) (by intro h0; rw [h0] at hq; simp at hq)
    h hr (ENNReal.inv_ne_top.2 (by intro h0; rw [h0] at hp; simp at hp))
    (ENNReal.inv_ne_top.2 (by intro h0; rw [h0] at hq; simp at hq))

theorem leibt_step_M (hd : 1 ≤ d) (α : ℝ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (r p₁ q₁ p₂ q₂ : ℝ≥0∞) (hr : 1 < r) (hr' : r < ⊤) (hp₁ : 1 < p₁) (hq₁ : 1 < q₁)
    (hp₂ : 1 < p₂) (hq₂ : 1 < q₂) (h1 : p₁⁻¹ + q₁⁻¹ = r⁻¹) (h2 : p₂⁻¹ + q₂⁻¹ = r⁻¹)
    (Cl : ℝ≥0∞)
    (hCl : ∀ f g : SchwartzMap 𝔼 ℂ,
      eLpNorm (⇑(HRS.Commutator.Whole.XLI.Fm α (HRS.Commutator.Whole.XLI.prodS f g))) r volume ≤
        Cl * (eLpNorm (⇑(HRS.Commutator.Whole.XLI.Fm α f)) p₁ volume * eLpNorm (⇑g) q₁ volume +
          eLpNorm (⇑(HRS.Commutator.Whole.XLI.Fm α g)) p₂ volume * eLpNorm (⇑f) q₂ volume))
    (M : ℕ) (hM : 1 ≤ M) {N N' : ℝ} (hN : N = ((M : ℝ) + 1 / 2) / η)
    (hN' : N' = ((((2 * d * M + d : ℕ)) : ℝ) + 1 / 2) / η) (K : ℕ)
    {f g h Ff Fg Fh : Torus d → ℝ} (hh : ∀ x, h x = f x * g x)
    (hfc : Continuous f) (hgc : Continuous g) (hFf : Continuous Ff) (hFg : Continuous Fg)
    (hFh : Continuous Fh)
    {Sf Sg Sh : ℝ} (hSf : 0 ≤ Sf) (hSg : 0 ≤ Sg) (hSh : 0 ≤ Sh)
    (Wf Wg Wh : SchwartzMap 𝔼 ℂ)
    (hWf : ∀ y, Wf y = leibt_u η f y * leibt_chi hd (e := 1) le_rfl (N⁻¹ • y))
    (hWg : ∀ y, Wg y = leibt_u η g y * leibt_chi hd (e := 1) le_rfl (N⁻¹ • y))
    (hWh : ∀ y, Wh y = leibt_u η h y * leibt_chi hd (e := 2) (by norm_num) (N⁻¹ • y))
    (hEf : ∀ x : 𝔼, ‖HRS.Commutator.Whole.XLI.Fm α Wf x -
        ((Ff (Torus.mk (η • x)) : ℝ) : ℂ) * leibt_chi hd (e := 1) le_rfl (N⁻¹ • x)‖ ≤
        Sf * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹)
    (hEg : ∀ x : 𝔼, ‖HRS.Commutator.Whole.XLI.Fm α Wg x -
        ((Fg (Torus.mk (η • x)) : ℝ) : ℂ) * leibt_chi hd (e := 1) le_rfl (N⁻¹ • x)‖ ≤
        Sg * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹)
    (hEh : ∀ x : 𝔼, ‖HRS.Commutator.Whole.XLI.Fm α Wh x -
        ((Fh (Torus.mk (η • x)) : ℝ) : ℂ) * leibt_chi hd (e := 2) (by norm_num) (N⁻¹ • x)‖ ≤
        Sh * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) :
    eLpNorm Fh r volume ≤
      Cl * ((leibt_kappa d p₁ * eLpNorm Ff p₁ volume +
            ENNReal.ofReal (Sf * N⁻¹) * eLpNorm (leibt_wt d K) p₁ volume) *
            (leibt_kappa d q₁ * eLpNorm g q₁ volume) +
          (leibt_kappa d p₂ * eLpNorm Fg p₂ volume +
            ENNReal.ofReal (Sg * N⁻¹) * eLpNorm (leibt_wt d K) p₂ volume) *
            (leibt_kappa d q₂ * eLpNorm f q₂ volume)) +
        ENNReal.ofReal (Sh * N⁻¹) * eLpNorm (leibt_wt d K) r volume := by
  have hN0 : 0 < N := by rw [hN]; positivity
  have hN1 : 1 ≤ N := by
    rw [hN, le_div_iff₀ hη]
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hr; simp at hr
  have hWprod : Wh = HRS.Commutator.Whole.XLI.prodS Wf Wg := by
    refine SchwartzMap.ext fun y => ?_
    rw [hWh, HRS.Commutator.Whole.XLI.prodS_apply, hWf, hWg]
    unfold leibt_u
    rw [hh]
    simp only [leibt_chi_apply]
    push_cast
    ring
  have hlam := leibt_Lam_prod (d := d) r p₁ q₁ hp₁ hq₁ h1 hr0 N
  have hlam2 := leibt_Lam_prod (d := d) r p₂ q₂ hp₂ hq₂ h2 hr0 N
  have e1 : (leibt_chi hd (e := 1) le_rfl : SchwartzMap 𝔼 ℂ) = leibt_chi hd (e := 1) le_rfl := rfl
  -- the pieces
  have H3 := leibt_bessel_upper hd hη α M hN hN1 hN' (e := 1) le_rfl Wf hFf hSf K hEf hp₁.le
  have H5 := leibt_bessel_upper hd hη α M hN hN1 hN' (e := 1) le_rfl Wg hFg hSg K hEg hp₂.le
  have H1 := leibt_bessel_lower hd hη α M hN hN1 (e := 2) (by norm_num) Wh hFh hSh K hEh hr.le hr'.ne
  have hcutg : eLpNorm (⇑Wg) q₁ volume ≤ leibt_Lam d N' q₁ * eLpNorm g q₁ volume := by
    have : (⇑Wg) = fun y : 𝔼 => ((g (Torus.mk (η • y)) : ℝ) : ℂ) * leibt_chi hd (e := 1) le_rfl (N⁻¹ • y) := by
      funext y; rw [hWg]; rfl
    rw [this]
    exact leibt_cut_le hd hη M hN hN' le_rfl hgc (by intro h0; rw [h0] at hq₁; simp at hq₁)
  have hcutf : eLpNorm (⇑Wf) q₂ volume ≤ leibt_Lam d N' q₂ * eLpNorm f q₂ volume := by
    have : (⇑Wf) = fun y : 𝔼 => ((f (Torus.mk (η • y)) : ℝ) : ℂ) * leibt_chi hd (e := 1) le_rfl (N⁻¹ • y) := by
      funext y; rw [hWf]; rfl
    rw [this]
    exact leibt_cut_le hd hη M hN hN' le_rfl hfc (by intro h0; rw [h0] at hq₂; simp at hq₂)
  have hNN₁ := leibt_Lam_N'_le hη M hN hN' p₁
  have hNN₂ := leibt_Lam_N'_le hη M hN hN' q₁
  have hNN₃ := leibt_Lam_N'_le hη M hN hN' p₂
  have hNN₄ := leibt_Lam_N'_le hη M hN hN' q₂
  refine leibt_step_alg (a := leibt_Lam d N r) (A₁ := leibt_Lam d N p₁) (B₁ := leibt_Lam d N q₁)
    (A₂ := leibt_Lam d N p₂) (B₂ := leibt_Lam d N q₂) (Cl := Cl)
    (κ₁ := leibt_kappa d p₁) (κ₂ := leibt_kappa d q₁) (κ₃ := leibt_kappa d p₂) (κ₄ := leibt_kappa d q₂)
    (sF := ENNReal.ofReal (Sf * N⁻¹) * eLpNorm (leibt_wt d K) p₁ volume)
    (sG := ENNReal.ofReal (Sg * N⁻¹) * eLpNorm (leibt_wt d K) p₂ volume)
    (sH := ENNReal.ofReal (Sh * N⁻¹) * eLpNorm (leibt_wt d K) r volume)
    (P := eLpNorm (⇑(HRS.Commutator.Whole.XLI.Fm α Wh)) r volume)
    (Pf := eLpNorm (⇑(HRS.Commutator.Whole.XLI.Fm α Wf)) p₁ volume)
    (Pg := eLpNorm (⇑(HRS.Commutator.Whole.XLI.Fm α Wg)) p₂ volume)
    (Qg := eLpNorm (⇑Wg) q₁ volume) (Qf := eLpNorm (⇑Wf) q₂ volume)
    (leibt_Lam_pos hN0 r).ne' (leibt_Lam_ne_top N r) hlam.symm hlam2.symm ?_ ?_ ?_ ?_ ?_ ?_
  · calc leibt_Lam d N r * eLpNorm Fh r volume
        ≤ eLpNorm (⇑(HRS.Commutator.Whole.XLI.Fm α Wh)) r volume +
          ENNReal.ofReal (Sh * N⁻¹) * (leibt_Lam d N r * eLpNorm (leibt_wt d K) r volume) := H1
      _ = _ := by ring
  · rw [hWprod]; exact hCl Wf Wg
  · refine H3.trans ?_
    calc leibt_Lam d N' p₁ * eLpNorm Ff p₁ volume +
          ENNReal.ofReal (Sf * N⁻¹) * (leibt_Lam d N p₁ * eLpNorm (leibt_wt d K) p₁ volume)
        ≤ leibt_kappa d p₁ * leibt_Lam d N p₁ * eLpNorm Ff p₁ volume +
          ENNReal.ofReal (Sf * N⁻¹) * (leibt_Lam d N p₁ * eLpNorm (leibt_wt d K) p₁ volume) := by gcongr
      _ = _ := by ring
  · refine hcutg.trans ?_
    calc leibt_Lam d N' q₁ * eLpNorm g q₁ volume
        ≤ leibt_kappa d q₁ * leibt_Lam d N q₁ * eLpNorm g q₁ volume := by gcongr
      _ = _ := by ring
  · refine H5.trans ?_
    calc leibt_Lam d N' p₂ * eLpNorm Fg p₂ volume +
          ENNReal.ofReal (Sg * N⁻¹) * (leibt_Lam d N p₂ * eLpNorm (leibt_wt d K) p₂ volume)
        ≤ leibt_kappa d p₂ * leibt_Lam d N p₂ * eLpNorm Fg p₂ volume +
          ENNReal.ofReal (Sg * N⁻¹) * (leibt_Lam d N p₂ * eLpNorm (leibt_wt d K) p₂ volume) := by gcongr
      _ = _ := by ring
  · refine hcutf.trans ?_
    calc leibt_Lam d N' q₂ * eLpNorm f q₂ volume
        ≤ leibt_kappa d q₂ * leibt_Lam d N q₂ * eLpNorm f q₂ volume := by gcongr
      _ = _ := by ring

end HRS.Commutator.TorusNote
