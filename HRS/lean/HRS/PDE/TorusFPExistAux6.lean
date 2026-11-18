import HRS.PDE.TorusFPExistAux5

/-!
# D1 existence, helper 6: the family of measures `μ_t`
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

section Family

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
  (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀]

theorem d1_integrable_P {t : ℝ} (ht : 0 ≤ t) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) :
    Integrable (d1_P hn hκ hU t ψ) μ₀ :=
  (d1_P_continuous hn hκ hU ht hψ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The linear functional `ψ ↦ ∫ U^{0,t} ψ dμ₀` on smooth functions. -/
def d1_lam {t : ℝ} (ht : 0 ≤ t) : d1_smoothSub n →ₗ[ℝ] ℝ where
  toFun g := ∫ x, d1_P hn hκ hU t (g : C(Torus n, ℝ)) x ∂μ₀
  map_add' a b := by
    have ha : Torus.IsSmooth (a : Torus n → ℝ) := a.2
    have hb : Torus.IsSmooth (b : Torus n → ℝ) := b.2
    have e : ∀ x, d1_P hn hκ hU t ((a + b : d1_smoothSub n) : C(Torus n, ℝ)) x =
        d1_P hn hκ hU t a x + d1_P hn hκ hU t b x := by
      intro x
      have := d1_P_lincomb hn hκ hU ht ha hb 1 1 x
      simp only [one_mul] at this
      exact this
    simp only [e]
    exact integral_add (d1_integrable_P hn hκ hU μ₀ ht ha) (d1_integrable_P hn hκ hU μ₀ ht hb)
  map_smul' c a := by
    have ha : Torus.IsSmooth (a : Torus n → ℝ) := a.2
    have e : ∀ x, d1_P hn hκ hU t ((c • a : d1_smoothSub n) : C(Torus n, ℝ)) x =
        c * d1_P hn hκ hU t a x := by
      intro x
      have := d1_P_lincomb hn hκ hU ht ha (d1_isSmooth_const (n := n) 0) c 0 x
      rw [d1_P_const hn hκ hU ht] at this
      simp only [mul_zero, add_zero] at this
      exact this
    simp only [e, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul c _

theorem d1_lam_apply {t : ℝ} (ht : 0 ≤ t) (g : d1_smoothSub n) :
    d1_lam hn hκ hU μ₀ ht g = ∫ x, d1_P hn hκ hU t (g : C(Torus n, ℝ)) x ∂μ₀ := rfl

theorem d1_P_abs_le_norm {t : ℝ} (ht : 0 ≤ t) (g : d1_smoothSub n) (x : Torus n) :
    |d1_P hn hκ hU t (g : C(Torus n, ℝ)) x| ≤ ‖(g : C(Torus n, ℝ))‖ := by
  have hg : Torus.IsSmooth (g : Torus n → ℝ) := g.2
  have h := d1_P_abs_le hn hκ hU ht hg (d1_isSmooth_const (n := n) 0)
    (c := ‖(g : C(Torus n, ℝ))‖) (fun x => by
      simpa using (g : C(Torus n, ℝ)).norm_coe_le_norm x) x
  rw [d1_P_const hn hκ hU ht] at h
  simpa using h

theorem d1_exists_measure {t : ℝ} (ht : 0 ≤ t) :
    ∃ ν : Measure (Torus n), IsProbabilityMeasure ν ∧
      ∀ ψ : Torus n → ℝ, Torus.IsSmooth ψ → ∫ x, ψ x ∂ν = ∫ x, d1_P hn hκ hU t ψ x ∂μ₀ := by
  have hb : ∀ g : d1_smoothSub n, |d1_lam hn hκ hU μ₀ ht g| ≤ ‖(g : C(Torus n, ℝ))‖ := by
    intro g
    rw [d1_lam_apply]
    calc |∫ x, d1_P hn hκ hU t (g : C(Torus n, ℝ)) x ∂μ₀|
        ≤ ∫ x, |d1_P hn hκ hU t (g : C(Torus n, ℝ)) x| ∂μ₀ := abs_integral_le_integral_abs
      _ ≤ ∫ _x, ‖(g : C(Torus n, ℝ))‖ ∂μ₀ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (integrable_const _)
            (ae_of_all _ fun x => d1_P_abs_le_norm hn hκ hU ht g x)
      _ = ‖(g : C(Torus n, ℝ))‖ := by simp
  have hp : ∀ g : d1_smoothSub n, (∀ x, 0 ≤ (g : C(Torus n, ℝ)) x) → 0 ≤ d1_lam hn hκ hU μ₀ ht g := by
    intro g hg
    rw [d1_lam_apply]
    exact integral_nonneg fun x => d1_P_nonneg hn hκ hU ht g.2 hg x
  obtain ⟨Λ, hΛb, hΛe, hΛp⟩ := d1_extend_functional (d1_lam hn hκ hU μ₀ ht) hb hp
  have h1 : Λ 1 = 1 := by
    have h1s : (1 : C(Torus n, ℝ)) ∈ d1_smoothSub n := d1_isSmooth_const (n := n) 1
    have := hΛe ⟨1, h1s⟩
    have e : ∀ x, d1_P hn hκ hU t ((((⟨1, h1s⟩ : d1_smoothSub n) : C(Torus n, ℝ))) : Torus n → ℝ) x = 1 :=
      fun x => d1_P_const hn hκ hU ht 1 x
    have h3 : Λ 1 = d1_lam hn hκ hU μ₀ ht ⟨1, h1s⟩ := this
    rw [h3, d1_lam_apply]
    simp only [e]
    simp
  obtain ⟨ν, hν, hνint⟩ := d1_exists_measure_of_functional Λ hΛp h1
  refine ⟨ν, hν, fun ψ hψ => ?_⟩
  have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
  have := hνint ⟨ψ, hψc⟩
  have h2 := hΛe ⟨⟨ψ, hψc⟩, hψ⟩
  simp only [Submodule.coe_mk] at h2
  rw [h2, d1_lam_apply] at this
  exact this

/-- The family `t ↦ μ_t`: `μ₀` for `t ≤ 0`. -/
def d1_mu (t : ℝ) : Measure (Torus n) :=
  open Classical in
  if h : 0 < t then Classical.choose (d1_exists_measure hn hκ hU μ₀ h.le) else μ₀

theorem d1_mu_of_nonpos {t : ℝ} (ht : t ≤ 0) : d1_mu hn hκ hU μ₀ t = μ₀ := by
  unfold d1_mu
  rw [dif_neg (not_lt.2 ht)]

theorem d1_mu_prob (t : ℝ) : IsProbabilityMeasure (d1_mu hn hκ hU μ₀ t) := by
  unfold d1_mu
  by_cases h : 0 < t
  · rw [dif_pos h]; exact (Classical.choose_spec (d1_exists_measure hn hκ hU μ₀ h.le)).1
  · rw [dif_neg h]; infer_instance

theorem d1_mu_integral {t : ℝ} (ht : 0 ≤ t) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∫ x, ψ x ∂(d1_mu hn hκ hU μ₀ t) = ∫ x, d1_P hn hκ hU t ψ x ∂μ₀ := by
  rcases ht.eq_or_lt with rfl | h
  · rw [d1_mu_of_nonpos hn hκ hU μ₀ le_rfl]
    simp [d1_P]
  · unfold d1_mu
    rw [dif_pos h]
    exact (Classical.choose_spec (d1_exists_measure hn hκ hU μ₀ h.le)).2 ψ hψ

end Family

end HRS
