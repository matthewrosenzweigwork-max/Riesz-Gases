import HRS.MS.S11Q3A4

/-!
# S11.3 / S11.4 (worker S11Q3), A5: jets and time derivative of `Γ_t = g * ρ_t`

`s11q3_Gam_jet`: the clamped family `Γ̄_t = Γ_{max t 0}` is a `s11q3_Jet2` (spatial `C²`, jointly continuous jets).
`s11q3_Gam_dt`, `s11q3_Gam_rightDeriv`: `∂_tΓ = g * D`.  `s11q3_Gam_bound`: `|g * φ|(x) ≤ B (A₀ + A₁|x|)` for Gaussian bounded `φ`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.S113BD

variable {d : ℕ} {s : ℝ}

section Gam2

variable {ρ D : ℝ → Euc d → ℝ} {c B : ℝ}

theorem s11q3_clamp_cont : Continuous fun p : ℝ × Euc d => (max p.1 0, p.2) :=
  (continuous_fst.max continuous_const).prodMk continuous_snd

theorem s11q3_clamp_mem (p : ℝ × Euc d) : (max p.1 0, p.2) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (Euc d)) :=
  Set.mk_mem_prod (Set.mem_Ici.2 (le_max_right _ _)) (mem_univ _)

theorem s11q3_Gam_jet (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) :
    s11q3_Jet2 (fun t x => s11q3_Gam d s (ρ (max t 0)) x)
      (fun t x => fderiv ℝ (s11q3_Gam d s (ρ (max t 0))) x)
      (fun t x => fderiv ℝ (fderiv ℝ (s11q3_Gam d s (ρ (max t 0)))) x) where
  c0 := (s11q3_convJoint (s := s) hd hs0 hsd R.hc R.hB R.j0 R.g0).comp_continuous s11q3_clamp_cont s11q3_clamp_mem
  c1 := by
    rw [continuous_clm_apply]
    intro e
    have hφ : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (ρ p.1) p.2 e) (Ici 0 ×ˢ univ) :=
      R.j1.clm_apply continuousOn_const
    have hb : ∀ t, 0 ≤ t → ∀ y, |fderiv ℝ (ρ t) y e| ≤ (B * ‖e‖) * Real.exp (-c * ‖y‖ ^ 2) := fun t ht y => by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (ρ t) y e‖ ≤ ‖fderiv ℝ (ρ t) y‖ * ‖e‖ := (fderiv ℝ (ρ t) y).le_opNorm e
        _ ≤ (B * Real.exp (-c * ‖y‖ ^ 2)) * ‖e‖ := mul_le_mul_of_nonneg_right (R.g1 t ht y) (norm_nonneg _)
        _ = _ := by ring
    have := (s11q3_convJoint (s := s) (φ := fun t y => fderiv ℝ (ρ t) y e) hd hs0 hsd R.hc
      (mul_nonneg R.hB (norm_nonneg e)) hφ hb).comp_continuous s11q3_clamp_cont s11q3_clamp_mem
    refine this.congr fun p => ?_
    exact (s11q3_Gam_fderiv hd hs0 hsd R (le_max_right p.1 0) p.2 e).symm
  c2 := by
    rw [continuous_clm_apply]
    intro v
    rw [continuous_clm_apply]
    intro e
    have hφ : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (ρ p.1)) p.2 v e) (Ici 0 ×ˢ univ) :=
      (R.j2.clm_apply continuousOn_const).clm_apply continuousOn_const
    have hb : ∀ t, 0 ≤ t → ∀ y, |fderiv ℝ (fderiv ℝ (ρ t)) y v e| ≤ (B * (‖v‖ * ‖e‖)) * Real.exp (-c * ‖y‖ ^ 2) :=
      fun t ht y => by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (fderiv ℝ (ρ t)) y v e‖ ≤ ‖fderiv ℝ (fderiv ℝ (ρ t)) y v‖ * ‖e‖ :=
            (fderiv ℝ (fderiv ℝ (ρ t)) y v).le_opNorm e
        _ ≤ (‖fderiv ℝ (fderiv ℝ (ρ t)) y‖ * ‖v‖) * ‖e‖ :=
            mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ (ρ t)) y).le_opNorm v) (norm_nonneg _)
        _ ≤ ((B * Real.exp (-c * ‖y‖ ^ 2)) * ‖v‖) * ‖e‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (R.g2 t ht y) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    have := (s11q3_convJoint (s := s) (φ := fun t y => fderiv ℝ (fderiv ℝ (ρ t)) y v e) hd hs0 hsd R.hc
      (mul_nonneg R.hB (mul_nonneg (norm_nonneg v) (norm_nonneg e))) hφ hb).comp_continuous
      s11q3_clamp_cont s11q3_clamp_mem
    refine this.congr fun p => ?_
    exact (s11q3_Gam_fderiv2 hd hs0 hsd R (le_max_right p.1 0) p.2 v e).symm
  h1 t z := (((s11q3_Gam_contDiff hd hs0 hsd R (le_max_right t 0)).differentiable (by norm_num)) z).hasFDerivAt
  h2 t z := ((((s11q3_Gam_contDiff hd hs0 hsd R (le_max_right t 0)).fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num)) z).hasFDerivAt

theorem s11q3_Reg.sliceD_cont (R : s11q3_Reg d ρ D c B) {t : ℝ} (ht : 0 ≤ t) : Continuous (D t) :=
  R.jD.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨Set.mem_Ici.2 ht, mem_univ _⟩)

theorem s11q3_Gam_dt (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) {t : ℝ} (ht : 0 < t)
    (x : Euc d) :
    HasDerivAt (fun τ => s11q3_Gam d s (ρ τ) x) (s11q3_Gam d s (D t) x) t := by
  have H : S113XGauss ρ D c B :=
    { hc := R.hc
      hB := R.hB
      rho_nn := fun t ht y => (R.pos t ht.le y).le
      rho_cont := fun t ht => (R.cd t ht.le).continuous
      D_cont := fun t ht => R.sliceD_cont ht.le
      rho_le := fun t ht y => R.g0 t ht.le y
      D_le := fun t ht y => R.gD t ht.le y
      deriv := fun t ht y => R.dA t ht y }
  exact s113x_Gamma_hasDerivAt hd hs0 hsd H ht x

theorem s11q3_GamD_cont (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) :
    ContinuousOn (fun p : ℝ × Euc d => s11q3_Gam d s (D p.1) p.2) (Ici 0 ×ˢ univ) :=
  s11q3_convJoint (s := s) hd hs0 hsd R.hc R.hB R.jD R.gD

theorem s11q3_Gam_cont0 (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) :
    ContinuousOn (fun p : ℝ × Euc d => s11q3_Gam d s (ρ p.1) p.2) (Ici 0 ×ˢ univ) :=
  s11q3_convJoint (s := s) hd hs0 hsd R.hc R.hB R.j0 R.g0

theorem s11q3_Gam_rightDeriv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) (x : Euc d) :
    ∀ t, 0 ≤ t → HasDerivWithinAt (fun τ => s11q3_Gam d s (ρ τ) x) (s11q3_Gam d s (D t) x) (Ici t) t := by
  have hm : MapsTo (fun τ : ℝ => (τ, x)) (Ici 0) (Ici (0 : ℝ) ×ˢ (univ : Set (Euc d))) :=
    fun τ hτ => ⟨hτ, mem_univ _⟩
  have hc : Continuous fun τ : ℝ => (τ, x) := continuous_id.prodMk continuous_const
  exact s11q3_rightDeriv ((s11q3_Gam_cont0 hd hs0 hsd R).comp hc.continuousOn hm)
    (fun t ht => s11q3_Gam_dt hd hs0 hsd R ht x) ((s11q3_GamD_cont hd hs0 hsd R).comp hc.continuousOn hm)

theorem s11q3_Gam_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) :
    ∃ A0 A1 : ℝ, 0 ≤ A0 ∧ 0 ≤ A1 ∧ ∀ t, 0 ≤ t → ∀ x : Euc d,
      |s11q3_Gam d s (ρ t) x| ≤ B * (A0 + A1 * ‖x‖) ∧ |s11q3_Gam d s (D t) x| ≤ B * (A0 + A1 * ‖x‖) := by
  obtain ⟨A0, A1, hA0, hA1, hbd⟩ := s113x_conv_bound (s := s) hd hs0 hsd R.hc
  exact ⟨A0, A1, hA0, hA1, fun t ht x =>
    ⟨(hbd B (ρ t) R.hB (R.cd t ht).continuous (R.g0 t ht) x).2, (hbd B (D t) R.hB (R.sliceD_cont ht) (R.gD t ht) x).2⟩⟩

end Gam2

end HRS.MS.S11Q3

end
