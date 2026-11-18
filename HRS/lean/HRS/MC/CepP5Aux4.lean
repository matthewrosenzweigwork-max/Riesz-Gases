import HRS.MC.CepP5Aux3

/-!
# Packet P5, Aux4: integration by parts against a compactly supported test function
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP5

open HRS HRS.MC.CepP3 HRS.MC.CepP4

variable {d N : ℕ}

theorem integrable_mul_O {O : Set (ℝ × (Fin N → Euc d))} {φ ψ : ℝ × (Fin N → Euc d) → ℝ}
    (hφ : ContinuousOn φ O) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψO : tsupport ψ ⊆ O) : Integrable (fun p => φ p * ψ p) := by
  haveI := isAddHaar_volume_cov (d := d) (N := N)
  have hK : IsCompact (tsupport ψ) := hψc
  have h1 : IntegrableOn (fun p => φ p * ψ p) (tsupport ψ) :=
    ((hφ.mono hψO).mul hψ.continuousOn).integrableOn_compact hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  exact fun p hp => subset_tsupport ψ (right_ne_zero_of_mul hp)

theorem ibp_O {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O) {u F : ℝ × (Fin N → Euc d) → ℝ}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u O) (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFc : HasCompactSupport F) (hFO : tsupport F ⊆ O) (v : ℝ × (Fin N → Euc d)) :
    ∫ p, u p * fderiv ℝ F p v = - ∫ p, fderiv ℝ u p v * F p := by
  haveI := isAddHaar_volume_cov (d := d) (N := N)
  have hF' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) := hF.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  have hFv : Continuous (fun p => fderiv ℝ F p v) := hF'.continuous.clm_apply continuous_const
  have hc1 : ContinuousOn (fun p => fderiv ℝ u p v) O :=
    (hu.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
  symm
  refine (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := u) (g := F) (v := v) ?_ ?_ ?_ ?_ ?_).symm
  · exact integrable_mul_O hc1 hF.continuous hFc hFO
  · exact integrable_mul_O hu.continuousOn hFv (hFc.fderiv_apply ℝ v)
      ((tsupport_fderiv_apply_subset ℝ v).trans hFO)
  · exact integrable_mul_O hu.continuousOn hF.continuous hFc hFO
  · intro x hx
    exact (hu.contDiffAt (hO.mem_nhds (hFO hx))).differentiableAt (by simp)
  · intro x _
    exact hF.differentiable (by simp) x

/-- Test functions: smooth, compactly supported inside `O`. -/
structure CK (O : Set (ℝ × (Fin N → Euc d))) (F : ℝ × (Fin N → Euc d) → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F
  compact : HasCompactSupport F
  sub : tsupport F ⊆ O

theorem CK.fderiv_apply {O : Set (ℝ × (Fin N → Euc d))} {F : ℝ × (Fin N → Euc d) → ℝ} (h : CK O F)
    (v : ℝ × (Fin N → Euc d)) : CK O (fun p => fderiv ℝ F p v) :=
  ⟨(h.smooth.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const,
    h.compact.fderiv_apply ℝ v, (tsupport_fderiv_apply_subset ℝ v).trans h.sub⟩

theorem contDiffOn_fderiv_apply {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O)
    {u : ℝ × (Fin N → Euc d) → ℝ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u O)
    (v : ℝ × (Fin N → Euc d)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => fderiv ℝ u p v) O :=
  (hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

/-- Second-order integration by parts. -/
theorem ibp2_O {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O) {u F : ℝ × (Fin N → Euc d) → ℝ}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u O) (hF : CK O F) (v : ℝ × (Fin N → Euc d)) :
    ∫ p, u p * fderiv ℝ (fderiv ℝ F) p v v = ∫ p, fderiv ℝ (fderiv ℝ u) p v v * F p := by
  have hF1 := hF.fderiv_apply v
  have h1 := ibp_O hO hu hF1.smooth hF1.compact hF1.sub v
  have hu1 := contDiffOn_fderiv_apply hO hu v
  have h2 := ibp_O hO hu1 hF.smooth hF.compact hF.sub v
  -- identify the derivatives
  have e1 : ∀ p, fderiv ℝ (fun q => fderiv ℝ F q v) p v = fderiv ℝ (fderiv ℝ F) p v v := by
    intro p
    have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
      (hF.smooth.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).differentiable (by simp) p
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  have e2 : ∀ p ∈ O, fderiv ℝ (fun q => fderiv ℝ u q v) p v = fderiv ℝ (fderiv ℝ u) p v v := by
    intro p hp
    have hd : DifferentiableAt ℝ (fderiv ℝ u) p :=
      ((hu.fderiv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hO (by simp)).contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  simp only [e1] at h1
  calc ∫ p, u p * fderiv ℝ (fderiv ℝ F) p v v = - ∫ p, fderiv ℝ u p v * fderiv ℝ F p v := h1
    _ = - ∫ p, fderiv ℝ F p v * fderiv ℝ u p v := by simp only [mul_comm]
    _ = ∫ p, fderiv ℝ (fun q => fderiv ℝ u q v) p v * F p := by
        rw [show (∫ p, fderiv ℝ F p v * fderiv ℝ u p v) = ∫ p, fderiv ℝ u p v * fderiv ℝ F p v from
          by simp only [mul_comm]] at *
        have := h2
        linarith
    _ = ∫ p, fderiv ℝ (fderiv ℝ u) p v v * F p := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        by_cases hp : p ∈ O
        · simp only [e2 p hp]
        · have : F p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hF.sub h))
          simp [this]

end HRS.MC.CepP5
