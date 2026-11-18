import HRS.PDE.D3PhiPAux9

/-!
# D3PHIP, helper 10: the integrated variable-exponent identity (packet A)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3pp_identity (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w)
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) {p : ℝ → ℝ}
    (hpac : AbsolutelyContinuousOnInterval p 0 T) (hp1 : ∀ r ∈ Set.Icc 0 T, 1 < p r) :
    ∀ t ∈ Set.Icc 0 T,
      IntegrableOn (fun r => d3phi_dir κ U ψ w p r) (Set.Icc 0 t) ∧
      IntegrableOn (fun r => (p r - 1) * d3phi_Sh κ U ψ ψt w p r) (Set.Icc 0 t) ∧
      IntegrableOn (fun r => deriv p r * d3phi_Ylog κ U ψ w p r) (Set.Icc 0 t) ∧
      d3phi_Y κ U ψ w p t + ∫ r in Set.Icc 0 t, d3phi_dir κ U ψ w p r
        = d3phi_Y κ U ψ w p 0 + ∫ r in Set.Icc 0 t,
            ((p r - 1) * d3phi_Sh κ U ψ ψt w p r + deriv p r * d3phi_Ylog κ U ψ w p r) := by
  intro t ht
  have hT0 := hT.le
  have hpc : ContinuousOn p (Set.Icc 0 T) := by simpa [Set.uIcc_of_le hT0] using hpac.continuousOn
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
  have hDir : IntegrableOn (fun r => d3phi_dir κ U ψ w p r) (Set.Icc 0 t) :=
    ((d3pp_dir_contOn hκ hU hw hψ hpc hp1).mono hsub).integrableOn_Icc
  have hSh : IntegrableOn (fun r => (p r - 1) * d3phi_Sh κ U ψ ψt w p r) (Set.Icc 0 t) :=
    (((hpc.sub continuousOn_const).mul (d3pp_Sh_contOn hκ hU hT hw hψ hpc)).mono hsub).integrableOn_Icc
  have hpint : IntegrableOn (deriv p) (Set.Icc 0 t) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hT0).1 hpac.intervalIntegrable_deriv).mono_set hsub
  have hYl : IntegrableOn (fun r => deriv p r * d3phi_Ylog κ U ψ w p r) (Set.Icc 0 t) :=
    hpint.mul_continuousOn ((d3pp_Ylog_contOn hκ hU hw hψ hpc).mono hsub) isCompact_Icc
  refine ⟨hDir, hSh, hYl, ?_⟩
  have hY := d3pp_Y_diff hκ hU hT hw hψ hpac ht
  have hinner : ∫ r in (0 : ℝ)..t, ∫ x, d3pp_D κ U ψ ψt w p (deriv p) r x ∂(d1_gibbsMeasure κ U) =
      ∫ r in (0 : ℝ)..t, (-d3phi_dir κ U ψ w p r +
        ((p r - 1) * d3phi_Sh κ U ψ ψt w p r + deriv p r * d3phi_Ylog κ U ψ w p r)) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht.1] at hr
    have := d3pp_inner hκ hU hw hψ (hsub hr) p (deriv p) (by linarith [hp1 r (hsub hr)])
    beta_reduce
    rw [this]
    ring
  have j1 : IntegrableOn (fun r => -d3phi_dir κ U ψ w p r) (Set.Icc 0 t) := hDir.neg
  have j2 : IntegrableOn (fun r => (p r - 1) * d3phi_Sh κ U ψ ψt w p r +
      deriv p r * d3phi_Ylog κ U ψ w p r) (Set.Icc 0 t) := hSh.add hYl
  rw [hinner, intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc,
    integral_add j1 j2, integral_neg] at hY
  linarith

end HRS
