import HRS.MS.DerCorAux2
import HRS.MS.GapRefAux1
import HRS.MS.TiltAux14
import HRS.MS.MovThermAux1
import HRS.MS.S21F_D02

/-!
# S21F, packet R26-T3.S01: bounded affine drift and invariance of the perturbed reference

`ρ₀ = (1+εψ)ρ_β` is in the uniform tilt class (`UnifRef`, as in `r26t3_reference_data`); the merged `s48_ref_data_unif` supplies a
`GapRef` drift `B` (`∇ρ₀ = ρ₀(-aβ x + B)`, `B ∈ C_b^n` for every `n` by `GapRef.cb`).  Then `∇log ρ₀ = -aβ x + B`,
`gap_invariant` gives infinitesimal invariance, `gap_moment` the second moment.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_unifref_init (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ) :
    HRS.MS.S48.UnifRef p.d p.s p.a p.β δ (R.ρ 0) := by
  have _ := hδ
  have hd := p.hd
  have hsd : p.s < p.d := by
    have := p.hs
    have : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
    linarith
  have hρβ : R.ρβ = thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq hd p.hs0 hsd p.ha p.hβ R.thermal
  have hA := R.admissible
  have hRes := R.resulting
  have hosc : 0 ≤ oscNorm (102 * (p.d : ℝ) + 1020) (fun x => R.ε * Real.sqrt (R.ρβ x) * R.ψ x) :=
    Real.sqrt_nonneg _
  have hcb : cbNorm (100 * p.d + 1001) (fun x => R.ε * R.ψ x) ≤ δ := by
    have := hA.small
    linarith
  have hcb0 := HRS.MS.S48.s48_cbu_bound hA.smooth hA.compactSupport R.ε δ (100 * p.d + 1001) hcb 0
    (Nat.zero_le _)
  have htilt : IsTiltData p.d p.s p.a p.β R.ψ R.ε :=
    ⟨hA.smooth, hA.compactSupport, by rw [← hρβ]; exact hA.meanZero, fun x => by
      have := hcb0 x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      linarith⟩
  exact Or.inr ⟨R.ε, R.ψ, htilt, hcb, by rw [hRes.init, hρβ]⟩

theorem s21f_gradient_log {d : ℕ} {ρ : Euc d → ℝ} (hs : ContDiff ℝ ∞ ρ) (hp : ∀ x, 0 < ρ x) (x : Euc d) :
    gradient (fun y => Real.log (ρ y)) x = (ρ x)⁻¹ • gradient ρ x := by
  have hd : DifferentiableAt ℝ ρ x := (hs.differentiable (by norm_num)) x
  have h := hd.hasFDerivAt.log (hp x).ne'
  unfold gradient
  rw [h.fderiv, map_smul]

theorem r26t3_initial_drift {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (n : ℕ) :
    ∃ B : Euc p.d → Euc p.d, ∃ Mb m₂ : ℝ,
      HasCbBound n Mb B ∧
      (∀ x, gradient (fun y => Real.log (R.ρ 0 y)) x = -(p.β * p.a) • x + B x) ∧
      IsInvariantMeasure (fun x => -(p.β * p.a) • x + B x) (r26t3_mu R 0) ∧
      Integrable (fun x => ‖x‖ ^ 2) (r26t3_mu R 0) ∧
      ∫ x, ‖x‖ ^ 2 ∂(r26t3_mu R 0) ≤ m₂ := by
  have hd := p.hd
  have hsd : p.s < p.d := by
    have := p.hs
    have : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
    linarith
  have hU0 := s21f_unifref_init p hδ hδh R
  obtain ⟨c, M₀, m₂, hc, hM₀, hpk⟩ := HRS.MS.S48.s48_ref_data_unif hd p.hs0 hsd (am := p.a) (ap := p.a)
    (βm := p.β) (βp := p.β) p.ha p.hβ le_rfl le_rfl δ
  obtain ⟨S, Mb, hS⟩ := hpk 0 0 (by omega)
  have hp := hS p.a p.β le_rfl le_rfl le_rfl le_rfl (R.ρ 0) hU0
  obtain ⟨B, hGap, -⟩ := hp.drift
  obtain ⟨Mbn, hMbn⟩ := hGap.cb n
  obtain ⟨-, hint, hmom⟩ := HRS.MS.Gap.gap_moment hGap
  have hq : p.a * p.β = p.β * p.a := mul_comm _ _
  refine ⟨B, Mbn, m₂, hMbn, fun x => ?_, ?_, hint, ?_⟩
  · rw [s21f_gradient_log hGap.smooth hGap.pos, hGap.grad, smul_smul, inv_mul_cancel₀ (hGap.pos x).ne',
      one_smul, hq]
  · have := HRS.MS.Gap.gap_invariant hGap
    rw [hq] at this
    exact this
  · show ∫ x, ‖x‖ ^ 2 ∂(HRS.Whole.withDensityReal (R.ρ 0)) ≤ m₂
    rw [hmom]; exact hp.moment

end HRS.MS.R26T3
