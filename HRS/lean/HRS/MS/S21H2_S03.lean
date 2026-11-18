import HRS.MS.S21H2_S03A
import HRS.MS.S21H2_S02
import HRS.MS.S21F_S01
import HRS.MS.PoisFinal

/-!
# S21H2, packet R26-T3.S03: differentiated Poisson equation produces one screened velocity

For a centered response `r = a_q` (`r26t3_response_smooth`), the affine Poisson theorem
`affine_poisson_deriv` (drift `-(βa) x + B x` from `r26t3_initial_drift`, invariant reference)
gives `χ` with `poissonOp b χ = r` and derivative bounds of orders `1..k+1`; `v = ∇χ` is the
screened velocity. The divergence identity `movDiv (ρ ∇χ) = ⟨∇ρ, ∇χ⟩ + ρ Δχ` (part A) and
`∇ρ = ρ (−βa x + B x)` (from `log ρ`) turn `poissonOp b χ = r` into `−div(ρ v) = ρ r`.
Helper names carry the prefix `s21h2_s03_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T3

open HRS HRS.Whole

theorem s21h2_s03_cbNorm_nonneg {d k : ℕ} (Φ : Euc d → ℝ) : 0 ≤ cbNorm k Φ := by
  unfold cbNorm
  exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _

theorem s21h2_s03_iter_le {d k j : ℕ} {Φ : Euc d → ℝ} (h : MemCb k Φ) (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j Φ x‖ ≤ cbNorm k Φ := by
  have hb : BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ j Φ z‖) := h.2 j hj
  have h0 : ‖iteratedFDeriv ℝ j Φ x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ := le_ciSup hb x
  have hsum : (⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) ≤ cbNorm k Φ := by
    unfold cbNorm
    exact Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i Φ z‖)
      (fun i _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  linarith

theorem s21h2_s03_grad_cd {d j : ℕ} {χ : Euc d → ℝ} (hχ : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) χ) :
    ContDiff ℝ (j : WithTop ℕ∞) (gradient χ) := by
  have hfd : ContDiff ℝ (j : WithTop ℕ∞) (fderiv ℝ χ) := hχ.fderiv_right (m := j) (by norm_cast)
  have e : gradient χ = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ χ := rfl
  rw [e]
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv.contDiff).comp hfd

/-- Smoothness and positivity of the initial density (the `GapPkg` of `r26t3_initial_drift`). -/
theorem s21h2_s03_smooth {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (R.ρ 0) ∧ ∀ x, 0 < R.ρ 0 x := by
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
  exact ⟨hGap.smooth, hGap.pos⟩

theorem r26t3_transport_one {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Euc p.d → ℝ, MemCb (r26t3_J p.d) q →
      ∃ v : Euc p.d → Euc p.d,
        HasCbBound (r26t3_k p.d) (C * cbNorm (r26t3_J p.d) q) v ∧
        (∀ x, -(movDiv (fun y => R.ρ 0 y • v y) x) = R.ρ 0 x * r26t3_a R q x) := by
  have hd := p.hd
  have hkd : r26t3_k p.d = 2 * p.d + 10 := rfl
  obtain ⟨hsm, hpos⟩ := s21h2_s03_smooth hδ hδh R
  obtain ⟨B, Mb, m₂, hB, hgrad, hinv, hint, hmom⟩ :=
    r26t3_initial_drift hδ hδh R (r26t3_k p.d + 1)
  obtain ⟨Cm, hCm⟩ := HRS.MS.PoisFinal.affine_poisson_deriv_proof (d := p.d) (by omega)
    (p.β * p.a) Mb m₂ (mul_pos p.hβ p.ha) (r26t3_k p.d + 1) (by omega)
  obtain ⟨C₂, hC₂0, hR⟩ := r26t3_response_smooth hδ hδh R hγ
  refine ⟨|Cm| * C₂, mul_nonneg (abs_nonneg _) hC₂0, fun q hq => ?_⟩
  obtain ⟨hRa, hRc, hRL, -⟩ := hR q hq
  have hD0 : 0 ≤ C₂ * cbNorm (r26t3_J p.d) q := mul_nonneg hC₂0 (s21h2_s03_cbNorm_nonneg _)
  have hbd : ∀ j, 1 ≤ j → j ≤ r26t3_k p.d + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (r26t3_a R q) x‖ ≤ C₂ * cbNorm (r26t3_J p.d) q := fun j _ hj x =>
    (s21h2_s03_iter_le hRa (by omega) x).trans hRc
  have hr : ContDiff ℝ ((r26t3_k p.d + 1 : ℕ) : WithTop ℕ∞) (r26t3_a R q) :=
    hRa.1.of_le (by norm_cast; omega)
  obtain ⟨χ, hχC, -, -, hχP, hχD⟩ :=
    hCm B hB (r26t3_mu R 0) hinv hint hmom (r26t3_a R q) hr _ hbd hRL.2
  have hχ1 : ContDiff ℝ ((r26t3_k p.d + 1 : ℕ) : WithTop ℕ∞) χ := hχC
  have hχ2 : ContDiff ℝ 2 χ := hχC.of_le (by norm_cast; omega)
  have hρ1 : ContDiff ℝ 1 (R.ρ 0) := hsm.of_le (by norm_cast)
  refine ⟨gradient χ, ?_, fun x => ?_⟩
  · unfold HasCbBound
    refine ⟨s21h2_s03_grad_cd hχ1, fun j hj x => ?_⟩
    have hj1 : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) χ := hχC.of_le (by norm_cast; omega)
    rw [s21h2_s03_grad_norm hj1 x]
    have h := hχD (j + 1) (by omega) (by omega) x
    calc ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ Cm * (C₂ * cbNorm (r26t3_J p.d) q) := h
      _ ≤ |Cm| * (C₂ * cbNorm (r26t3_J p.d) q) :=
          mul_le_mul_of_nonneg_right (le_abs_self Cm) hD0
      _ = |Cm| * C₂ * cbNorm (r26t3_J p.d) q := by ring
  · have hgρ : gradient (R.ρ 0) x = R.ρ 0 x • (-(p.β * p.a) • x + B x) := by
      rw [← hgrad x, s21f_gradient_log hsm hpos x, smul_smul, mul_inv_cancel₀ (hpos x).ne', one_smul]
    have hP := hχP x
    simp only [poissonOp] at hP
    rw [s21h2_s03_movDiv hρ1 hχ2 x, hgρ, real_inner_smul_left]
    linear_combination (R.ρ 0 x) * hP

end HRS.MS.R26T3
