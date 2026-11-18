import HRS.Whole.Static
import HRS.MS.WlStatic2

/-!
# HRS.MS.WlStaticTie -- `r2_log_static` and `r2_log_static_commutator` (WL-11)

Statements exactly the frozen `HRS.Whole.r2_log_static` and `HRS.Whole.r2_log_static_commutator`
(no adjustment); conjuncts 1-3 are `wl_gibbsWellDefined`, `wl_static_linear`, `wl_hasLogMarginalDensityBounds`,
conjunct 4 is `wl11_quadratic_variance_bound`; the commutator clause is conjunct 4 with `B = Λ`,
`h = commutatorKernel d 0 v` (`commutatorKernel_log_isBounded_proof`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole

/-- Monotonicity of `HasLogMarginalDensityBounds` in the constant (it enters both the sup bound and the rate). -/
theorem wl11_hlmdb_mono {d : ℕ} {π μ : Measure (Euc d)} {C C' β : ℝ} {N : ℕ}
    (H : HRS.Whole.HasLogMarginalDensityBounds π μ C β N) (hC : C ≤ C') :
    HRS.Whole.HasLogMarginalDensityBounds π μ C' β N := by
  obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := H
  refine ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, (hφb x).2.trans ?_⟩, hφ2, hφn.trans ?_⟩
  · refine mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _)
  · have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact div_le_div_of_nonneg_right hC this

/-- **Theorem S3.5 `W:thm:r2-log-static`**. -/
theorem r2_log_static_proof : type_of% @HRS.Whole.r2_log_static := by
  intro d hd βm βp A hβm hβ
  obtain ⟨C2, h2⟩ := wl_static_linear hd βm βp A hβm hβ
  obtain ⟨C3, h3⟩ := wl_hasLogMarginalDensityBounds hd βm βp A hβm hβ
  obtain ⟨C4, h4⟩ := wl11_quadratic_variance_bound hd βm βp A hβm hβ
  refine ⟨max C2 (max C3 C4), fun ρ hρ hA β hβmem N hN => ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hC2 : C2 ≤ max C2 (max C3 C4) := le_max_left _ _
  have hC3 : C3 ≤ max C2 (max C3 C4) := (le_max_left _ _).trans (le_max_right _ _)
  have hC4 : C4 ≤ max C2 (max C3 C4) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨wl_gibbsWellDefined hd A ρ hρ hA β (hβm.trans_le hβmem.1).le N (by omega), ?_, ?_, ?_⟩
  · intro f hf
    refine (h2 ρ hρ hA β hβmem N hN f hf).trans (ENNReal.ofReal_le_ofReal ?_)
    have hI : 0 ≤ ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) := integral_nonneg fun x => sq_nonneg _
    gcongr
  · exact wl11_hlmdb_mono (h3 ρ hρ hA β hβmem N hN) hC3
  · intro B h hBK
    obtain ⟨h4a, h4b⟩ := h4 ρ hρ hA β hβmem N hN B h hBK
    exact ⟨HRS.MS.Wr.wr14a_qvb_mono (by gcongr) h4a, HRS.MS.Wr.wr14a_qvb_mono (by gcongr) h4b⟩

/-- **Theorem S3.5, commutator clause**. -/
theorem r2_log_static_commutator_proof : type_of% @HRS.Whole.r2_log_static_commutator := by
  intro d hd βm βp A hβm hβ
  obtain ⟨C4, h4⟩ := wl11_quadratic_variance_bound hd βm βp A hβm hβ
  refine ⟨C4, fun ρ hρ hA β hβmem N hN Λ v hv => ?_⟩
  exact h4 ρ hρ hA β hβmem N hN (Λ : ℝ) (HRS.Whole.commutatorKernel d 0 v)
    (HRS.MS.Comm.commutatorKernel_log_isBounded_proof (by omega) Λ v hv)

example := (@r2_log_static_proof : type_of% @HRS.Whole.r2_log_static)

example := (@r2_log_static_commutator_proof : type_of% @HRS.Whole.r2_log_static_commutator)

end HRS.MS.Wl
