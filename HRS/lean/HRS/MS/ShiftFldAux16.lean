import HRS.MS.ShiftFldAux15

/-!
# S79P: the nonlocal term as a Riesz convolution (a.e.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

/-- A continuous cutoff, `= 1` on `closedBall 0 R`, supported in `closedBall 0 (R+1)`. -/
def s79g_cut (R : ℝ) (x : Euc d) : ℝ := max 0 (min 1 (R + 1 - ‖x‖))

theorem s79g_cut_cont (R : ℝ) : Continuous (s79g_cut (d := d) R) := by
  unfold s79g_cut; fun_prop

theorem s79g_cut_supp (R : ℝ) : HasCompactSupport (s79g_cut (d := d) R) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) (R + 1)) ?_
  intro x hx
  by_contra hn
  have : R + 1 < ‖x‖ := by simpa using hn
  apply hx
  unfold s79g_cut
  have : min 1 (R + 1 - ‖x‖) ≤ 0 := (min_le_right _ _).trans (by linarith)
  exact max_eq_left this

theorem s79g_cut_one {R : ℝ} {x : Euc d} (hx : ‖x‖ ≤ R) : s79g_cut R x = 1 := by
  unfold s79g_cut
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem s79g_nl_ae (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u : Euc d → ℝ} (hu : HRS.MemCb 2 u)
    (hc : Continuous (nlTermRd (quadraticGradientDyn d s a β) (thermalDensity d s a β) u)) :
    ∀ᵐ x, nlTermRd (quadraticGradientDyn d s a β) (thermalDensity d s a β) u x =
      ∫ y, rieszKernel d s (x - y) * (thermalDensity d s a β y *
        Aop d s a β (thermalDensity d s a β) u y) := by
  obtain ⟨hhc, hhi⟩ := s79g_h_integrable hd hs.le hsd ha hβ hρ hu
  set h : Euc d → ℝ := fun y => thermalDensity d s a β y * Aop d s a β (thermalDensity d s a β) u y
    with hh
  set G : Euc d → ℝ := fun x => ∫ y, rieszKernel d s (x - y) * h y with hG
  have hFub := fun {φ : Euc d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) =>
    s79g_fubini hs hsd hφ hφc hhc hhi
  have hGloc : LocallyIntegrable G := by
    rw [locallyIntegrable_iff]
    intro k hk
    obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall (0 : Euc d)
    have hI := (hFub (s79g_cut_cont (d := d) R) (s79g_cut_supp R)).2.1
    have hI' : IntegrableOn (fun x => s79g_cut R x * G x) k := hI.integrableOn
    refine hI'.congr_fun (fun x hx => ?_) hk.isClosed.measurableSet
    have : ‖x‖ ≤ R := by simpa using hR hx
    simp only [s79g_cut_one this, one_mul]
  have hNloc : LocallyIntegrable
      (nlTermRd (quadraticGradientDyn d s a β) (thermalDensity d s a β) u) := hc.locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hNloc hGloc (fun ψ hψ hψc => ?_)
  have hψ2 : ContDiff ℝ 2 ψ := by exact_mod_cast contDiff_infty.1 hψ 2
  simp only [smul_eq_mul]
  rw [s79g_nlw hd hs.le hsd ha hβ hu hψ2 hψc, s79g_nlw2 hd hs.le hsd ha hβ hρ hu hψ2 hψc]
  rw [(hFub hψ2.continuous hψc).2.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hh]
  ring

end HRS.MS.S79G
