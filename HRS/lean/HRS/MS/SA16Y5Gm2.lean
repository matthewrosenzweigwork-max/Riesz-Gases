import HRS.MS.SA16Y5Gm1
import HRS.MS.SA16Y5Lb4

/-!
# S.A.16 (SA16Y5) Gm2: `wrep (Γ_a y) = g_a ⋆ F` when `wrep y = F` is continuous and bounded (K3 helper)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Gm2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y5_Gam_wrep {a : ℝ} (ha : 0 < a) (k : ℕ) (y : WmpSpace d k p) {F : Euc d → ℝ}
    (hF : wrep d k p y =ᵐ[volume] F) (hFc : Continuous F) {B : ℝ} (hB : ∀ x, |F x| ≤ B) :
    wrep d (k + 1) p (sa16r_Gam d k p a y) =ᵐ[volume] sa16r_cv (sa16r_g d a) F := by
  have hp1 : (1 : ℝ) ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hp0 : (ENNReal.ofReal p) ≠ 0 := by
    have : (0 : ℝ) < p := by linarith
    exact (ENNReal.ofReal_pos.2 this).ne'
  obtain ⟨x, hxr, hxt⟩ := mem_closure_iff_seq_limit.1 ((sa16r_Jcc_dense d k p) y)
  choose φ hφ using hxr
  have hdist : Tendsto (fun n => ‖sa16r_Jcc d k p (φ n) - y‖) atTop (𝓝 0) := by
    have : Tendsto (fun n => sa16r_Jcc d k p (φ n)) atTop (𝓝 y) := by
      have e : (fun n => sa16r_Jcc d k p (φ n)) = x := funext hφ
      rw [e]; exact hxt
    exact tendsto_iff_norm_sub_tendsto_zero.1 this
  have hgm : Measurable (sa16r_g d a) := sa16r_g_meas
  have hgi := sa16r_g_int (d := d) ha
  -- the estimate
  have hbound : ∀ n, eLpNorm (fun z => wrep d (k + 1) p (sa16r_Gam d k p a y) z - sa16r_cv (sa16r_g d a) F z)
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (‖sa16r_Gam d k p a‖ * ‖sa16r_Jcc d k p (φ n) - y‖) +
        ENNReal.ofReal ‖sa16r_Jcc d k p (φ n) - y‖ := by
    intro n
    set yn := sa16r_Jcc d k p (φ n) with hyn
    have hφn : IsCcInfty (φ n).1 := (φ n).2
    have e1 : wrep d (k + 1) p (sa16r_Gam d k p a yn) =ᵐ[volume] sa16r_cv (sa16r_g d a) (φ n).1 := by
      have := sa16r_Gam_cc (p := p) ha k hφn
      rw [hyn, sa16r_Jcc_eq]
      exact this
    have e2 : wrep d k p yn =ᵐ[volume] (φ n).1 := by
      rw [hyn, sa16r_Jcc_eq]
      exact sa16r_cc_elt_wrep hφn k
    -- first term
    have t1 : eLpNorm (fun z => wrep d (k + 1) p (sa16r_Gam d k p a y) z - sa16r_cv (sa16r_g d a) (φ n).1 z)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (‖sa16r_Gam d k p a‖ * ‖yn - y‖) := by
      have h := sa16y5_wrep_eLpNorm_le (k + 1) (sa16r_Gam d k p a y - sa16r_Gam d k p a yn)
      have hnorm : ‖sa16r_Gam d k p a y - sa16r_Gam d k p a yn‖ ≤ ‖sa16r_Gam d k p a‖ * ‖yn - y‖ := by
        rw [← map_sub]
        calc _ ≤ ‖sa16r_Gam d k p a‖ * ‖y - yn‖ := (sa16r_Gam d k p a).le_opNorm _
          _ = _ := by rw [norm_sub_rev]
      calc _ = eLpNorm (wrep d (k + 1) p (sa16r_Gam d k p a y - sa16r_Gam d k p a yn)) (ENNReal.ofReal p) volume := by
            refine eLpNorm_congr_ae ?_
            filter_upwards [sa16y5_wrep_sub (k + 1) (sa16r_Gam d k p a y) (sa16r_Gam d k p a yn), e1] with z hz1 hz2
            rw [hz1, hz2]
        _ ≤ ENNReal.ofReal ‖sa16r_Gam d k p a y - sa16r_Gam d k p a yn‖ := h
        _ ≤ _ := ENNReal.ofReal_le_ofReal hnorm
    -- second term
    have t2 : eLpNorm (fun z => sa16r_cv (sa16r_g d a) (φ n).1 z - sa16r_cv (sa16r_g d a) F z)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ‖yn - y‖ := by
      obtain ⟨bφ, hbφ⟩ := sa16r_cc_bdd hφn
      have hsub : (fun z => sa16r_cv (sa16r_g d a) (φ n).1 z - sa16r_cv (sa16r_g d a) F z) =
          sa16r_cv (sa16r_g d a) (fun y => (φ n).1 y - F y) := by
        funext z
        rw [sa16y5_cv_sub_bdd hgi hφn.1.continuous hFc hbφ hB z]
      rw [hsub]
      have hc : Continuous (fun y => (φ n).1 y - F y) := hφn.1.continuous.sub hFc
      have y1 := sa16y5_young hgm hgi hc hp1
      have gl : ∫ z, |sa16r_g d a z| = 1 := sa16y5_g_abs_L1 ha
      rw [gl, ENNReal.ofReal_one, one_mul] at y1
      refine y1.trans ?_
      have h := sa16y5_wrep_eLpNorm_le k (yn - y)
      calc _ = eLpNorm (wrep d k p (yn - y)) (ENNReal.ofReal p) volume := by
            refine eLpNorm_congr_ae ?_
            filter_upwards [sa16y5_wrep_sub k yn y, e2, hF] with z hz1 hz2 hz3
            rw [hz1, hz2, hz3]
        _ ≤ _ := h
    have htri : eLpNorm (fun z => wrep d (k + 1) p (sa16r_Gam d k p a y) z - sa16r_cv (sa16r_g d a) F z)
        (ENNReal.ofReal p) volume ≤
        eLpNorm (fun z => wrep d (k + 1) p (sa16r_Gam d k p a y) z - sa16r_cv (sa16r_g d a) (φ n).1 z)
          (ENNReal.ofReal p) volume +
        eLpNorm (fun z => sa16r_cv (sa16r_g d a) (φ n).1 z - sa16r_cv (sa16r_g d a) F z)
          (ENNReal.ofReal p) volume := by
      have : (fun z => wrep d (k + 1) p (sa16r_Gam d k p a y) z - sa16r_cv (sa16r_g d a) F z) =
          (fun z => wrep d (k + 1) p (sa16r_Gam d k p a y) z - sa16r_cv (sa16r_g d a) (φ n).1 z) +
          (fun z => sa16r_cv (sa16r_g d a) (φ n).1 z - sa16r_cv (sa16r_g d a) F z) := by
        funext z; simp only [Pi.add_apply]; ring
      rw [this]
      exact eLpNorm_add_le (ENNReal.one_le_ofReal.2 hp1)
    exact htri.trans (add_le_add t1 t2)
  have hlim : Tendsto (fun n => ENNReal.ofReal (‖sa16r_Gam d k p a‖ * ‖sa16r_Jcc d k p (φ n) - y‖) +
      ENNReal.ofReal ‖sa16r_Jcc d k p (φ n) - y‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal (‖sa16r_Gam d k p a‖ * ‖sa16r_Jcc d k p (φ n) - y‖)) atTop
        (𝓝 0) := by
      have := (hdist.const_mul ‖sa16r_Gam d k p a‖)
      rw [mul_zero] at this
      simpa using ENNReal.tendsto_ofReal this
    have h2 : Tendsto (fun n => ENNReal.ofReal ‖sa16r_Jcc d k p (φ n) - y‖) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hdist
    simpa using h1.add h2
  have hzero : eLpNorm (fun z => wrep d (k + 1) p (sa16r_Gam d k p a y) z - sa16r_cv (sa16r_g d a) F z)
      (ENNReal.ofReal p) volume ≤ 0 := ge_of_tendsto' hlim hbound
  have h0 := (eLpNorm_eq_zero_iff hp0).1 (le_antisymm hzero bot_le)
  filter_upwards [h0] with z hz
  simpa [sub_eq_zero] using hz

end Gm2

end HRS.Whole.AppendixA.Phase2SA16R
