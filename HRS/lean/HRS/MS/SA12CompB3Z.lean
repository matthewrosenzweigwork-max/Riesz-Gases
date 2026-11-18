import HRS.MS.UlocCb
import HRS.Whole.AppendixAAdjoint

/-!
# S.A.12 B3: time-coherent continuous `C²` representatives of a uloc solution at level `mStar d`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa12z_norm_iteratedFDeriv_le_cbNorm {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) {j : ℕ}
    (hj : j ≤ k) (x : Euc d) : ‖iteratedFDeriv ℝ j f x‖ ≤ cbNorm k f := by
  have h0 : ‖iteratedFDeriv ℝ j f x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖ :=
    le_ciSup (hf.2 j hj) x
  refine h0.trans ?_
  unfold cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

/-- The jets of two continuous `C²` representatives differ on the unit ball around `z` by the local
Sobolev embedding of the localized difference. -/
theorem sa12z_jet_diff_le {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {q C₂ : ℝ}
    (hC₂ : ∀ f : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev q f →
      ∃ g : Euc d → ℝ, g =ᵐ[volume] f ∧ ContDiff ℝ 2 g ∧
        ∀ i ≤ 2, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤
          C₂ * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq q f))
    (z : Euc d) {u w F₁ F₂ : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (hw : ContDiff ℝ 2 w)
    (hu' : u =ᵐ[volume] F₁) (hw' : w =ᵐ[volume] F₂)
    (hf : HRS.PDE.ToolboxRd.MemSobolev q (fun x => χ (x - z) * (F₁ x - F₂ x))) :
    ∀ i ≤ 2, ∀ x ∈ Metric.ball z 1, ‖iteratedFDeriv ℝ i (fun y => u y - w y) x‖ ≤
      C₂ * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq q (fun x => χ (x - z) * (F₁ x - F₂ x))) := by
  obtain ⟨g, hgae, hgcd, hgb⟩ := hC₂ _ hf
  have hae : g =ᵐ[volume.restrict (Metric.ball z 1)] fun y => u y - w y := by
    have h1 := ae_restrict_of_ae (μ := volume) (s := Metric.ball z 1) hgae
    have h2 := ae_restrict_of_ae (μ := volume) (s := Metric.ball z 1) hu'
    have h3 := ae_restrict_of_ae (μ := volume) (s := Metric.ball z 1) hw'
    filter_upwards [h1, h2, h3, ae_restrict_mem measurableSet_ball] with y hy1 hy2 hy3 hyb
    have hc : χ (y - z) = 1 := by
      apply hχ.2.2.2.2
      rw [mem_closedBall_zero_iff]
      have : dist y z < 1 := hyb
      rw [dist_eq_norm] at this
      exact this.le
    rw [hy1, hc, one_mul, hy2, hy3]
  have heq := Measure.eqOn_open_of_ae_eq hae Metric.isOpen_ball hgcd.continuous.continuousOn
    (hu.sub hw).continuous.continuousOn
  intro i hi x hx
  have hev : g =ᶠ[𝓝 x] fun y => u y - w y :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) (fun y hy => heq hy)
  rw [← (hev.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hgb i hi x

-- BEGIN SA12.B3
end HRS.MH.AdjointRd.Phase2SA12Companions
