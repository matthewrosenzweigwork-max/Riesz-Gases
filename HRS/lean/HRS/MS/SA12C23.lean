import HRS.MS.SA12C22

/-!
# S.A.12(c), packet E7.04 (part 7): jets of the remainder convolution

`∂^β (1_Y f ⋆ Ã - χ̂(·-c) f ⋆ B̃)(x0) = ∫_W ρ_v^β(z) f(x0 - z) dz`, `v = x0 - c`, `W = (-L/2, L/2]^d`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12c_pd_sub' {f g : Euc d → ℝ} {z : Euc d} (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z)
    {n : ℕ} (β : Fin n → Fin d) :
    partialDeriv β (fun u => f u - g u) z = partialDeriv β f z - partialDeriv β g z := by
  unfold partialDeriv
  have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := n) (hf.of_le (by exact_mod_cast le_top))
    (hg.of_le (by exact_mod_cast le_top))
  have e : (fun u => f u - g u) = f - g := rfl
  rw [e, this]
  rfl

/-- `κ^β(v,z) = D^βÃ(z) - χ̂(v-z) D^βB̃(z)`. -/
def sa12cKap (s L c0 : ℝ) (q χ χh γ : Euc d → ℝ) {n : ℕ} (β : Fin n → Fin d) (v z : Euc d) : ℝ :=
  partialDeriv β (sa12cA s L c0 q χ γ) z - χh (v - z) * partialDeriv β (sa12cB s L χ) z

theorem sa12c_T_jet {s L c0 : ℝ} (hL : 40 ≤ L)
    {q χ χh γ : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (hγ : IsPeriodicRieszKernel d s L γ)
    (hq : ContDiff ℝ ∞ q)
    {f : Euc d → ℝ} (hf : Continuous f) (c x0 : Euc d) (hx0 : ‖x0 - c‖ < 2)
    {n : ℕ} (β : Fin n → Fin d) :
    partialDeriv β (fun x => sa12cConv ((sa12cYcell d L x0).indicator f) (sa12cA s L c0 q χ γ) x -
        sa12cConv (fun y => χh (y - c) * f y) (sa12cB s L χ) x) x0 =
      ∫ z in sa12cWcell d L, sa12cKap s L c0 q χ χh γ β (x0 - c) z * f (x0 - z) := by
  have hL0 : 0 < L := by linarith
  set Y := sa12cYcell d L x0 with hY
  have hYm := sa12cYcell_meas L x0
  set A := sa12cA s L c0 q χ γ with hA
  set B := sa12cB s L χ with hB
  have hAs : ContDiff ℝ ∞ A := sa12cA_contDiff hL0 hq hχ hγ
  have hBs : ContDiff ℝ ∞ B := sa12cB_contDiff hL0 hχ
  have hAcs : HasCompactSupport A := sa12cA_compact hL0 hχ
  have hBcs : HasCompactSupport B := sa12cB_compact hL0 hχ
  set f1 : Euc d → ℝ := Y.indicator f with hf1d
  set f2 : Euc d → ℝ := fun y => χh (y - c) * f y with hf2d
  have hf1 : LocallyIntegrable f1 volume := hf.locallyIntegrable.indicator hYm
  have hf2c : Continuous f2 := (hχ.2.1.continuous.comp (continuous_id.sub continuous_const)).mul hf
  have hf2 : LocallyIntegrable f2 volume := hf2c.locallyIntegrable
  have hT1 := sa12c_conv_contDiff hf1 hAs hAcs
  have hT2 := sa12c_conv_contDiff hf2 hBs hBcs
  rw [sa12c_pd_sub' hT1.contDiffAt hT2.contDiffAt, sa12c_conv_pd hf1 hAs hAcs, sa12c_conv_pd hf2 hBs hBcs]
  have hAβ : Continuous (partialDeriv β A) := (sa12z3_pd_contDiff_inf hAs β).continuous
  have hBβ : Continuous (partialDeriv β B) := (sa12z3_pd_contDiff_inf hBs β).continuous
  have I1 : Integrable (fun t => f1 t * partialDeriv β A (x0 - t)) volume := by
    have := (sa12c_pd_compact hAcs β).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hf1 hAβ x0
    simpa [ConvolutionExistsAt] using this
  have I2 : Integrable (fun t => f2 t * partialDeriv β B (x0 - t)) volume := by
    have := (sa12c_pd_compact hBcs β).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hf2 hBβ x0
    simpa [ConvolutionExistsAt] using this
  rw [← integral_sub I1 I2]
  have hWY : ∀ z : Euc d, x0 - z ∈ Y ↔ z ∈ sa12cWcell d L := by
    intro z
    simp only [hY, sa12cYcell, sa12cWcell, Set.mem_ofPred_eq, PiLp.sub_apply]
    refine forall_congr' fun i => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hid : ∀ t, f1 t * partialDeriv β A (x0 - t) - f2 t * partialDeriv β B (x0 - t) =
      Y.indicator (fun t => f t * sa12cKap s L c0 q χ χh γ β (x0 - c) (x0 - t)) t := by
    intro t
    by_cases hty : t ∈ Y
    · rw [Set.indicator_of_mem hty]
      simp only [hf1d, hf2d, Set.indicator_of_mem hty, sa12cKap]
      have e : x0 - c - (x0 - t) = t - c := by abel
      rw [e]; ring
    · rw [Set.indicator_of_notMem hty]
      have hχ0 : χh (t - c) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h8 := hχ.2.2.2.1 hmem
        rw [Metric.mem_ball, dist_zero_right] at h8
        exact hty (sa12cYcell_ball hL hx0 h8)
      simp [hf1d, hf2d, hty, hχ0]
  simp_rw [hid]
  have hrefl := integral_sub_left_eq_self (fun t => Y.indicator
    (fun t => f t * sa12cKap s L c0 q χ χh γ β (x0 - c) (x0 - t)) t) volume x0
  rw [← hrefl, ← integral_indicator (sa12c_W_meas (d := d) L)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ sa12cWcell d L
  · change Y.indicator (fun t => f t * sa12cKap s L c0 q χ χh γ β (x0 - c) (x0 - t)) (x0 - z) = _
    rw [Set.indicator_of_mem ((hWY z).2 hz)]
    rw [Set.indicator_of_mem hz]
    simp only [sub_sub_cancel]; ring
  · change Y.indicator (fun t => f t * sa12cKap s L c0 q χ χh γ β (x0 - c) (x0 - t)) (x0 - z) = _
    rw [Set.indicator_of_notMem (fun h => hz ((hWY z).1 h)), Set.indicator_of_notMem hz]

end HRS.MH.AdjointRd.Phase2SA12C
