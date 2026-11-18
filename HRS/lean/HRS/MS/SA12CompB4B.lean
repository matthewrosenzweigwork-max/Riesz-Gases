import HRS.MS.SA12CompB4A
import HRS.MP.RdGenerator
import HRS.MP.RdGenAux

/-!
# S.A.12 B4, part B: joint continuity of the cancellation convolution `rgT` in a parameter
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.RdGen

variable {d : ℕ}

theorem sa12z_rgT_continuousOn (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {κ : Euc d → ℝ} (hκ : RgKer d s σ κ) {S : Set ℝ} {g : ℝ → Euc d → ℝ}
    (hg : ∀ τ ∈ S, Differentiable ℝ (g τ)) {b0 b1 : ℝ} (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (h0 : ∀ τ ∈ S, ∀ y, ‖g τ y‖ ≤ b0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ τ ∈ S, ∀ y, ‖fderiv ℝ (g τ) y‖ ≤ b1)
    (hc : ContinuousOn (fun q : ℝ × Euc d => g q.1 q.2) (S ×ˢ univ)) :
    ContinuousOn (fun q : ℝ × Euc d => rgT κ (g q.1) q.2) (S ×ˢ univ) := by
  intro p hp
  obtain ⟨τ₀, x₀⟩ := p
  unfold rgT
  have hpow : (0 : ℝ) ≤ 2 ^ ((d : ℝ) + 1) := by positivity
  refine continuousWithinAt_of_dominated (bound := rgMaj d s σ (b0 * 2 ^ ((d : ℝ) + 1)) b1 x₀)
    ?_ ?_ (rg_maj_integrable hd hsd σ _ b1 x₀) ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact rg_aesm hκ.meas (hg q.1 hq.1).continuous q.2
  · have hball : ∀ᶠ q in 𝓝[S ×ˢ (univ : Set (Euc d))] (τ₀, x₀), ‖q.2 - x₀‖ < 1 := by
      have : ∀ᶠ q in 𝓝 ((τ₀, x₀) : ℝ × Euc d), ‖q.2 - x₀‖ < 1 := by
        have hcq : Continuous (fun q : ℝ × Euc d => ‖q.2 - x₀‖) := by fun_prop
        exact hcq.continuousAt.eventually (gt_mem_nhds (by simp))
      exact nhdsWithin_le_nhds this
    filter_upwards [self_mem_nhdsWithin, hball] with q hq hqb
    filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
    refine (rg_norm_le hs0 hκ (hg q.1 hq.1) hb0 hb1 (h0 q.1 hq.1) (h1 q.1 hq.1) q.2 z hz).trans ?_
    unfold rgMaj
    have hpe := rg_peetre (x := q.2) (x0 := x₀) z hqb
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hκ.sigma_nonneg
    calc 4 ^ (s + 1) * b0 * (1 + ‖q.2 - z‖) ^ (-((d : ℝ) + 1))
        ≤ 4 ^ (s + 1) * b0 * (2 ^ ((d : ℝ) + 1) * (1 + ‖x₀ - z‖) ^ (-((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hpe (by positivity)
      _ = 4 ^ (s + 1) * (b0 * 2 ^ ((d : ℝ) + 1)) * (1 + ‖x₀ - z‖) ^ (-((d : ℝ) + 1)) := by ring
  · refine Eventually.of_forall fun z => ?_
    have hshift : ContinuousWithinAt (fun q : ℝ × Euc d => g q.1 (q.2 - z)) (S ×ˢ univ) (τ₀, x₀) := by
      have hmap : MapsTo (fun q : ℝ × Euc d => (q.1, q.2 - z)) (S ×ˢ univ) (S ×ˢ univ) :=
        fun q hq => ⟨hq.1, mem_univ _⟩
      have hcont : ContinuousWithinAt (fun q : ℝ × Euc d => (q.1, q.2 - z)) (S ×ˢ univ) (τ₀, x₀) :=
        (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousWithinAt
      have h1 : ContinuousWithinAt (fun q : ℝ × Euc d => g q.1 q.2) (S ×ˢ univ) (τ₀, x₀ - z) :=
        hc _ (hmap (x := (τ₀, x₀)) hp)
      exact ContinuousWithinAt.comp (f := fun q : ℝ × Euc d => (q.1, q.2 - z)) (x := (τ₀, x₀)) h1 hcont hmap
    have hbase : ContinuousWithinAt (fun q : ℝ × Euc d => g q.1 q.2) (S ×ˢ univ) (τ₀, x₀) := hc _ hp
    have : (fun q : ℝ × Euc d => κ z • rgR (g q.1) q.2 z) =
        fun q => κ z • (if ‖z‖ ≤ 1 / 4 then g q.1 (q.2 - z) - g q.1 q.2 else g q.1 (q.2 - z)) := by
      funext q; rfl
    show ContinuousWithinAt (fun q : ℝ × Euc d => κ z • rgR (g q.1) q.2 z) _ _
    rw [this]
    have hX : ContinuousWithinAt (fun q : ℝ × Euc d =>
        (if ‖z‖ ≤ 1 / 4 then g q.1 (q.2 - z) - g q.1 q.2 else g q.1 (q.2 - z))) (S ×ˢ univ) (τ₀, x₀) := by
      by_cases hz : ‖z‖ ≤ 1 / 4
      · simp only [hz, if_true]
        exact hshift.sub hbase
      · simp only [hz, if_false]
        exact hshift
    exact ContinuousWithinAt.smul (f := fun _ : ℝ × Euc d => κ z) continuousWithinAt_const hX

end HRS.MH.AdjointRd.Phase2SA12Companions
