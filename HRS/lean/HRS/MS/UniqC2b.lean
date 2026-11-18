import HRS.MS.UniqC2

/-!
# Packet C2, part 2: continuity of the cancellation-convention convolution in `(r,x)`

For a kernel `κ` (`RgKer`) and a family `g r` of decaying Lipschitz functions whose values depend
continuously on `(r,x)`, the map `(r,x) ↦ rgT κ (g r) x` is continuous (dominated convergence, with the
`x`-independent majorant of `rg_hasFDerivAt` and the Peetre inequality `rg_peetre`).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.UniqC2
open HRS HRS.Whole HRS.MP.RdGen

variable {d : ℕ}

lemma c2_rgT_cont (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {S : Set ℝ} {g : ℝ → Euc d → ℝ} {b0 b1 : ℝ} (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hdiff : ∀ r ∈ S, Differentiable ℝ (g r))
    (h0 : ∀ r ∈ S, ∀ y, ‖g r y‖ ≤ b0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ r ∈ S, ∀ y, ‖fderiv ℝ (g r) y‖ ≤ b1)
    (hjoint : ContinuousOn (fun p : ℝ × Euc d => g p.1 p.2) (S ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Euc d => rgT κ (g p.1) p.2) (S ×ˢ Set.univ) := by
  intro p₀ hp₀
  obtain ⟨r₀, x₀⟩ := p₀
  unfold ContinuousWithinAt
  show Tendsto (fun p : ℝ × Euc d => ∫ z, κ z • rgR (g p.1) p.2 z) _ (𝓝 (∫ z, κ z • rgR (g r₀) x₀ z))
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := rgMaj d s σ (b0 * 2 ^ ((d : ℝ) + 1)) b1 x₀) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact rg_aesm hκ.meas (hdiff p.1 hp.1).continuous p.2
  · have hn : ∀ᶠ p : ℝ × Euc d in 𝓝[S ×ˢ Set.univ] (r₀, x₀), ‖p.2 - x₀‖ < 1 := by
      apply eventually_nhdsWithin_of_eventually_nhds
      have : Tendsto (fun p : ℝ × Euc d => p.2) (𝓝 (r₀, x₀)) (𝓝 x₀) := continuous_snd.tendsto _
      have := this.sub_const x₀
      simp only [sub_self] at this
      exact this.norm.eventually (gt_mem_nhds (by simpa using one_pos))
    filter_upwards [self_mem_nhdsWithin, hn] with p hp hpn
    filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
    have := rg_norm_le hs0 hκ (hdiff p.1 hp.1) hb0 hb1 (h0 p.1 hp.1) (h1 p.1 hp.1) p.2 z hz
    refine this.trans ?_
    unfold rgMaj
    apply mul_le_mul_of_nonneg_left _ hκ.sigma_nonneg
    refine add_le_add_right ?_ _
    have hp2 := rg_peetre (d := d) z hpn
    have h4 : (0 : ℝ) ≤ 4 ^ (s + 1) * b0 := by positivity
    calc 4 ^ (s + 1) * b0 * (1 + ‖p.2 - z‖) ^ (-((d : ℝ) + 1))
        ≤ 4 ^ (s + 1) * b0 * (2 ^ ((d : ℝ) + 1) * (1 + ‖x₀ - z‖) ^ (-((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hp2 h4
      _ = 4 ^ (s + 1) * (b0 * 2 ^ ((d : ℝ) + 1)) * (1 + ‖x₀ - z‖) ^ (-((d : ℝ) + 1)) := by ring
  · exact rg_maj_integrable hd hsd σ _ b1 x₀
  · refine Eventually.of_forall fun z => ?_
    have hshift : ContinuousWithinAt (fun p : ℝ × Euc d => g p.1 (p.2 - z)) (S ×ˢ Set.univ) (r₀, x₀) := by
      have hc : ContinuousOn (fun p : ℝ × Euc d => (p.1, p.2 - z)) (S ×ˢ Set.univ) :=
        (continuousOn_fst.prodMk (continuousOn_snd.sub continuousOn_const))
      exact (hjoint.comp hc (fun p hp => ⟨hp.1, Set.mem_univ _⟩)) _ hp₀
    have hbase : ContinuousWithinAt (fun p : ℝ × Euc d => g p.1 p.2) (S ×ˢ Set.univ) (r₀, x₀) :=
      hjoint _ hp₀
    unfold rgR
    by_cases h : ‖z‖ ≤ 1 / 4
    · simp only [h, if_true]
      exact (hshift.sub hbase).const_smul (κ z)
    · simp only [h, if_false]
      exact hshift.const_smul (κ z)

end HRS.MS.UniqC2
