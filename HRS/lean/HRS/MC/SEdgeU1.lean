import HRS.MC.SEdgeVocab

/-!
# Packet U1: uniformity from pointwise convergence and equi-Lipschitz continuity
(relocated proof of `sed_U1_uniform_of_equilip`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.U1

theorem sed_U1_uniform_of_equilip_proof {E : Type*} [SeminormedAddCommGroup E] {a : ℕ → ℝ → E}
    {a₀ : ℝ → E} {L T : ℝ} (hL : ∀ (N : ℕ) (t t' : ℝ), ‖a N t - a N t'‖ ≤ L * |t - t'|)
    (hlim : ∀ t ∈ Set.Icc (-T) T, Tendsto (fun N => a N t) atTop (𝓝 (a₀ t))) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Set.Icc (-T) T, ‖a N t - a₀ t‖ ≤ ε := by
  intro ε hε
  set L' : ℝ := max L 0 with hL'
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hL'b : ∀ (N : ℕ) (t t' : ℝ), ‖a N t - a N t'‖ ≤ L' * |t - t'| := fun N t t' =>
    (hL N t t').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  -- the limit is Lipschitz on the interval
  have hLim : ∀ t ∈ Set.Icc (-T) T, ∀ t' ∈ Set.Icc (-T) T, ‖a₀ t - a₀ t'‖ ≤ L' * |t - t'| := by
    intro t ht t' ht'
    have := ((hlim t ht).sub (hlim t' ht')).norm
    exact le_of_tendsto' this fun N => hL'b N t t'
  set δ : ℝ := ε / (3 * (L' + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hLδ : L' * δ ≤ ε / 3 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨S, hSsub, hSfin, hcov⟩ :=
    finite_cover_balls_of_compact (isCompact_Icc (a := -T) (b := T)) hδpos
  have hev : ∀ᶠ N in atTop, ∀ t ∈ S, ‖a N t - a₀ t‖ < ε / 3 := by
    rw [hSfin.eventually_all]
    intro t ht
    have := (hlim t (hSsub ht)).eventually (Metric.ball_mem_nhds (a₀ t) (show 0 < ε / 3 by positivity))
    filter_upwards [this] with N hN
    simpa [dist_eq_norm] using hN
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN t ht => ?_⟩
  have := hcov ht
  simp only [Set.mem_iUnion] at this
  obtain ⟨s, hs, hts⟩ := this
  have hts' : |t - s| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hts
  have h1 := hL'b N t s
  have h2 := hN₀ N hN s hs
  have h3 := hLim s (hSsub hs) t ht
  have h4 : L' * |t - s| ≤ L' * δ := mul_le_mul_of_nonneg_left hts'.le hL'0
  have h5 : L' * |s - t| ≤ L' * δ := by rw [abs_sub_comm]; exact h4
  calc ‖a N t - a₀ t‖ = ‖(a N t - a N s) + (a N s - a₀ s) + (a₀ s - a₀ t)‖ := by congr 1; abel
    _ ≤ ‖a N t - a N s‖ + ‖a N s - a₀ s‖ + ‖a₀ s - a₀ t‖ := norm_add₃_le
    _ ≤ ε := by linarith


end HRS.MC.SEdge.U1
