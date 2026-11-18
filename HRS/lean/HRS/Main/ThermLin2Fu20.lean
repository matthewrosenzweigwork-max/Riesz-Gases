import HRS.Main.ThermLin2Fu19
import HRS.Main.GFB1Aux2

/-!
# THERMLIN2 Fu20: from fixed-time pairing bounds to a simultaneous norm bound in `ℝ≥0∞`

Abstract (no PDE input): if `R` is a.s. continuous on `[0,T']` and `ofReal |⟨R_t, φ⟩| ≤ ofReal ‖φ‖_{H^m} · Rhs_t` a.s. for
each fixed time and smooth test, and `Rhs_s ≤ e^{c(t-s)} Rhs_t` for `s ≤ t`, then `‖R_t‖ₑ ≤ Rhs_t` for all `t` a.s.
(rational grid from below `⌊(n+1)t⌋/(n+1)` as in `gf_norm_of_pairings_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c

variable {d : ℕ}

theorem tl2fu_norm_le_of_pairings {m : ℝ} (F : NegSobolev d m) (Bt : ℝ≥0∞)
    (hH : ∀ p : gfb1Idx d, ENNReal.ofReal |NegSobolev.eval F (gfb1Phi m p)| ≤
      ENNReal.ofReal (sobolevNorm m (gfb1Phi m p)) * Bt) :
    ‖F‖ₑ ≤ Bt := by
  by_cases hB : Bt = ⊤
  · rw [hB]; exact le_top
  have hBt : Bt = ENNReal.ofReal Bt.toReal := (ENNReal.ofReal_toReal hB).symm
  have hB0 : 0 ≤ Bt.toReal := ENNReal.toReal_nonneg
  have hF : ‖F‖ ≤ Bt.toReal := by
    refine gfb1_norm_le F _ hB0 fun p => ?_
    have h1 := hH p
    have hs : 0 ≤ sobolevNorm m (gfb1Phi m p) := by unfold sobolevNorm; exact Real.sqrt_nonneg _
    rw [hBt, ← ENNReal.ofReal_mul hs] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hs hB0)).1 h1
    rw [mul_comm]; exact h2
  rw [← ofReal_norm, hBt]
  exact ENNReal.ofReal_le_ofReal hF

theorem tl2fu_grid_bound {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (m T' c : ℝ)
    (R : ℝ → Ω → NegSobolev d m) (Rhs : ℝ → Ω → ℝ≥0∞)
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 T'))
    (hmono : ∀ ω, ∀ s t : ℝ, 0 ≤ s → s ≤ t → Rhs s ω ≤ ENNReal.ofReal (Real.exp (c * (t - s))) * Rhs t ω)
    (hpair : ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ∀ᵐ ω ∂P, ENNReal.ofReal |NegSobolev.eval (R t ω) φ| ≤ ENNReal.ofReal ‖lpFun m φ‖ * Rhs t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T', ‖R t ω‖ₑ ≤ Rhs t ω := by
  have hE : ∀ᵐ ω ∂P, ∀ (p : gfb1Idx d) (j : ℤ) (n : ℕ),
      (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T' →
      ENNReal.ofReal |NegSobolev.eval (R ((j : ℝ) / ((n : ℝ) + 1)) ω) (gfb1Phi m p)| ≤
        ENNReal.ofReal ‖lpFun m (gfb1Phi m p)‖ * Rhs ((j : ℝ) / ((n : ℝ) + 1)) ω := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun j => ae_all_iff.2 fun n => ?_
    by_cases hmem : (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T'
    · filter_upwards [hpair _ hmem _ (gfb1_phi_smooth m p)] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hmem
  filter_upwards [hRc, hE] with ω hRω hEω
  have hgrid : ∀ (j : ℤ) (n : ℕ), (j : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) T' →
      ‖R ((j : ℝ) / ((n : ℝ) + 1)) ω‖ₑ ≤ Rhs ((j : ℝ) / ((n : ℝ) + 1)) ω := by
    intro j n hmem
    refine tl2fu_norm_le_of_pairings _ _ fun p => (hEω p j n hmem).trans ?_
    have := norm_lpFun_le m (gfb1Phi m p)
    gcongr
  intro t ht
  by_cases htop : Rhs t ω = ⊤
  · rw [htop]; exact le_top
  have hseq : Tendsto (fun n : ℕ => gfb1Grid n t) atTop (𝓝[Set.Icc 0 T'] t) :=
    tendsto_nhdsWithin_iff.2 ⟨gfb1Grid_tendsto t, Filter.Eventually.of_forall fun n => gfb1Grid_mem ht n⟩
  have hconvR : Tendsto (fun n : ℕ => ‖R (gfb1Grid n t) ω‖ₑ) atTop (𝓝 ‖R t ω‖ₑ) :=
    ((continuous_enorm.tendsto _).comp ((hRω t ht).tendsto)).comp hseq
  have hconvB : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (c * (t - gfb1Grid n t))) * Rhs t ω) atTop
      (𝓝 (Rhs t ω)) := by
    have h0 : Tendsto (fun n : ℕ => c * (t - gfb1Grid n t)) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := t)).sub (gfb1Grid_tendsto t)).const_mul c
      simpa using this
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (c * (t - gfb1Grid n t)))) atTop (𝓝 1) := by
      have := (ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto 0).comp h0))
      simpa using this
    have := ENNReal.Tendsto.mul_const h1 (Or.inr htop)
    simpa using this
  refine le_of_tendsto_of_tendsto hconvR hconvB (Filter.Eventually.of_forall fun n => ?_)
  have hg := gfb1Grid_mem ht n
  have hgrid' := hgrid ⌊((n : ℝ) + 1) * t⌋ n hg
  refine hgrid'.trans ?_
  exact hmono ω _ _ hg.1 (gfb1Grid_bounds n t).2

end HRS.ThermLin.Plan2
