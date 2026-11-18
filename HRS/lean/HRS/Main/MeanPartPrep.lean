import Mathlib
import HRS.Main.Headline
import HRS.Main.MeanPartHK
import HRS.Main.MeanPartMetricEval
import HRS.Energy.StaticLimitGauss

/-!
# Mean-particle packet (L1): the prepared data of Corollary 5.17

`mpp_preparedData` : from `IsMeanTransient` build `S : PreparedData d` with `S.s = s`, `S.β = β`,
`S.V = 0`, `S.ρ0 = 1 + εψ_k` and `S.ρ t = ρ t` for `t ≥ 0` (`S.ρ = ρ ∘ max 0`, since
`PreparedData.hρ` asks the identity `mfPath ρc = S.ρ` on all of `ℝ`).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {d : ℕ}

/-- Extending an `H^K` coefficient solution by its initial value to negative times. -/
theorem mpp_hk_extend {s : ℝ} {V : Torus d → ℝ} {invβ K : ℝ} {ρ₀ : Torus d → ℝ}
    {ρc : ℝ → PDE.Coeff d} (h : PDE.IsMFSolutionHK d s V invβ K ρ₀ ρc) :
    PDE.IsMFSolutionHK d s V invβ K ρ₀ (fun t => ρc (max 0 t)) := by
  have hmax : ∀ t : ℝ, 0 ≤ t → max 0 t = t := fun t ht => max_eq_right ht
  refine ⟨by simpa using h.init, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := h.cont
    refine ⟨fun τ hτ => ?_, fun τ₀ hτ₀ => ?_⟩
    · simpa [hmax τ hτ] using h1 τ hτ
    · have := h2 τ₀ hτ₀
      refine (this.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      have hτ' : 0 ≤ τ := hτ
      simp [hmax τ hτ', hmax τ₀ hτ₀]
  · intro j t ht
    refine ((h.integrable j t ht)).congr_fun (fun σ hσ => ?_) measurableSet_Icc
    simp [hmax σ hσ.1]
  · intro j t ht
    show ρc (max 0 t) j = _
    rw [hmax t ht]
    refine (h.eq j t ht).trans ?_
    congr 1
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [Set.uIcc_of_le ht] at hσ
    simp [hmax σ hσ.1]

/-- **Lemma L1 (Corollary 5.17).** The prepared data of `mean_particles`. -/
theorem mpp_preparedData (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (ε A : ℝ) (ρ : ℝ → Torus d → ℝ) (C : ℝ) (Cj : ℕ → ℝ)
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) :
    ∃ S : Main.PreparedData d, S.s = s ∧ S.β = β ∧ S.V = (fun _ => 0) ∧
      S.ρ0 = (fun x => 1 + ε * PDE.cosTest k x) ∧ ∀ t : ℝ, 0 ≤ t → S.ρ t = ρ t := by
  have hmax : ∀ t : ℝ, 0 ≤ t → max 0 t = t := fun t ht => max_eq_right ht
  obtain ⟨hsm, hpos⟩ := hρ.smooth_pos 0 le_rfl
  have hsm' : Torus.IsSmooth (fun x : Torus d => 1 + ε * PDE.cosTest k x) := by
    simpa [hρ.init] using hsm
  have hpos' : ∀ x : Torus d, 0 < 1 + ε * PDE.cosTest k x := by
    intro x; simpa [hρ.init] using hpos x
  have hcont : Continuous (fun x : Torus d => 1 + ε * PDE.cosTest k x) :=
    StaticLimitAux.continuous_of_smooth hsm'
  have hψint : Integrable (fun x : Torus d => PDE.cosTest k x) := by
    have : Continuous (fun x : Torus d => PDE.cosTest k x) :=
      Torus.continuous_of_continuous_lift (Cor516Aux.isCk_cosTest' k 0).continuous
    exact mphk_integrable_of_continuous this
  have hK := mphk_hk_of_meanTransient hd hs0 hsd hβ k ε A ρ C Cj hρ
  refine ⟨⟨s, hs0, hsd, hd, β, hβ, fun _ => 0, (by unfold Torus.IsSmooth Torus.IsCk Torus.lift; exact contDiff_const), fun x => 1 + ε * PDE.cosTest k x,
    ⟨⟨fun x => (hpos' x).le, hcont.measurable, ?_⟩, hsm', hpos'⟩,
    fun t => ρ (max 0 t), ?_, ?_⟩, rfl, rfl, rfl, rfl, ?_⟩
  · rw [integral_add (integrable_const _) (hψint.const_mul ε), integral_const_mul,
      mp_integral_cosTest k hk]
    simp
  · simp [hρ.init]
  · intro K hKd
    obtain ⟨ρc, hρc, hpath⟩ := hK K hKd
    refine ⟨fun t => ρc (max 0 t), mpp_hk_extend ?_, ?_⟩
    · simpa [hρ.init] using hρc
    · funext t
      exact hpath (max 0 t) (le_max_left _ _)
  · intro t ht
    simp [hmax t ht]

end HRS
