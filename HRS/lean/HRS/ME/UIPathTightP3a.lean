import HRS.ME.UIPath
import HRS.ME.RetPathLaw
import HRS.ME.RetGlueB
import HRS.MD.EQFrozen29Rest
import HRS.MD.EQLawPath
import HRS.Sections.AdjKGlue
import HRS.Main.MeanPartMetricB

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.UIPathTight

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- **P3a** (convergence of the stationary windows at `u = 0`; scope note 1.1 step 2).  For any choice of
stationary Gibbs flows `(P₂ n, X₂ n)` with `N = n + 2` particles on the horizon `0 + T`, the windows
`windowZeta m T 0` converge in law in `C([0,T]; E_m)` to the window of any stationary Gaussian field
`Z_β` (the statement includes the AEMeasurability of the windows).  Route:
`equilibrium_paths_direct_proof` at `βm = βp = β`, `u = 0`, `wassersteinE_mono`, `tendsto_deltaN`,
`mp_tendstoInDistribution_of_wE1`, `windowZeta_aemeasurable`, `adjk_toPath_aemeasurable_proof`. -/
theorem stationary_windows_converge (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (T : ℝ) (hT : 0 ≤ T)
    (Ω₂ : ℕ → Type) [∀ n, MeasurableSpace (Ω₂ n)] (P₂ : ∀ n, Measure (Ω₂ n))
    [∀ n, IsProbabilityMeasure (P₂ n)]
    (X₀₂ : ∀ n, Ω₂ n → Config d (n + 2)) (W₂ : ∀ n, ℝ≥0 → Ω₂ n → (Fin (n + 2) → Euc d))
    (X₂ : ∀ n, ℝ≥0 → Ω₂ n → Config d (n + 2))
    (h₂ : ∀ n, IsStationaryGibbsFlow (P₂ n) s hs0 hsd V β hβ (0 + T) (X₀₂ n) (W₂ n) (X₂ n))
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z) :
    TendstoInDistribution (fun n ω => Main.windowZeta m T 0 (P₂ n) (X₂ n) ω)
      atTop (windowPath m T 0 Z) P₂ P' := by
  have hmd : (d : ℝ) < 2 * m := by
    have h1 : (d : ℝ) + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨C, hC, hall⟩ := HRS.MD.EQFrozen29Rest.equilibrium_paths_direct_proof (d := d) hd hs0 hsd V
    hV β β hβ le_rfl m hm T hT
  have hW2 : ∀ n : ℕ, wassersteinE 2 (law (P₂ n) (Main.windowZeta m T 0 (P₂ n) (X₂ n)))
      (law P' (windowPath m T 0 Z)) ≤ ENNReal.ofReal (C * (((n + 2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) +
        Real.sqrt (deltaN d s (n + 2)))) := fun n =>
    (hall β ⟨le_rfl, le_rfl⟩ ρβ hρβ 0 le_rfl (n + 2) (by omega) (P₂ n) (X₀₂ n) (W₂ n) (X₂ n) (h₂ n)
      P' Z hZ).2
  have hδ : Tendsto (fun n : ℕ => deltaN d s (n + 2)) atTop (𝓝 0) :=
    (HRS.External.RefMarg.tendsto_deltaN hd hs0 hsd).comp (tendsto_add_atTop_nat 2)
  have hsq : Tendsto (fun n : ℕ => Real.sqrt (deltaN d s (n + 2))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hδ
    rw [Real.sqrt_zero] at h
    exact h
  have hpow : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)) |>.congr fun n => by
        simp [Function.comp_apply, neg_div]
  have hbd : Tendsto (fun n : ℕ => ENNReal.ofReal (C * (((n + 2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) +
      Real.sqrt (deltaN d s (n + 2))))) atTop (𝓝 0) := by
    have h := ((hpow.add hsq).const_mul C)
    simp only [add_zero, mul_zero] at h
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rw [ENNReal.ofReal_zero] at this
    exact this
  have hae1 : ∀ n, AEMeasurable (Main.windowZeta m T 0 (P₂ n) (X₂ n)) (P₂ n) := fun n =>
    HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ (by omega) le_rfl hT (P₂ n) (h₂ n) hmd
  have hae2 : AEMeasurable (windowPath m T 0 Z) P' :=
    (HRS.MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ ρβ m T P' Z hZ 0 le_rfl).1
  refine mp_tendstoInDistribution_of_wE1 _ _ P₂ P' hae1 hae2 ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbd (fun n => bot_le)
    (fun n => ?_)
  exact (wassersteinE_mono 1 2 le_rfl (by norm_num) _ _).trans (hW2 n)

end HRS.ME.UIPathTight
