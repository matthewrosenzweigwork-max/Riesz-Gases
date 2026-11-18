import HRS.MD.EQ29Vocab
import HRS.MD.EQLawPath
import HRS.MD.EQLawFlow

/-!
# EQ-COMP final (chunk D): `eq_direct_assembly_proof`

`equilibrium_paths_direct` from `eq_burnin` (not proved: its statement is copied verbatim into the hypothesis), the stationarity of the
window law (`eq_path_stationary_proof`) and the existence of long flows (`eq_flow_exists_proof`); the limit `a → ∞` at fixed `N`.
The tie against `HRS.MD.EQ29.eq_direct_assembly` is `HRS/MD/EQAsmDirectTie.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MD

namespace EQAsmDirect

open HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

theorem eq_direct_assembly_proof (hd : 2 ≤ d)
    (hburn : ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
      (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
      (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (T : ℝ) (hT : 0 ≤ T),
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
        IsThermalDensity (periodicRiesz d s) V β ρβ →
        ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (Z : ℝ → Ω' → NegSobolev d m),
          IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
          smoothDist 2 (law P (Main.windowZeta m T a P X)) (law P' (Main.windowPath m T 0 Z)) ≤
              C * (Real.exp (-c * a) + Real.sqrt (deltaN d s N)) ∧
          wassersteinE 2 (law P (Main.windowZeta m T a P X)) (law P' (Main.windowPath m T 0 Z)) ≤
              ENNReal.ofReal (C * (Real.exp (-c * a) + (N : ℝ) ^ (-(1 : ℝ) / 4) +
                Real.sqrt (deltaN d s N))))
    (hpath : type_of% (@HRS.MD.EQLawPath.eq_path_stationary_proof d))
    (hflow : type_of% (@HRS.MD.EQLawFlow.eq_flow_exists_proof d)) :
    type_of% (@HRS.Main.equilibrium_paths_direct d) := by
  intro _ s hs0 hsd V hV βm βp hβm hββ m hm T hT
  obtain ⟨C, c, hC, hc, h⟩ := hburn hd hs0 hsd V hV βm βp hβm hββ m hm T hT
  refine ⟨C, hC, ?_⟩
  intro β hβ ρβ hρ u hu N hN Ω _ P _ X₀ W X hX Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hmd : (d : ℝ) / 2 < m := by
    have h1 : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
    linarith
  have key : ∀ a : ℝ, 0 ≤ a →
      smoothDist 2 (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
          C * (Real.exp (-c * a) + Real.sqrt (deltaN d s N)) ∧
      wassersteinE 2 (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * (Real.exp (-c * a) + (N : ℝ) ^ (-(1 : ℝ) / 4) +
            Real.sqrt (deltaN d s N))) := by
    intro a ha
    obtain ⟨Ω'', _, P'', _, X₀', W', X', hX'⟩ :=
      hflow hd hs0 hsd V hV hβ0 hN (a + T) (by linarith)
    have hlaw := hpath hd hs0 hsd V hV hβ0 m hmd T hT hN P X₀ W X u hu hX P'' X₀' W' X' a ha hX'
    rw [hlaw]
    exact h β hβ ρβ hρ a ha N hN P'' X₀' W' X' hX' P' Z hZ
  constructor
  · have hlim : Tendsto (fun a : ℝ => C * (Real.exp (-c * a) + Real.sqrt (deltaN d s N))) atTop
        (𝓝 (C * (0 + Real.sqrt (deltaN d s N)))) := by
      have h1 : Tendsto (fun a : ℝ => Real.exp (-c * a)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun a : ℝ => -c * a) atTop atBot :=
          tendsto_id.const_mul_atTop_of_neg (by linarith)
        exact Real.tendsto_exp_atBot.comp h2
      exact ((h1.add_const _).const_mul C)
    have := ge_of_tendsto hlim (eventually_atTop.2 ⟨0, fun a ha => (key a ha).1⟩)
    simpa using this
  · have hlim : Tendsto (fun a : ℝ => ENNReal.ofReal (C * (Real.exp (-c * a) +
          (N : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt (deltaN d s N)))) atTop
        (𝓝 (ENNReal.ofReal (C * (0 + (N : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt (deltaN d s N))))) := by
      have h1 : Tendsto (fun a : ℝ => Real.exp (-c * a)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun a : ℝ => -c * a) atTop atBot :=
          tendsto_id.const_mul_atTop_of_neg (by linarith)
        exact Real.tendsto_exp_atBot.comp h2
      exact ENNReal.tendsto_ofReal (((h1.add_const _).add_const _).const_mul C)
    have := ge_of_tendsto hlim (eventually_atTop.2 ⟨0, fun a ha => (key a ha).2⟩)
    simpa using this

-- Inline check: the conclusion is the frozen statement once `eq_burnin` is supplied as an argument.
example (hd : 2 ≤ d) := fun hb =>
  (@eq_direct_assembly_proof d hd hb (@HRS.MD.EQLawPath.eq_path_stationary_proof d)
    (@HRS.MD.EQLawFlow.eq_flow_exists_proof d) : type_of% (@HRS.Main.equilibrium_paths_direct d))

end EQAsmDirect

end MD

end HRS
