import HRS.Main.ThermLin2E1d
import HRS.Main.ThermLin2As1
import HRS.Main.ThermLin2Ba3
import HRS.Main.ThermLin2Ba4
import HRS.Main.ThermLin2St5

/-!
# THERMLIN2, packet As, part 2: E2 (`tl2_assembly`)

Assembly of the Gaussian comparison `Y` versus `Z_β` from the chain of the plan:
`tl2_lin_window_eq` (replace `Y` by the canonical process of `tl2_canonical`), the swap of the factors of the product
measure (`tl2As_swap_law`), `tl2_init_shift` with `V`, `κ = ν` (initial datum), `tl2_zero_start_comparison` (E1),
`tl2_zero_start_vs_stationary` (D5), and `wassersteinE_triangle`.

**Black box.**  This file uses the plan statement `tl2_zero_start_comparison` (E1, `HRS.Main.ThermLinPlan2`) as a black
box (it is proved in parallel); the orchestrator swaps it for `tl2_zero_start_comparison_proof` at integration.  Hence
`#print axioms tl2_assembly_proof` shows `sorryAx` until the swap.  All other ingredients are the `_proof` theorems.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.ThermLin

variable {d : ℕ}

/-- E2 proof (uses plan statement `tl2_zero_start_comparison` as a black box).  The decay constants of `Vev` are those of
`tl2_Vev_decay_proof` (independent of the horizon `a + T`), the zero-start `W`-system is built once per `a`
(`tl2As_Wsystem`) and passed to both E1 and D5, and the final constants are `C = K₀ + C₁ + C₂`,
`c = min c₀ (min c₁ c₂)`. -/
theorem tl2_assembly_proof (S : HRS.Main.PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν]
        {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        HRS.Main.IsPreparedLinear S m (a + T) ν P' Y₀ Y →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        wassersteinE 1 (law P' (HRS.Main.windowPath m T a Y)) (law P'' (HRS.Main.windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) * (1 + ∫⁻ y, ‖y‖ₑ ∂ν) ∧
        wassersteinE 2 (law P' (HRS.Main.windowPath m T a Y)) (law P'' (HRS.Main.windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) *
            (1 + (∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2)) := by
  obtain ⟨K₀, c₀, hK₀, hc₀, hVdec⟩ := tl2_Vev_decay_proof S m hm
  obtain ⟨C1, c1, hC1, hc1, hE1⟩ := tl2_zero_start_comparison_proof S hρβ m hm T hT
  obtain ⟨C2, c2, hC2, hc2, hD5⟩ := tl2_zero_start_vs_stationary_proof S hρβ m hm T hT
  obtain ⟨Cw, cw, hCw, hcw, Wev, hWd, hWpkg⟩ := tl2_Wpkg_proof S hρβ m
  obtain ⟨Cmax, -, hEv⟩ := hWpkg 1 one_pos
  have hWp : ∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Wev T' := hEv.plain
  set c : ℝ := min c₀ (min c1 c2) with hcdef
  have hcpos : 0 < c := lt_min hc₀ (lt_min hc1 hc2)
  have hcc₀ : c ≤ c₀ := min_le_left _ _
  have hcc1 : c ≤ c1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcc2 : c ≤ c2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨K₀ + C1 + C2, c, by positivity, hcpos, ?_⟩
  intro a ha ν _ Ω' _ P' _ Y₀ Y hY Ω'' _ P'' _ Z hZ
  have hTa : 0 < a + T := by linarith
  have hmono : ∀ (x c' : ℝ), 0 ≤ x → c ≤ c' → x * Real.exp (-c' * a) ≤ x * Real.exp (-c * a) := by
    intro x c' hx hcc
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hx
  -- the canonical zero-start system for `V` on the horizon `a + T`
  obtain ⟨Ωg, mΩg, Pg, hPg, ℱ, G, Zs, Vev, hVd, hVp, -, hG, hGc, hGz, hZS, hZsm, hZsc, hprep⟩ :=
    tl2_canonical_proof S m hm (a + T) hTa
  haveI := hPg
  have hcan := hprep ν
  -- the zero-start `W`-system on the same horizon (one system for E1 and D5)
  obtain ⟨Ω₂, mΩ₂, P₂, hP₂, ℱ₂, Ĝ, Zb, hĜ, hZb, hZbm, hZbc⟩ := tl2As_Wsystem S hρβ m hm hEv hTa
  haveI := hP₂
  have hdecV : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Vev t 0‖ ≤ K₀ * Real.exp (-c₀ * t) := by
    intro t ht _
    have := hVdec Vev hVd hVp 0 t le_rfl ht
    simpa using this
  -- measurability of the window paths (so that all laws are probability measures)
  have hAEcan : AEMeasurable (Uniform.windowPath a T
      (fun t (p : NegSobolev d m × Ωg) => Vev t 0 p.1 + Zs t p.2)) (ν.prod Pg) :=
    HRS.Uniform.Comp28.aem_wp_a (ν.prod Pg) ha hT.le _ (fun t _ => hcan.sol.meas t) hcan.sol.cont
  have hL4 : law P'' (HRS.Main.windowPath m T 0 Z) = law P'' (Uniform.windowPath 0 T Z) := by
    rw [tl2Ba_uwin_eq]; rfl
  -- step 1: `Y` is replaced by the canonical process, factors swapped
  have hL1 : law P' (HRS.Main.windowPath m T a Y) = law (Pg.prod ν)
      (Uniform.windowPath a T (fun t (w : Ωg × NegSobolev d m) => Vev t 0 w.2 + Zs t w.1)) := by
    rw [tl2_lin_window_eq_proof S m hm T a hT ha Pg Zs Vev ν hcan P' Y₀ Y hY, ← tl2Ba_uwin_eq]
    exact tl2As_swap_law Pg ν _ hAEcan
  haveI : CompleteSpace (PathSp T (NegSobolev d m)) :=
    inferInstanceAs (CompleteSpace C(Set.Icc (0 : ℝ) T, NegSobolev d m))
  haveI : SecondCountableTopology (PathSp T (NegSobolev d m)) :=
    inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))
  have key : ∀ p : ℝ, (p = 1 ∨ p = 2) →
      wassersteinE p (law (Pg.prod ν)
        (Uniform.windowPath a T (fun t (w : Ωg × NegSobolev d m) => Vev t 0 w.2 + Zs t w.1)))
        (law P'' (Uniform.windowPath 0 T Z)) ≤
        ENNReal.ofReal ((K₀ + C1 + C2) * Real.exp (-c * a)) * (1 + (∫⁻ x, ‖x‖ₑ ^ p ∂ν) ^ (1 / p)) := by
    intro p hp
    have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
    have s1 := tl2_init_shift_proof hT ha hK₀ hc₀.le Vev (hVp _ hTa.le) hdecV Pg Zs hZsm hZsc ν p hp
    have s2 := hE1 a ha p hp Pg G Zs Vev hVd hVp hG hGc hGz hZS hZsm hZsc Wev hWd hWp P₂ Ĝ Zb hĜ hZb hZbm hZbc
    have s3 := hD5 a ha p hp Wev hWd hWp P₂ Ĝ Zb hĜ hZb hZbm hZbc P'' Z hZ
    have t1 := wassersteinE_triangle p hp1 (law (Pg.prod ν)
      (Uniform.windowPath a T (fun t (w : Ωg × NegSobolev d m) => Vev t 0 w.2 + Zs t w.1)))
      (law Pg (Uniform.windowPath a T Zs)) (law P'' (Uniform.windowPath 0 T Z))
    have t2 := wassersteinE_triangle p hp1 (law Pg (Uniform.windowPath a T Zs))
      (law P₂ (Uniform.windowPath a T Zb)) (law P'' (Uniform.windowPath 0 T Z))
    have s3' : wassersteinE p (law P₂ (Uniform.windowPath a T Zb)) (law P'' (Uniform.windowPath 0 T Z)) ≤
        ENNReal.ofReal (C2 * Real.exp (-c2 * a)) := s3
    set M : ℝ≥0∞ := (∫⁻ x, ‖x‖ₑ ^ p ∂ν) ^ (1 / p) with hM
    have hb1 : ENNReal.ofReal (K₀ * Real.exp (-c₀ * a)) * M ≤
        ENNReal.ofReal (K₀ * Real.exp (-c * a)) * M := by
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hmono K₀ c₀ hK₀ hcc₀)) zero_le
    have hb2 : ENNReal.ofReal (C1 * Real.exp (-c1 * a)) ≤ ENNReal.ofReal (C1 * Real.exp (-c * a)) :=
      ENNReal.ofReal_le_ofReal (hmono C1 c1 hC1.le hcc1)
    have hb3 : ENNReal.ofReal (C2 * Real.exp (-c2 * a)) ≤ ENNReal.ofReal (C2 * Real.exp (-c * a)) :=
      ENNReal.ofReal_le_ofReal (hmono C2 c2 hC2.le hcc2)
    have har := tl2As_arith (x₀ := K₀ * Real.exp (-c * a)) (x₁ := C1 * Real.exp (-c * a))
      (x₂ := C2 * Real.exp (-c * a)) (by positivity) (by positivity) (by positivity) M
    have hsum : K₀ * Real.exp (-c * a) + C1 * Real.exp (-c * a) + C2 * Real.exp (-c * a) =
        (K₀ + C1 + C2) * Real.exp (-c * a) := by ring
    rw [hsum] at har
    calc wassersteinE p (law (Pg.prod ν)
          (Uniform.windowPath a T (fun t (w : Ωg × NegSobolev d m) => Vev t 0 w.2 + Zs t w.1)))
          (law P'' (Uniform.windowPath 0 T Z))
        ≤ ENNReal.ofReal (K₀ * Real.exp (-c₀ * a)) * M + ENNReal.ofReal (C1 * Real.exp (-c1 * a)) +
            ENNReal.ofReal (C2 * Real.exp (-c2 * a)) := by
          refine t1.trans ?_
          have := add_le_add s1 (t2.trans (add_le_add s2 s3'))
          rw [← add_assoc] at this
          exact this
      _ ≤ ENNReal.ofReal (K₀ * Real.exp (-c * a)) * M + ENNReal.ofReal (C1 * Real.exp (-c * a)) +
            ENNReal.ofReal (C2 * Real.exp (-c * a)) := by gcongr
      _ ≤ _ := har
  refine ⟨?_, ?_⟩
  · have := key 1 (Or.inl rfl)
    simp only [ENNReal.rpow_one, div_one] at this
    rw [hL1, hL4]
    exact this
  · rw [hL1, hL4]
    exact key 2 (Or.inr rfl)

example := (@tl2_assembly_proof : type_of% @tl2_assembly)

end HRS.ThermLin.Plan2
