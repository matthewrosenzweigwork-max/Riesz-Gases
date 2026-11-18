import HRS.Main.ThermLin2Ba1

/-!
# THERMLIN2, packet Ba, part 3: A3 (`tl2_lin_window_eq`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- A3 proof: `t25p_lin_unique` with an auxiliary dual evolution along `S.ρ` (any dual evolution with a bound on `[0,a+T]`
will do; the process `Vev t 0 y + Zs t` of `hcan` does not have to be built from it). -/
theorem tl2_lin_window_eq_proof (S : HRS.Main.PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T a : ℝ) (hT : 0 < T)
    (ha : 0 ≤ a) {Ωg : Type} [MeasurableSpace Ωg] (Pg : Measure Ωg) [IsProbabilityMeasure Pg]
    (Zs : ℝ → Ωg → NegSobolev d m) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν]
    (hcan : HRS.Main.IsPreparedLinear S m (a + T) ν (ν.prod Pg) (fun p => p.1) (fun t p => Vev t 0 p.1 + Zs t p.2))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m)
    (hY : HRS.Main.IsPreparedLinear S m (a + T) ν P' Y₀ Y) :
    law P' (HRS.Main.windowPath m T a Y) =
      law (ν.prod Pg) (HRS.Main.windowPath m T a (fun t p => Vev t 0 p.1 + Zs t p.2)) := by
  have htr := HRS.T25.t25_traj S
  obtain ⟨Cr, cr, hCr, hcr, VA, hdualA, -, hdecA, -⟩ := adjk_evolution_along_trajectory S.hd htr m
  have hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖VA t r‖ ≤ Cr := by
    intro r t hr hrt _
    refine (hdecA r t hr hrt).trans ?_
    have h1 : Real.exp (-cr * (t - r)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sub_nonneg.2 hrt]
    nlinarith
  exact t25p_lin_unique S.hd htr hT ha hdualA hCr.le hKb P' (ν.prod Pg) Y₀ hY.meas Y hY.sol
    (fun p => p.1) hcan.meas _ hcan.sol (hY.law_init.trans hcan.law_init.symm)

example := (@tl2_lin_window_eq_proof : type_of% @tl2_lin_window_eq)

end HRS.ThermLin.Plan2
