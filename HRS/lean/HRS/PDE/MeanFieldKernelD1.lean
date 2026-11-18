import HRS.Energy.Modulated
import HRS.Kernel.D1

/-!
# Lower bound of the periodic Riesz kernel for `d ≥ 1` (MF-01, packet KF1)

`periodicRiesz_ge` (`HRS/Energy/Modulated.lean`) is stated for `2 ≤ d`, but the argument
(`heatRiesz_ge`) only uses `2 ≤ d` through `rieszConst_pos` and `periodicRiesz_tendsto`, which
hold for `1 ≤ d` (`KernelD1Aux.rieszConst_pos_d1`, `KernelD1Aux.tendsto_d1`).  This file repeats
the argument for `1 ≤ d`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Real

namespace HRS

variable {d : ℕ}

theorem heatRiesz_ge_of_one_le {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x : Torus d, x ≠ 0 → -B ≤ heatRiesz d s ε x := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set c : ℝ := Real.exp 1 * (1 + ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    have : 0 ≤ ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) :=
      tsum_nonneg fun _ => (Real.exp_pos _).le
    positivity
  set A : ℝ := rieszConst d s * (2 * π) ^ (s - d) / Real.Gamma a with hA
  have hA0 : 0 ≤ A := by
    have := KernelD1Aux.rieszConst_pos_d1 hd hs0 hsd
    have := Real.Gamma_pos_of_pos ha
    rw [hA]; positivity
  refine ⟨A * (c * Real.Gamma a), fun ε hε x hx => ?_⟩
  rw [heatRiesz_eq_integral hsd hε x]
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * psiFn x (t + ε)) (Ioi 0) := by
    obtain ⟨M, hM0, hM⟩ := psi_bound x hx
    have hcont := psi_continuousOn x
    have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (a - 1) * psiFn x (t + ε))
        (volume.restrict (Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) ?_
      refine hcont.comp (continuousOn_id.add continuousOn_const) fun t ht => ?_
      simp only [mem_Ioi] at ht ⊢
      linarith
    refine Integrable.mono' ((Real.GammaIntegral_convergent ha).const_mul M) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    have h1 := hM (t + ε) (by linarith)
    have h2 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    have h3 := Real.rpow_pos_of_pos ht' (a - 1)
    calc t ^ (a - 1) * |psiFn x (t + ε)| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = _ := by ring
  have hG : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent ha
  have hlow : -(c * Real.Gamma a) ≤ ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x (t + ε) := by
    have h1 : ∫ t in Ioi (0:ℝ), -(c * (Real.exp (-t) * t ^ (a - 1))) = -(c * Real.Gamma a) := by
      rw [integral_neg, integral_const_mul, Real.Gamma_eq_integral ha]
    rw [← h1]
    refine setIntegral_mono_on (hG.const_mul c).neg hint measurableSet_Ioi ?_
    intro t ht
    have ht' : 0 < t := ht
    have h2 := psi_ge x (show 0 < t + ε by linarith)
    have h3 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    have h4 := Real.rpow_pos_of_pos ht' (a - 1)
    have h5 : -(c * Real.exp (-t)) ≤ psiFn x (t + ε) := by
      refine le_trans ?_ h2
      rw [neg_mul, neg_le_neg_iff, ← hc]
      exact mul_le_mul_of_nonneg_left h3 hc0
    calc -(c * (Real.exp (-t) * t ^ (a - 1))) = t ^ (a - 1) * (-(c * Real.exp (-t))) := by ring
      _ ≤ t ^ (a - 1) * psiFn x (t + ε) := by gcongr
  have : -(A * (c * Real.Gamma a)) ≤ A * ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x (t + ε) := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left hlow hA0
  exact this

/-- `periodicRiesz_ge` for `1 ≤ d`. -/
theorem periodicRiesz_ge_of_one_le {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ B : ℝ, ∀ x : Torus d, -B ≤ periodicRiesz d s x := by
  obtain ⟨B0, hB0⟩ := heatRiesz_ge_of_one_le (d := d) hd hs0 hsd
  refine ⟨|B0| + |periodicRiesz d s 0|, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    have := neg_abs_le (periodicRiesz d s 0)
    have := abs_nonneg B0
    linarith
  · have h := ge_of_tendsto (KernelD1Aux.tendsto_d1 hsd x hx)
      (Filter.eventually_of_mem (self_mem_nhdsWithin) fun ε hε => hB0 ε hε x hx)
    have := le_abs_self B0
    have := abs_nonneg (periodicRiesz d s 0)
    linarith

end HRS
