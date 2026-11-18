import HRS.MS.ProClosureS111PhysicalOrbit
import HRS.MS.R2WinOrbAux13
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
The actual stationary orbits satisfy the frozen `R2OrbitSummable`
predicate. The singleton interval at the final starting time is treated
separately, so no equality of its totalized derivative with the physical
right derivative is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R2WinOrb

theorem weightedSup_zero_le_r2CbNormE {d j k : ℕ} (hjk : j ≤ k)
    (f : Euc d → ℝ) : weightedSupE j 0 f ≤ r2CbNormE k f := by
  unfold weightedSupE derivSupE
  refine iSup_le fun n => iSup_le fun idx => iSup_le fun x => ?_
  simp only [Real.rpow_zero, one_mul]
  have hp : |partialDeriv idx f x| ≤ ‖iteratedFDeriv ℝ (n : ℕ) f x‖ := by
    have hh := (iteratedFDeriv ℝ (n : ℕ) f x).le_opNorm
      (fun l => EuclideanSpace.single (idx l) 1)
    simpa [partialDeriv, EuclideanSpace.norm_single] using hh
  refine (ENNReal.ofReal_le_ofReal hp).trans ?_
  unfold r2CbNormE
  refine (le_iSup (fun y : Euc d => ENNReal.ofReal
    ‖iteratedFDeriv ℝ (n : ℕ) f y‖) x).trans ?_
  exact Finset.single_le_sum (f := fun z => ⨆ y : Euc d,
    ENNReal.ofReal ‖iteratedFDeriv ℝ z f y‖) (fun _ _ => zero_le)
      (Finset.mem_range.2 (by have := n.isLt; omega))

theorem stationary_weight_square_summable {d : ℕ} (hd : 1 ≤ d) :
    Summable (fun alpha : MultiIndex d => s103_b d alpha ^ 2) := by
  have hb := s103_summable hd
  have hp := hb.mul_of_nonneg hb (fun alpha => s103_b_nonneg alpha)
    (fun alpha => s103_b_nonneg alpha)
  have hdiag : Function.Injective (fun alpha : MultiIndex d => (alpha, alpha)) :=
    fun alpha beta h => congrArg Prod.fst h
  simpa only [Function.comp_def, pow_two] using hp.comp_injective hdiag

theorem physical_orbit_summable {d : ℕ} (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    (H : ℝ) (hH : 0 < H) (r : ℕ) (hr : r + 1 ≤ 4 * d + 42) :
    R2OrbitSummable ((quadraticGradientDyn d s a beta).coeff (fun _ => rho))
      ((24 * d + 240 : ℕ) : ℝ) H r := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := fun alpha : MultiIndex d => oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  obtain ⟨B, c, hB, hc, hbound⟩ := s103_orbit_iter hd hs0 hsd ha hbeta hrho
  have hA : ∀ alpha : MultiIndex d, 0 ≤ B * s103_b d alpha :=
    fun alpha => mul_nonneg hB (s103_b_nonneg alpha)
  have hU : ∀ alpha : MultiIndex d, ∀ v ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc v H,
      ContDiff ℝ (4 * d + 42) (propagatorW C v t (phi alpha)) ∧
      r2CbNormE (4 * d + 42) (propagatorW C v t (phi alpha)) ≤
        ENNReal.ofReal (B * s103_b d alpha) := by
    intro alpha v hv t ht
    have ht0 := hv.1.trans ht.1
    have hex := (physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha ht0).1
    exact hbound alpha t ht0 0 (by norm_num) _
      (HRS.MS.Fcau.propagatorW_isClassical hex) v ⟨hv.1, ht.1⟩
  have hG : ∀ alpha : MultiIndex d, ∀ v ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc v H,
      ContDiff ℝ (4 * d + 42)
        (propagatorW C v t (generatorW C t (phi alpha))) ∧
      r2CbNormE (4 * d + 42)
        (propagatorW C v t (generatorW C t (phi alpha))) ≤
        ENNReal.ofReal (B * s103_b d alpha) := by
    intro alpha v hv t ht
    have ht0 := hv.1.trans ht.1
    have hex := (physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha ht0).2
    exact hbound alpha t ht0 1 (by norm_num) _
      (HRS.MS.Fcau.propagatorW_isClassical hex) v ⟨hv.1, ht.1⟩
  have hD : ∀ alpha : MultiIndex d, ∀ v ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc v H,
      (∀ x, DifferentiableWithinAt ℝ (fun z => propagatorW C v z (phi alpha) x)
        (Icc v H) t) ∧
      ContDiff ℝ (4 * d + 42)
        (fun x => derivWithin (fun z => propagatorW C v z (phi alpha) x) (Icc v H) t) ∧
      r2CbNormE (4 * d + 42)
        (fun x => derivWithin (fun z => propagatorW C v z (phi alpha) x) (Icc v H) t) ≤
        ENNReal.ofReal (B * s103_b d alpha) := by
    intro alpha v hv t ht
    have hdv : ∀ x, HasDerivWithinAt (fun z => propagatorW C v z (phi alpha) x)
        (propagatorW C v t (generatorW C t (phi alpha)) x) (Icc v H) t :=
      fun x => (physical_terminal_derivative hd hs0 hsd ha hbeta hrho alpha hv.1 ht.1 x).mono
        (fun z hz => hz.1)
    refine ⟨fun x => (hdv x).differentiableWithinAt, ?_⟩
    by_cases hvH : v < H
    · have heq : (fun x => derivWithin (fun z => propagatorW C v z (phi alpha) x)
          (Icc v H) t) = propagatorW C v t (generatorW C t (phi alpha)) :=
        funext fun x => (hdv x).derivWithin (uniqueDiffOn_Icc hvH t ht)
      rw [heq]
      exact hG alpha v hv t ht
    · have hvEq : v = H := le_antisymm hv.2 (le_of_not_gt hvH)
      have htEq : t = H := le_antisymm ht.2 (hvEq ▸ ht.1)
      have heq : (fun x => derivWithin (fun z => propagatorW C v z (phi alpha) x)
          (Icc v H) t) = (fun _ => (0 : ℝ)) := by
        funext x
        apply derivWithin_zero_of_not_accPt
        rw [hvEq, htEq, Icc_self, accPt_principal_iff_clusterPt]
        simp [ClusterPt]
      rw [heq]
      exact ⟨contDiff_const, by simp [r2CbNormE]⟩
  constructor
  · intro alpha v hv t ht
    exact ⟨(hU alpha v hv t ht).1.of_le (by exact_mod_cast hr),
      (hD alpha v hv t ht).1,
      (hD alpha v hv t ht).2.1.of_le (by exact_mod_cast hr)⟩
  · have hsq : Summable (fun alpha : MultiIndex d => (B * s103_b d alpha) ^ 2) := by
      have hb := (stationary_weight_square_summable (by omega : 1 ≤ d)).mul_left (B ^ 2)
      convert hb using 1
      ext alpha
      ring
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun alpha => ?_)
      (hsq.mul_left 2).tsum_ofReal_lt_top
    refine iSup_le fun v => iSup_le fun hv => iSup_le fun t => iSup_le fun ht => ?_
    have hu := (weightedSup_zero_le_r2CbNormE hr _).trans (hU alpha v hv t ht).2
    have hd := (weightedSup_zero_le_r2CbNormE hr _).trans (hD alpha v hv t ht).2.2
    calc _ ≤ (ENNReal.ofReal (B * s103_b d alpha)) ^ 2 +
        (ENNReal.ofReal (B * s103_b d alpha)) ^ 2 := by gcongr
      _ = ENNReal.ofReal (2 * (B * s103_b d alpha) ^ 2) := by
        simp only [pow_two, ← ENNReal.ofReal_mul (hA alpha)]
        rw [← ENNReal.ofReal_add (mul_nonneg (hA alpha) (hA alpha))
          (mul_nonneg (hA alpha) (hA alpha))]
        congr 1
        ring

#print axioms physical_orbit_summable

end HRS.MS.ProClosureS111
