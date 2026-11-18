import HRS.MS.SA16Y5Vg3
import HRS.MS.SA16ZT1
import HRS.MS.SA16RHeat13

/-!
# S.A.16 (SA16Y5) Kr1: radial integrals of `|z|^{-s}` over balls and `|z|^{-(s+1)}` outside balls (K1, part 1)

`sa16y5_radial_near`: `∫_{|z| ≤ R} |z|^{-s} = c_d R^{d-s}/(d-s)` (`s < d`), `sa16y5_radial_far`: `∫_{|z| ≥ ε} |z|^{-t} = c_d ε^{d-t}/(t-d)` (`t > d`),
with `c_d = d · vol(B_1)`, from `integral_fun_norm_addHaar`.  These give the scaling `‖ρ_near‖_1 ≲ ε^{d-s}`, `‖∇ρ_far‖_1 ≲ ε^{d-s-1}` of the heat-composed Riesz kernel.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Kr1
variable {d : ℕ}

lemma sa16y5_radial_near (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) {R : ℝ} (hR : 0 < R) :
    ∫ z : Euc d, (if ‖z‖ ≤ R then ‖z‖ ^ (-s) else 0) =
      ((d : ℝ) * volume.real (ball (0 : Euc d) 1)) * (R ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h := integral_fun_norm_addHaar (volume : Measure (Euc d)) (fun r : ℝ => if r ≤ R then r ^ (-s) else 0)
  rw [finrank_euclideanSpace_fin] at h
  simp only [nsmul_eq_mul, smul_eq_mul] at h
  rw [h]
  have h2 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (if y ≤ R then y ^ (-s) else 0) = R ^ ((d : ℝ) - s) / ((d : ℝ) - s) := by
    have e : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) * (if y ≤ R then y ^ (-s) else 0) =
        (Ioc 0 R).indicator (fun y : ℝ => y ^ ((d : ℝ) - 1 - s)) y := by
      intro y hy
      have hy0 : 0 < y := hy
      by_cases hyR : y ≤ R
      · rw [if_pos hyR, indicator_of_mem (show y ∈ Ioc 0 R from ⟨hy0, hyR⟩)]
        rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
        congr 1
        have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
          rw [Nat.cast_sub hd]; simp
        rw [this]; ring
      · rw [if_neg hyR, indicator_of_notMem (fun h => hyR h.2)]; simp
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc 0 R = Ioc 0 R from by
        ext y; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩,
      ← intervalIntegral.integral_of_le hR.le]
    rw [integral_rpow (Or.inl (by linarith)), show ((d : ℝ) - 1 - s + 1) = (d : ℝ) - s by ring,
      Real.zero_rpow (by linarith : (d : ℝ) - s ≠ 0), sub_zero]
  rw [h2]
  ring

lemma sa16y5_radial_far (hd : 1 ≤ d) {t : ℝ} (htd : (d : ℝ) < t) {ε : ℝ} (hε : 0 < ε) :
    ∫ z : Euc d, (if ε ≤ ‖z‖ then ‖z‖ ^ (-t) else 0) =
      ((d : ℝ) * volume.real (ball (0 : Euc d) 1)) * (ε ^ ((d : ℝ) - t) / (t - (d : ℝ))) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h := integral_fun_norm_addHaar (volume : Measure (Euc d)) (fun r : ℝ => if ε ≤ r then r ^ (-t) else 0)
  rw [finrank_euclideanSpace_fin] at h
  simp only [nsmul_eq_mul, smul_eq_mul] at h
  rw [h]
  have h2 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (if ε ≤ y then y ^ (-t) else 0) =
      ε ^ ((d : ℝ) - t) / (t - (d : ℝ)) := by
    have e : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) * (if ε ≤ y then y ^ (-t) else 0) =
        (Ici ε).indicator (fun y : ℝ => y ^ ((d : ℝ) - 1 - t)) y := by
      intro y hy
      have hy0 : 0 < y := hy
      by_cases hyR : ε ≤ y
      · rw [if_pos hyR, indicator_of_mem (show y ∈ Ici ε from hyR)]
        rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
        congr 1
        have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
          rw [Nat.cast_sub hd]; simp
        rw [this]; ring
      · rw [if_neg hyR, indicator_of_notMem (show y ∉ Ici ε from hyR)]; simp
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ici,
      show Ioi (0 : ℝ) ∩ Ici ε = Ici ε from by
        ext y; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; exact ⟨fun h => h.2, fun h => ⟨hε.trans_le h, h⟩⟩,
      integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) hε]
    have : (d : ℝ) - 1 - t + 1 = (d : ℝ) - t := by ring
    rw [this]
    rw [neg_div, ← div_neg, neg_sub]
  rw [h2]
  ring

end Kr1

end HRS.Whole.AppendixA.Phase2SA16R
