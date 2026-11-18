import HRS.MH.MfclSpec
import HRS.MD.EQTransShift
import HRS.Sections.Q41Aux14
import HRS.Main.EqBiasFinal

/-!
# Mfcl packets A10 and A11: the deterministic bias of the centring shift
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.MfclP

open HRS HRS.Main HRS.LZ HRS.MD.EQ29 HRS.MD.EQTransShift

theorem centerShift_ratio_tendsto_proof : type_of% @HRS.MH.Mfcl.centerShift_ratio_tendsto := by
  intro d hd s hs1 hsd V hV β hβ ρβ hρβ φ hφ
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨hφc, M, hM0, hM⟩ := et_smooth_bound hφ
  have hφm : AEStronglyMeasurable φ (withDensityReal ρβ) := hφc.aestronglyMeasurable
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine (et_bias_pair_tendsto hd hs1 hsd V hV hβ hρβ hφm hM).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN2
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  obtain ⟨hac, -⟩ := HRS.Main.equilibrium_marginal_L2_proof hd hs0 hsd V hV β β hβ le_rfl |>.choose_spec.2
    β ⟨le_rfl, le_rfl⟩ ρβ hρβ N hN2
  rw [et_centerShift_eq hd hs0 hsd V hV hβ hρβ hφm hM hN0 hac]
  have hδ : 0 < (N : ℝ) ^ (1 - (d : ℝ) / s) := Real.rpow_pos_of_pos hNr _
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  field_simp

theorem centerShift_lower_proof : type_of% @HRS.MH.Mfcl.centerShift_lower := by
  intro d hd s hs1 hsd V hV β hβ ρβ hρβ hnc
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hsm : Torus.IsSmooth ρβ := (Q41.q41_thermal_regular hd hs0 hsd hβ hV hρβ).2
  have hb : 0 < supercriticalBias d s β ρβ ρβ :=
    supercriticalBias_pos_proof hd hs1 hsd V hV β hβ ρβ hρβ hnc
  have hlim := centerShift_ratio_tendsto_proof hd hs1 hsd V hV hβ ρβ hρβ ρβ hsm
  have hev := hlim.eventually (lt_mem_nhds (half_lt_self hb))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  refine ⟨supercriticalBias d s β ρβ ρβ / 2, half_pos hb, max N₁ 2, le_max_right _ _, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hD : 0 < Real.sqrt N * (N : ℝ) ^ (1 - (d : ℝ) / s) :=
    mul_pos (Real.sqrt_pos.2 hNpos) (Real.rpow_pos_of_pos hNpos _)
  have hδ : deltaN d s N = (N : ℝ) ^ (1 - (d : ℝ) / s) := by
    unfold deltaN
    rw [if_neg (not_lt.2 hs1.le), if_neg hs1.ne']
  have hr := hN₁ N hN1
  rw [lt_div_iff₀ hD] at hr
  rw [hδ]
  linarith

end HRS.MH.MfclP
