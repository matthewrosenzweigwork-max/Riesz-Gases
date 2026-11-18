import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB2a
import HRS.MC.SEdgeB2b
import HRS.MC.SEdgeB3
import HRS.PDE.EnergyR2Fn

/-!
# Packet `s7_S7b_weighted_moments`, helper 1: envelope of `h_v` with explicit Lipschitz constants
`|h_v(x,y)| <= K (sum_k L_k) (g(x-y) + c)` whenever `v_k` is `L_k`-Lipschitz; `K, c` do not depend on `v`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem s7b_envelope (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 ≤ periodicRiesz d s 0 + c ∧
      (∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) ∧
      ∀ (v : Fin d → Torus d → ℝ) (L : Fin d → ℝ), (∀ k, 0 ≤ L k) →
        (∀ k, HRS.KernelGrad.IsLipschitz (L k) (v k)) → ∀ x y : Torus d,
        |Q66.q66_hv d s v x y| ≤ K * (∑ k, L k) * (periodicRiesz d s (x - y) + c) := by
  have hdpos : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨Cg, hCg⟩ := HRS.Quad.periodicRiesz_lower_env hd hs0 hsd
  obtain ⟨C, hC⟩ := HRS.KernelGrad.periodicRieszGrad_bound_tdist hd hs0 hsd
  have hg1 : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + Cg := fun z hz => by
    have := HRS.Quad.one_le_envT (d := d) (s := s) z
    have := hCg z hz
    linarith
  set c : ℝ := max Cg (1 - periodicRiesz d s 0) with hcdef
  have hcC : Cg ≤ c := le_max_left _ _
  have hc0 : 0 ≤ periodicRiesz d s 0 + c := by
    have : 1 - periodicRiesz d s 0 ≤ c := le_max_right _ _
    linarith
  refine ⟨max C 0 * (1 + d), c, by positivity, hc0, fun z hz => ?_, ?_⟩
  · have := hg1 z hz
    linarith
  intro v L hL0 hL x y
  by_cases hxy : x = y
  · subst hxy
    have : Q66.q66_hv d s v x x = 0 := by
      unfold Q66.q66_hv
      simp
    rw [this, abs_zero]
    have hLs : 0 ≤ ∑ k, L k := Finset.sum_nonneg fun k _ => hL0 k
    have : 0 ≤ periodicRiesz d s (x - x) + c := by simpa using hc0
    positivity
  set z := x - y with hzdef
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy
  set t := HRS.KernelGrad.tdist z 0 with ht
  have htpos : 0 < t := by
    rcases (HRS.KernelGrad.tdist_nonneg z 0).lt_or_eq with h | h
    · exact h
    · exact absurd ((HRS.Commutator.EnergyAux.tdist_eq_zero_iff z).1 h.symm) hz
  have htd : t ≤ d := HRS.Commutator.SliceAux.tdist_le_dim z
  have hxy_t : HRS.KernelGrad.tdist x y = t := HRS.KernelGrad.tdist_eq_sub_zero x y
  have hgrad : ∀ k, |(periodicRieszGrad d s z) k| ≤ max C 0 * (t ^ (-s - 1) + 1) := fun k => by
    have h1 : |(periodicRieszGrad d s z) k| ≤ ‖periodicRieszGrad d s z‖ := by
      have := PiLp.norm_apply_le (periodicRieszGrad d s z) k
      rwa [Real.norm_eq_abs] at this
    refine h1.trans ((hC z hz).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hterm : ∀ k, |(v k x - v k y) * (periodicRieszGrad d s (x - y)) k| ≤
      L k * (max C 0 * (t ^ (-s) + t)) := fun k => by
    rw [abs_mul]
    have h1 : |v k x - v k y| ≤ L k * t := by
      have := hL k x y
      rwa [hxy_t] at this
    have h2 := hgrad k
    have h3 : t * (t ^ (-s - 1) + 1) = t ^ (-s) + t := by
      have : t ^ (-s - 1 + 1) = t ^ (-s - 1) * t := Real.rpow_add_one htpos.ne' _
      rw [show -s - 1 + 1 = -s by ring] at this
      rw [this]; ring
    calc |v k x - v k y| * |(periodicRieszGrad d s (x - y)) k|
        ≤ (L k * t) * (max C 0 * (t ^ (-s - 1) + 1)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (hL0 k) htpos.le)
      _ = L k * (max C 0 * (t * (t ^ (-s - 1) + 1))) := by ring
      _ = _ := by rw [h3]
  have hsum : |Q66.q66_hv d s v x y| ≤ (∑ k, L k) * (max C 0 * (t ^ (-s) + t)) := by
    unfold Q66.q66_hv
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => hterm k
  have hg := hCg z hz
  have hg1z := hg1 z hz
  have hr := HRS.MC.SEdge.B2a.b2a_rpow_le_envT (d := d) (s := s) z
  have hmax : 0 ≤ max C 0 := le_max_right _ _
  have hLs : 0 ≤ ∑ k, L k := Finset.sum_nonneg fun k _ => hL0 k
  have hpos : 0 ≤ (∑ k, L k) * max C 0 := mul_nonneg hLs hmax
  have hbound : t ^ (-s) + t ≤ (1 + d) * (periodicRiesz d s z + Cg) := by
    have : HRS.Quad.envT s z ≤ periodicRiesz d s z + Cg := by linarith
    nlinarith
  have hbound' : (periodicRiesz d s z + Cg) ≤ (periodicRiesz d s z + c) := by linarith
  have hgpos : 0 ≤ periodicRiesz d s z + Cg := by linarith
  calc |Q66.q66_hv d s v x y| ≤ (∑ k, L k) * (max C 0 * (t ^ (-s) + t)) := hsum
    _ = ((∑ k, L k) * max C 0) * (t ^ (-s) + t) := by ring
    _ ≤ ((∑ k, L k) * max C 0) * ((1 + d) * (periodicRiesz d s z + c)) :=
        mul_le_mul_of_nonneg_left (hbound.trans (by gcongr)) hpos
    _ = _ := by ring

end HRS.MC.Sec7.S7b

end
