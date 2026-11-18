import HRS.MC.SEdgeVocab
import HRS.Energy.Commutator.SliceAux
import HRS.Energy.Commutator.EnergyAux
import HRS.Kernel.GradOp
import HRS.Equilibrium.LocalDivMain
import HRS.Equilibrium.QuadraticVariance

/-!
# Packet B2a: the envelope bound `|h_v(x,y)| <= B (g(x-y) + c)` (relocated proof of `sed_B2a_envelope`)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B2a

open HRS.Sec7

variable {d : ℕ} {s : ℝ}

theorem b2a_tdist_eq_eucDist {d : ℕ} (z : Torus d) :
    HRS.KernelGrad.tdist z 0 = Torus.eucDist z 0 := by
  obtain ⟨w, hw, hw'⟩ := HRS.KernelGrad.exists_mk_box z
  rw [← hw, HRS.KernelGrad.tdist_mk hw', PairCorrAux.eucDist_mk_zero' hw']

theorem b2a_rpow_le_envT {d : ℕ} {s : ℝ} (z : Torus d) :
    HRS.KernelGrad.tdist z 0 ^ (-s) ≤ HRS.Quad.envT s z := by
  unfold HRS.Quad.envT singEnvelope
  rw [← b2a_tdist_eq_eucDist]
  by_cases hs : s = 0
  · subst hs
    simp only [neg_zero, Real.rpow_zero, ite_true]
    have := abs_nonneg (Real.log (HRS.KernelGrad.tdist z 0))
    linarith
  · simp only [hs, ite_false]
    linarith

theorem b2a_main {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j)) :
    ∃ B c : ℝ, (∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) ∧
      ∀ x y : Torus d, x ≠ y →
        |Q66.q66_hv d s v x y| ≤ B * (periodicRiesz d s (x - y) + c) := by
  have hdpos : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨Cg, hCg⟩ := HRS.Quad.periodicRiesz_lower_env hd hs0 hsd
  obtain ⟨C, hC⟩ := HRS.KernelGrad.periodicRieszGrad_bound_tdist hd hs0 hsd
  have hlip : ∀ k, ∃ L : ℝ, 0 ≤ L ∧ HRS.KernelGrad.IsLipschitz L (v k) := fun k =>
    HRS.KernelGrad.isLipschitz_of_isCk
      (show Torus.IsCk 1 (v k) from
        (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (v k)) from hv k).of_le
          (by exact_mod_cast le_top))
  choose L hL0 hL using hlip
  have hg1 : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + Cg := fun z hz => by
    have := HRS.Quad.one_le_envT (d := d) (s := s) z
    have := hCg z hz
    linarith
  refine ⟨(∑ k, L k) * max C 0 * (1 + d), Cg, hg1, fun x y hxy => ?_⟩
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
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)
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
  have hr := b2a_rpow_le_envT (d := d) (s := s) z
  have hmax : 0 ≤ max C 0 := le_max_right _ _
  have hLs : 0 ≤ ∑ k, L k := Finset.sum_nonneg fun k _ => hL0 k
  have hpos : 0 ≤ (∑ k, L k) * max C 0 := mul_nonneg hLs hmax
  have hbound : t ^ (-s) + t ≤ (1 + d) * (periodicRiesz d s z + Cg) := by
    have : HRS.Quad.envT s z ≤ periodicRiesz d s z + Cg := by linarith
    nlinarith
  calc |Q66.q66_hv d s v x y| ≤ (∑ k, L k) * (max C 0 * (t ^ (-s) + t)) := hsum
    _ = ((∑ k, L k) * max C 0) * (t ^ (-s) + t) := by ring
    _ ≤ ((∑ k, L k) * max C 0) * ((1 + d) * (periodicRiesz d s z + Cg)) :=
        mul_le_mul_of_nonneg_left hbound hpos
    _ = _ := by ring

theorem sed_B2a_envelope_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j)) :
    ∃ B c : ℝ, (∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) ∧
      ∀ x y : Torus d, x ≠ y →
        |Q66.q66_hv d s v x y| ≤ B * (periodicRiesz d s (x - y) + c) :=
  b2a_main hd hs0 hs hv


end HRS.MC.SEdge.B2a
