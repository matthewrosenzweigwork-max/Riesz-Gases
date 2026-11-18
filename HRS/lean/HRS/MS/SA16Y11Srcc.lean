import HRS.MS.SA16Y11Kdc
import HRS.MS.SA16Y11Src

/-!
# S.A.16 (SA16Y11) Srcc: critical copy of `Src` (`s = d-1`)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Srcc
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 3200000 in
theorem sa16y11c_src_bound (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s = (d : ℝ) - 1) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ (t : ℝ), 0 < t → ∀ μ1 μ2 : ℝ → Euc d → ℝ,
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ1 r)) →
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ2 r)) →
      ∀ δ : ℝ, 0 ≤ δ → (∀ r ∈ Icc (0 : ℝ) t, sa16y5_Dec (m + 2) δ (fun y => μ1 r y - μ2 r y)) →
      ∀ b1 b2 : ℝ → Euc d → Euc d, ∀ δb : ℝ, 0 ≤ δb →
      (∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => b1 r y j) ∧
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => b2 r y j)) →
      (∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, ∀ k ≤ m + 1, ∀ x,
        ‖iteratedFDeriv ℝ k (fun y => b1 r y j - b2 r y j) x‖ ≤ δb) →
      ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, ∀ (B1 B2 : ℝ),
      SA16BddCoef (m + 1) B1 (sa16y4_bcInt d N t b1 σ) → SA16BddCoef (m + 1) B2 (sa16y4_bcInt d N t b2 σ) →
      ∀ (ν1 ν2 : ℝ) (y : WmpSpace d (m + 1 + 1) p),
        jetEnergy d m p ((ν1 - ν2) • sa16so_Lap d m p y +
          sa16r_iota d m p ((sa16y5_Kint d m N p s M t μ1 b1 σ - sa16y5_Kint d m N p s M t μ2 b2 σ) y)) ^ (1 / p) ≤
          Ce * (|ν1 - ν2| + δb + δ) * ‖y‖ := by
  obtain ⟨C1, C2, hC1, hC2, hK⟩ := sa16y11c_Kint_diff d m hd s p MB Λ hs0 hs1 hfar
  obtain ⟨-, ⟨Cj, hCj, hjn⟩, -, -⟩ := closed_jet_energy_calculus d m p
  have hcL0 : 0 ≤ sa16so_cL d m := by unfold sa16so_cL; positivity
  set cL : ℝ := sa16so_cL d m with hcL
  refine ⟨Cj * (cL + C1 + C2), by positivity, fun M hM t ht μ1 μ2 h1 h2 δ hδ hDd b1 b2 δb hδb hsm hder N hN1 σ hσ B1 B2
    hb1 hb2 ν1 ν2 y => ?_⟩
  have hk := hK M hM t ht μ1 μ2 h1 h2 δ hδ hDd b1 b2 δb hδb hsm hder N hN1 σ hσ B1 B2 hb1 hb2 y
  have hL : ‖(ν1 - ν2) • sa16so_Lap d m p y‖ ≤ |ν1 - ν2| * cL * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact ((sa16so_Lap d m p).le_opNorm y).trans (mul_le_mul_of_nonneg_right (sa16so_Lap_norm m) (norm_nonneg _))
  have hS := (norm_add_le _ _).trans (add_le_add hL hk)
  have hjy : jetEnergy d m p ((ν1 - ν2) • sa16so_Lap d m p y +
      sa16r_iota d m p ((sa16y5_Kint d m N p s M t μ1 b1 σ - sa16y5_Kint d m N p s M t μ2 b2 σ) y)) ^ (1 / p) ≤
      Cj * ‖(ν1 - ν2) • sa16so_Lap d m p y +
      sa16r_iota d m p ((sa16y5_Kint d m N p s M t μ1 b1 σ - sa16y5_Kint d m N p s M t μ2 b2 σ) y)‖ :=
    (hjn _).2
  refine hjy.trans ?_
  have hy0 := norm_nonneg y
  have : |ν1 - ν2| * cL * ‖y‖ + (C1 * δb + C2 * δ) * ‖y‖ ≤ (cL + C1 + C2) * (|ν1 - ν2| + δb + δ) * ‖y‖ := by
    have hnu := abs_nonneg (ν1 - ν2)
    nlinarith [mul_nonneg hnu hy0, mul_nonneg hδb hy0, mul_nonneg hδ hy0, mul_nonneg hcL0 (mul_nonneg hδb hy0),
      mul_nonneg hcL0 (mul_nonneg hδ hy0), mul_nonneg hC1.le (mul_nonneg hnu hy0), mul_nonneg hC1.le (mul_nonneg hδ hy0),
      mul_nonneg hC2.le (mul_nonneg hnu hy0), mul_nonneg hC2.le (mul_nonneg hδb hy0), mul_nonneg hcL0 (mul_nonneg hnu hy0),
      mul_nonneg hC1.le (mul_nonneg hδb hy0), mul_nonneg hC2.le (mul_nonneg hδ hy0)]
  calc Cj * ‖_‖ ≤ Cj * (|ν1 - ν2| * cL * ‖y‖ + (C1 * δb + C2 * δ) * ‖y‖) := mul_le_mul_of_nonneg_left hS hCj.le
    _ ≤ Cj * ((cL + C1 + C2) * (|ν1 - ν2| + δb + δ) * ‖y‖) := mul_le_mul_of_nonneg_left this hCj.le
    _ = Cj * (cL + C1 + C2) * (|ν1 - ν2| + δb + δ) * ‖y‖ := by ring

end Srcc

end HRS.Whole.AppendixA.Phase2SA16R

end
