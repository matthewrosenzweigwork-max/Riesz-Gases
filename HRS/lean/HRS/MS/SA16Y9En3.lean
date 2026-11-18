import HRS.MS.SA16Y9En2
import HRS.MS.SA16Y4Lm1
import HRS.MS.SA16Y3EnD13

/-!
# S.A.16 (SA16Y9) En3: difference of two mild approximations (sub-type interface, stability P4)

For two `SA16Approx` data `A1`, `A2` (same `t, CG, Bm`) with the same initial datum `φ n`, the difference `w = u¹_n - u²_n` has
`(ι² w)' = L¹ w + S`, `L¹ G = ν¹ΔG + ι B_{bc¹} G - T0¹ ι²G`, and the explicit source `sa16y9_src`
`S = (ν¹-ν²)Δu² + ι(B_{bc¹}u² - B_{bc²}u²) - (T0¹-T0²)ι²u²`.  `sa16y9_mild_diff_sub` gives
`jetEnergy(ι²w τ)^{1/p} ≤ e^{c₊τ/p} s τ` whenever `jetEnergy(S σ)^{1/p} ≤ s`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2 HRS.Whole.AppendixA.Phase2SA16S

section En3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the source of the difference of two approximations -/
def sa16y9_src {m : ℕ} {t CG Bm : ℝ} (A1 A2 : SA16Approx d m p t CG Bm) (n : ℕ) (τ : ℝ) : WmpSpace d m p :=
  (A1.ν n - A2.ν n) • sa16so_Lap d m p (A2.u n τ) +
    sa16r_iota d m p (sa16so_B d (m + 1) p (A1.bc n τ) (A2.u n τ) - sa16so_B d (m + 1) p (A2.bc n τ) (A2.u n τ)) -
    (A1.T0 n τ - A2.T0 n τ) (sa16sz_iota2 d m p (A2.u n τ))

lemma sa16y9_jetEnergy_zero (k : ℕ) : jetEnergy d k p (0 : WmpSpace d k p) = 0 := by
  have hp0 : p ≠ 0 := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  rw [sa16v2_jetEnergy_eq_norm]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [Real.zero_rpow hp0]

lemma sa16y9_deriv_f {m : ℕ} {t CG Bm : ℝ} (A : SA16Approx d m p t CG Bm) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) :
    sa16sx_f m (A.ν n) (A.K n) (A.u n) τ = A.ν n • sa16so_Lap d m p (A.u n τ) +
      sa16r_iota d m p (sa16so_B d (m + 1) p (A.bc n τ) (A.u n τ)) - A.T0 n τ (sa16sz_iota2 d m p (A.u n τ)) := by
  unfold sa16sx_f
  rw [A.hK n τ]
  have h1 := congrArg (fun L => L (sa16r_iota d (m + 1) p (A.u n τ))) (A.hcomp n τ hτ)
  simp only [ContinuousLinearMap.comp_apply] at h1
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub, h1]
  unfold sa16sz_iota2
  simp only [ContinuousLinearMap.comp_apply]
  abel

lemma sa16y9_iota2_u0 {m : ℕ} {t CG Bm : ℝ} (A : SA16Approx d m p t CG Bm) (ht : 0 < t) (n : ℕ) :
    sa16sz_iota2 d m p (A.u n 0) = sa16sz_iota2 d m p (A.φ n) := by
  have hBk : 0 ≤ A.Bk n := (ContinuousLinearMap.opNorm_nonneg _).trans (A.hKb n 0 ⟨le_rfl, ht.le⟩)
  have h0 := sa16sx_strong (A.hν n) ht (A.K n) (fun r hr => A.hKb n r hr) hBk (A.hKc n) (A.φ n) (A.hu n)
    (A.hsol n) 0 ⟨le_rfl, ht.le⟩
  simp only [intervalIntegral.integral_same, add_zero] at h0
  unfold sa16sz_iota2
  simp only [ContinuousLinearMap.comp_apply]
  exact h0

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sa16y9_mild_diff_sub {m : ℕ} {t CG Bm B s : ℝ} (A1 A2 : SA16Approx d m p t CG Bm) (ht : 0 < t) (n : ℕ)
    (hφ : A1.φ n = A2.φ n) (hs : 0 ≤ s)
    (hbc1 : ∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (A1.bc n σ))
    (hS : ∀ τ ∈ Ioo (0 : ℝ) t, jetEnergy d m p (sa16y9_src A1 A2 n τ) ^ (1 / p) ≤ s) :
    ∀ τ ∈ Icc (0 : ℝ) t, jetEnergy d m p (sa16sz_iota2 d m p (A1.u n τ - A2.u n τ)) ^ (1 / p) ≤
      Real.exp (max (p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CG) 0 / p * τ) * (s * τ) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hdu : ∀ (A : SA16Approx d m p t CG Bm) {τ : ℝ}, τ ∈ Ioo (0 : ℝ) t →
      HasDerivAt (fun r => sa16sz_iota2 d m p (A.u n r))
        (A.ν n • sa16so_Lap d m p (A.u n τ) +
          sa16r_iota d m p (sa16so_B d (m + 1) p (A.bc n τ) (A.u n τ)) -
          A.T0 n τ (sa16sz_iota2 d m p (A.u n τ))) τ := by
    intro A τ hτ
    have hBk : 0 ≤ A.Bk n := (ContinuousLinearMap.opNorm_nonneg _).trans (A.hKb n 0 ⟨le_rfl, ht.le⟩)
    have := sa16sx_hasDerivAt (A.hν n) ht (A.K n) (fun r hr => A.hKb n r hr) hBk (A.hKc n) (A.φ n) (A.hu n)
      (A.hsol n) hτ
    rw [← sa16y9_deriv_f A n (Ioo_subset_Icc_self hτ)]
    exact this
  have hmain := fun r (hr : r ∈ Ioo (0 : ℝ) t) (G : WmpSpace d (m + 1 + 1) p) =>
    sa16y3_gen_energyD_CJ (p := p) m (A1.hν n).le (hbc1 r ⟨hr.1.le, hr.2.le⟩) (A1.hbo n r ⟨hr.1.le, hr.2.le⟩)
      (A1.T0 n r) (A1.hT0 n r ⟨hr.1.le, hr.2.le⟩) G
  have key := sa16y9_energy_diff2 (m := m) (T := t) hs
    (fun r G => A1.ν n • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p (A1.bc n r) G) -
      A1.T0 n r (sa16sz_iota2 d m p G)) hmain
    (w := fun τ => A1.u n τ - A2.u n τ) ((A1.hu n).sub (A2.hu n)) (sa16y9_src A1 A2 n) hS ?_
  · intro τ hτ
    have := key τ hτ
    have h0 : sa16sz_iota2 d m p (A1.u n 0 - A2.u n 0) = 0 := by
      rw [map_sub, sa16y9_iota2_u0 A1 ht n, sa16y9_iota2_u0 A2 ht n, hφ, sub_self]
    simp only [h0, sa16y9_jetEnergy_zero, Real.zero_rpow (one_div_ne_zero (by linarith : p ≠ 0)), zero_add] at this
    exact this
  · intro τ hτ
    have h12 := (hdu A1 hτ).sub (hdu A2 hτ)
    have hfun : (fun r => sa16sz_iota2 d m p (A1.u n r - A2.u n r)) =
        fun r => sa16sz_iota2 d m p (A1.u n r) - sa16sz_iota2 d m p (A2.u n r) :=
      funext fun r => map_sub _ _ _
    rw [hfun]
    refine h12.congr_deriv ?_
    unfold sa16y9_src
    simp only [map_sub, sub_smul, ContinuousLinearMap.sub_apply, smul_sub]
    module

end En3

end HRS.Whole.AppendixA.Phase2SA16R
