import HRS.MS.SA16Y9Lw1

/-!
# S.A.16 (SA16Y9) En4: difference of two level-`m+2` approximations measured at level `m` (stability, G1b)

`sa16y9_mild_diff_low`: `A1`, `A2 : SA16Approx d (m+2) p t CG Bm` (solutions in `W^{m+4,p}`), `v_a = ι²_{m+2} u^a_n ∈ W^{m+2,p}`.
Given level-`m` operators `Tl_a` with `ι²_m ∘ T0^a = Tl_a ∘ ι²_m`, the difference `v₁ - v₂` satisfies the energy inequality of
`sa16y9_energy_diff2` at level `m` with the source `sa16y9_srcl`
`S = (ν¹-ν²)Δ_m v₂ + ι_m(B_{m+1}(bc¹) v₂ - B_{m+1}(bc²) v₂) - (Tl₁-Tl₂)ι²_m v₂`, whence `jetEnergy(ι²_m(v₁-v₂))^{1/p} ≤ e^{c₊τ/p} s τ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2 HRS.Whole.AppendixA.Phase2SA16S

section En4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y9_hasDerivAt_u {k : ℕ} {t CG Bm : ℝ} (A : SA16Approx d k p t CG Bm) (ht : 0 < t) (n : ℕ) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) t) :
    HasDerivAt (fun r => sa16sz_iota2 d k p (A.u n r))
      (A.ν n • sa16so_Lap d k p (A.u n τ) +
        sa16r_iota d k p (sa16so_B d (k + 1) p (A.bc n τ) (A.u n τ)) -
        A.T0 n τ (sa16sz_iota2 d k p (A.u n τ))) τ := by
  have hBk : 0 ≤ A.Bk n := (ContinuousLinearMap.opNorm_nonneg _).trans (A.hKb n 0 ⟨le_rfl, ht.le⟩)
  have := sa16sx_hasDerivAt (A.hν n) ht (A.K n) (fun r hr => A.hKb n r hr) hBk (A.hKc n) (A.φ n) (A.hu n)
    (A.hsol n) hτ
  rw [← sa16y9_deriv_f A n (Ioo_subset_Icc_self hτ)]
  exact this

/-- the source of the lowered difference -/
def sa16y9_srcl {m : ℕ} {t CG Bm : ℝ} (A1 A2 : SA16Approx d (m + 2) p t CG Bm)
    (Tl1 Tl2 : ℕ → ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p) (n : ℕ) (τ : ℝ) : WmpSpace d m p :=
  (A1.ν n - A2.ν n) • sa16so_Lap d m p (sa16sz_iota2 d (m + 2) p (A2.u n τ)) +
    sa16r_iota d m p (sa16so_B d (m + 1) p (A1.bc n τ) (sa16sz_iota2 d (m + 2) p (A2.u n τ)) -
      sa16so_B d (m + 1) p (A2.bc n τ) (sa16sz_iota2 d (m + 2) p (A2.u n τ))) -
    (Tl1 n τ - Tl2 n τ) (sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A2.u n τ)))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- the lowered derivative identity -/
lemma sa16y9_low_deriv {m : ℕ} {t CG Bm : ℝ} (A : SA16Approx d (m + 2) p t CG Bm)
    (Tl : ℕ → ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t)
    (hc3 : (sa16sz_iota2 d m p).comp (A.T0 n τ) = (Tl n τ).comp (sa16sz_iota2 d m p)) :
    sa16sz_iota2 d m p (A.ν n • sa16so_Lap d (m + 2) p (A.u n τ) +
        sa16r_iota d (m + 2) p (sa16so_B d (m + 2 + 1) p (A.bc n τ) (A.u n τ)) -
        A.T0 n τ (sa16sz_iota2 d (m + 2) p (A.u n τ))) =
      A.ν n • sa16so_Lap d m p (sa16sz_iota2 d (m + 2) p (A.u n τ)) +
        sa16r_iota d m p (sa16so_B d (m + 1) p (A.bc n τ) (sa16sz_iota2 d (m + 2) p (A.u n τ))) -
        Tl n τ (sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A.u n τ))) := by
  have h1 := congrArg (fun L => L (A.u n τ)) (sa16y9_Lap_low (d := d) (p := p) m)
  have h2 := congrArg (fun L => L (A.u n τ)) (sa16y9_B_low (d := d) (p := p) m (A.hbo n τ hτ))
  have h3 := congrArg (fun L => L (sa16sz_iota2 d (m + 2) p (A.u n τ))) hc3
  simp only [ContinuousLinearMap.comp_apply] at h1 h2 h3
  rw [map_sub, map_add, map_smul, h1, h2, h3]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sa16y9_mild_diff_low {m : ℕ} {t CG Bm B s CGl : ℝ} (A1 A2 : SA16Approx d (m + 2) p t CG Bm)
    (Tl1 Tl2 : ℕ → ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p) (ht : 0 < t) (n : ℕ)
    (hφ : A1.φ n = A2.φ n) (hs : 0 ≤ s)
    (hc31 : ∀ σ ∈ Icc (0 : ℝ) t, (sa16sz_iota2 d m p).comp (A1.T0 n σ) = (Tl1 n σ).comp (sa16sz_iota2 d m p))
    (hc32 : ∀ σ ∈ Icc (0 : ℝ) t, (sa16sz_iota2 d m p).comp (A2.T0 n σ) = (Tl2 n σ).comp (sa16sz_iota2 d m p))
    (hTl1 : ∀ σ ∈ Icc (0 : ℝ) t, ‖Tl1 n σ‖ ≤ CGl)
    (hbc1 : ∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (A1.bc n σ))
    (hS : ∀ τ ∈ Ioo (0 : ℝ) t, jetEnergy d m p (sa16y9_srcl A1 A2 Tl1 Tl2 n τ) ^ (1 / p) ≤ s) :
    ∀ τ ∈ Icc (0 : ℝ) t, jetEnergy d m p (sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A1.u n τ) -
        sa16sz_iota2 d (m + 2) p (A2.u n τ))) ^ (1 / p) ≤
      Real.exp (max (p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CGl) 0 / p * τ) * (s * τ) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hmain := fun r (hr : r ∈ Ioo (0 : ℝ) t) (G : WmpSpace d (m + 1 + 1) p) =>
    sa16y3_gen_energyD_CJ (p := p) m (A1.hν n).le (hbc1 r ⟨hr.1.le, hr.2.le⟩)
      (SA16BddCoef.mk (A1.hbo n r ⟨hr.1.le, hr.2.le⟩).nonneg (A1.hbo n r ⟨hr.1.le, hr.2.le⟩).smooth
        (fun i j hj x => (A1.hbo n r ⟨hr.1.le, hr.2.le⟩).bound i j (by omega) x))
      (Tl1 n r) (hTl1 r ⟨hr.1.le, hr.2.le⟩) G
  have hw : ContinuousOn (fun τ => sa16sz_iota2 d (m + 2) p (A1.u n τ) - sa16sz_iota2 d (m + 2) p (A2.u n τ))
      (Icc 0 t) :=
    ((sa16sz_iota2 d (m + 2) p).continuous.comp_continuousOn (A1.hu n)).sub
      ((sa16sz_iota2 d (m + 2) p).continuous.comp_continuousOn (A2.hu n))
  have key := sa16y9_energy_diff2 (m := m) (T := t) hs
    (fun r G => A1.ν n • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p (A1.bc n r) G) -
      Tl1 n r (sa16sz_iota2 d m p G)) hmain
    (w := fun τ => sa16sz_iota2 d (m + 2) p (A1.u n τ) - sa16sz_iota2 d (m + 2) p (A2.u n τ)) hw
    (sa16y9_srcl A1 A2 Tl1 Tl2 n) hS ?_
  · intro τ hτ
    have := key τ hτ
    have h0 : sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A1.u n 0) - sa16sz_iota2 d (m + 2) p (A2.u n 0)) = 0 := by
      rw [sa16y9_iota2_u0 A1 ht n, sa16y9_iota2_u0 A2 ht n, hφ, sub_self, map_zero]
    simp only [h0, sa16y9_jetEnergy_zero, Real.zero_rpow (one_div_ne_zero (by linarith : p ≠ 0)), zero_add] at this
    exact this
  · intro τ hτ
    have hτc := Ioo_subset_Icc_self hτ
    have hd1 := (sa16sz_iota2 d m p).hasFDerivAt.comp_hasDerivAt τ (sa16y9_hasDerivAt_u A1 ht n hτ)
    have hd2 := (sa16sz_iota2 d m p).hasFDerivAt.comp_hasDerivAt τ (sa16y9_hasDerivAt_u A2 ht n hτ)
    have h12 := hd1.sub hd2
    have hfun : (fun r => sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A1.u n r) -
        sa16sz_iota2 d (m + 2) p (A2.u n r))) = fun r => (sa16sz_iota2 d m p ∘ fun r => sa16sz_iota2 d (m + 2) p (A1.u n r)) r -
          (sa16sz_iota2 d m p ∘ fun r => sa16sz_iota2 d (m + 2) p (A2.u n r)) r :=
      funext fun r => by simp [map_sub]
    rw [hfun]
    refine h12.congr_deriv ?_
    have e1 := sa16y9_low_deriv A1 Tl1 n hτc (hc31 τ hτc)
    have e2 := sa16y9_low_deriv A2 Tl2 n hτc (hc32 τ hτc)
    rw [e1, e2]
    unfold sa16y9_srcl
    simp only [map_sub, sub_smul, ContinuousLinearMap.sub_apply, smul_sub]
    module

end En4

end HRS.Whole.AppendixA.Phase2SA16R
