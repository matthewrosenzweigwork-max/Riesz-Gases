import HRS.MS.SA16Y9Gc2

/-!
# S.A.16 (SA16Y9) En5: difference of two level-`m+2` iso approximations measured at level `m` (iso pipeline, step 6)

Analogue of `En4` for `SA16ApproxI` (`K = B_bc - N`): `sa16y9i_mild_diff_low`.
Given level-`m` operators `Nl_a : W^{m+2} →L W^{m+1}` with `ι²_m ι_{m+2} N^a = ι_m Nl_a ι²_{m+2}` and the level-`m` dissipation of `Nl₁`, the
difference `v₁ - v₂`, `v_a = ι²_{m+2} u^a_n`, satisfies `jetEnergy(ι²_m(v₁-v₂))^{1/p} ≤ e^{c₊τ/p} s τ` whenever the source
`S = (ν¹-ν²)Δ_m v₂ + ι_m(B(bc¹)v₂ - B(bc²)v₂) - ι_m((Nl₁-Nl₂)v₂)` has `jetEnergy(S)^{1/p} ≤ s`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2 HRS.Whole.AppendixA.Phase2SA16S

section En5
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y9i_iota2_u0 {m : ℕ} {t Bm : ℝ} (A : SA16ApproxI d m p t Bm) (ht : 0 < t) (n : ℕ) :
    sa16sz_iota2 d m p (A.u n 0) = sa16sz_iota2 d m p (A.φ n) := by
  have hBk : 0 ≤ A.Bk n := (ContinuousLinearMap.opNorm_nonneg _).trans (A.hKb n 0 ⟨le_rfl, ht.le⟩)
  have h0 := sa16sx_strong (A.hν n) ht (A.K n) (fun r hr => A.hKb n r hr) hBk (A.hKc n) (A.φ n) (A.hu n)
    (A.hsol n) 0 ⟨le_rfl, ht.le⟩
  simp only [intervalIntegral.integral_same, add_zero] at h0
  unfold sa16sz_iota2
  simp only [ContinuousLinearMap.comp_apply]
  exact h0

lemma sa16y9i_hasDerivAt_u {k : ℕ} {t Bm : ℝ} (A : SA16ApproxI d k p t Bm) (ht : 0 < t) (n : ℕ) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) t) :
    HasDerivAt (fun r => sa16sz_iota2 d k p (A.u n r))
      (A.ν n • sa16so_Lap d k p (A.u n τ) +
        sa16r_iota d k p (sa16so_B d (k + 1) p (A.bc n τ) (A.u n τ)) -
        sa16r_iota d k p (A.N n τ (A.u n τ))) τ := by
  have hBk : 0 ≤ A.Bk n := (ContinuousLinearMap.opNorm_nonneg _).trans (A.hKb n 0 ⟨le_rfl, ht.le⟩)
  have := sa16sx_hasDerivAt (A.hν n) ht (A.K n) (fun r hr => A.hKb n r hr) hBk (A.hKc n) (A.φ n) (A.hu n)
    (A.hsol n) hτ
  refine this.congr_deriv ?_
  unfold sa16sx_f
  rw [A.hK n τ]
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  abel

/-- the source of the lowered difference -/
def sa16y9i_srcl {m : ℕ} {t Bm : ℝ} (A1 A2 : SA16ApproxI d (m + 2) p t Bm)
    (Nl1 Nl2 : ℕ → ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p) (n : ℕ) (τ : ℝ) : WmpSpace d m p :=
  (A1.ν n - A2.ν n) • sa16so_Lap d m p (sa16sz_iota2 d (m + 2) p (A2.u n τ)) +
    sa16r_iota d m p (sa16so_B d (m + 1) p (A1.bc n τ) (sa16sz_iota2 d (m + 2) p (A2.u n τ)) -
      sa16so_B d (m + 1) p (A2.bc n τ) (sa16sz_iota2 d (m + 2) p (A2.u n τ))) -
    sa16r_iota d m p ((Nl1 n τ - Nl2 n τ) (sa16sz_iota2 d (m + 2) p (A2.u n τ)))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- the lowered derivative identity -/
lemma sa16y9i_low_deriv {m : ℕ} {t Bm : ℝ} (A : SA16ApproxI d (m + 2) p t Bm)
    (Nl : ℕ → ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p) (n : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) t)
    (hc3 : (sa16sz_iota2 d m p).comp ((sa16r_iota d (m + 2) p).comp (A.N n τ)) =
      (sa16r_iota d m p).comp ((Nl n τ).comp (sa16sz_iota2 d (m + 2) p))) :
    sa16sz_iota2 d m p (A.ν n • sa16so_Lap d (m + 2) p (A.u n τ) +
        sa16r_iota d (m + 2) p (sa16so_B d (m + 2 + 1) p (A.bc n τ) (A.u n τ)) -
        sa16r_iota d (m + 2) p (A.N n τ (A.u n τ))) =
      A.ν n • sa16so_Lap d m p (sa16sz_iota2 d (m + 2) p (A.u n τ)) +
        sa16r_iota d m p (sa16so_B d (m + 1) p (A.bc n τ) (sa16sz_iota2 d (m + 2) p (A.u n τ))) -
        sa16r_iota d m p (Nl n τ (sa16sz_iota2 d (m + 2) p (A.u n τ))) := by
  have h1 := congrArg (fun L => L (A.u n τ)) (sa16y9_Lap_low (d := d) (p := p) m)
  have h2 := congrArg (fun L => L (A.u n τ)) (sa16y9_B_low (d := d) (p := p) m (A.hbo n τ hτ))
  have h3 := congrArg (fun L => L (A.u n τ)) hc3
  simp only [ContinuousLinearMap.comp_apply] at h1 h2 h3
  rw [map_sub, map_add, map_smul, h1, h2, h3]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sa16y9i_mild_diff_low {m : ℕ} {t Bm B s cN : ℝ} (A1 A2 : SA16ApproxI d (m + 2) p t Bm)
    (Nl1 Nl2 : ℕ → ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p) (ht : 0 < t) (n : ℕ)
    (hφ : A1.φ n = A2.φ n) (hs : 0 ≤ s)
    (hc31 : ∀ σ ∈ Icc (0 : ℝ) t, (sa16sz_iota2 d m p).comp ((sa16r_iota d (m + 2) p).comp (A1.N n σ)) =
      (sa16r_iota d m p).comp ((Nl1 n σ).comp (sa16sz_iota2 d (m + 2) p)))
    (hc32 : ∀ σ ∈ Icc (0 : ℝ) t, (sa16sz_iota2 d m p).comp ((sa16r_iota d (m + 2) p).comp (A2.N n σ)) =
      (sa16r_iota d m p).comp ((Nl2 n σ).comp (sa16sz_iota2 d (m + 2) p)))
    (hdiss : ∀ σ ∈ Icc (0 : ℝ) t, ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (Nl1 n σ G))) ≤
        cN * jetEnergy d m p (sa16sz_iota2 d m p G))
    (hbc1 : ∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (A1.bc n σ))
    (hS : ∀ τ ∈ Ioo (0 : ℝ) t, jetEnergy d m p (sa16y9i_srcl A1 A2 Nl1 Nl2 n τ) ^ (1 / p) ≤ s) :
    ∀ τ ∈ Icc (0 : ℝ) t, jetEnergy d m p (sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A1.u n τ) -
        sa16sz_iota2 d (m + 2) p (A2.u n τ))) ^ (1 / p) ≤
      Real.exp (max (p * sa16sz_cTr d m p B + cN) 0 / p * τ) * (s * τ) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hmain := fun r (hr : r ∈ Ioo (0 : ℝ) t) (G : WmpSpace d (m + 1 + 1) p) =>
    sa16y3_gen_energy_dissD (p := p) m (A1.hν n).le (hbc1 r ⟨hr.1.le, hr.2.le⟩)
      (SA16BddCoef.mk (A1.hbo n r ⟨hr.1.le, hr.2.le⟩).nonneg (A1.hbo n r ⟨hr.1.le, hr.2.le⟩).smooth
        (fun i j hj x => (A1.hbo n r ⟨hr.1.le, hr.2.le⟩).bound i j (by omega) x))
      (fun G => sa16r_iota d m p (Nl1 n r G)) (fun G => hdiss r ⟨hr.1.le, hr.2.le⟩ G) G
  have hw : ContinuousOn (fun τ => sa16sz_iota2 d (m + 2) p (A1.u n τ) - sa16sz_iota2 d (m + 2) p (A2.u n τ))
      (Icc 0 t) :=
    ((sa16sz_iota2 d (m + 2) p).continuous.comp_continuousOn (A1.hu n)).sub
      ((sa16sz_iota2 d (m + 2) p).continuous.comp_continuousOn (A2.hu n))
  have key := sa16y9_energy_diff2 (m := m) (T := t) hs
    (fun r G => A1.ν n • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p (A1.bc n r) G) -
      sa16r_iota d m p (Nl1 n r G)) hmain
    (w := fun τ => sa16sz_iota2 d (m + 2) p (A1.u n τ) - sa16sz_iota2 d (m + 2) p (A2.u n τ)) hw
    (sa16y9i_srcl A1 A2 Nl1 Nl2 n) hS ?_
  · intro τ hτ
    have := key τ hτ
    have h0 : sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A1.u n 0) - sa16sz_iota2 d (m + 2) p (A2.u n 0)) = 0 := by
      rw [sa16y9i_iota2_u0 A1 ht n, sa16y9i_iota2_u0 A2 ht n, hφ, sub_self, map_zero]
    simp only [h0, sa16y9_jetEnergy_zero, Real.zero_rpow (one_div_ne_zero (by linarith : p ≠ 0)), zero_add] at this
    exact this
  · intro τ hτ
    have hτc := Ioo_subset_Icc_self hτ
    have hd1 := (sa16sz_iota2 d m p).hasFDerivAt.comp_hasDerivAt τ (sa16y9i_hasDerivAt_u A1 ht n hτ)
    have hd2 := (sa16sz_iota2 d m p).hasFDerivAt.comp_hasDerivAt τ (sa16y9i_hasDerivAt_u A2 ht n hτ)
    have h12 := hd1.sub hd2
    have hfun : (fun r => sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A1.u n r) -
        sa16sz_iota2 d (m + 2) p (A2.u n r))) = fun r => (sa16sz_iota2 d m p ∘ fun r => sa16sz_iota2 d (m + 2) p (A1.u n r)) r -
          (sa16sz_iota2 d m p ∘ fun r => sa16sz_iota2 d (m + 2) p (A2.u n r)) r :=
      funext fun r => by simp [map_sub]
    rw [hfun]
    refine h12.congr_deriv ?_
    have e1 := sa16y9i_low_deriv A1 Nl1 n hτc (hc31 τ hτc)
    have e2 := sa16y9i_low_deriv A2 Nl2 n hτc (hc32 τ hτc)
    rw [e1, e2]
    unfold sa16y9i_srcl
    simp only [map_sub, sub_smul, ContinuousLinearMap.sub_apply, smul_sub]
    module

end En5

end HRS.Whole.AppendixA.Phase2SA16R
