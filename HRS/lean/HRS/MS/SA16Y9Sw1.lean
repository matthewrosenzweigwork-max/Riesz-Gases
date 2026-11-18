import HRS.MS.SA16Y9Cr5
import HRS.MS.SA16Y10Sr1
import HRS.MS.SA16Y10Gi1
import HRS.MS.SA16Y10Bd3
import HRS.MS.SA16Y10Fd2
import HRS.MS.SA16Y10Cn1

/-!
# S.A.16 (SA16Y9) Sw1: `Sa16SubSrc` from the SA16Y10 results (`sa16y9_sub_src`)

Wires `sa16y10_GInt_diff_sub` (nonlocal difference), `sa16y10_bcInt_diff` (drift-coefficient difference), `sa16y10_drift_diff` (drift from density) and
`sa16y10_decay_of_coeffNormE` (frozen coefficient norm to weighted bounds) into the explicit source bound `Sa16SubSrc` of the sub regime.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Sw1
variable {d : ℕ}

/-- the interpolated truncated drift coefficients of a regular datum are bounded (qualitatively) -/
lemma sa16y9_bcInt_bdd (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB Λ ΛV G₀ νbar T : ℝ) :
    ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ N : ℕ, 1 ≤ N →
      ∃ B : ℝ, ∀ σ ∈ Icc (0 : ℝ) t,
        SA16BddCoef (m + 1) B (sa16y4_bcInt d N t (fun r => meanFieldDriftW D (μ r)) σ) := by
  obtain ⟨A, L, hA0, hL0, hbc⟩ := sa16y4_drift_const hd hs0 hsd m MB Λ ΛV G₀
  obtain ⟨B, hB0, B', hFam⟩ := sa16y4_trunc_mol_coef d m hA0 hL0
  intro D μ hD t ht N hN
  have htT : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  refine ⟨B' N, fun σ hσ => ?_⟩
  have hcoef : ∀ i ∈ Finset.range (N + 1),
      SA16BddCoef (m + 1) (B' N) (fun j => sa16y4_tm d N (fun y => meanFieldDriftW D (μ (t - (i : ℝ) * t / N)) y j)) := by
    intro i hi
    obtain ⟨hbs, hb0, hbL⟩ := hbc νbar T D μ hD _ (htT _ (sa16y4_node_mem hN ht.1 hi))
    have hbs1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (meanFieldDriftW D (μ (t - (i : ℝ) * t / N))) :=
      hbs.of_le (by exact_mod_cast Nat.le_succ _)
    have hcomp := fun j => sa16y4_comp_bounds (k := m + 1) (by omega) hbs1 hb0
      (fun k hk1 hkk x => hbL k hk1 (by omega) x) j
    exact (hFam N _ (fun j => (hcomp j).1) (fun j y => (hcomp j).2.1 y)
      (fun j k hk1 hkk x => (hcomp j).2.2 k hk1 hkk x)).2
  have hw0 : ∀ i ∈ Finset.range (N + 1), 0 ≤ sa16y4_hat N t i σ := fun i _ => sa16y4_hat_nonneg N t i σ
  have hw1 : ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ = 1 := sa16y4_hat_sum hN ht.1 hσ
  exact sa16y4_bddCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) hw0 hw1
    (c := fun i j => sa16y4_tm d N (fun y => meanFieldDriftW D (μ (t - (i : ℝ) * t / N)) y j)) hcoef

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sa16y9_sub_src (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (p : ℝ) [Fact (2 ≤ p)]
    (MB Λ ΛV G₀ νbar T : ℝ) (hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)) :
    Sa16SubSrc d s m p MB Λ ΛV G₀ νbar T := by
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ d := by linarith [hsub.1]
    exact_mod_cast this
  obtain ⟨KG, hKG0, hGI⟩ := sa16y10_GInt_diff_sub d m hd2 s p MB Λ hs0 hsub.1 hsub.2
  obtain ⟨KB, hKB0, hBd⟩ := sa16y10_bcInt_diff d m p
  obtain ⟨A, L, hA0, hL0, hbc⟩ := sa16y4_drift_const hd hs0 hsd m MB Λ ΛV G₀
  set CL : ℝ := ‖sa16so_Lap d m p‖ with hCL
  set Ci : ℝ := ‖sa16r_iota d m p‖ with hCi
  have hCL0 : 0 ≤ CL := ContinuousLinearMap.opNorm_nonneg _
  have hCi0 : 0 ≤ Ci := ContinuousLinearMap.opNorm_nonneg _
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set Cn : ℝ := (d : ℝ) ^ (m + 2) * 2 ^ (d + 3) with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  set Cdr : ℝ := ((d : ℝ) * d * MB) * ((d : ℝ) * Phase2SA16P.sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s) * Cn with hCdr
  set Ks : ℝ := max CL (Ci * (KB * Cdr) + KG * Cn) with hKs
  refine ⟨Ks, le_trans hCL0 (le_max_left _ _), fun D₁ D₂ μ₁ μ₂ hD1 hD2 hM hV δ hδ0 hδ t ht n σ hσ v => ?_⟩
  have hMB : ∀ i j, |D₁.M i j| ≤ MB := hD1.hM
  have hMB0 : 0 ≤ MB := (abs_nonneg _).trans (hMB ⟨0, by omega⟩ ⟨0, by omega⟩)
  have htT : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hreg1 : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ₁ r) := fun r hr =>
    sa16y9_regDensity_mono (by omega) (sa16so_regDensity_of_MF hD1.hμ.regular (htT r hr))
  have hreg2 : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ₂ r) := fun r hr =>
    sa16y9_regDensity_mono (by omega) (sa16so_regDensity_of_MF hD2.hμ.regular (htT r hr))
  have hdec : ∀ r ∈ Icc (0 : ℝ) t, ∀ κ ≤ m + 2, ∀ x,
      ‖iteratedFDeriv ℝ κ (fun y => μ₁ r y - μ₂ r y) x‖ ≤ (Cn * δ) * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) :=
    fun r hr => sa16y10_decay_of_coeffNormE hd hδ0 (hδ r (htT r hr))
  have hKGb := hGI t ht.1 D₁.M hMB μ₁ μ₂ hreg1 hreg2 (Cn * δ) (by positivity) hdec (n + 1) (by omega) σ hσ
  -- the drift difference
  have hdrift : ∀ r ∈ Icc (0 : ℝ) t, ∀ i : Fin d,
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => meanFieldDriftW D₁ (μ₁ r) x i - meanFieldDriftW D₂ (μ₂ r) x i) ∧
      ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j (fun x => meanFieldDriftW D₁ (μ₁ r) x i - meanFieldDriftW D₂ (μ₂ r) x i) x‖ ≤
        Cdr * δ := by
    intro r hr i
    have hdw : ∀ j ≤ m + 2, ∀ y, ‖iteratedFDeriv ℝ j (fun y => μ₁ r y - μ₂ r y) y‖ ≤ (Cn * δ) * Phase2SA16P.sa16p_w d y := by
      intro j hj y
      refine (hdec r hr j hj y).trans (le_of_eq ?_)
      unfold Phase2SA16P.sa16p_w
      congr 2
      push_cast
      ring
    obtain ⟨h1, h2⟩ := Phase2SA16P.sa16y10_drift_diff hd hs0 hsd m (D₁ := D₁) (D₂ := D₂) hD1.hs.1 hD2.hs.1 hMB hM
      (hreg1 r hr) (hreg2 r hr) hV hdw i
    refine ⟨h1, fun j hj x => (h2 j hj x).trans (le_of_eq ?_)⟩
    rw [hCdr]; ring
  have hm1 : m ≤ m := le_rfl
  have hCdδ : 0 ≤ Cdr * δ :=
    le_trans (norm_nonneg _) ((hdrift 0 ⟨le_rfl, ht.1.le⟩ ⟨0, hd⟩).2 0 (Nat.zero_le _) 0)
  obtain ⟨B₁, hB₁⟩ := sa16y9_bcInt_bdd hd s hs0 hsd m MB Λ ΛV G₀ νbar T D₁ μ₁ (sa16y9_data_mono (by omega) hD1) t ht (n + 1) (by omega)
  obtain ⟨B₂, hB₂⟩ := sa16y9_bcInt_bdd hd s hs0 hsd m MB Λ ΛV G₀ νbar T D₂ μ₂ (sa16y9_data_mono (by omega) hD2) t ht (n + 1) (by omega)
  have hbc1 : ∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, Continuous (fun y => meanFieldDriftW D₁ (μ₁ r) y j) := by
    intro r hr j
    exact (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp
      (hbc νbar T D₁ μ₁ (sa16y9_data_mono (by omega) hD1) r (htT r hr)).1.continuous
  have hbc2 : ∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, Continuous (fun y => meanFieldDriftW D₂ (μ₂ r) y j) := by
    intro r hr j
    exact (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp
      (hbc νbar T D₂ μ₂ (sa16y9_data_mono (by omega) hD2) r (htT r hr)).1.continuous
  have hBb := hBd t ht.1 (n + 1) (by omega) (fun r => meanFieldDriftW D₁ (μ₁ r)) (fun r => meanFieldDriftW D₂ (μ₂ r))
    (Cdr * δ) hCdδ
    (fun r hr j => ⟨hbc1 r hr j, hbc2 r hr j⟩)
    (fun r hr j => (hdrift r hr j).1)
    (fun r hr j y => by
      have := (hdrift r hr j).2 0 (by omega) y
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
    (fun r hr j i _ hi x => (hdrift r hr j).2 i hi x)
    (B₁ := B₁) (B₂ := B₂) (fun σ' hσ' => hB₁ σ' hσ') (fun σ' hσ' => hB₂ σ' hσ') σ hσ
  -- assemble
  have hnu : ‖(D₁.invβ - D₂.invβ) • sa16so_Lap d m p v‖ ≤ |D₁.invβ - D₂.invβ| * (CL * ‖v‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((sa16so_Lap d m p).le_opNorm v) (abs_nonneg _)
  have hBv : ‖sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) σ) v -
      sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) σ) v‖ ≤
      (KB * (Cdr * δ)) * ‖v‖ := by
    have e : sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) σ) v -
        sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) σ) v =
        (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) σ) -
          sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) σ)) v := rfl
    rw [e]
    exact (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right hBb (norm_nonneg _))
  have hBι : ‖sa16r_iota d m p (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) σ) v -
      sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) σ) v)‖ ≤
      Ci * ((KB * (Cdr * δ)) * ‖v‖) :=
    ((sa16r_iota d m p).le_opNorm _).trans (mul_le_mul_of_nonneg_left hBv hCi0)
  have hGv : ‖(sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ σ - sa16y4_GInt d m (n + 1) p s D₂.M t μ₂ σ)
      (sa16sz_iota2 d m p v)‖ ≤ (KG * (Cn * δ)) * ‖v‖ := by
    have hMeq : D₁.M = D₂.M := hM
    rw [← hMeq]
    have h3 : ‖(sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ σ - sa16y4_GInt d m (n + 1) p s D₁.M t μ₂ σ)
        (sa16sz_iota2 d m p v)‖ ≤ ‖(sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ σ -
          sa16y4_GInt d m (n + 1) p s D₁.M t μ₂ σ).comp (sa16sz_iota2 d m p)‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm
        ((sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ σ - sa16y4_GInt d m (n + 1) p s D₁.M t μ₂ σ).comp
          (sa16sz_iota2 d m p)) v
    exact h3.trans (mul_le_mul_of_nonneg_right hKGb (norm_nonneg _))
  have hnd : 0 ≤ |D₁.invβ - D₂.invβ| + δ := add_nonneg (abs_nonneg _) hδ0
  have hn1 := norm_sub_le
    ((D₁.invβ - D₂.invβ) • sa16so_Lap d m p v +
      sa16r_iota d m p (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) σ) v -
        sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) σ) v))
    ((sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ σ - sa16y4_GInt d m (n + 1) p s D₂.M t μ₂ σ) (sa16sz_iota2 d m p v))
  have hn2 := norm_add_le ((D₁.invβ - D₂.invβ) • sa16so_Lap d m p v)
    (sa16r_iota d m p (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) σ) v -
        sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) σ) v))
  have hK1 : CL ≤ Ks := le_max_left _ _
  have hK2 : Ci * (KB * Cdr) + KG * Cn ≤ Ks := le_max_right _ _
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  have hfin : |D₁.invβ - D₂.invβ| * (CL * ‖v‖) + Ci * ((KB * (Cdr * δ)) * ‖v‖) + (KG * (Cn * δ)) * ‖v‖ ≤
      Ks * (|D₁.invβ - D₂.invβ| + δ) * ‖v‖ := by
    have habs := abs_nonneg (D₁.invβ - D₂.invβ)
    have h1 : |D₁.invβ - D₂.invβ| * (CL * ‖v‖) ≤ |D₁.invβ - D₂.invβ| * (Ks * ‖v‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK1 hv0) habs
    have h2 : (Ci * (KB * Cdr) + KG * Cn) * δ * ‖v‖ ≤ Ks * δ * ‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hδ0) hv0
    nlinarith [h1, h2]
  linarith [hn1, hn2, hnu, hBι, hGv, hfin]

end Sw1

end HRS.Whole.AppendixA.Phase2SA16R
