import HRS.MS.SA12X2R36Q1
import HRS.MS.SA12X2R36W2
import HRS.MS.SA12X2R36W3
import HRS.MS.SA12X2R36W

/-!
# S.A.12 R36 (SA12X2), part Q2: the per-term pairing bound P1

For `Q = ∂^idx(a∂_jF)` (`|idx| = n ≤ m`), the classical term `∫φ ∂_i(K ⋆ Q)` equals
`-∫∂_iφ (K⋆∂_jΦ) + ∫∂_iφ (K⋆ψ'')` with `Φ = ∂^idx(aF)` and `ψ'' = ∂^idx(F∂_ja)` (`Q1`), and is bounded by
W3 (top) and W2 (lower).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.MH.AdjointRdP

variable {d : ℕ}

/-- Tuple partials vanish off a closed set containing the support. -/
theorem sa12x2_pd_zero_gen {g : Euc d → ℝ} {T : Set (Euc d)} (hg : tsupport g ⊆ T) {j : ℕ}
    (idx : Fin j → Fin d) {x : Euc d} (hx : x ∉ T) : partialDeriv idx g x = 0 := by
  unfold partialDeriv
  have hsub : tsupport (iteratedFDeriv ℝ j g) ⊆ T :=
    (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := g) j).trans hg
  have hx' : x ∉ tsupport (iteratedFDeriv ℝ j g) := fun h => hx (hsub h)
  rw [image_eq_zero_of_notMem_tsupport hx']
  simp

/-- The classical term splits into the top piece and the lower piece (kernel-side weak form). -/
theorem sa12x2_split_term {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m n : ℕ} (hn : n ≤ m) {c : Euc d} {R : ℝ}
    (a F φ : Euc d → ℝ) (i j : Fin d) (idx : Fin n → Fin d)
    (ha : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a) (hF : ContDiff ℝ ∞ F)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hasup : tsupport a ⊆ closedBall c R) :
    ∫ x, φ x * fderiv ℝ (fun x => ∫ y, rieszKernel d s (x - y) *
          partialDeriv idx (fun y => a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) y) x
        (EuclideanSpace.single i (1 : ℝ)) =
      -(∫ x, fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) * ∫ y, rieszKernel d s (x - y) *
          fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y (EuclideanSpace.single j (1 : ℝ))) +
        ∫ x, fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) * ∫ y, rieszKernel d s (x - y) *
          partialDeriv idx (fun y => F y * fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) y := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  set e : Euc d := EuclideanSpace.single j (1 : ℝ) with he
  set ei : Euc d := EuclideanSpace.single i (1 : ℝ) with hei
  have haF : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun y => a y * F y) := by
    refine ContDiff.mul ?_ ?_
    · exact ha.of_le (by exact_mod_cast (show n + 1 ≤ m + 1 by omega))
    · exact hF.of_le (sa12x2_le_top _)
  have hdiff : Differentiable ℝ a := ha.differentiable (by exact_mod_cast Nat.succ_ne_zero m)
  have hQg : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => a y * fderiv ℝ F y e) := by
    refine ContDiff.mul ha ?_
    exact ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).of_le (sa12x2_le_top _)
  have hQ1 : ContDiff ℝ 1 (fun y => partialDeriv idx (fun y => a y * fderiv ℝ F y e) y) :=
    sa12x2_pd_cd (k := 1) (hQg.of_le (by exact_mod_cast (show n + 1 ≤ m + 1 by omega))) idx
  have hΦ1 : ContDiff ℝ 1 (fun y => partialDeriv idx (fun y => a y * F y) y) :=
    sa12x2_pd_cd (k := 1) haF idx
  have hdaC : ContDiff ℝ n (fun y => fderiv ℝ a y e) :=
    (ha.fderiv_right (m := n) (by exact_mod_cast (show n + 1 ≤ m + 1 by omega))).clm_apply contDiff_const
  have hψ0 : ContDiff ℝ 0 (fun y => partialDeriv idx (fun y => F y * fderiv ℝ a y e) y) :=
    sa12x2_pd_cd (k := 0) (by simpa using (hF.of_le (sa12x2_le_top _)).mul hdaC) idx
  -- supports
  have hsupQ : tsupport (fun y => a y * fderiv ℝ F y e) ⊆ closedBall c R :=
    tsupport_mul_subset_left.trans hasup
  have hsupΦ : tsupport (fun y => a y * F y) ⊆ closedBall c R :=
    tsupport_mul_subset_left.trans hasup
  have hsupda : tsupport (fun y => fderiv ℝ a y e) ⊆ closedBall c R := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    have h1 : fderiv ℝ a y ≠ 0 := fun h0 => Function.mem_support.1 hy (by simp [h0])
    exact hasup (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 h1))
  have hsupψ : tsupport (fun y => F y * fderiv ℝ a y e) ⊆ closedBall c R :=
    tsupport_mul_subset_right.trans hsupda
  have hQc : HasCompactSupport (fun y => partialDeriv idx (fun y => a y * fderiv ℝ F y e) y) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R) ?_
    intro y hy
    by_contra hyc
    exact Function.mem_support.1 hy (sa12x2_pd_zero_gen hsupQ idx hyc)
  have hΦc : HasCompactSupport (fun y => partialDeriv idx (fun y => a y * F y) y) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R) ?_
    intro y hy
    by_contra hyc
    exact Function.mem_support.1 hy (sa12x2_pd_zero_gen hsupΦ idx hyc)
  have hψc : HasCompactSupport (fun y => partialDeriv idx (fun y => F y * fderiv ℝ a y e) y) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R) ?_
    intro y hy
    by_contra hyc
    exact Function.mem_support.1 hy (sa12x2_pd_zero_gen hsupψ idx hyc)
  have hΦcont : Continuous (fun y => partialDeriv idx (fun y => a y * F y) y) := hΦ1.continuous
  have hψcont : Continuous (fun y => partialDeriv idx (fun y => F y * fderiv ℝ a y e) y) :=
    hψ0.continuous
  have hQ_eq : ∀ y, partialDeriv idx (fun y => a y * fderiv ℝ F y e) y =
      fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y e -
        partialDeriv idx (fun y => F y * fderiv ℝ a y e) y :=
    fun y => sa12x2_Q_identity ha hF hn idx j y
  -- the inner convolution splits
  have hΞc : Continuous (fun y => fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y e) :=
    (hΦ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hΞcc : HasCompactSupport (fun y => fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y e) :=
    hΦc.fderiv_apply ℝ e
  have hinner : ∀ x : Euc d, ∫ y, rieszKernel d s (x - y) *
        partialDeriv idx (fun y => a y * fderiv ℝ F y e) y =
      (∫ y, rieszKernel d s (x - y) * fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y e) -
        ∫ y, rieszKernel d s (x - y) * partialDeriv idx (fun y => F y * fderiv ℝ a y e) y := by
    intro x
    rw [← integral_sub (r3_conv_integrable hK hΞc hΞcc x) (r3_conv_integrable hK hψcont hψc x)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hQ_eq y]
    ring
  -- the classical term by IBP onto φ
  rw [sa12x2_ibp_conv_test hK hφ hφc hQ1 hQc ei]
  simp only [hinner]
  have hAc : Continuous (fun x => ∫ y, rieszKernel d s (x - y) *
      fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y e) :=
    (r3_contDiff_conv hK (n := 0) (contDiff_zero.mpr hΞc) hΞcc).continuous
  have hBc : Continuous (fun x => ∫ y, rieszKernel d s (x - y) *
      partialDeriv idx (fun y => F y * fderiv ℝ a y e) y) :=
    (r3_contDiff_conv hK (n := 0) (contDiff_zero.mpr hψcont) hψc).continuous
  have hdφ : Continuous (fun x => fderiv ℝ φ x ei) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x ei) := hφc.fderiv_apply ℝ ei
  have hIA : Integrable (fun x => fderiv ℝ φ x ei * ∫ y, rieszKernel d s (x - y) *
      fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y e) :=
    (hdφ.mul hAc).integrable_of_hasCompactSupport hdφc.mul_right
  have hIB : Integrable (fun x => fderiv ℝ φ x ei * ∫ y, rieszKernel d s (x - y) *
      partialDeriv idx (fun y => F y * fderiv ℝ a y e) y) :=
    (hdφ.mul hBc).integrable_of_hasCompactSupport hdφc.mul_right
  have hsplitO := integral_sub hIA hIB
  simp only [mul_sub]
  rw [hsplitO]
  ring

/-- The closure of the support of a tuple partial lies in any closed set containing the support. -/
theorem sa12x2_pd_tsupport {g : Euc d → ℝ} {T : Set (Euc d)} (hg : tsupport g ⊆ T) (hT : IsClosed T)
    {j : ℕ} (idx : Fin j → Fin d) : tsupport (partialDeriv idx g) ⊆ T := by
  apply closure_minimal _ hT
  intro y hy
  by_contra hyT
  exact Function.mem_support.1 hy (sa12x2_pd_zero_gen hg idx hyT)

/-- P1: the per-term pairing bound (top piece by W3, lower piece by W2). -/
theorem sa12x2_term_bound {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ (m n : ℕ) (hn : n ≤ m) (c : Euc d)
      (a F φ : Euc d → ℝ) (i j : Fin d) (idx : Fin n → Fin d),
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a → ContDiff ℝ ∞ F → ContDiff ℝ 1 φ →
      HasCompactSupport φ → tsupport a ⊆ closedBall c R → tsupport φ ⊆ closedBall c R →
      |∫ x, φ x * fderiv ℝ (fun x => ∫ y, rieszKernel d s (x - y) *
          partialDeriv idx (fun y => a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) y) x
          (EuclideanSpace.single i (1 : ℝ))| ≤
        (∫ h, |r3Kn d s r h|) * ((∫ x, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) ^ 2) +
            (∫ y, (fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y
              (EuclideanSpace.single j (1 : ℝ))) ^ 2) +
            ∫ y, (partialDeriv idx (fun y => F y * fderiv ℝ a y
              (EuclideanSpace.single j (1 : ℝ))) y) ^ 2) +
        C1 * r ^ (-(s + 2 - d)) * ((∫ x, φ x ^ 2) +
            (∫ y, (partialDeriv idx (fun y => a y * F y) y) ^ 2) +
            ∫ y, (partialDeriv idx (fun y => F y * fderiv ℝ a y
              (EuclideanSpace.single j (1 : ℝ))) y) ^ 2) := by
  obtain ⟨C0, hC0, hW2⟩ := sa12x2_weak_low (d := d) (s := s) hd hs0 hsd hs2 R hR
  obtain ⟨C2, hC2, hW3⟩ := sa12x2_weak_top (d := d) (s := s) hd hs0 hsd hs2
  refine ⟨C0 + C2, by linarith, ?_⟩
  intro r hr hr1 m n hn c a F φ i j idx ha hF hφ hφc hasup hφs
  rw [sa12x2_split_term hs0 hsd hn a F φ i j idx ha hF hφ hφc hasup]
  have haF : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun y => a y * F y) := by
    refine ContDiff.mul ?_ ?_
    · exact ha.of_le (by exact_mod_cast (show n + 1 ≤ m + 1 by omega))
    · exact hF.of_le (sa12x2_le_top _)
  have hdaC : ContDiff ℝ n (fun y => fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) :=
    (ha.fderiv_right (m := n) (by exact_mod_cast (show n + 1 ≤ m + 1 by omega))).clm_apply contDiff_const
  have hΦ1 : ContDiff ℝ 1 (fun y => partialDeriv idx (fun y => a y * F y) y) :=
    sa12x2_pd_cd (k := 1) haF idx
  have hψ0 : ContDiff ℝ 0 (fun y => partialDeriv idx (fun y => F y *
      fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) y) :=
    sa12x2_pd_cd (k := 0) (by simpa using (hF.of_le (sa12x2_le_top _)).mul hdaC) idx
  have hsupΦ : tsupport (fun y => a y * F y) ⊆ closedBall c R := tsupport_mul_subset_left.trans hasup
  have hsupda : tsupport (fun y => fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) ⊆ closedBall c R := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    have h1 : fderiv ℝ a y ≠ 0 := fun h0 => Function.mem_support.1 hy (by simp [h0])
    exact hasup (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 h1))
  have hsupψ : tsupport (fun y => F y * fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) ⊆
      closedBall c R := tsupport_mul_subset_right.trans hsupda
  have hΦc : HasCompactSupport (fun y => partialDeriv idx (fun y => a y * F y) y) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R)
      (fun y hy => sa12x2_pd_tsupport hsupΦ isClosed_closedBall idx (subset_tsupport _ hy))
  have hψc : HasCompactSupport (fun y => partialDeriv idx (fun y => F y *
      fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) y) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R)
      (fun y hy => sa12x2_pd_tsupport hsupψ isClosed_closedBall idx (subset_tsupport _ hy))
  have hψsup : tsupport (fun y => partialDeriv idx (fun y => F y *
      fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) y) ⊆ closedBall c R :=
    sa12x2_pd_tsupport hsupψ isClosed_closedBall idx
  have hnei : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ ≤ 1 := by simp
  have hnei' : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ ≤ 1 := by simp
  have hX := hW3 r hr φ (fun y => partialDeriv idx (fun y => a y * F y) y)
    (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) hnei' hnei hφ hφc hΦ1 hΦc
  have hY := hW2 r hr hr1 c φ (fun y => partialDeriv idx (fun y => F y *
      fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) y) (EuclideanSpace.single i (1 : ℝ)) hnei'
      hφ hφc hφs hψ0.continuous hψc hψsup
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  have hK0 : 0 ≤ ∫ h, |r3Kn d s r h| := integral_nonneg fun _ => abs_nonneg _
  have hA : 0 ≤ ∫ x, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ ∫ y, (fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y
      (EuclideanSpace.single j (1 : ℝ))) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hCc : 0 ≤ ∫ y, (partialDeriv idx (fun y => F y * fderiv ℝ a y
      (EuclideanSpace.single j (1 : ℝ))) y) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hD : 0 ≤ ∫ x, φ x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hE : 0 ≤ ∫ y, (partialDeriv idx (fun y => a y * F y) y) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have ht : 0 ≤ r ^ (-(s + 2 - d)) := Real.rpow_nonneg hr.le _
  have p1 := mul_nonneg hK0 hB
  have p2 := mul_nonneg hK0 hCc
  have p3 := mul_nonneg (mul_nonneg hC0 ht) hD
  have p4 := mul_nonneg (mul_nonneg hC0 ht) hE
  have p5 := mul_nonneg (mul_nonneg hC0 ht) hCc
  have p6 := mul_nonneg (mul_nonneg hC2 ht) hD
  have p7 := mul_nonneg (mul_nonneg hC2 ht) hE
  have p8 := mul_nonneg (mul_nonneg hC2 ht) hCc
  linarith [hX, hY, p1, p2, p3, p4, p5, p6, p7, p8]

end HRS.MH.AdjointRd.Phase2SA12
