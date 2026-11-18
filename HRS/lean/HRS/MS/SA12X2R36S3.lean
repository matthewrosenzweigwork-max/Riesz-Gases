import HRS.MS.SA12X2R36S2

/-!
# S.A.12 R36 (SA12X3), part S3: the per-term cell bound

For a term `∫ φ ∂_i(K ⋆ ∂^idx(a ∂_lF))` with `φ = w² ∂^idx F`:
`|term| ≤ κ_r K (En + Di) + C₁ r^{-θ} K En` where `κ_r = ∫|Kn_r|`, `K = 8B₁² + 2 Kc + 2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRdP

variable {d : ℕ}

theorem sa12x2_cellEnergy_nonneg (m : ℕ) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z : Euc d)
    (F : Euc d → ℝ) : 0 ≤ cellEnergy m χ Ψ τ z F := by
  unfold cellEnergy jetSq
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun idx _ => integral_nonneg fun x => sq_nonneg _)

theorem sa12x2_cellDissip_nonneg (m : ℕ) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z : Euc d)
    (F : Euc d → ℝ) : 0 ≤ cellDissip m χ Ψ τ z F := by
  unfold cellDissip dissipSq
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun idx _ => Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)

theorem sa12x2_cell_term {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (m' : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ {E : Finset (Fin d → ℤ)} {χ : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} {z : Fin d → ℤ}
        {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
        (hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
          HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))))
        {c : Euc d} {w a : Euc d → ℝ} {B B1 : ℝ} (hB : 0 ≤ B) (hB1 : 0 ≤ B1)
        (ha : ContDiff ℝ ((m' + 2 : ℕ) : WithTop ℕ∞) a)
        (hBj : ∀ j ≤ m' + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ B)
        (hasup : tsupport a ⊆ closedBall c R)
        (hWa : ∀ x ∈ tsupport a, 1 ≤ sa12z3_W E χ Ψ τ z x)
        (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) (hw1 : ∀ x, |w x| ≤ 1)
        (hwB : ∀ x, ‖fderiv ℝ w x‖ ≤ B1) (hwsup : tsupport w ⊆ closedBall c R)
        (hwW : ∀ x, w x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x)
        (n : ℕ) (hn : n ≤ m' + 1) (idx : Fin n → Fin d) (i l : Fin d),
      |∫ x, (w x ^ 2 * partialDeriv idx F x) * fderiv ℝ (fun x => ∫ y, rieszKernel d s (x - y) *
          partialDeriv idx (fun y => a y * fderiv ℝ F y (EuclideanSpace.single l (1 : ℝ))) y) x
          (EuclideanSpace.single i (1 : ℝ))| ≤
        (∫ h, |r3Kn d s r h|) * ((8 * B1 ^ 2 + 2 * sa12x2_Kc d (m' + 1) B + 2) *
          ((∑ k ∈ E, cellEnergy (m' + 1) χ Ψ τ (cellPt d (z + k)) F) +
            ∑ k ∈ E, cellDissip (m' + 1) χ Ψ τ (cellPt d (z + k)) F)) +
        C1 * r ^ (-(s + 2 - d)) * ((8 * B1 ^ 2 + 2 * sa12x2_Kc d (m' + 1) B + 2) *
          ∑ k ∈ E, cellEnergy (m' + 1) χ Ψ τ (cellPt d (z + k)) F) := by
  obtain ⟨C1, hC1, hP1⟩ := sa12x2_term_bound (d := d) (s := s) hd hs0 hsd hs2 R hR
  refine ⟨C1, hC1, ?_⟩
  intro r hr hr1 E χ Ψ τ z F hF hω c w a B B1 hB hB1 ha hBj hasup hWa hw hwc hw1 hwB hwsup hwW n hn idx i l
  have hpinf : ContDiff ℝ ∞ (partialDeriv idx F) := sa12z3_pd_contDiff_inf hF idx
  have hp1 : ContDiff ℝ 1 (partialDeriv idx F) := hpinf.of_le (sa12x2_le_top _)
  have hφ1 : ContDiff ℝ 1 (fun y => w y ^ 2 * partialDeriv idx F y) := (hw.pow 2).mul hp1
  have hφc : HasCompactSupport (fun y => w y ^ 2 * partialDeriv idx F y) :=
    (hwc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right (f' := partialDeriv idx F)
  have hφsup : tsupport (fun y => w y ^ 2 * partialDeriv idx F y) ⊆ closedBall c R := by
    have h1 : tsupport (fun y => w y ^ 2) ⊆ tsupport w :=
      closure_minimal (fun y hy => subset_tsupport w (fun h0 => hy (by simp [h0]))) (isClosed_tsupport w)
    exact (tsupport_mul_subset_left (f := fun y => w y ^ 2) (g := partialDeriv idx F)).trans
      (h1.trans hwsup)
  have hacs : HasCompactSupport a :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R)
      (fun y hy => hasup (subset_tsupport _ hy))
  have hP := hP1 r hr hr1 (m' + 1) n hn c a F (fun y => w y ^ 2 * partialDeriv idx F y) i l idx ha hF hφ1 hφc
    hasup hφsup
  obtain ⟨hD, hA⟩ := sa12x2_phi_bounds (m' + 1) n hn hF hω hw hwc hw1 hB1 hwB hwW idx i
  obtain ⟨hBb, hEb, hCb⟩ := sa12x2_a_bounds m' hd hF hω hB ha hBj hacs hWa n hn idx l
  have haF : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun y => a y * F y) := by
    refine ContDiff.mul ?_ ?_
    · exact ha.of_le (by exact_mod_cast (show n + 1 ≤ m' + 2 by omega))
    · exact hF.of_le (sa12x2_le_top _)
  have hBeq : (∫ y, (fderiv ℝ (partialDeriv idx (fun y => a y * F y)) y
      (EuclideanSpace.single l (1 : ℝ))) ^ 2) =
      ∫ x, (partialDeriv (Fin.snoc idx l : Fin (n + 1) → Fin d) (fun y => a y * F y) x) ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [sa12x2_pd_snoc n (fun y => a y * F y) haF idx l y]
  rw [hBeq] at hP
  have hKn : 0 ≤ ∫ h, |r3Kn d s r h| := integral_nonneg fun _ => abs_nonneg _
  have hEn := sa12x2_cellEnergy_nonneg (d := d) (m' + 1) χ Ψ τ
  have hEn' : 0 ≤ ∑ k ∈ E, cellEnergy (m' + 1) χ Ψ τ (cellPt d (z + k)) F :=
    Finset.sum_nonneg fun k _ => hEn _ F
  have hDi' : 0 ≤ ∑ k ∈ E, cellDissip (m' + 1) χ Ψ τ (cellPt d (z + k)) F :=
    Finset.sum_nonneg fun k _ => sa12x2_cellDissip_nonneg (m' + 1) χ Ψ τ _ F
  have hKc := sa12x2_Kc_nonneg d (m' + 1) B
  have ht : 0 ≤ r ^ (-(s + 2 - d)) := Real.rpow_nonneg hr.le _
  set En := ∑ k ∈ E, cellEnergy (m' + 1) χ Ψ τ (cellPt d (z + k)) F with hEn_def
  set Di := ∑ k ∈ E, cellDissip (m' + 1) χ Ψ τ (cellPt d (z + k)) F with hDi_def
  set Kc := sa12x2_Kc d (m' + 1) B with hKc_def
  have hB1sq : 0 ≤ B1 ^ 2 := sq_nonneg _
  have h1 : (∫ x, (fderiv ℝ (fun y => w y ^ 2 * partialDeriv idx F y) x (EuclideanSpace.single i (1 : ℝ))) ^ 2) +
      (∫ x, (partialDeriv (Fin.snoc idx l : Fin (n + 1) → Fin d) (fun y => a y * F y) x) ^ 2) +
      (∫ y, (partialDeriv idx (fun y => F y * fderiv ℝ a y (EuclideanSpace.single l (1 : ℝ))) y) ^ 2) ≤
      (8 * B1 ^ 2 + 2 * Kc + 2) * (En + Di) := by
    nlinarith [mul_nonneg hKc hEn', mul_nonneg hKc hDi', mul_nonneg hB1sq hDi', mul_nonneg hB1sq hEn']
  have h2 : (∫ x, (w x ^ 2 * partialDeriv idx F x) ^ 2) +
      (∫ y, (partialDeriv idx (fun y => a y * F y) y) ^ 2) +
      (∫ y, (partialDeriv idx (fun y => F y * fderiv ℝ a y (EuclideanSpace.single l (1 : ℝ))) y) ^ 2) ≤
      (8 * B1 ^ 2 + 2 * Kc + 2) * En := by
    nlinarith [mul_nonneg hKc hEn', mul_nonneg hB1sq hEn']
  have hφeq : (fun x => w x ^ 2 * partialDeriv idx F x * fderiv ℝ (fun x => ∫ y, rieszKernel d s (x - y) *
          partialDeriv idx (fun y => a y * fderiv ℝ F y (EuclideanSpace.single l (1 : ℝ))) y) x
          (EuclideanSpace.single i (1 : ℝ))) = fun x => (fun y => w y ^ 2 * partialDeriv idx F y) x *
        fderiv ℝ (fun x => ∫ y, rieszKernel d s (x - y) *
          partialDeriv idx (fun y => a y * fderiv ℝ F y (EuclideanSpace.single l (1 : ℝ))) y) x
          (EuclideanSpace.single i (1 : ℝ)) := rfl
  refine hP.trans ?_
  have e1 := mul_le_mul_of_nonneg_left h1 hKn
  have e2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC1 ht)
  linarith

end HRS.MH.AdjointRd.Phase2SA12Near
