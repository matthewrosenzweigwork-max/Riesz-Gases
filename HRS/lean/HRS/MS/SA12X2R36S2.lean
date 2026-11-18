import HRS.MS.SA12X2R36S1
import HRS.MS.SA12X2R36Q2

/-!
# S.A.12 R36 (SA12X3), part S2: cover bounds for the density-side jets

For `a ∈ C^(m+1)` (`m = m'+1`) compactly supported with jets bounded by `B`, `F` smooth, `n ≤ m`:
* `∫ (∂^{snoc idx l}(aF))² ≤ K (En + Di)`;
* `∫ (∂^idx(aF))² ≤ K En`;
* `∫ (∂^idx(F ∂_l a))² ≤ K En`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

/-- The Leibniz constant. -/
def sa12x2_Kc (d m : ℕ) (B : ℝ) : ℝ :=
  B ^ 2 * ((2 : ℝ) ^ (m + 1)) ^ 2 * ((m : ℝ) + 2) * (d : ℝ) ^ (m + 1)

theorem sa12x2_Kc_nonneg (d m : ℕ) (B : ℝ) : 0 ≤ sa12x2_Kc d m B := by
  unfold sa12x2_Kc; positivity

theorem sa12x2_Kc_mono (hd : 1 ≤ d) (m : ℕ) (B : ℝ) : sa12x2_Kc d m B ≤ sa12x2_Kc d (m + 1) B := by
  unfold sa12x2_Kc
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : ((2 : ℝ) ^ (m + 1)) ^ 2 ≤ ((2 : ℝ) ^ (m + 1 + 1)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)) 2
  have h3 : ((m : ℝ) + 2) ≤ (((m + 1 : ℕ) : ℝ) + 2) := by push_cast; linarith
  have h4 : (d : ℝ) ^ (m + 1) ≤ (d : ℝ) ^ (m + 1 + 1) := pow_le_pow_right₀ hd' (Nat.le_succ _)
  gcongr

/-- Continuity, compact support and the cover property of a tuple partial of a function supported in `tsupport a`. -/
theorem sa12x2_pd_aux {a g : Euc d → ℝ} (hacs : HasCompactSupport a) (hg : tsupport g ⊆ tsupport a) {n : ℕ}
    (hgd : ContDiff ℝ n g) (idx : Fin n → Fin d) {W : Euc d → ℝ} (hWa : ∀ x ∈ tsupport a, 1 ≤ W x) :
    Continuous (partialDeriv idx g) ∧ HasCompactSupport (partialDeriv idx g) ∧
      ∀ x, partialDeriv idx g x ≠ 0 → 1 ≤ W x := by
  refine ⟨?_, ?_, ?_⟩
  · exact (sa12x2_pd_cd (k := 0) (by simpa using hgd) idx).continuous
  · exact HasCompactSupport.of_support_subset_isCompact hacs.isCompact
      (fun y hy => sa12x2_pd_tsupport hg (isClosed_tsupport a) idx (subset_tsupport _ hy))
  · intro x hx
    apply hWa
    by_contra hxa
    exact hx (sa12x2_pd_zero_gen hg idx hxa)

theorem sa12x2_a_bounds (m' : ℕ) (hd : 1 ≤ d) {E : Finset (Fin d → ℤ)} {χ : Euc d → ℝ}
    {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} {z : Fin d → ℤ} {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))))
    {a : Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B) (ha : ContDiff ℝ ((m' + 2 : ℕ) : WithTop ℕ∞) a)
    (hBj : ∀ j ≤ m' + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ B) (hacs : HasCompactSupport a)
    (hWa : ∀ x ∈ tsupport a, 1 ≤ sa12z3_W E χ Ψ τ z x) (n : ℕ) (hn : n ≤ m' + 1)
    (idx : Fin n → Fin d) (l : Fin d) :
    (∫ x, (partialDeriv (Fin.snoc idx l : Fin (n + 1) → Fin d) (fun y => a y * F y) x) ^ 2 ≤
      sa12x2_Kc d (m' + 1) B * ((∑ k ∈ E, cellEnergy (m' + 1) χ Ψ τ (cellPt d (z + k)) F) +
        ∑ k ∈ E, cellDissip (m' + 1) χ Ψ τ (cellPt d (z + k)) F)) ∧
    (∫ x, (partialDeriv idx (fun y => a y * F y) x) ^ 2 ≤
      sa12x2_Kc d (m' + 1) B * ∑ k ∈ E, cellEnergy (m' + 1) χ Ψ τ (cellPt d (z + k)) F) ∧
    (∫ x, (partialDeriv idx (fun y => F y * fderiv ℝ a y (EuclideanSpace.single l (1 : ℝ))) x) ^ 2 ≤
      sa12x2_Kc d (m' + 1) B * ∑ k ∈ E, cellEnergy (m' + 1) χ Ψ τ (cellPt d (z + k)) F) := by
  have hK0 := sa12x2_Kc_nonneg d (m' + 1) B
  have hKm := sa12x2_Kc_mono hd m' B
  have hFt : ContDiff ℝ ((m' + 2 : ℕ) : WithTop ℕ∞) F := hF.of_le (sa12x2_le_top _)
  have haF : ContDiff ℝ ((m' + 2 : ℕ) : WithTop ℕ∞) (fun y => a y * F y) := ha.mul hFt
  have hsup : tsupport (fun y => a y * F y) ⊆ tsupport a := tsupport_mul_subset_left
  have ha1 : ContDiff ℝ ((m' + 1 : ℕ) : WithTop ℕ∞) a := ha.of_le (by exact_mod_cast Nat.le_succ _)
  refine ⟨?_, ?_, ?_⟩
  · -- (a): order n+1 ≤ m+1 of aF, dissipation level
    obtain ⟨hc, hs, hW⟩ := sa12x2_pd_aux hacs hsup (n := n + 1)
      (haF.of_le (by exact_mod_cast Nat.succ_le_succ hn)) (Fin.snoc idx l) hWa
    refine (sa12x2_cover_gen (m' + 1) hF hω hK0 hK0 hc hs ?_ hW).trans (le_of_eq (by ring))
    intro x
    have h1 := sa12x2_leib_Z (m := m' + 1) hB hd ha hF hBj (j := n + 1) (by omega) (Fin.snoc idx l) x
    have h2 := sa12x2_Z_le (m' + 1) F x
    have h3 := sa12z3_Y_nonneg (m' + 1) F x
    have h4 := sa12x2_Yd_nonneg (m' + 1) F x
    unfold sa12x2_Kc at hK0 ⊢
    refine h1.trans ?_
    have hZ := HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z_nonneg (m' + 1) F x
    nlinarith [mul_le_mul_of_nonneg_left h2 hK0]
  · -- (b): order n ≤ m of aF, energy level
    obtain ⟨hc, hs, hW⟩ := sa12x2_pd_aux hacs hsup (n := n)
      (haF.of_le (by exact_mod_cast (by omega : n ≤ m' + 2))) idx hWa
    have hZY : ∀ x, HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m' F x = sa12z3_Y (m' + 1) F x := fun x => rfl
    have := sa12x2_cover_gen (m' + 1) hF hω (K1 := sa12x2_Kc d (m' + 1) B) (K2 := 0) hK0 le_rfl hc hs
      (fun x => by
        have h1 := sa12x2_leib_Z (m := m') hB hd ha1 hF (fun j hj x => hBj j (by omega) x)
          (j := n) hn idx x
        rw [hZY] at h1
        have h3 := sa12z3_Y_nonneg (m' + 1) F x
        have : sa12x2_Kc d m' B * sa12z3_Y (m' + 1) F x ≤ sa12x2_Kc d (m' + 1) B * sa12z3_Y (m' + 1) F x :=
          mul_le_mul_of_nonneg_right hKm h3
        have e : B ^ 2 * ((2 : ℝ) ^ (m' + 1)) ^ 2 * ((m' : ℝ) + 2) * (d : ℝ) ^ (m' + 1) *
            sa12z3_Y (m' + 1) F x = sa12x2_Kc d m' B * sa12z3_Y (m' + 1) F x := rfl
        rw [e] at h1
        simpa using h1.trans this) hW
    simpa using this
  · -- (c): F ∂_l a, energy level
    set e : Euc d := EuclideanSpace.single l (1 : ℝ) with he
    have hdaC : ContDiff ℝ ((m' + 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ a y e) :=
      (ha.fderiv_right (m := ((m' + 1 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast le_refl _)).clm_apply contDiff_const
    have hdaB : ∀ j ≤ m' + 1, ∀ x, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ a y e) x‖ ≤ B := by
      intro j hj x
      have hfd : ContDiffAt ℝ ((m' + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ a) x :=
        (ha.fderiv_right (m := ((m' + 1 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast le_refl _)).contDiffAt
      have h1 := norm_iteratedFDeriv_clm_apply_const (c := e) (n := j) (x := x) hfd (by exact_mod_cast hj)
      rw [norm_iteratedFDeriv_fderiv] at h1
      have hne : ‖e‖ = 1 := by simp [he]
      rw [hne, one_mul] at h1
      exact h1.trans (hBj (j + 1) (by omega) x)
    have hsupa : tsupport (fun y => fderiv ℝ a y e) ⊆ tsupport a := by
      apply closure_minimal _ (isClosed_tsupport a)
      intro y hy
      have h1 : fderiv ℝ a y ≠ 0 := fun h0 => Function.mem_support.1 hy (by simp [h0])
      exact support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 h1)
    have hsupψ : tsupport (fun y => F y * fderiv ℝ a y e) ⊆ tsupport a :=
      tsupport_mul_subset_right.trans hsupa
    have hψC : ContDiff ℝ n (fun y => F y * fderiv ℝ a y e) :=
      (hF.of_le (sa12x2_le_top _)).mul (hdaC.of_le (by exact_mod_cast hn))
    obtain ⟨hc, hs, hW⟩ := sa12x2_pd_aux hacs hsupψ hψC idx hWa
    have hZY : ∀ x, HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m' F x = sa12z3_Y (m' + 1) F x := fun x => rfl
    have hcomm : (fun y => F y * fderiv ℝ a y e) = fun y => fderiv ℝ a y e * F y := by
      funext y; exact mul_comm _ _
    have := sa12x2_cover_gen (m' + 1) hF hω (K1 := sa12x2_Kc d (m' + 1) B) (K2 := 0) hK0 le_rfl hc hs
      (fun x => by
        have h1 := sa12x2_leib_Z (m := m') hB hd hdaC hF hdaB (j := n) hn idx x
        rw [hZY] at h1
        have h3 := sa12z3_Y_nonneg (m' + 1) F x
        have : sa12x2_Kc d m' B * sa12z3_Y (m' + 1) F x ≤ sa12x2_Kc d (m' + 1) B * sa12z3_Y (m' + 1) F x :=
          mul_le_mul_of_nonneg_right hKm h3
        have e : B ^ 2 * ((2 : ℝ) ^ (m' + 1)) ^ 2 * ((m' : ℝ) + 2) * (d : ℝ) ^ (m' + 1) *
            sa12z3_Y (m' + 1) F x = sa12x2_Kc d m' B * sa12z3_Y (m' + 1) F x := rfl
        rw [e] at h1
        rw [hcomm]
        simpa using h1.trans this) hW
    simpa using this

end HRS.MH.AdjointRd.Phase2SA12Near
