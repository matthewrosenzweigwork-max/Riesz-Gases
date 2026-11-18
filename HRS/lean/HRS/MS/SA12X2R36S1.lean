import HRS.MS.SA12X2R36S0
import HRS.MS.SA12X2R36P0
import HRS.MS.SA12X2R36Q1

/-!
# S.A.12 R36 (SA12X3), part S1: cover bounds for the test function `φ = w² ∂^idx F`

`∫ φ² ≤ ∑ cellEnergy` and `∫ (∂_iφ)² ≤ 8 B₁² ∑ cellEnergy + 2 ∑ cellDissip`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12x2_sq_le_Y {m n : ℕ} (hn : n ≤ m) (F : Euc d → ℝ) (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx F x ^ 2 ≤ sa12z3_Y m F x := by
  unfold sa12z3_Y
  refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ γ : Fin r → Fin d, partialDeriv γ F x ^ 2)
    (fun r _ => Finset.sum_nonneg fun γ _ => sq_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hn)))
  exact Finset.single_le_sum (f := fun γ : Fin n → Fin d => partialDeriv γ F x ^ 2)
    (fun γ _ => sq_nonneg _) (Finset.mem_univ idx)

theorem sa12x2_sq_le_Yd {m n : ℕ} (hn : n ≤ m) (F : Euc d → ℝ) (idx : Fin n → Fin d) (i : Fin d)
    (x : Euc d) :
    partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x ^ 2 ≤ sa12x2_Yd m F x := by
  unfold sa12x2_Yd
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun r => ∑ γ : Fin r → Fin d, ∑ i : Fin d, partialDeriv (Fin.snoc γ i : Fin (r + 1) → Fin d) F x ^ 2)
    (fun r _ => Finset.sum_nonneg fun γ _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hn)))
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun γ : Fin n → Fin d => ∑ i : Fin d, partialDeriv (Fin.snoc γ i : Fin (n + 1) → Fin d) F x ^ 2)
    (fun γ _ => Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.mem_univ idx))
  exact Finset.single_le_sum (f := fun i : Fin d => partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ i)

/-- The product rule for `φ = w² p`. -/
theorem sa12x2_phi_deriv {w p : Euc d → ℝ} (hw : ContDiff ℝ 1 w) (hp : ContDiff ℝ 1 p) (v x : Euc d) :
    fderiv ℝ (fun y => w y ^ 2 * p y) x v =
      2 * w x * fderiv ℝ w x v * p x + w x ^ 2 * fderiv ℝ p x v := by
  have hwd : DifferentiableAt ℝ w x := (hw.differentiable one_ne_zero) x
  have hpd : DifferentiableAt ℝ p x := (hp.differentiable one_ne_zero) x
  have h1 : HasFDerivAt (fun y => w y ^ 2) ((2 * w x) • fderiv ℝ w x) x := by
    have := hwd.hasFDerivAt.pow 2
    simpa using this
  have h2 := h1.mul hpd.hasFDerivAt
  have h3 : fderiv ℝ (fun y => w y ^ 2 * p y) x = _ := h2.fderiv
  rw [h3]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem sa12x2_phi_bounds (m n : ℕ) (hn : n ≤ m) {E : Finset (Fin d → ℤ)} {χ : Euc d → ℝ}
    {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} {z : Fin d → ℤ} {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))))
    {w : Euc d → ℝ} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) (hw1 : ∀ x, |w x| ≤ 1)
    {B1 : ℝ} (hB1 : 0 ≤ B1) (hwB : ∀ x, ‖fderiv ℝ w x‖ ≤ B1)
    (hwW : ∀ x, w x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x) (idx : Fin n → Fin d) (i : Fin d) :
    (∫ x, (w x ^ 2 * partialDeriv idx F x) ^ 2 ≤ ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F) ∧
    (∫ x, (fderiv ℝ (fun y => w y ^ 2 * partialDeriv idx F y) x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤
      8 * B1 ^ 2 * (∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F) +
        2 * ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F) := by
  have hpinf : ContDiff ℝ ∞ (partialDeriv idx F) := sa12z3_pd_contDiff_inf hF idx
  have hp1 : ContDiff ℝ 1 (partialDeriv idx F) := hpinf.of_le (sa12x2_le_top _)
  have hφ1 : ContDiff ℝ 1 (fun y => w y ^ 2 * partialDeriv idx F y) := (hw.pow 2).mul hp1
  have hφc : HasCompactSupport (fun y => w y ^ 2 * partialDeriv idx F y) := by
    have h := (hwc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right (f' := partialDeriv idx F)
    exact h
  have hw2 : ∀ x, w x ^ 2 ≤ 1 := by
    intro x
    have := hw1 x
    nlinarith [sq_abs (w x), abs_nonneg (w x)]
  constructor
  · -- D
    have := sa12x2_cover_gen m hF hω (K1 := 1) (K2 := 0) zero_le_one le_rfl
      (f := fun x => w x ^ 2 * partialDeriv idx F x) hφ1.continuous hφc
      (fun x => by
        have h1 := sa12x2_sq_le_Y hn F idx x
        have h2 : (w x ^ 2 * partialDeriv idx F x) ^ 2 ≤ partialDeriv idx F x ^ 2 := by
          have : (w x ^ 2) ^ 2 ≤ 1 := by
            have := hw2 x
            nlinarith [sq_nonneg (w x)]
          calc (w x ^ 2 * partialDeriv idx F x) ^ 2 = (w x ^ 2) ^ 2 * partialDeriv idx F x ^ 2 := by ring
            _ ≤ 1 * partialDeriv idx F x ^ 2 := by gcongr
            _ = _ := one_mul _
        have h3 := sa12x2_Yd_nonneg m F x
        nlinarith)
      (fun x hx => hwW x (fun h0 => hx (by simp [h0])))
    simpa using this
  · -- A
    set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
    have hFn : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F := hF.of_le (sa12x2_le_top _)
    have hkey : ∀ x, fderiv ℝ (fun y => w y ^ 2 * partialDeriv idx F y) x e =
        2 * w x * fderiv ℝ w x e * partialDeriv idx F x +
          w x ^ 2 * partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x := by
      intro x
      rw [sa12x2_phi_deriv hw hp1 e x, sa12x2_pd_snoc n F hFn idx i x]
    have hfc : Continuous (fun x => fderiv ℝ (fun y => w y ^ 2 * partialDeriv idx F y) x e) :=
      (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hfs := hφc.fderiv_apply (𝕜 := ℝ) e
    have hne : ‖e‖ ≤ 1 := by simp [he]
    have := sa12x2_cover_gen m hF hω (K1 := 8 * B1 ^ 2) (K2 := 2) (by positivity) (by norm_num)
      (f := fun x => fderiv ℝ (fun y => w y ^ 2 * partialDeriv idx F y) x e) hfc hfs
      (fun x => by
        rw [hkey x]
        have hwe : |fderiv ℝ w x e| ≤ B1 := by
          have h := (fderiv ℝ w x).le_opNorm e
          rw [← Real.norm_eq_abs]
          calc ‖fderiv ℝ w x e‖ ≤ ‖fderiv ℝ w x‖ * ‖e‖ := h
            _ ≤ B1 * 1 := by gcongr; exact hwB x
            _ = B1 := mul_one _
        have hwe2 : (fderiv ℝ w x e) ^ 2 ≤ B1 ^ 2 := by
          have := sq_le_sq' (abs_le.1 hwe).1 (abs_le.1 hwe).2
          exact this
        have hY := sa12x2_sq_le_Y hn F idx x
        have hYd := sa12x2_sq_le_Yd hn F idx i x
        have hww := hw2 x
        have hw2' : (w x ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (w x)]
        set a := partialDeriv idx F x with ha
        set q := partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x with hq
        set u := fderiv ℝ w x e with hu
        have h1 : (2 * w x * u * a + w x ^ 2 * q) ^ 2 ≤
            2 * (2 * w x * u * a) ^ 2 + 2 * (w x ^ 2 * q) ^ 2 := by
          nlinarith [sq_nonneg (2 * w x * u * a - w x ^ 2 * q)]
        have h2 : (2 * w x * u * a) ^ 2 ≤ 4 * B1 ^ 2 * sa12z3_Y m F x := by
          have : (2 * w x * u * a) ^ 2 = 4 * w x ^ 2 * u ^ 2 * a ^ 2 := by ring
          rw [this]
          have hu2 : w x ^ 2 * u ^ 2 ≤ B1 ^ 2 := by
            calc w x ^ 2 * u ^ 2 ≤ 1 * B1 ^ 2 := by gcongr
              _ = B1 ^ 2 := one_mul _
          have hnn : 0 ≤ a ^ 2 := sq_nonneg _
          calc 4 * w x ^ 2 * u ^ 2 * a ^ 2 = 4 * (w x ^ 2 * u ^ 2) * a ^ 2 := by ring
            _ ≤ 4 * B1 ^ 2 * a ^ 2 := by gcongr
            _ ≤ 4 * B1 ^ 2 * sa12z3_Y m F x := by gcongr
        have h3 : (w x ^ 2 * q) ^ 2 ≤ sa12x2_Yd m F x := by
          calc (w x ^ 2 * q) ^ 2 = (w x ^ 2) ^ 2 * q ^ 2 := by ring
            _ ≤ 1 * q ^ 2 := by gcongr
            _ ≤ sa12x2_Yd m F x := by rw [one_mul]; exact hYd
        nlinarith)
      (fun x hx => hwW x (fun h0 => hx (by rw [hkey x]; simp [h0])))
    exact this

end HRS.MH.AdjointRd.Phase2SA12Near
