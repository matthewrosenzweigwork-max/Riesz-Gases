import HRS.MS.UniqN4bH

/-!
# N4b of `UniqPlan.md`, part I: the far-field bound and the bound for one index pair

* `n4b_pair_far`: `|∫ f (1 - θ) (∂_jρ' H_i + ρ' ∂_jH_i)| ≤ C A²` (`n4b_far`, `n4b_psi_L1`).
* `n4b_pair`: `|∫ f ∂_j(ρ' H_i)| ≤ ε ∫_{B̄(p,8L)} |∇f|² + C A²`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqN2b HRS.MS.UniqN0

variable {d : ℕ}

theorem n4b_pair_far {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L K Lθ Cρ δ : ℝ}
    (hCρ : 0 ≤ Cρ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin d) (p : Euc d) (ς θ ρ' f : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      N4bCut d p L K Lθ δ ς θ → N4bRho d Cρ ρ' → ContDiff ℝ ∞ f → LocMass A f →
      Integrable (fun y => f y * ((1 - θ y) * (D1 j ρ' y * kernelConvDeriv d s i (fun x => ς x * f x) y +
          ρ' y * D1 j (kernelConvDeriv d s i (fun x => ς x * f x)) y))) volume ∧
      |∫ y, f y * ((1 - θ y) * (D1 j ρ' y * kernelConvDeriv d s i (fun x => ς x * f x) y +
          ρ' y * D1 j (kernelConvDeriv d s i (fun x => ς x * f x)) y))| ≤ C * A ^ 2 := by
  obtain ⟨Cf, hCf0, hfar⟩ := n4b_far hs0 hsd hδ
  obtain ⟨K1, hK10, hK1⟩ := exists_closedBall_l1_real d (2 * L)
  refine ⟨Cf * Cρ * K1, by positivity, ?_⟩
  intro i j p ς θ ρ' f A hA hc hr hf hfm
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  set ψ : Euc d → ℝ := fun x => ς x * f x with hψdef
  have hςc : HasCompactSupport ς :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hc.ςs
  have hψ2 : ContDiff ℝ 2 ψ := hc.ς2.mul (hf.of_le (by simp))
  have hψc : HasCompactSupport ψ := hςc.mul_right
  have hψts : tsupport ψ ⊆ tsupport ς := closure_mono (Function.support_mul_subset_left ς f)
  have hψL1 : ∫ x, |ψ x| ≤ K1 * A :=
    n4b_psi_L1 hA hc.ς01 hc.ςs hf1.continuous hψ2.continuous hψc (hK1 A f hA hfm p)
  have h1θ : ∀ y, |1 - θ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (by linarith [(hc.θ01 y).2])]; linarith [(hc.θ01 y).1]
  have hsep' : ∀ y, 1 - θ y ≠ 0 → ∀ x ∈ tsupport ψ, δ ≤ ‖y - x‖ := by
    intro y hy x hx
    have := hc.sep x y (hψts hx) (subset_tsupport _ (Function.mem_support.2 hy))
    rwa [norm_sub_rev] at this
  obtain ⟨hI, hB⟩ := hfar i j hr.c1 hCρ hr.dec0 (hr.dec1 j) hψ2 hψc hc.θ1.continuous h1θ hsep' hA hfm
    (mul_nonneg hK10 hA) hψL1
  refine ⟨hI, hB.trans (le_of_eq ?_)⟩
  ring

theorem n4b_pair (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L K Lθ Cρ δ : ℝ}
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hLθ : 0 ≤ Lθ) (hCρ : 0 ≤ Cρ) (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin d) (p : Euc d) (ς θ ρ' f : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      N4bCut d p L K Lθ δ ς θ → N4bRho d Cρ ρ' → ContDiff ℝ ∞ f → LocMass A f →
      |∫ y, f y * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d s i (fun x => ς x * f x) y) y
          (EuclideanSpace.single j (1 : ℝ))| ≤
        ε * (∫ y in closedBall p (8 * L), ‖fderiv ℝ f y‖ ^ 2) + C * A ^ 2 := by
  obtain ⟨Cn, hCn0, hnear⟩ := n4b_pair_near hd hs0 hsd hL hK hLθ hCρ (δ := δ) hε
  obtain ⟨Cf, hCf0, hfar⟩ := n4b_pair_far hs0 hsd (L := L) (K := K) (Lθ := Lθ) hCρ hδ
  refine ⟨Cn + Cf, by positivity, ?_⟩
  intro i j p ς θ ρ' f A hA hc hr hf hfm
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hςc : HasCompactSupport ς :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hc.ςs
  have hψ2 : ContDiff ℝ 2 (fun x => ς x * f x) := hc.ς2.mul (hf.of_le (by simp))
  have hψc : HasCompactSupport (fun x => ς x * f x) := hςc.mul_right
  have hθc : HasCompactSupport θ :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hc.θs
  have hXc := n4b_X_cont hs0 hsd hr.c1 hψ2 hψc i j
  have hnearI : Integrable (fun y => θ y * f y * (D1 j ρ' y *
      kernelConvDeriv d s i (fun x => ς x * f x) y +
      ρ' y * D1 j (kernelConvDeriv d s i (fun x => ς x * f x)) y)) volume :=
    (((hc.θ1.continuous.mul hf1.continuous).mul hXc)).integrable_of_hasCompactSupport
      (hθc.mul_right.mul_right)
  obtain ⟨hfarI, hfarB⟩ := hfar i j p ς θ ρ' f A hA hc hr hf hfm
  have hsplit : ∫ y, f y * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d s i (fun x => ς x * f x) y) y
      (EuclideanSpace.single j (1 : ℝ)) =
      (∫ y, θ y * f y * (D1 j ρ' y * kernelConvDeriv d s i (fun x => ς x * f x) y +
        ρ' y * D1 j (kernelConvDeriv d s i (fun x => ς x * f x)) y)) +
      ∫ y, f y * ((1 - θ y) * (D1 j ρ' y * kernelConvDeriv d s i (fun x => ς x * f x) y +
        ρ' y * D1 j (kernelConvDeriv d s i (fun x => ς x * f x)) y)) := by
    rw [← integral_add hnearI hfarI]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [n4b_X_eq hs0 hsd hr.c1 hψ2 hψc i j y]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1 := hnear i j p ς θ ρ' f A hA hc hr hf hfm
  nlinarith [h1, hfarB]

end HRS.MS.UniqN4b
