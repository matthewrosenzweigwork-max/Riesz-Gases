import HRS.MS.SA12X3C7C3

/-!
# S.A.12 C7 (SA12X3), part C4 (7C): the far term pairing

Given the `L²` bounds `∫ (w T)² ≤ Mass` of the derivatives `T = ∂^{snoc idx i}γ ⊛ (1-η) μ ∂_jF` of the far box term (supplied by T7),
`-2 jetPair m w F Far ≤ (∑_j C(m,j) d^j) (En + d⁴ MB² Mass)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- The far box term of `periodic_near_identity`. -/
def sa12x3_Far (L : ℝ) (γ : Euc d → ℝ) (c : Euc d) (M : Matrix (Fin d) (Fin d) ℝ) (η μ F : Euc d → ℝ)
    (x : Euc d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, M j i * ∫ y in {y | y - c ∈ centeredBox d L},
    fderiv ℝ γ (x - y) (EuclideanSpace.single i (1 : ℝ)) *
      ((1 - η y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))

/-- The `x`-derivative of the far box term, one component. -/
def sa12x3_Tfar (L : ℝ) (γ : Euc d → ℝ) (c : Euc d) (η μ F : Euc d → ℝ) {n : ℕ} (idx : Fin n → Fin d)
    (i j : Fin d) (x : Euc d) : ℝ :=
  ∫ y in {y | y - c ∈ centeredBox d L},
    partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) γ (x - y) *
      ((1 - η y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))

theorem sa12x3_far_pd {s L : ℝ} {γ : Euc d → ℝ}
    (hγ : HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ) {h R' R'' : ℝ} (hh : 0 < h) (hR : 0 < R'')
    (hR'' : R' + h / 2 ≤ R'') (hRL : R'' < L / 2) {c : Euc d} (M : Matrix (Fin d) (Fin d) ℝ)
    {w η μ F : Euc d → ℝ} (hw : Continuous w) (hη : Continuous η) (hμ : Continuous μ) (hF : ContDiff ℝ ∞ F)
    (hwN : ∀ x, w x ≠ 0 → x ∈ ball c R' ∧ ∀ y ∈ ball x h, η y = 1) :
    ∃ Sh : Fin d → Fin d → Euc d → ℝ, (∀ i j, ContDiff ℝ ∞ (Sh i j)) ∧
      (∀ x, w x ≠ 0 → sa12x3_Far L γ c M η μ F x = ∑ i : Fin d, ∑ j : Fin d, M j i * Sh i j x) ∧
      ∀ (n : ℕ) (idx : Fin n → Fin d) (i j : Fin d) (x : Euc d), w x ≠ 0 →
        partialDeriv idx (Sh i j) x = sa12x3_Tfar L γ c η μ F idx i j x := by
  set N : Set (Euc d) := {x | w x ≠ 0} ∩ ball c R' with hN
  have hNo : IsOpen N := (isOpen_ne_fun hw continuous_const).inter isOpen_ball
  have hNc : ∀ x ∈ N, ‖x - c‖ + h / 2 ≤ R'' := by
    intro x hx
    have := mem_ball_iff_norm.1 hx.2
    linarith
  have hdF : ∀ j : Fin d, Continuous (fun y => fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    ((hF.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const
  have hHc : ∀ j : Fin d, Continuous (fun y => (1 - η y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) :=
    fun j => (continuous_const.sub hη).mul (hμ.mul (hdF j))
  have hH0 : ∀ j : Fin d, ∀ x ∈ N, ∀ y ∈ ball x h,
      (1 - η y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) = 0 := by
    intro j x hx y hy
    rw [(hwN x hx.1).2 y hy]
    simp
  have hfd : ∀ i j : Fin d, ∃ Sh : Euc d → ℝ, ContDiff ℝ ∞ Sh ∧
      (∀ x ∈ N, Sh x = ∫ y in {y | y - c ∈ centeredBox d L}, fderiv ℝ γ (x - y) (EuclideanSpace.single i (1 : ℝ)) *
        ((1 - η y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))) ∧
      ∀ (n : ℕ) (idx : Fin n → Fin d), ∀ x ∈ N, partialDeriv idx Sh x =
        ∫ y in {y | y - c ∈ centeredBox d L}, partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) γ (x - y) *
          ((1 - η y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) :=
    fun i j => sa12x3_far_deriv hγ hh hR hRL hNo hNc (hHc j) (hH0 j) i
  choose Sh hSh1 hSh2 hSh3 using hfd
  refine ⟨Sh, hSh1, fun x hx => ?_, fun n idx i j x hx => ?_⟩
  · have hxN : x ∈ N := ⟨hx, (hwN x hx).1⟩
    unfold sa12x3_Far
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hSh2 i j x hxN]
  · have hxN : x ∈ N := ⟨hx, (hwN x hx).1⟩
    rw [hSh3 i j n idx x hxN]
    rfl

end HRS.MH.AdjointRd.Phase2SA12Near
