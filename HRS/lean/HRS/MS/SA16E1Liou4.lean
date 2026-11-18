import HRS.MS.SA16E1Liou3

/-!
# S.A.16 E1: Liouville's formula
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution

/-- The matrix of columns `M e_j`. -/
def e1N {d : ℕ} (M : ℝ → Euc d →L[ℝ] Euc d) (σ : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => M σ (EuclideanSpace.single j (1 : ℝ)) i

theorem e1_det_eq {d : ℕ} (f : Euc d →L[ℝ] Euc d) :
    LinearMap.det (f : Euc d →ₗ[ℝ] Euc d) = (e1N (fun _ => f) 0).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (f : Euc d →ₗ[ℝ] Euc d)]
  congr 1

section Liou

variable {d : ℕ} {T L : ℝ} {A M : ℝ → Euc d →L[ℝ] Euc d}

theorem e1_col_deriv (hM : ∀ τ ∈ Icc (0:ℝ) T, ∀ v : Euc d,
      M τ v = v - ∫ s in (0:ℝ)..τ, A s (M s v)) {τ : ℝ} (hτ : τ ∈ Ioo 0 T) (v : Euc d)
    (hLeb : HasDerivAt (fun x => ∫ t in (0:ℝ)..x, A t (M t v)) (A τ (M τ v)) τ) :
    HasDerivAt (fun σ => M σ v) (-(A τ (M τ v))) τ := by
  refine (hLeb.const_sub v).congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with σ hσ
  exact hM σ hσ v

theorem e1_det_deriv (hM : ∀ τ ∈ Icc (0:ℝ) T, ∀ v : Euc d,
      M τ v = v - ∫ s in (0:ℝ)..τ, A s (M s v)) {τ : ℝ} (hτ : τ ∈ Ioo 0 T)
    (hLeb : ∀ j : Fin d, HasDerivAt (fun x => ∫ t in (0:ℝ)..x,
      A t (M t (EuclideanSpace.single j (1:ℝ)))) (A τ (M τ (EuclideanSpace.single j (1:ℝ)))) τ) :
    HasDerivAt (fun σ => (e1N M σ).det)
      (-(∑ i, A τ (EuclideanSpace.single i (1:ℝ)) i) * (e1N M τ).det) τ := by
  classical
  have hcol := fun j : Fin d => e1_col_deriv hM hτ (EuclideanSpace.single j (1:ℝ)) (hLeb j)
  have hrow : ∀ i, HasDerivAt (fun σ => e1N M σ i)
      (fun j => -(A τ (M τ (EuclideanSpace.single j (1:ℝ)))) i) τ := fun i =>
    hasDerivAt_pi.2 fun j => by
      have := ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt τ (hcol j)
      simpa [e1N, Function.comp_def] using this
  have hd := e1_hasDerivAt_det (e1N M)
    (Matrix.of fun i j => -(A τ (M τ (EuclideanSpace.single j (1:ℝ)))) i) hrow
  convert hd using 1
  have hrow' : ∀ i, (Matrix.of fun i j => -(A τ (M τ (EuclideanSpace.single j (1:ℝ)))) i) i =
      ∑ k, (-(A τ (EuclideanSpace.single k (1:ℝ)) i)) • e1N M τ k := by
    intro i
    ext j
    have h := e1_A_sum (A := A) τ (M τ (EuclideanSpace.single j (1:ℝ)))
    have h' := congrArg (fun w : Euc d => w i) h
    simp only [PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply] at h'
    simp only [Matrix.of_apply, h', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e1N, ← Finset.sum_neg_distrib,
      neg_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have : ∀ i, ((e1N M τ).updateRow i
      ((Matrix.of fun i j => -(A τ (M τ (EuclideanSpace.single j (1:ℝ)))) i) i)).det =
      -(A τ (EuclideanSpace.single i (1:ℝ)) i) * (e1N M τ).det := by
    intro i
    rw [hrow' i, Matrix.det_updateRow_sum (e1N M τ) i (fun k => -(A τ (EuclideanSpace.single k (1:ℝ)) i))]
    rfl
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_mul, Finset.sum_neg_distrib]

end Liou

end HRS.Whole.AppendixA.Phase2SA16Evolution
