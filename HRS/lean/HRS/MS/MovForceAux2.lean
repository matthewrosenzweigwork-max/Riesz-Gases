import HRS.MS.MovForceAux1

/-!
# MOV-B1 (2): smoothness of the force and `div (g ∇h) = g * Δh` (S6.1, step 2)

Namespace `HRS.MS.MovForce`, prefix `mv1_`.

* `mv1_force_contDiff (k) : h ∈ C^{k+1}`, `MovGauss (k+1) h` `⟹` `movForce d s h ∈ C^k`; `mv1_force_contDiff_infty`
  for `C^∞` with Gaussian bounds of all orders.
* `mv1_div_force : movDiv (movForce d s h) x = convFun g (Δ h) x` for `h ∈ C²` with `MovGauss 2 h`
  (`Δ = Laplacian.laplacian`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovForce

open HRS.Whole

variable {d : ℕ}

/-- `∂_e u` inherits the Gaussian bounds (order drops by one). -/
lemma mv1_gauss_partial {k : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u)
    (hg : MovGauss (k + 1) u) (i : Fin d) :
    MovGauss k (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) := by
  intro j hj
  obtain ⟨C, c, hc, hb⟩ := hg (j + 1) (by omega)
  refine ⟨C, c, hc, fun x => ?_⟩
  have hfd : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (m := k) (by rw [Nat.cast_succ])
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ)
    (f := fderiv ℝ u) (c := (EuclideanSpace.single i (1 : ℝ) : Euc d)) (x := x) (n := j)
    (N := (k : WithTop ℕ∞)) hfd.contDiffAt (by exact_mod_cast hj)
  rw [norm_iteratedFDeriv_fderiv] at h1
  have h2 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h2, one_mul] at h1
  exact h1.trans (hb x)

lemma mv1_partial_contDiff {k : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u)
    (i : Fin d) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) :=
  (hu.fderiv_right (m := k) (by rw [Nat.cast_succ])).clm_apply contDiff_const

/-- A continuous linear functional on `ℝ^d` is the sum of its values on the basis. -/
lemma mv1_clm_eq_sum (L : Euc d →L[ℝ] ℝ) :
    L = ∑ i, L (EuclideanSpace.single i 1) • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
  ext e
  have he : e = ∑ i, e i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr e
    simpa using this.symm
  conv_lhs => rw [he]
  simp [map_sum, mul_comm]

section Riesz

variable {s : ℝ}

/-- The `k`-fold smoothness of the potential `g * u`. -/
theorem mv1_conv_contDiff (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∀ (k : ℕ) (u : Euc d → ℝ), ContDiff ℝ (k : WithTop ℕ∞) u → MovGauss k u →
      ContDiff ℝ (k : WithTop ℕ∞) (HRS.Whole.convFun (rieszKernel d s) u) := by
  intro k
  induction k with
  | zero =>
    intro u hu hg
    obtain ⟨C, c, hc, hb⟩ := hg 0 le_rfl
    have hC : 0 ≤ C := by
      have := hb 0
      simp at this
      exact le_trans (abs_nonneg _) this
    have h0 : ∀ y, |u y| ≤ C * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
      have := hb y
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have huc : Continuous u := by simpa using hu
    obtain ⟨hk, hB, hBint⟩ := mv1_g_data (d := d) (s := s) hd hs0 hsd hc
    have := mv1_continuous_conv hc hk hB hBint hC huc h0
    have e : HRS.Whole.convFun (rieszKernel d s) u = fun x' => ∫ z, rieszKernel d s z * u (x' - z) :=
      funext fun x' => mv1_convFun_eq _ _ x'
    simp only [Nat.cast_zero, contDiff_zero]
    rw [e]; exact this
  | succ k ih =>
    intro u hu hg
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast Nat.le_add_left 1 k)
    have hg1 : MovGauss 1 u := fun j hj => hg j (by omega)
    obtain ⟨C, c, hC, hc, h0, h1⟩ := mv1_gauss01 hg1
    have hL : ∀ x, ∃ L : Euc d →L[ℝ] ℝ, HasFDerivAt (HRS.Whole.convFun (rieszKernel d s) u) L x ∧
        L = ∑ i, HRS.Whole.convFun (rieszKernel d s)
          (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) x •
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
      intro x
      obtain ⟨L, hL, hLe, -⟩ := mv1_hasFDerivAt_convFun hd hs0 hsd hc hC hu1 h0 h1 x
      refine ⟨L, hL, ?_⟩
      rw [mv1_clm_eq_sum L]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hLe, mv1_convFun_eq]
    have hder : Differentiable ℝ (HRS.Whole.convFun (rieszKernel d s) u) := fun x =>
      (hL x).elim fun _ h => h.1.differentiableAt
    have hfd : fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) u) = fun x =>
        ∑ i, HRS.Whole.convFun (rieszKernel d s)
          (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) x •
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
      funext x
      obtain ⟨L, hL', hLe⟩ := hL x
      rw [hL'.fderiv, hLe]
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨hder, fun h => absurd h (by simp), ?_⟩
    rw [hfd]
    refine ContDiff.sum fun i _ => ?_
    have := (ih _ (mv1_partial_contDiff hu i) (mv1_gauss_partial hu hg i)).smul
      (contDiff_const (c := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)))
    exact this

/-- The force of a `C^{k+1}` Gaussian-bounded profile is `C^k`. -/
theorem mv1_force_contDiff (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) {h : Euc d → ℝ}
    (hh : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) h) (hg : MovGauss (k + 1) h) :
    ContDiff ℝ (k : WithTop ℕ∞) (movForce d s h) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast Nat.le_add_left 1 k)
  obtain ⟨C, c, hC, hc, h0, h1⟩ := mv1_gauss01 (fun j hj => hg j (by omega))
  have hcomp : ∀ i : Fin d, ContDiff ℝ (k : WithTop ℕ∞) (fun y => (movForce d s h y) i) := by
    intro i
    have : (fun y => (movForce d s h y) i) = HRS.Whole.convFun (rieszKernel d s)
        (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) :=
      funext fun y => mv1_force_eq_conv_grad hd hs0 hsd hc hC hh1 h0 h1 y i
    rw [this]
    exact mv1_conv_contDiff hd hs0 hsd k _ (mv1_partial_contDiff hh i) (mv1_gauss_partial hh hg i)
  exact contDiff_euclidean.2 hcomp

/-- Smooth version. -/
theorem mv1_force_contDiff_infty (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h : Euc d → ℝ}
    (hh : ContDiff ℝ ∞ h) (hg : ∀ k, MovGauss k h) :
    ContDiff ℝ ∞ (movForce d s h) := by
  rw [contDiff_infty]
  intro n
  exact mv1_force_contDiff hd hs0 hsd n (hh.of_le (by exact_mod_cast le_top)) (hg _)

/-- `Δ u = ∑_i ∂_i ∂_i u` (iterated directional derivative form). -/
lemma mv1_laplacian_eq {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (x : Euc d) :
    Laplacian.laplacian u x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hL := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin d) ℝ)
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have := fderiv_clm_apply (c := fderiv ℝ u) (u := fun _ : Euc d => (EuclideanSpace.single i (1 : ℝ) : Euc d))
    (x := x) h1 (differentiableAt_const _)
  rw [this, iteratedFDeriv_two_apply]
  simp

/-- `div (∇g * h) = g * Δh` for `h ∈ C²` with Gaussian bounds up to order two. -/
theorem mv1_div_force (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h : Euc d → ℝ}
    (hh : ContDiff ℝ 2 h) (hg : MovGauss 2 h) (x : Euc d) :
    movDiv (movForce d s h) x =
      HRS.Whole.convFun (rieszKernel d s) (fun y => Laplacian.laplacian h y) x := by
  have hh' : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) h := by simpa using hh
  have hg' : MovGauss (1 + 1) h := hg
  have hF : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (movForce d s h) :=
    mv1_force_contDiff hd hs0 hsd 1 hh' hg'
  have hFd : DifferentiableAt ℝ (movForce d s h) x :=
    (hF.differentiable (by norm_num)) x
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  obtain ⟨C, c, hC, hc, h0, h1⟩ := mv1_gauss01 (fun j hj => hg j (by omega))
  -- component by component
  have hcomp : ∀ i : Fin d, fderiv ℝ (movForce d s h) x (EuclideanSpace.single i 1) i =
      ∫ z, rieszKernel d s z *
        fderiv ℝ (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) (x - z)
          (EuclideanSpace.single i 1) := by
    intro i
    have e1 : (fun y => (movForce d s h y) i) = HRS.Whole.convFun (rieszKernel d s)
        (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) :=
      funext fun y => mv1_force_eq_conv_grad hd hs0 hsd hc hC hh1 h0 h1 y i
    have e2 : fderiv ℝ (fun y => (movForce d s h y) i) x =
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ (movForce d s h) x) :=
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hFd.hasFDerivAt).fderiv
    have e3 : fderiv ℝ (movForce d s h) x (EuclideanSpace.single i 1) i =
        fderiv ℝ (fun y => (movForce d s h y) i) x (EuclideanSpace.single i 1) := by
      rw [e2]; simp
    rw [e3, e1]
    have hui : ContDiff ℝ 1 (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) :=
      mv1_partial_contDiff (k := 1) hh' i
    obtain ⟨C', c', hC', hc', h0', h1'⟩ := mv1_gauss01 (mv1_gauss_partial (k := 1) hh' hg' i)
    obtain ⟨L, hL, hLe, -⟩ := mv1_hasFDerivAt_convFun hd hs0 hsd hc' hC' hui h0' h1' x
    rw [hL.fderiv, hLe]
  have hint : ∀ i : Fin d, Integrable (fun z => rieszKernel d s z *
        fderiv ℝ (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) (x - z)
          (EuclideanSpace.single i 1)) := by
    intro i
    have hui : ContDiff ℝ 1 (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) :=
      mv1_partial_contDiff (k := 1) hh' i
    obtain ⟨C', c', hC', hc', h0', h1'⟩ := mv1_gauss01 (mv1_gauss_partial (k := 1) hh' hg' i)
    obtain ⟨L, hL, -, hI⟩ := mv1_hasFDerivAt_convFun hd hs0 hsd hc' hC' hui h0' h1' x
    exact hI _
  unfold movDiv
  simp_rw [hcomp]
  rw [← integral_finsetSum _ (fun i _ => hint i), mv1_convFun_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [mv1_laplacian_eq hh (x - z), Finset.mul_sum]

end Riesz

end HRS.MS.MovForce
