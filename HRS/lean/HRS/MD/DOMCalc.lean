/-
# HRS.MD.DOMCalc — packet DOM-LEIB/CUT, calculus toolkit on `ℝ^d`

Partial derivatives `dk`, `ddk` along the basis vectors, Laplacian as `∑_k ddk`, Leibniz rules for the
gradient and the Laplacian of a product, the chain rule for `θ ∘ T`, translation invariance, and the
bound for the gradient/Laplacian of a finite product of factors with values in `[0,1]`.
-/
import HRS.Torus.Basic

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.MD.DOMProof

variable {d : ℕ}

/-- `∂_k f (y)`. -/
def dk (f : Euc d → ℝ) (k : Fin d) (y : Euc d) : ℝ := fderiv ℝ f y (EuclideanSpace.single k 1)

/-- `∂_k ∂_k f (y)`. -/
def ddk (f : Euc d → ℝ) (k : Fin d) (y : Euc d) : ℝ :=
  fderiv ℝ (dk f k) y (EuclideanSpace.single k 1)

theorem domp_differentiableAt_dk {f : Euc d → ℝ} {x : Euc d} (hf : ContDiffAt ℝ 2 f x) (k : Fin d) :
    DifferentiableAt ℝ (dk f k) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (m := 1) (by norm_num)
  exact (h1.clm_apply contDiffAt_const).differentiableAt (by simp)

theorem domp_lap_eq_sum_ddk {f : Euc d → ℝ} {x : Euc d} (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian f x = ∑ k, ddk f k x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [EuclideanSpace.basisFun_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  unfold ddk dk
  rw [fderiv_clm_apply hdiff (differentiableAt_const _)]
  simp

theorem domp_gradient_apply (f : Euc d → ℝ) (x : Euc d) (k : Fin d) :
    gradient f x k = dk f k x := by
  have h := inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := EuclideanSpace.single k 1)
  rw [EuclideanSpace.inner_single_right] at h
  simpa [dk] using h

theorem domp_norm_gradient_sq (f : Euc d → ℝ) (x : Euc d) :
    ‖gradient f x‖ ^ 2 = ∑ k, dk f k x ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.norm_eq_abs, sq_abs, domp_gradient_apply]

theorem domp_inner_gradient (f g : Euc d → ℝ) (x : Euc d) :
    inner ℝ (gradient f x) (gradient g x) = ∑ k, dk f k x * dk g k x := by
  simp only [PiLp.inner_apply, domp_gradient_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem domp_gradient_mul {f g : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun z => f z * g z) x = f x • gradient g x + g x • gradient f x := by
  apply (InnerProductSpace.toDual ℝ (Euc d)).injective
  rw [toDual_gradient, map_add, map_smul, map_smul, toDual_gradient, toDual_gradient]
  have h : HasFDerivAt (fun z => f z * g z) (f x • fderiv ℝ g x + g x • fderiv ℝ f x) x :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  exact h.fderiv

theorem domp_dk_mul {f g : Euc d → ℝ} {y : Euc d} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (k : Fin d) :
    dk (fun z => f z * g z) k y = f y * dk g k y + g y * dk f k y := by
  unfold dk
  have h : HasFDerivAt (fun z => f z * g z) (f y • fderiv ℝ g y + g y • fderiv ℝ f y) y :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [h.fderiv]
  simp

theorem domp_ddk_mul {f g : Euc d → ℝ} {x : Euc d} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (k : Fin d) :
    ddk (fun z => f z * g z) k x =
      f x * ddk g k x + 2 * (dk f k x * dk g k x) + g x * ddk f k x := by
  have hev : dk (fun z => f z * g z) k =ᶠ[𝓝 x] fun z => f z * dk g k z + g z * dk f k z := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with z hfz hgz
    exact domp_dk_mul (hfz.differentiableAt (by simp)) (hgz.differentiableAt (by simp)) k
  have hdf := domp_differentiableAt_dk hf k
  have hdg := domp_differentiableAt_dk hg k
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by simp)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by simp)
  have hH : HasFDerivAt (fun z => f z * dk g k z + g z * dk f k z)
      (f x • fderiv ℝ (dk g k) x + dk g k x • fderiv ℝ f x +
        (g x • fderiv ℝ (dk f k) x + dk f k x • fderiv ℝ g x)) x :=
    (hfd.hasFDerivAt.mul hdg.hasFDerivAt).add (hgd.hasFDerivAt.mul hdf.hasFDerivAt)
  unfold ddk
  rw [hev.fderiv_eq, hH.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  unfold dk
  have : fderiv ℝ f x (EuclideanSpace.single k 1) * fderiv ℝ g x (EuclideanSpace.single k 1) =
      fderiv ℝ g x (EuclideanSpace.single k 1) * fderiv ℝ f x (EuclideanSpace.single k 1) := mul_comm _ _
  linarith

theorem domp_lap_mul {f g : Euc d → ℝ} {x : Euc d} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    Laplacian.laplacian (fun z => f z * g z) x =
      f x * Laplacian.laplacian g x + 2 * inner ℝ (gradient f x) (gradient g x) +
        g x * Laplacian.laplacian f x := by
  have hfg : ContDiffAt ℝ 2 (fun z => f z * g z) x := hf.mul hg
  rw [domp_lap_eq_sum_ddk hfg, domp_lap_eq_sum_ddk hf, domp_lap_eq_sum_ddk hg,
    domp_inner_gradient]
  simp_rw [domp_ddk_mul hf hg]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

/-! ### Chain rule -/

theorem domp_dk_comp' (θ : ℝ → ℝ) {T : Euc d → ℝ} {y : Euc d} (hθ : DifferentiableAt ℝ θ (T y))
    (hT : DifferentiableAt ℝ T y) (k : Fin d) :
    dk (fun z => θ (T z)) k y = deriv θ (T y) * dk T k y := by
  unfold dk
  have h : HasFDerivAt (fun z => θ (T z)) (deriv θ (T y) • fderiv ℝ T y) y :=
    hθ.hasDerivAt.comp_hasFDerivAt y hT.hasFDerivAt
  rw [h.fderiv]
  simp

theorem domp_ddk_comp (θ : ℝ → ℝ) (hθ : ContDiff ℝ 2 θ) {T : Euc d → ℝ} {x : Euc d}
    (hT : ContDiffAt ℝ 2 T x) (k : Fin d) :
    ddk (fun z => θ (T z)) k x =
      deriv (deriv θ) (T x) * dk T k x ^ 2 + deriv θ (T x) * ddk T k x := by
  have hθ1 : Differentiable ℝ θ := hθ.differentiable (by norm_num)
  have hθ2 : Differentiable ℝ (deriv θ) := by
    have : ContDiff ℝ 1 (deriv θ) := hθ.iterate_deriv' 1 1 |>.of_le le_rfl
    exact this.differentiable (by norm_num)
  have hev : dk (fun z => θ (T z)) k =ᶠ[𝓝 x] fun z => deriv θ (T z) * dk T k z := by
    filter_upwards [hT.eventually (by simp)] with z hTz
    exact domp_dk_comp' θ (hθ1 _) (hTz.differentiableAt (by simp)) k
  have hdT := domp_differentiableAt_dk hT k
  have hTd : DifferentiableAt ℝ T x := hT.differentiableAt (by simp)
  have hH : HasFDerivAt (fun z => deriv θ (T z) * dk T k z)
      (deriv θ (T x) • fderiv ℝ (dk T k) x + dk T k x • (deriv (deriv θ) (T x) • fderiv ℝ T x)) x :=
    ((hθ2 (T x)).hasDerivAt.comp_hasFDerivAt x hTd.hasFDerivAt).mul hdT.hasFDerivAt
  unfold ddk
  rw [hev.fderiv_eq, hH.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  unfold dk
  ring

/-! ### Translation -/

theorem domp_dk_comp_add (f : Euc d → ℝ) (a u : Euc d) (k : Fin d) :
    dk (fun z => f (a + z)) k u = dk f k (a + u) := by
  unfold dk
  rw [fderiv_comp_add_left]

theorem domp_ddk_comp_add (f : Euc d → ℝ) (a u : Euc d) (k : Fin d) :
    ddk (fun z => f (a + z)) k u = ddk f k (a + u) := by
  unfold ddk
  have : dk (fun z => f (a + z)) k = fun z => dk f k (a + z) := funext fun z => domp_dk_comp_add f a z k
  rw [this, fderiv_comp_add_left]

theorem domp_gradient_comp_add (f : Euc d → ℝ) (a : Euc d) :
    gradient (fun z => f (a + z)) 0 = gradient f a := by
  apply (InnerProductSpace.toDual ℝ (Euc d)).injective
  rw [toDual_gradient, toDual_gradient, fderiv_comp_add_left, add_zero]

theorem domp_lap_comp_add (f : Euc d → ℝ) (a : Euc d) :
    Laplacian.laplacian (fun z => f (a + z)) 0 = Laplacian.laplacian f a := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (fun z => f (a + z))
      (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp [iteratedFDeriv_comp_add_left]

/-! ### Finite products of factors with values in `[0,1]` -/

theorem domp_prod_deriv_bound {ι : Type*} (S : Finset ι) (g : ι → Euc d → ℝ) (x : Euc d)
    (hg : ∀ p ∈ S, ContDiffAt ℝ 2 (g p) x) (h0 : ∀ p ∈ S, 0 ≤ g p x ∧ g p x ≤ 1)
    (α γ : ι → ℝ) (hα : ∀ p ∈ S, ‖gradient (g p) x‖ ≤ α p)
    (hγ : ∀ p ∈ S, |Laplacian.laplacian (g p) x| ≤ γ p) :
    (0 ≤ ∏ p ∈ S, g p x ∧ ∏ p ∈ S, g p x ≤ 1) ∧
    ContDiffAt ℝ 2 (fun z => ∏ p ∈ S, g p z) x ∧
    ‖gradient (fun z => ∏ p ∈ S, g p z) x‖ ≤ ∑ p ∈ S, α p ∧
    |Laplacian.laplacian (fun z => ∏ p ∈ S, g p z) x| ≤ ∑ p ∈ S, γ p + 2 * (∑ p ∈ S, α p) ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⟨by simp, by simp⟩, contDiffAt_const, ?_, ?_⟩
    · simp
    · simp
  | insert a S ha ih =>
    have hgS : ∀ p ∈ S, ContDiffAt ℝ 2 (g p) x := fun p hp => hg p (Finset.mem_insert_of_mem hp)
    obtain ⟨⟨hP0, hP1⟩, hPc, hPg, hPl⟩ := ih hgS (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
      (fun p hp => hα p (Finset.mem_insert_of_mem hp)) (fun p hp => hγ p (Finset.mem_insert_of_mem hp))
    have hga := hg a (Finset.mem_insert_self _ _)
    have ⟨ha0, ha1⟩ := h0 a (Finset.mem_insert_self _ _)
    have hαa := hα a (Finset.mem_insert_self _ _)
    have hγa := hγ a (Finset.mem_insert_self _ _)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    set P : ℝ := ∏ p ∈ S, g p x with hP
    set A : ℝ := ∑ p ∈ S, α p with hA
    set Γ : ℝ := ∑ p ∈ S, γ p with hΓ
    have hA0 : 0 ≤ A := (norm_nonneg _).trans hPg
    have hαa0 : 0 ≤ α a := (norm_nonneg _).trans hαa
    refine ⟨⟨mul_nonneg ha0 hP0, by nlinarith⟩, hga.mul hPc, ?_, ?_⟩
    · rw [domp_gradient_mul (hga.differentiableAt (by simp)) (hPc.differentiableAt (by simp))]
      calc ‖g a x • gradient (fun z => ∏ p ∈ S, g p z) x + (∏ p ∈ S, g p x) • gradient (g a) x‖
          ≤ ‖g a x • gradient (fun z => ∏ p ∈ S, g p z) x‖ + ‖P • gradient (g a) x‖ := norm_add_le _ _
        _ = g a x * ‖gradient (fun z => ∏ p ∈ S, g p z) x‖ + P * ‖gradient (g a) x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0,
              abs_of_nonneg hP0]
        _ ≤ 1 * A + 1 * α a := by
            gcongr
        _ = α a + A := by ring
    · rw [domp_lap_mul hga hPc]
      have hin : |inner ℝ (gradient (g a) x) (gradient (fun z => ∏ p ∈ S, g p z) x)| ≤ α a * A :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul hαa hPg (norm_nonneg _) hαa0)
      have hl1 : |g a x * Laplacian.laplacian (fun z => ∏ p ∈ S, g p z) x| ≤ Γ + 2 * A ^ 2 := by
        rw [abs_mul, abs_of_nonneg ha0]
        calc g a x * |Laplacian.laplacian (fun z => ∏ p ∈ S, g p z) x| ≤ 1 * (Γ + 2 * A ^ 2) :=
            mul_le_mul ha1 hPl (abs_nonneg _) zero_le_one
          _ = Γ + 2 * A ^ 2 := one_mul _
      have hl2 : |(∏ p ∈ S, g p x) * Laplacian.laplacian (g a) x| ≤ γ a := by
        rw [abs_mul, abs_of_nonneg hP0]
        calc P * |Laplacian.laplacian (g a) x| ≤ 1 * γ a := mul_le_mul hP1 hγa (abs_nonneg _) zero_le_one
          _ = γ a := one_mul _
      have hmid : |2 * inner ℝ (gradient (g a) x) (gradient (fun z => ∏ p ∈ S, g p z) x)| ≤ 2 * (α a * A) := by
        rw [abs_mul, abs_two]; linarith
      have key : |g a x * Laplacian.laplacian (fun z => ∏ p ∈ S, g p z) x +
          2 * inner ℝ (gradient (g a) x) (gradient (fun z => ∏ p ∈ S, g p z) x) +
          P * Laplacian.laplacian (g a) x| ≤ (Γ + 2 * A ^ 2) + 2 * (α a * A) + γ a := by
        refine (abs_add_three _ _ _).trans ?_
        linarith
      refine key.trans ?_
      nlinarith [mul_nonneg hαa0 hA0, sq_nonneg (α a)]

end HRS.MD.DOMProof

end
