import Mathlib
import HRS.MS.PoissonSpike
import HRS.MS.PoisKolmAux2

/-!
# POIS-GRADSM (part 1): the pointwise Bernstein computation

Supplement foundation packet POIS-GRADSM (S1 `pois_gradsmooth`), calculus layer.  Everything here is a
statement about a single `C³` function `φ : ℝ^d → ℝ` (to be read as `u(t, ·) = sg t f`), the generator
`kolmL q B φ = Δφ + b·∇φ`, `b y = -q y + B y` (`PoisKolmAux2`), and the directional derivative
`gsD e φ y = Dφ(y) e`.

* `gs_second_order`: the second-order necessary condition at a local maximum of a `C²` function.
* `gs_D_comm`, `gs_D3_comm`, `gs_D_kolmL`: derivatives commute (symmetry of the Hessian), hence
  `∂_e (L φ) = L (∂_e φ) + Dφ(Db e)` for `φ ∈ C³`, `B ∈ C¹`.
* `gs_D2_W`, `gs_fderiv_W`: first and second derivatives of `A φ² + t ψ²`.
* `gs_bernstein_point`: for `‖e‖ = 1`, `‖DB z‖ ≤ Mb`, `0 ≤ t ≤ 1`, `A ≥ Mb + 1`, `q ≥ 0`
  `2Aφ Lφ + (∂_eφ)² + 2t ∂_eφ ∂_e(Lφ) ≤ L(A φ² + t (∂_eφ)²)` at every point; this is the inequality
  `∂_t Z ≤ L Z` for `Z = A u² + t (∂_e u)²` once `∂_t u = L u` and `∂_t ∂_e u = ∂_e L u`.
* `gs_max_step`: at a global (local) maximum `z` of `W - κ(1+|y|²)` one has
  `L W (z) ≤ κ (2d + 2⟪z, b z⟫)` (gradient zero, Laplacian `≤ 0`).

Helper lemmas carry the prefix `gs_`.  Adjustment with respect to the sketch (documented, harmless):
the Bernstein function is taken in a fixed unit direction `e` (`Z_e = A u² + t (∂_e u)²`) instead of
`A u² + t |∇u|²`; the supremum over `e` recovers `|∇u|`, and no `|D²u|²` bookkeeping is needed.
-/

open Filter Topology Set
open HRS.MS.PoissonSpike HRS.MS.PoisKolm
open scoped RealInnerProductSpace

noncomputable section
namespace HRS.MS.PoisGrad
variable {d : ℕ}

theorem gs_second_order {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) {z : Euc d}
    (hmax : IsLocalMax ψ z) :
    fderiv ℝ ψ z = 0 ∧ ∀ ξ, iteratedFDeriv ℝ 2 ψ z ![ξ, ξ] ≤ 0 := by
  have hline : ∀ ξ : Euc d, IsLocalMax (fun s : ℝ => ψ (z + s • ξ)) 0 := fun ξ => by
    have hg : Continuous fun s : ℝ => z + s • ξ := by fun_prop
    have h0 : IsLocalMax ψ ((fun s : ℝ => z + s • ξ) 0) := by simpa using hmax
    exact h0.comp_continuous (b := (0:ℝ)) hg.continuousAt
  refine ⟨ContinuousLinearMap.ext fun ξ => ?_, fun ξ => ?_⟩
  · have := (hline ξ).hasDerivAt_eq_zero (by simpa using line_hasDerivAt hψ z ξ 0)
    simpa using this
  · have := (localMax_second (Filter.Eventually.of_forall fun s => line_hasDerivAt hψ z ξ s)
      (line_hasDerivAt2 hψ z ξ 0) (by simpa using hline ξ)).2
    simpa using this

/-- directional derivative as a function -/
def gsD (e : Euc d) (φ : Euc d → ℝ) : Euc d → ℝ := fun y => fderiv ℝ φ y e

theorem gs_D_contDiff {n : ℕ} {φ : Euc d → ℝ} (hφ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) φ) (e : Euc d) :
    ContDiff ℝ (n : WithTop ℕ∞) (gsD e φ) := by
  have := (hφ.fderiv_right (m := n) (by exact_mod_cast le_refl _)).clm_apply
    (contDiff_const (c := e))
  exact this

theorem gs_fderiv_D {φ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) (e : Euc d) (y a : Euc d) :
    fderiv ℝ (gsD e φ) y a = fderiv ℝ (fderiv ℝ φ) y a e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const e y))
  have e1 : gsD e φ = fun y => fderiv ℝ φ y e := rfl
  rw [e1, this.fderiv]
  simp

theorem gs_symm {φ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) (y a b : Euc d) :
    fderiv ℝ (fderiv ℝ φ) y a b = fderiv ℝ (fderiv ℝ φ) y b a :=
  (hφ.contDiffAt.isSymmSndFDerivAt (by simp)) a b

theorem gs_D_comm {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (a b y : Euc d) :
    gsD a (gsD b ψ) y = gsD b (gsD a ψ) y := by
  show fderiv ℝ (gsD b ψ) y a = fderiv ℝ (gsD a ψ) y b
  rw [gs_fderiv_D hψ, gs_fderiv_D hψ, gs_symm hψ]


/-- second derivative of a combination of squares along a line -/
theorem gs_D2_W {φ ψ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (A t : ℝ)
    (z a : Euc d) :
    iteratedFDeriv ℝ 2 (fun y => A * φ y ^ 2 + t * ψ y ^ 2) z ![a, a] =
      A * (2 * φ z * iteratedFDeriv ℝ 2 φ z ![a, a] + 2 * (fderiv ℝ φ z a) ^ 2) +
      t * (2 * ψ z * iteratedFDeriv ℝ 2 ψ z ![a, a] + 2 * (fderiv ℝ ψ z a) ^ 2) := by
  set W : Euc d → ℝ := fun y => A * φ y ^ 2 + t * ψ y ^ 2 with hW
  have hWc : ContDiff ℝ 2 W := by
    have := (hφ.pow 2).const_smul A |>.add ((hψ.pow 2).const_smul t)
    simpa [hW, smul_eq_mul] using this
  have hfd : ∀ y, fderiv ℝ W y a = A * (2 * φ y * fderiv ℝ φ y a) + t * (2 * ψ y * fderiv ℝ ψ y a) := by
    intro y
    have h1 := ((hφ.differentiable (by norm_num) y).hasFDerivAt.pow 2).const_mul A
    have h2 := ((hψ.differentiable (by norm_num) y).hasFDerivAt.pow 2).const_mul t
    have h3 : HasFDerivAt W _ y := h1.add h2
    rw [h3.fderiv]
    simp
  have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ W (z + s • a) a) (iteratedFDeriv ℝ 2 W z ![a, a]) 0 := by
    simpa using line_hasDerivAt2 hWc z a 0
  have p1 : HasDerivAt (fun s : ℝ => φ (z + s • a)) (fderiv ℝ φ z a) 0 := by
    simpa using line_hasDerivAt hφ z a 0
  have p2 : HasDerivAt (fun s : ℝ => ψ (z + s • a)) (fderiv ℝ ψ z a) 0 := by
    simpa using line_hasDerivAt hψ z a 0
  have q1 : HasDerivAt (fun s : ℝ => fderiv ℝ φ (z + s • a) a) (iteratedFDeriv ℝ 2 φ z ![a, a]) 0 := by
    simpa using line_hasDerivAt2 hφ z a 0
  have q2 : HasDerivAt (fun s : ℝ => fderiv ℝ ψ (z + s • a) a) (iteratedFDeriv ℝ 2 ψ z ![a, a]) 0 := by
    simpa using line_hasDerivAt2 hψ z a 0
  have h3 := (((p1.const_mul 2).mul q1).const_mul A).add (((p2.const_mul 2).mul q2).const_mul t)
  have h4 : (fun s : ℝ => fderiv ℝ W (z + s • a) a) =
      fun s => A * (2 * φ (z + s • a) * fderiv ℝ φ (z + s • a) a) +
        t * (2 * ψ (z + s • a) * fderiv ℝ ψ (z + s • a) a) := funext fun s => hfd _
  have h5 : HasDerivAt (fun s : ℝ => fderiv ℝ W (z + s • a) a)
      (A * (2 * (fderiv ℝ φ z) a * (fderiv ℝ φ z) a + 2 * φ z * (iteratedFDeriv ℝ 2 φ z) ![a, a]) +
      t * (2 * (fderiv ℝ ψ z) a * (fderiv ℝ ψ z) a + 2 * ψ z * (iteratedFDeriv ℝ 2 ψ z) ![a, a])) 0 := by
    rw [h4]
    refine (h3.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    · simp
    · simp
  have := h2.unique h5
  rw [this]
  ring


/-- the standard basis vector -/
abbrev gsE (i : Fin d) : Euc d := EuclideanSpace.single i 1

theorem gs_sum_sq (g : Euc d →L[ℝ] ℝ) : ∑ i : Fin d, (g (gsE i)) ^ 2 = ‖g‖ ^ 2 := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_sq_norm_inner_right
    ((InnerProductSpace.toDual ℝ (Euc d)).symm g)
  have h2 : ‖(InnerProductSpace.toDual ℝ (Euc d)).symm g‖ = ‖g‖ := LinearIsometryEquiv.norm_map _ _
  rw [← h2, ← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp [gsE, Real.norm_eq_abs, sq_abs]

theorem gs_lap_eq {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) (y : Euc d) :
    ∑ i : Fin d, fderiv ℝ (fderiv ℝ χ) y (gsE i) (gsE i) =
      ∑ i : Fin d, gsD (gsE i) (gsD (gsE i) χ) y := by
  refine Finset.sum_congr rfl fun i _ => ?_
  show _ = fderiv ℝ (gsD (gsE i) χ) y (gsE i)
  rw [gs_fderiv_D hχ]

theorem gs_D3_comm {φ : Euc d → ℝ} (hφ : ContDiff ℝ 3 φ) (e a y : Euc d) :
    gsD e (gsD a (gsD a φ)) y = gsD a (gsD a (gsD e φ)) y := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hχ : ContDiff ℝ 2 (gsD a φ) := gs_D_contDiff (n := 2) hφ a
  rw [gs_D_comm hχ e a y]
  have : gsD e (gsD a φ) = gsD a (gsD e φ) := funext fun y => gs_D_comm h2 e a y
  rw [this]

theorem gs_D_kolmL {q : ℝ} {B : Euc d → Euc d} (hB : ContDiff ℝ 1 B) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ 3 φ) (e y : Euc d) :
    gsD e (kolmL q B φ) y = kolmL q B (gsD e φ) y + fderiv ℝ φ y (-q • e + fderiv ℝ B y e) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hv : ContDiff ℝ 2 (gsD e φ) := gs_D_contDiff (n := 2) hφ e
  have hdD : ∀ a, ContDiff ℝ 1 (gsD a (gsD a φ)) := fun a =>
    gs_D_contDiff (n := 1) (gs_D_contDiff (n := 2) hφ a) a
  have hS : (fun y => ∑ i : Fin d, fderiv ℝ (fderiv ℝ φ) y (gsE i) (gsE i)) =
      fun y => ∑ i : Fin d, gsD (gsE i) (gsD (gsE i) φ) y := funext (gs_lap_eq h2)
  -- the drift term
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    ((hφ.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) y
  have hbd : HasFDerivAt (fun y : Euc d => -q • y + B y) (-q • ContinuousLinearMap.id ℝ (Euc d) + fderiv ℝ B y) y := by
    exact ((hasFDerivAt_id y).const_smul (-q)).add (hB.differentiable (by norm_num) y).hasFDerivAt
  have hT := hdφ.hasFDerivAt.clm_apply hbd
  have hLeq : kolmL q B φ = fun y => (∑ i : Fin d, gsD (gsE i) (gsD (gsE i) φ) y) +
      fderiv ℝ φ y (-q • y + B y) := by
    funext y; rw [kl_L_eq, gs_lap_eq h2]
  have hSd : HasFDerivAt (fun y => ∑ i : Fin d, gsD (gsE i) (gsD (gsE i) φ) y)
      (∑ i : Fin d, fderiv ℝ (gsD (gsE i) (gsD (gsE i) φ)) y) y :=
    HasFDerivAt.fun_sum fun i _ => ((hdD (gsE i)).differentiable (by norm_num) y).hasFDerivAt
  have hTot : HasFDerivAt (fun y => (∑ i : Fin d, gsD (gsE i) (gsD (gsE i) φ) y) +
      fderiv ℝ φ y (-q • y + B y)) _ y := hSd.add hT
  have hL : gsD e (kolmL q B φ) y = fderiv ℝ (kolmL q B φ) y e := rfl
  rw [hL, hLeq, hTot.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  have e1 : ∀ i : Fin d, fderiv ℝ (gsD (gsE i) (gsD (gsE i) φ)) y e =
      gsD (gsE i) (gsD (gsE i) (gsD e φ)) y := fun i => by
    show gsD e (gsD (gsE i) (gsD (gsE i) φ)) y = _
    exact gs_D3_comm hφ e (gsE i) y
  simp only [e1]
  rw [kl_L_eq, gs_lap_eq hv]
  have e2 : fderiv ℝ (fderiv ℝ φ) y e (-q • y + B y) = fderiv ℝ (gsD e φ) y (-q • y + B y) := by
    rw [gs_fderiv_D h2, gs_symm h2]
  rw [e2]
  have e3 : fderiv ℝ (gsD e φ) y (-q • y + B y) = fderiv ℝ (gsD e φ) y (-q • y + B y) := rfl
  simp only [map_add, map_smul, smul_eq_mul]
  ring


theorem gs_fderiv_W {φ ψ : Euc d → ℝ} (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (A t : ℝ)
    (y a : Euc d) :
    fderiv ℝ (fun y => A * φ y ^ 2 + t * ψ y ^ 2) y a =
      A * (2 * φ y * fderiv ℝ φ y a) + t * (2 * ψ y * fderiv ℝ ψ y a) := by
  have h1 := ((hφ.differentiable (by norm_num) y).hasFDerivAt.pow 2).const_mul A
  have h2 := ((hψ.differentiable (by norm_num) y).hasFDerivAt.pow 2).const_mul t
  have h3 : HasFDerivAt (fun y => A * φ y ^ 2 + t * ψ y ^ 2) _ y := h1.add h2
  rw [h3.fderiv]
  simp

/-- The pointwise Bernstein inequality `∂_t Z ≤ L Z` for `Z = A u² + t (∂_e u)²`. -/
theorem gs_bernstein_point {q Mb : ℝ} {B : Euc d → Euc d} (hB : ContDiff ℝ 1 B) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ 3 φ) {e : Euc d} (he : ‖e‖ = 1) {z : Euc d}
    (hBz : ‖fderiv ℝ B z‖ ≤ Mb) {A t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hA : Mb + 1 ≤ A)
    (hq : 0 ≤ q) :
    2 * A * φ z * kolmL q B φ z + (gsD e φ z) ^ 2 + 2 * t * gsD e φ z * gsD e (kolmL q B φ) z ≤
      kolmL q B (fun y => A * φ y ^ 2 + t * (gsD e φ y) ^ 2) z := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have h1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hv : ContDiff ℝ 2 (gsD e φ) := gs_D_contDiff (n := 2) hφ e
  have hv1 : ContDiff ℝ 1 (gsD e φ) := hv.of_le (by norm_num)
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans hBz
  -- Hessian part
  have hHess : ∑ i : Fin d, fderiv ℝ (fderiv ℝ (fun y => A * φ y ^ 2 + t * (gsD e φ y) ^ 2)) z
        (gsE i) (gsE i) =
      A * (2 * φ z * ∑ i : Fin d, fderiv ℝ (fderiv ℝ φ) z (gsE i) (gsE i) +
        2 * ∑ i : Fin d, (fderiv ℝ φ z (gsE i)) ^ 2) +
      t * (2 * gsD e φ z * ∑ i : Fin d, fderiv ℝ (fderiv ℝ (gsD e φ)) z (gsE i) (gsE i) +
        2 * ∑ i : Fin d, (fderiv ℝ (gsD e φ) z (gsE i)) ^ 2) := by
    have := fun i : Fin d => gs_D2_W h2 hv A t z (gsE i)
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at this
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hKW := kl_L_eq q B (fun y => A * φ y ^ 2 + t * (gsD e φ y) ^ 2) z
  have hKφ := kl_L_eq q B φ z
  have hKv := kl_L_eq q B (gsD e φ) z
  have hD := gs_D_kolmL (q := q) hB hφ e z
  rw [hKW, hHess, gs_fderiv_W h1 hv1, hD, hKφ, hKv, gs_sum_sq]
  set n : ℝ := ‖fderiv ℝ φ z‖ with hn
  have hS2 : 0 ≤ ∑ i : Fin d, (fderiv ℝ (gsD e φ) z (gsE i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hn0 : 0 ≤ n := norm_nonneg _
  have hvn : |gsD e φ z| ≤ n := by
    have := (fderiv ℝ φ z).le_opNorm e
    rw [he, mul_one, Real.norm_eq_abs] at this
    exact this
  have hw : |fderiv ℝ φ z (fderiv ℝ B z e)| ≤ n * Mb := by
    have h3 := (fderiv ℝ φ z).le_opNorm (fderiv ℝ B z e)
    have h4 := (fderiv ℝ B z).le_opNorm e
    rw [he, mul_one] at h4
    rw [Real.norm_eq_abs] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (h4.trans hBz) hn0)
  have hvw : |gsD e φ z * fderiv ℝ φ z (fderiv ℝ B z e)| ≤ n * (n * Mb) := by
    rw [abs_mul]; exact mul_le_mul hvn hw (abs_nonneg _) hn0
  have hvw' : gsD e φ z * fderiv ℝ φ z (fderiv ℝ B z e) ≤ n * (n * Mb) := (le_abs_self _).trans hvw
  have hv2 : (gsD e φ z) ^ 2 ≤ n ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hvn 2
  have hdr : fderiv ℝ φ z (-q • e + fderiv ℝ B z e) =
      -q * gsD e φ z + fderiv ℝ φ z (fderiv ℝ B z e) := by
    rw [map_add, map_smul, smul_eq_mul]; rfl
  rw [hdr]
  have h5 : t * (gsD e φ z * fderiv ℝ φ z (fderiv ℝ B z e)) ≤ n * (n * Mb) := by
    have : 0 ≤ n * (n * Mb) := by positivity
    nlinarith
  have h6 : 0 ≤ t * q * (gsD e φ z) ^ 2 := by positivity
  nlinarith [mul_nonneg ht0 hS2, sq_nonneg n, mul_nonneg hn0 hn0, mul_le_mul_of_nonneg_left hA (sq_nonneg n)]


theorem gs_pen_fderiv (κ : ℝ) (z a : Euc d) :
    fderiv ℝ (fun y : Euc d => κ * (1 + ‖y‖ ^ 2)) z a = κ * (2 * inner ℝ z a) := by
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1).const_mul κ
  rw [h.fderiv]
  simp

theorem gs_pen_contDiff (κ : ℝ) : ContDiff ℝ 2 (fun y : Euc d => κ * (1 + ‖y‖ ^ 2)) :=
  contDiff_const.mul (contDiff_const.add (contDiff_norm_sq ℝ))

theorem gs_pen_D2 (κ : ℝ) (z a : Euc d) :
    iteratedFDeriv ℝ 2 (fun y : Euc d => κ * (1 + ‖y‖ ^ 2)) z ![a, a] = 2 * κ * ‖a‖ ^ 2 := by
  have h2 := line_hasDerivAt2 (gs_pen_contDiff (d := d) κ) z a 0
  simp only [zero_smul, add_zero] at h2
  have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ (fun y : Euc d => κ * (1 + ‖y‖ ^ 2)) (z + s • a) a)
      (κ * (2 * ‖a‖ ^ 2)) 0 := by
    have h4 : (fun s : ℝ => fderiv ℝ (fun y : Euc d => κ * (1 + ‖y‖ ^ 2)) (z + s • a) a) =
        fun s => κ * (2 * (inner ℝ z a + s * ‖a‖ ^ 2)) := by
      funext s
      rw [gs_pen_fderiv, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp
    rw [h4]
    have := ((hasDerivAt_id (0:ℝ)).mul_const (‖a‖ ^ 2)).const_add (inner ℝ z a) |>.const_mul 2 |>.const_mul κ
    simpa using this
  have := h2.unique h3
  rw [this]; ring

/-- The penalised maximum step: at a maximum of `W - κ(1+|y|²)`. -/
theorem gs_max_step (q : ℝ) (B : Euc d → Euc d) {W : Euc d → ℝ} (hW : ContDiff ℝ 2 W) {κ : ℝ}
    {z : Euc d} (hmax : IsLocalMax (fun y => W y - κ * (1 + ‖y‖ ^ 2)) z) :
    kolmL q B W z ≤ κ * (2 * d + 2 * inner ℝ z (-q • z + B z)) := by
  have hψ : ContDiff ℝ 2 (fun y => W y - κ * (1 + ‖y‖ ^ 2)) := hW.sub (gs_pen_contDiff κ)
  obtain ⟨h1, h2⟩ := gs_second_order hψ hmax
  have hdW : DifferentiableAt ℝ W z := hW.differentiable (by norm_num) z
  have hdP : DifferentiableAt ℝ (fun y : Euc d => κ * (1 + ‖y‖ ^ 2)) z :=
    (gs_pen_contDiff κ).differentiable (by norm_num) z
  have h1' : ∀ a, fderiv ℝ W z a = κ * (2 * inner ℝ z a) := fun a => by
    have h3 : HasFDerivAt (fun y => W y - κ * (1 + ‖y‖ ^ 2)) _ z :=
      hdW.hasFDerivAt.sub hdP.hasFDerivAt
    have := congrArg (fun L => L a) h1
    simp only [h3.fderiv, ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply] at this
    rw [← gs_pen_fderiv κ z a]
    linarith
  have h2' : ∀ i : Fin d, fderiv ℝ (fderiv ℝ W) z (gsE i) (gsE i) ≤ 2 * κ := fun i => by
    have := h2 (gsE i)
    have this' : iteratedFDeriv ℝ 2 (W - fun y : Euc d => κ * (1 + ‖y‖ ^ 2)) z ![gsE i, gsE i] ≤ 0 := this
    rw [iteratedFDeriv_sub_apply hW.contDiffAt (gs_pen_contDiff κ).contDiffAt] at this'
    replace this := this'
    simp only [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply] at this
    rw [gs_pen_D2] at this
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at this
    have hn : ‖gsE i‖ = 1 := by simp [gsE]
    rw [hn] at this
    linarith
  rw [kl_L_eq, h1']
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2' i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  rw [inner_add_right] at *
  nlinarith [this]

end HRS.MS.PoisGrad
