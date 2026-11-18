import HRS.MS.SpecAux82

/-!
# S8L: the Bochner inequality for `N = |∇e|²` in coordinates (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For `e ∈ C³`, `W ∈ C²` with `D²W ≥ -κ` and an orthonormal basis `b`,
`L_W = -Δ + ⟨∇W, ∇·⟩` satisfies
`L_W N ≤ 2 ⟨∇e, ∇(L_W e)⟩ + 2κ N - |∇N|²/(2(N+ω))` (`s8p_bochner`, from the exact identity `s8p_bochner_id`).
Derivatives are handled through the scalar functions `g c = D e · c`, whose second derivatives are symmetric (`s8p_third_symm`).
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- derivative of `x ↦ f'(x) v`. -/
theorem s8p_fderiv_apply {f : V → ℝ} (hf : ContDiff ℝ 2 f) (v w x : V) :
    fderiv ℝ (fun x => fderiv ℝ f x v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) x := (hf.fderiv_right (m := 1) (by norm_num) : ContDiff ℝ 1 (fderiv ℝ f)).differentiable (by norm_num) x
  have := (h1.hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have e : fderiv ℝ (fun x => fderiv ℝ f x v) x = _ := this.fderiv
  rw [e]; simp [ContinuousLinearMap.flip_apply]

/-- symmetry of the second derivative -/
theorem s8p_symm2 {f : V → ℝ} (hf : ContDiff ℝ 2 f) (x v w : V) :
    fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v := by
  have := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  exact this v w


/-- `g c = x ↦ D e x c`. -/
def s8p_g (e : V → ℝ) (c : V) : V → ℝ := fun x => fderiv ℝ e x c

theorem s8p_g_contDiff {e : V → ℝ} (he : ContDiff ℝ 3 e) (c : V) : ContDiff ℝ 2 (s8p_g e c) :=
  (he.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

theorem s8p_fderiv_g {e : V → ℝ} (he : ContDiff ℝ 3 e) (c v x : V) :
    fderiv ℝ (s8p_g e c) x v = fderiv ℝ (fderiv ℝ e) x v c :=
  s8p_fderiv_apply (he.of_le (by norm_num)) c v x

/-- Symmetry of third derivatives: `D²(g c)(a,b) = D²(g b)(a,c)`. -/
theorem s8p_third_symm {e : V → ℝ} (he : ContDiff ℝ 3 e) (x a b c : V) :
    fderiv ℝ (fderiv ℝ (s8p_g e c)) x a b = fderiv ℝ (fderiv ℝ (s8p_g e b)) x a c := by
  have e2 : ContDiff ℝ 2 e := he.of_le (by norm_num)
  have h1 : ∀ c b, fderiv ℝ (fderiv ℝ (s8p_g e c)) x a b =
      fderiv ℝ (fun x' => fderiv ℝ (fderiv ℝ e) x' b c) x a := fun c b => by
    have := s8p_fderiv_apply (s8p_g_contDiff he c) b a x
    rw [← this]
    have hf : (fun x' => fderiv ℝ (s8p_g e c) x' b) = fun x' => fderiv ℝ (fderiv ℝ e) x' b c :=
      funext fun x' => s8p_fderiv_g he c b x'
    rw [hf]
  rw [h1 c b, h1 b c]
  have hf : (fun x' => fderiv ℝ (fderiv ℝ e) x' b c) = fun x' => fderiv ℝ (fderiv ℝ e) x' c b :=
    funext fun x' => s8p_symm2 e2 x' b c
  rw [hf]


section Bochner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ V)

/-- `N = Σ (∂_i e)²`. -/
def s8p_N (e : V → ℝ) (x : V) : ℝ := ∑ i, (s8p_g e (b i) x) ^ 2

theorem s8p_N_eq (e : V → ℝ) (x : V) : s8p_N b e x = ‖fderiv ℝ e x‖ ^ 2 := by
  unfold s8p_N s8p_g
  rw [OrthonormalBasis.norm_dual b]

theorem s8p_N_contDiff {e : V → ℝ} (he : ContDiff ℝ 3 e) : ContDiff ℝ 2 (s8p_N b e) := by
  unfold s8p_N
  exact ContDiff.sum fun i _ => (s8p_g_contDiff he (b i)).pow 2

theorem s8p_N_fderiv {e : V → ℝ} (he : ContDiff ℝ 3 e) (x w : V) :
    fderiv ℝ (s8p_N b e) x w = ∑ i, 2 * s8p_g e (b i) x * fderiv ℝ (fderiv ℝ e) x w (b i) := by
  have hd : ∀ i, HasFDerivAt (fun x => s8p_g e (b i) x ^ 2)
      ((2 * s8p_g e (b i) x) • fderiv ℝ (s8p_g e (b i)) x) x := fun i => by
    have := ((s8p_g_contDiff he (b i)).differentiable (by norm_num) x).hasFDerivAt.pow 2
    simpa using this
  have := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
  have eN : s8p_N b e = ∑ i, (fun x => s8p_g e (b i) x ^ 2) := by
    funext x; simp [s8p_N]
  have e1 : fderiv ℝ (s8p_N b e) x = ∑ i, (2 * s8p_g e (b i) x) • fderiv ℝ (s8p_g e (b i)) x := by
    rw [eN]; exact this.fderiv
  rw [e1]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s8p_fderiv_g he]


theorem s8p_N_fderiv2 {e : V → ℝ} (he : ContDiff ℝ 3 e) (x w' w : V) :
    fderiv ℝ (fderiv ℝ (s8p_N b e)) x w' w = ∑ i, 2 * (fderiv ℝ (fderiv ℝ e) x w' (b i) *
      fderiv ℝ (fderiv ℝ e) x w (b i) + s8p_g e (b i) x * fderiv ℝ (fderiv ℝ (s8p_g e (b i))) x w' w) := by
  rw [← s8p_fderiv_apply (s8p_N_contDiff b he) w w' x]
  have hfun : (fun x' => fderiv ℝ (s8p_N b e) x' w) =
      ∑ i, (fun x' => 2 * (s8p_g e (b i) x' * fderiv ℝ (s8p_g e (b i)) x' w)) := by
    funext x'
    rw [s8p_N_fderiv b he]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [s8p_fderiv_g he]; ring
  rw [hfun]
  have hd : ∀ i, HasFDerivAt (fun x' => 2 * (s8p_g e (b i) x' * fderiv ℝ (s8p_g e (b i)) x' w))
      ((2:ℝ) • (s8p_g e (b i) x • fderiv ℝ (fun x' => fderiv ℝ (s8p_g e (b i)) x' w) x +
        fderiv ℝ (s8p_g e (b i)) x w • fderiv ℝ (s8p_g e (b i)) x)) x := fun i => by
    have h1 : DifferentiableAt ℝ (s8p_g e (b i)) x := ((s8p_g_contDiff he (b i)).differentiable (by norm_num)) x
    have h2 : DifferentiableAt ℝ (fun x' => fderiv ℝ (s8p_g e (b i)) x' w) x := by
      have := ((s8p_g_contDiff he (b i)).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
      exact this.clm_apply (differentiableAt_const w)
    have := (h1.hasFDerivAt.mul h2.hasFDerivAt).const_mul 2
    simpa [add_comm] using this
  have := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
  rw [this.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s8p_fderiv_apply (s8p_g_contDiff he (b i)) w w' x, s8p_fderiv_g he, s8p_fderiv_g he]
  ring

/-- The Laplacian in the basis `b`. -/
def s8p_lap (f : V → ℝ) (x : V) : ℝ := ∑ j, fderiv ℝ (fderiv ℝ f) x (b j) (b j)

/-- `L_W f = -Δ f + ⟨∇W, ∇f⟩`. -/
def s8p_Lw (W f : V → ℝ) (x : V) : ℝ := -s8p_lap b f x + ∑ j, fderiv ℝ W x (b j) * fderiv ℝ f x (b j)

theorem s8p_lap_fderiv {e : V → ℝ} (he : ContDiff ℝ 3 e) (x : V) (i : ι) :
    fderiv ℝ (s8p_lap b e) x (b i) = ∑ j, fderiv ℝ (fderiv ℝ (s8p_g e (b j))) x (b i) (b j) := by
  have hfun : s8p_lap b e = ∑ j, (fun x' => fderiv ℝ (s8p_g e (b j)) x' (b j)) := by
    funext x'
    simp only [s8p_lap, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [s8p_fderiv_g he]
  have hd : ∀ j, HasFDerivAt (fun x' => fderiv ℝ (s8p_g e (b j)) x' (b j))
      (fderiv ℝ (fun x' => fderiv ℝ (s8p_g e (b j)) x' (b j)) x) x := fun j => by
    have := ((s8p_g_contDiff he (b j)).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
    exact (this.clm_apply (differentiableAt_const (b j))).hasFDerivAt
  rw [hfun, (HasFDerivAt.sum (u := Finset.univ) (fun j _ => hd j)).fderiv]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact s8p_fderiv_apply (s8p_g_contDiff he (b j)) (b j) (b i) x

theorem s8p_Lw_fderiv {e W : V → ℝ} (he : ContDiff ℝ 3 e) (hW : ContDiff ℝ 2 W) (x : V) (i : ι) :
    fderiv ℝ (s8p_Lw b W e) x (b i) = -(∑ j, fderiv ℝ (fderiv ℝ (s8p_g e (b j))) x (b i) (b j)) +
      ∑ j, (fderiv ℝ (fderiv ℝ W) x (b i) (b j) * s8p_g e (b j) x +
        fderiv ℝ W x (b j) * fderiv ℝ (fderiv ℝ e) x (b i) (b j)) := by
  have hlap : DifferentiableAt ℝ (s8p_lap b e) x := by
    have hfun : s8p_lap b e = ∑ j, (fun x' => fderiv ℝ (s8p_g e (b j)) x' (b j)) := by
      funext x'
      simp only [s8p_lap, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [s8p_fderiv_g he]
    rw [hfun]
    refine DifferentiableAt.sum fun j _ => ?_
    have := ((s8p_g_contDiff he (b j)).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
    exact this.clm_apply (differentiableAt_const (b j))
  have hterm : ∀ j, HasFDerivAt (fun x' => fderiv ℝ W x' (b j) * s8p_g e (b j) x')
      (fderiv ℝ W x (b j) • fderiv ℝ (s8p_g e (b j)) x +
        s8p_g e (b j) x • fderiv ℝ (fun x' => fderiv ℝ W x' (b j)) x) x := fun j => by
    have h1 : DifferentiableAt ℝ (fun x' => fderiv ℝ W x' (b j)) x := by
      have := ((hW.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
      exact this.clm_apply (differentiableAt_const (b j))
    have h2 : DifferentiableAt ℝ (s8p_g e (b j)) x := ((s8p_g_contDiff he (b j)).differentiable (by norm_num)) x
    exact h1.hasFDerivAt.mul h2.hasFDerivAt
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun j _ => hterm j)
  have hfun2 : s8p_Lw b W e = fun x' => -s8p_lap b e x' + (∑ j, fun x'' => fderiv ℝ W x'' (b j) * s8p_g e (b j) x'') x' := by
    funext x'
    simp only [s8p_Lw, Finset.sum_apply]
    rfl
  have hLw : HasFDerivAt (s8p_Lw b W e) (-(fderiv ℝ (s8p_lap b e) x) +
      ∑ j, (fderiv ℝ W x (b j) • fderiv ℝ (s8p_g e (b j)) x +
        s8p_g e (b j) x • fderiv ℝ (fun x' => fderiv ℝ W x' (b j)) x)) x := by
    rw [hfun2]
    exact hlap.hasFDerivAt.neg.add hsum
  rw [hLw.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [s8p_lap_fderiv b he]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [s8p_fderiv_g he, s8p_fderiv_apply hW (b j) (b i) x]
  ring

/-- **Bochner identity** in coordinates. -/
theorem s8p_bochner_id {e W : V → ℝ} (he : ContDiff ℝ 3 e) (hW : ContDiff ℝ 2 W) (x : V) :
    s8p_Lw b W (s8p_N b e) x =
      2 * ∑ i, s8p_g e (b i) x * fderiv ℝ (s8p_Lw b W e) x (b i)
        - 2 * ∑ j, ∑ i, (fderiv ℝ (fderiv ℝ e) x (b j) (b i)) ^ 2
        - 2 * ∑ i, ∑ j, fderiv ℝ (fderiv ℝ W) x (b i) (b j) * s8p_g e (b i) x * s8p_g e (b j) x := by
  have e2 : ContDiff ℝ 2 e := he.of_le (by norm_num)
  set u : ι → ℝ := fun i => s8p_g e (b i) x with hu
  set H : ι → ι → ℝ := fun j i => fderiv ℝ (fderiv ℝ e) x (b j) (b i) with hH
  set T : ι → ι → ι → ℝ := fun i j k => fderiv ℝ (fderiv ℝ (s8p_g e (b i))) x (b j) (b k) with hT
  set DW : ι → ℝ := fun j => fderiv ℝ W x (b j) with hDW
  set D2W : ι → ι → ℝ := fun i j => fderiv ℝ (fderiv ℝ W) x (b i) (b j) with hD2W
  have hHs : ∀ i j, H i j = H j i := fun i j => s8p_symm2 e2 x (b i) (b j)
  have hs1 : ∀ i, ∑ j, T i j j = ∑ j, T j i j := fun i => by
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := s8p_third_symm he x (b j) (b j) (b i)
    have h2 := s8p_symm2 (s8p_g_contDiff he (b j)) x (b j) (b i)
    show fderiv ℝ (fderiv ℝ (s8p_g e (b i))) x (b j) (b j) = fderiv ℝ (fderiv ℝ (s8p_g e (b j))) x (b i) (b j)
    rw [h1, h2]
  have hA : s8p_lap b (s8p_N b e) x = ∑ j, ∑ i, 2 * (H j i * H j i + u i * T i j j) := by
    simp only [s8p_lap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [s8p_N_fderiv2 b he]
  have hB : ∑ j, fderiv ℝ W x (b j) * fderiv ℝ (s8p_N b e) x (b j) = ∑ j, DW j * ∑ i, 2 * u i * H j i := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [s8p_N_fderiv b he]
  have hC : ∀ i, fderiv ℝ (s8p_Lw b W e) x (b i) = -(∑ j, T j i j) + ∑ j, (D2W i j * u j + DW j * H i j) := fun i => by
    rw [s8p_Lw_fderiv b he hW]
  have hLHS : s8p_Lw b W (s8p_N b e) x = -s8p_lap b (s8p_N b e) x +
      ∑ j, fderiv ℝ W x (b j) * fderiv ℝ (s8p_N b e) x (b j) := rfl
  rw [hLHS, hA, hB]
  simp_rw [hC]
  have e1 : ∑ j, ∑ i, 2 * (H j i * H j i + u i * T i j j) =
      2 * ∑ j, ∑ i, (H j i) ^ 2 + 2 * ∑ i, u i * ∑ j, T j i j := by
    have a1 : ∀ j i, 2 * (H j i * H j i + u i * T i j j) = 2 * (H j i) ^ 2 + 2 * (u i * T i j j) :=
      fun j i => by ring
    simp_rw [a1, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hs1 i]
  have e2 : ∑ j, DW j * ∑ i, 2 * u i * H j i = 2 * ∑ i, u i * ∑ j, DW j * H i j := by
    have a2 : ∀ j, DW j * ∑ i, 2 * u i * H j i = ∑ i, 2 * (u i * (DW j * H j i)) := fun j => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [a2]
    rw [Finset.sum_comm]
    have a4 : ∀ i, ∑ j, 2 * (u i * (DW j * H j i)) = 2 * (u i * ∑ j, DW j * H i j) := fun i => by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hHs j i]
    simp_rw [a4]
    rw [Finset.mul_sum]
  have e3 : ∑ i, u i * (-(∑ j, T j i j) + ∑ j, (D2W i j * u j + DW j * H i j)) =
      -(∑ i, u i * ∑ j, T j i j) + ∑ i, ∑ j, D2W i j * u i * u j + ∑ i, u i * ∑ j, DW j * H i j := by
    have a3 : ∀ i, u i * (-(∑ j, T j i j) + ∑ j, (D2W i j * u j + DW j * H i j)) =
        -(u i * ∑ j, T j i j) + ∑ j, D2W i j * u i * u j + u i * ∑ j, DW j * H i j := fun i => by
      have h1 : u i * ∑ j, D2W i j * u j = ∑ j, D2W i j * u i * u j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [Finset.sum_add_distrib, mul_add, mul_add, mul_neg, h1]; ring
    simp_rw [a3, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [e1, e2, e3]
  ring

/-- **Bochner inequality** for `N = |∇e|²`. -/
theorem s8p_bochner {e W : V → ℝ} (he : ContDiff ℝ 3 e) (hW : ContDiff ℝ 2 W) {κ ω : ℝ} (hω : 0 < ω)
    (hκ : ∀ x v, -(κ * ‖v‖ ^ 2) ≤ fderiv ℝ (fderiv ℝ W) x v v) (x : V) :
    s8p_Lw b W (s8p_N b e) x ≤
      2 * ∑ i, s8p_g e (b i) x * fderiv ℝ (s8p_Lw b W e) x (b i) + 2 * κ * s8p_N b e x -
        ‖fderiv ℝ (s8p_N b e) x‖ ^ 2 / (2 * (s8p_N b e x + ω)) := by
  rw [s8p_bochner_id b he hW x]
  set u : ι → ℝ := fun i => s8p_g e (b i) x with hu
  set H : ι → ι → ℝ := fun j i => fderiv ℝ (fderiv ℝ e) x (b j) (b i) with hH
  set S : ℝ := ∑ j, ∑ i, (H j i) ^ 2 with hS
  have hN : s8p_N b e x = ∑ i, u i ^ 2 := rfl
  have hN0 : 0 ≤ s8p_N b e x := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- Hessian of W
  have h1 : ∑ i, ∑ j, fderiv ℝ (fderiv ℝ W) x (b i) (b j) * u i * u j ≥ -(κ * s8p_N b e x) := by
    set v : V := ∑ i, u i • b i with hv
    have e1 : fderiv ℝ (fderiv ℝ W) x v v = ∑ i, ∑ j, fderiv ℝ (fderiv ℝ W) x (b i) (b j) * u i * u j := by
      simp only [hv, map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [s8p_symm2 hW x (b j) (b i)]; ring
    have e2 : ‖v‖ ^ 2 = s8p_N b e x := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [hv, sum_inner, inner_sum, inner_smul_left, inner_smul_right, b.inner_eq_ite, hN]
      simp [Finset.sum_ite_eq, sq]
    have := hκ x v
    rw [e1, e2] at this
    exact this
  -- Cauchy-Schwarz for the gradient of N
  have h2 : ‖fderiv ℝ (s8p_N b e) x‖ ^ 2 ≤ 4 * s8p_N b e x * S := by
    rw [OrthonormalBasis.norm_dual b]
    have : ∀ k, (fderiv ℝ (s8p_N b e) x (b k)) ^ 2 ≤ 4 * s8p_N b e x * ∑ i, (H k i) ^ 2 := fun k => by
      rw [s8p_N_fderiv b he]
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u (fun i => H k i)
      have e3 : ∑ i, 2 * s8p_g e (b i) x * fderiv ℝ (fderiv ℝ e) x (b k) (b i) = 2 * ∑ i, u i * H k i := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hu, hH]; rw [s8p_symm2 (he.of_le (by norm_num)) x (b k) (b i)] ; ring
      rw [e3]
      calc (2 * ∑ i, u i * H k i) ^ 2 = 4 * (∑ i, u i * H k i) ^ 2 := by ring
        _ ≤ 4 * ((∑ i, u i ^ 2) * ∑ i, H k i ^ 2) := by linarith [this]
        _ = _ := by rw [hN]; ring
    calc _ ≤ ∑ k, 4 * s8p_N b e x * ∑ i, (H k i) ^ 2 := Finset.sum_le_sum fun k _ => this k
      _ = 4 * s8p_N b e x * S := by rw [← Finset.mul_sum]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have h3 : ‖fderiv ℝ (s8p_N b e) x‖ ^ 2 / (2 * (s8p_N b e x + ω)) ≤ 2 * S := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hω.le hS0]
  linarith [h1, h3]

end Bochner

end HRS.MS.Spec
