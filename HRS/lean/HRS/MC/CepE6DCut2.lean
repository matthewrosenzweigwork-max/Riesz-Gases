import HRS.MC.CepE6DCut

/-!
# Packet CEPE6D, part 1b: `g_ε` on `ℝ^N`, its gradient `v_ε` and Hessian (Itô input)
-/

open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace HRS.MC.CepE6D

variable {N : ℕ}

/-- `g_ε(z) = ∑_{k<l} χ_ε(z_l - z_k)`, on all of `ℝ^N`. -/
def gg (ε : ℝ) (z : Ch6D N) : ℝ :=
  ∑ k : Fin N, ∑ l : Fin N, if k < l then chi ε (z l - z k) else 0

/-- `v_ε = ∇ g_ε = ∑_{k<l} χ_ε'(z_l - z_k) (e_l - e_k)`. -/
def vv (ε : ℝ) (z : Ch6D N) : Ch6D N :=
  ∑ k : Fin N, ∑ l : Fin N, if k < l then
    chi1 ε (z l - z k) • (EuclideanSpace.single l (1 : ℝ) - EuclideanSpace.single k (1 : ℝ)) else 0

/-- Second derivative of `g_ε` as a bilinear form. -/
def hessForm (ε : ℝ) (z u w : Ch6D N) : ℝ :=
  ∑ k : Fin N, ∑ l : Fin N, if k < l then chi2 ε (z l - z k) * ((u l - u k) * (w l - w k)) else 0

/-- The functional `u ↦ u_l - u_k`. -/
def lin (N : ℕ) (k l : Fin N) : Ch6D N →L[ℝ] ℝ := EuclideanSpace.proj l - EuclideanSpace.proj k

theorem lin_apply (k l : Fin N) (u : Ch6D N) : lin N k l u = u l - u k := by
  simp [lin]

theorem inner_vv (ε : ℝ) (z u : Ch6D N) :
    ⟪vv ε z, u⟫ = ∑ k : Fin N, ∑ l : Fin N, if k < l then chi1 ε (z l - z k) * (u l - u k) else 0 := by
  unfold vv
  simp only [sum_inner]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp [inner_smul_left, inner_sub_left, EuclideanSpace.inner_single_left]
  · simp


/-- First derivative of the `(k,l)`-term. -/
def D1 (ε : ℝ) (k l : Fin N) (z : Ch6D N) : Ch6D N →L[ℝ] ℝ :=
  if k < l then chi1 ε (z l - z k) • lin N k l else 0

/-- Second derivative of the `(k,l)`-term. -/
def D2 (ε : ℝ) (k l : Fin N) (z : Ch6D N) : Ch6D N →L[ℝ] (Ch6D N →L[ℝ] ℝ) :=
  if k < l then (chi2 ε (z l - z k) • lin N k l).smulRight (lin N k l) else 0

theorem hasFDerivAt_term (ε : ℝ) (k l : Fin N) (z : Ch6D N) :
    HasFDerivAt (fun y : Ch6D N => if k < l then chi ε (y l - y k) else 0) (D1 ε k l z) z := by
  by_cases hkl : k < l
  · have h := (chi_hasDerivAt ε (lin N k l z)).comp_hasFDerivAt z (lin N k l).hasFDerivAt
    have h' : HasFDerivAt (fun y : Ch6D N => chi ε (y l - y k))
        (chi1 ε (lin N k l z) • lin N k l) z :=
      h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [lin_apply])
    simpa [D1, hkl, lin_apply] using h'
  · simpa [D1, hkl] using hasFDerivAt_const (0 : ℝ) z

theorem hasFDerivAt_D1 (ε : ℝ) (k l : Fin N) (z : Ch6D N) :
    HasFDerivAt (fun y : Ch6D N => D1 ε k l y) (D2 ε k l z) z := by
  by_cases hkl : k < l
  · have h0 := (chi1_hasDerivAt ε (lin N k l z)).comp_hasFDerivAt z (lin N k l).hasFDerivAt
    have h0' : HasFDerivAt (fun y : Ch6D N => chi1 ε (y l - y k))
        (chi2 ε (lin N k l z) • lin N k l) z :=
      h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [lin_apply])
    have h := h0'.smul_const (lin N k l)
    simpa [D1, D2, hkl, lin_apply] using h
  · simpa [D1, D2, hkl] using hasFDerivAt_const (0 : Ch6D N →L[ℝ] ℝ) z

theorem hasFDerivAt_gg (ε : ℝ) (z : Ch6D N) :
    HasFDerivAt (gg ε) (∑ k : Fin N, ∑ l : Fin N, D1 ε k l z) z := by
  have := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) (x := z)
    (A := fun k (y : Ch6D N) => ∑ l : Fin N, if k < l then chi ε (y l - y k) else 0)
    (A' := fun k => ∑ l : Fin N, D1 ε k l z)
    (fun k _ => HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) (x := z)
      (A := fun l (y : Ch6D N) => if k < l then chi ε (y l - y k) else 0)
      (A' := fun l => D1 ε k l z) (fun l _ => hasFDerivAt_term ε k l z))
  exact this

theorem fderiv_gg_eq (ε : ℝ) : fderiv ℝ (gg ε) = fun z : Ch6D N => ∑ k : Fin N, ∑ l : Fin N, D1 ε k l z :=
  funext fun z => (hasFDerivAt_gg ε z).fderiv

theorem hasFDerivAt_fderiv_gg (ε : ℝ) (z : Ch6D N) :
    HasFDerivAt (fderiv ℝ (gg ε)) (∑ k : Fin N, ∑ l : Fin N, D2 ε k l z) z := by
  rw [fderiv_gg_eq]
  exact HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) (x := z)
    (A := fun k (y : Ch6D N) => ∑ l : Fin N, D1 ε k l y)
    (A' := fun k => ∑ l : Fin N, D2 ε k l z)
    (fun k _ => HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) (x := z)
      (A := fun l (y : Ch6D N) => D1 ε k l y)
      (A' := fun l => D2 ε k l z) (fun l _ => hasFDerivAt_D1 ε k l z))


theorem sumD1_apply (ε : ℝ) (z u : Ch6D N) :
    (∑ k : Fin N, ∑ l : Fin N, D1 ε k l z) u =
      ∑ k : Fin N, ∑ l : Fin N, if k < l then chi1 ε (z l - z k) * (u l - u k) else 0 := by
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  unfold D1
  split_ifs <;> simp [lin_apply]

theorem sumD2_apply (ε : ℝ) (z u w : Ch6D N) :
    (∑ k : Fin N, ∑ l : Fin N, D2 ε k l z) u w = hessForm ε z u w := by
  simp only [ContinuousLinearMap.sum_apply]
  unfold hessForm
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  unfold D2
  split_ifs <;> simp [lin_apply]
  ring

/-- `∇ g_ε = v_ε`, in `HasFDerivAt` form. -/
theorem hasFDerivAt_gg_inner (ε : ℝ) (z : Ch6D N) :
    HasFDerivAt (gg ε) (innerSL ℝ (vv ε z)) z := by
  have h := hasFDerivAt_gg ε z
  convert h using 1
  ext u
  rw [sumD1_apply, innerSL_apply_apply, inner_vv]

theorem hasGradientAt_gg (ε : ℝ) (z : Ch6D N) : HasGradientAt (gg ε) (vv ε z) z := by
  refine hasGradientAt_iff_hasFDerivAt.2 ?_
  convert hasFDerivAt_gg_inner ε z using 1
  ext u
  simp [InnerProductSpace.toDual_apply_apply]

theorem gradient_gg (ε : ℝ) (z : Ch6D N) : gradient (gg ε) z = vv ε z :=
  (hasGradientAt_gg ε z).gradient

theorem fderiv_gg_apply (ε : ℝ) (z u : Ch6D N) : fderiv ℝ (gg ε) z u = ⟪vv ε z, u⟫ := by
  rw [(hasFDerivAt_gg_inner ε z).fderiv]; simp [innerSL_apply_apply]

/-- The Hessian of `g_ε`: `D²g_ε(z)[u,w] = ∑_{k<l} χ_ε''(z_l - z_k)(u_l - u_k)(w_l - w_k)`. -/
theorem fderiv_fderiv_gg_apply (ε : ℝ) (z u w : Ch6D N) :
    fderiv ℝ (fderiv ℝ (gg ε)) z u w = hessForm ε z u w := by
  rw [(hasFDerivAt_fderiv_gg ε z).fderiv, sumD2_apply]

theorem gg_contDiff (ε : ℝ) : ContDiff ℝ ∞ (gg (N := N) ε) := by
  unfold gg
  refine ContDiff.sum fun k _ => ContDiff.sum fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, if_true]
    have : (fun y : Ch6D N => chi ε (y l - y k)) = chi ε ∘ lin N k l := by
      funext y; simp [lin_apply]
    rw [this]; exact (chi_contDiff ε).comp (ContinuousLinearMap.contDiff (lin N k l))
  · simp [hkl]; exact contDiff_const

theorem vv_contDiff (ε : ℝ) : ContDiff ℝ ∞ (vv (N := N) ε) := by
  unfold vv
  refine ContDiff.sum fun k _ => ContDiff.sum fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, if_true]
    have : (fun y : Ch6D N => chi1 ε (y l - y k)) = chi1 ε ∘ lin N k l := by
      funext y; simp [lin_apply]
    have h1 : ContDiff ℝ ∞ (fun y : Ch6D N => chi1 ε (y l - y k)) := by
      rw [this]; exact (chi1_contDiff ε).comp (ContinuousLinearMap.contDiff (lin N k l))
    exact h1.smul contDiff_const
  · simp [hkl]; exact contDiff_const

/-- The Laplacian: `∑_i D²g_ε(z)[e_i,e_i] = 2 ∑_{k<l} χ_ε''(z_l - z_k)`. -/
theorem laplacian_gg (ε : ℝ) (z : Ch6D N) :
    ∑ i : Fin N, fderiv ℝ (fderiv ℝ (gg ε)) z (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) =
      2 * ∑ k : Fin N, ∑ l : Fin N, if k < l then chi2 ε (z l - z k) else 0 := by
  simp only [fderiv_fderiv_gg_apply, hessForm]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k < l
  · have hne : k ≠ l := hkl.ne
    simp only [hkl, if_true, EuclideanSpace.single_apply]
    rw [← Finset.mul_sum]
    have : ∑ i : Fin N, ((if l = i then (1 : ℝ) else 0) - if k = i then 1 else 0) *
        ((if l = i then (1 : ℝ) else 0) - if k = i then 1 else 0) = 2 := by
      simp only [sub_mul, mul_sub]
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, hne, hne.symm]
      norm_num
    rw [this]; ring
  · simp [hkl]


/-! ### Component form, bounds, support -/

/-- The `(j,k)` summand of the `j`-th component of `v_ε`. -/
def acomp (ε : ℝ) (z : Ch6D N) (j k : Fin N) : ℝ :=
  if k < j then chi1 ε (z j - z k) else if j < k then - chi1 ε (z k - z j) else 0

theorem acomp_eq (ε : ℝ) (z : Ch6D N) (j k : Fin N) :
    acomp ε z j k = (if k < j then chi1 ε (z j - z k) else 0) -
      (if j < k then chi1 ε (z k - z j) else 0) := by
  unfold acomp
  by_cases h1 : k < j
  · have h2 : ¬ j < k := not_lt.2 h1.le
    simp [h1, h2]
  · by_cases h2 : j < k <;> simp [h1, h2]

theorem abs_acomp_le (ε : ℝ) (z : Ch6D N) (j k : Fin N) : |acomp ε z j k| ≤ 1 := by
  unfold acomp
  split_ifs
  · exact abs_chi1_le ε _
  · rw [abs_neg]; exact abs_chi1_le ε _
  · simp

theorem vv_apply (ε : ℝ) (z : Ch6D N) (j : Fin N) : vv ε z j = ∑ k : Fin N, acomp ε z j k := by
  have h := inner_vv ε z (EuclideanSpace.single j (1 : ℝ))
  have h0 : ⟪vv ε z, EuclideanSpace.single j (1 : ℝ)⟫ = vv ε z j := by
    simp [EuclideanSpace.inner_single_right]
  rw [← h0, h]
  simp only [acomp_eq, Finset.sum_sub_distrib]
  have e : ∀ k l : Fin N, (if k < l then chi1 ε (z l - z k) *
      ((EuclideanSpace.single j (1 : ℝ) : Ch6D N) l - (EuclideanSpace.single j (1 : ℝ) : Ch6D N) k)
      else 0) = (if k < l then chi1 ε (z l - z k) * (EuclideanSpace.single j (1 : ℝ) : Ch6D N) l
        else 0) - (if k < l then chi1 ε (z l - z k) *
          (EuclideanSpace.single j (1 : ℝ) : Ch6D N) k else 0) := by
    intro k l; split_ifs <;> simp [mul_sub]
  simp only [e, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [EuclideanSpace.single_apply]
    rw [Finset.sum_eq_single j]
    · by_cases hk : k < j <;> simp [hk]
    · intro l _ hl; simp [hl]
    · simp
  · simp only [EuclideanSpace.single_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single j]
    · by_cases hk : j < l <;> simp [hk]
    · intro k _ hk; simp [hk]
    · simp

theorem sum_pairs_count (N : ℕ) :
    2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then (1 : ℝ) else 0) = (N : ℝ) ^ 2 - N := by
  have h1 : ∑ k : Fin N, ∑ l : Fin N, (if k < l then (1 : ℝ) else 0) =
      ∑ k : Fin N, ∑ l : Fin N, (if l < k then (1 : ℝ) else 0) := Finset.sum_comm
  have h2 : ∑ k : Fin N, ∑ l : Fin N, ((if k < l then (1 : ℝ) else 0) + (if l < k then 1 else 0) +
      (if k = l then 1 else 0)) = (N : ℝ) ^ 2 := by
    have : ∀ k l : Fin N, ((if k < l then (1 : ℝ) else 0) + (if l < k then 1 else 0) +
        (if k = l then 1 else 0)) = 1 := by
      intro k l
      rcases lt_trichotomy k l with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h; simp
      · simp [h, h.ne', not_lt.2 h.le]
    simp [this]; ring
  simp only [Finset.sum_add_distrib] at h2
  have h3 : ∑ k : Fin N, ∑ l : Fin N, (if k = l then (1 : ℝ) else 0) = N := by simp
  linarith

theorem norm_vv_le_sq_sub (ε : ℝ) (z : Ch6D N) : ‖vv ε z‖ ≤ (N : ℝ) ^ 2 - N := by
  have hterm : ∀ k l : Fin N, ‖(if k < l then
      chi1 ε (z l - z k) • (EuclideanSpace.single l (1 : ℝ) - EuclideanSpace.single k (1 : ℝ)) else
      (0 : Ch6D N))‖ ≤ if k < l then (2 : ℝ) else 0 := by
    intro k l
    split_ifs
    · rw [norm_smul]
      have h1 : ‖EuclideanSpace.single l (1 : ℝ) - EuclideanSpace.single k (1 : ℝ)‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        simp; norm_num
      have h2 : ‖chi1 ε (z l - z k)‖ ≤ 1 := abs_chi1_le ε _
      calc _ ≤ 1 * 2 := mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = 2 := by norm_num
    · simp
  unfold vv
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun l _ => hterm k l)).trans ?_
  have := sum_pairs_count N
  have e : ∑ k : Fin N, ∑ l : Fin N, (if k < l then (2 : ℝ) else 0) =
      2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [e, this]

theorem norm_vv_le (ε : ℝ) (z : Ch6D N) : ‖vv ε z‖ ≤ (N : ℝ) ^ 2 := by
  have := norm_vv_le_sq_sub ε z
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/-- Support: `v_ε(z) = 0` unless some pair has `min(d, 1-d) < ε/2`. -/
theorem vv_eq_zero (ε : ℝ) (hε : 0 < ε) (z : Ch6D N)
    (h : ∀ k l : Fin N, k < l → ε / 2 ≤ min (z l - z k) (1 - (z l - z k))) : vv ε z = 0 := by
  unfold vv
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  by_cases hkl : k < l
  · have := le_min_iff.1 (h k l hkl)
    simp [hkl, chi1_eq_zero hε this.1 this.2]
  · simp [hkl]

theorem norm_vv_le_indicator (ε : ℝ) (hε : 0 < ε) (z : Ch6D N) :
    ‖vv ε z‖ ≤ if (∃ k l : Fin N, k < l ∧ min (z l - z k) (1 - (z l - z k)) < ε / 2) then
      (N : ℝ) ^ 2 else 0 := by
  split_ifs with h
  · exact norm_vv_le ε z
  · push Not at h
    rw [vv_eq_zero ε hε z fun k l hkl => h k l hkl]; simp

/-- `|Δ g_ε(z)| ≤ 2 ∑_{k<l} (Cz/ε) 1_{min(d_kl, 1-d_kl) < ε/2}`. -/
theorem abs_laplacian_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) (z : Ch6D N) :
    |2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then chi2 ε (z l - z k) else 0)| ≤
      2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then
        (if min (z l - z k) (1 - (z l - z k)) < ε / 2 then Cz / ε else 0) else 0) := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  by_cases h1 : k < l
  · simp only [h1, if_true]; exact abs_chi2_le_indicator _ hε hε1
  · simp [h1]

theorem abs_laplacian_le_sq (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) (z : Ch6D N) :
    |2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then chi2 ε (z l - z k) else 0)| ≤
      (N : ℝ) ^ 2 * (Cz / ε) := by
  refine (abs_laplacian_le ε hε hε1 z).trans ?_
  have hC : 0 ≤ Cz / ε := div_nonneg (by linarith [one_le_Cz]) hε.le
  have e : ∑ k : Fin N, ∑ l : Fin N, (if k < l then
        (if min (z l - z k) (1 - (z l - z k)) < ε / 2 then Cz / ε else 0) else 0) ≤
      (∑ k : Fin N, ∑ l : Fin N, (if k < l then (1 : ℝ) else 0)) * (Cz / ε) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l _ => ?_
    split_ifs <;> simp [hC]
  have := sum_pairs_count N
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [mul_le_mul_of_nonneg_right e (by norm_num : (0 : ℝ) ≤ 2)]


/-- On pairs with `0 ≤ z_l - z_k ≤ 1` (e.g. the closed alcove), `0 ≤ g_ε ≤ ε N²`. -/
theorem gg_bounds (ε : ℝ) (hε : 0 < ε) (z : Ch6D N)
    (h : ∀ k l : Fin N, k < l → 0 ≤ z l - z k ∧ z l - z k ≤ 1) :
    0 ≤ gg ε z ∧ gg ε z ≤ ε * (N : ℝ) ^ 2 := by
  have hk : ∀ k l : Fin N, 0 ≤ (if k < l then chi ε (z l - z k) else 0) ∧
      (if k < l then chi ε (z l - z k) else 0) ≤ ε * (if k < l then (1 : ℝ) else 0) := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, if_true, mul_one]
      exact ⟨chi_nonneg (h k l hkl).1 (h k l hkl).2, chi_le hε (h k l hkl).1 (h k l hkl).2⟩
    · simp [hkl]
  refine ⟨Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => (hk k l).1, ?_⟩
  calc gg ε z ≤ ∑ k : Fin N, ∑ l : Fin N, ε * (if k < l then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => (hk k l).2
    _ = ε * ∑ k : Fin N, ∑ l : Fin N, (if k < l then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    _ ≤ ε * (N : ℝ) ^ 2 := by
        have := sum_pairs_count N
        have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have hS : 0 ≤ ∑ k : Fin N, ∑ l : Fin N, (if k < l then (1 : ℝ) else 0) :=
          Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by split_ifs <;> norm_num
        exact mul_le_mul_of_nonneg_left (by nlinarith) hε.le

/-- **Theorem (1), the cutoff functional and its calculus** (`0 < ε ≤ 1/8`, all `N`, all `z ∈ ℝ^N`):
`g_ε` is smooth, `∇ g_ε = v_ε`, `D² g_ε` is given by `hessForm`, the Laplacian (trace over the standard
basis) is `2 ∑_{k<l} χ_ε''(z_l - z_k)`; `|v_ε| ≤ N²`; `v_ε = 0` unless some pair has `min(d,1-d) < ε/2`;
`|χ_ε''(d)| ≤ (Cz/ε) 1_{min(d,1-d) < ε/2}` (and hence `|Δ g_ε| ≤ N² Cz/ε`). -/
theorem cepe6d_cutoff_calculus (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) (N : ℕ) :
    ContDiff ℝ ∞ (gg (N := N) ε) ∧ ContDiff ℝ ∞ (vv (N := N) ε) ∧
    (∀ z : Ch6D N, HasGradientAt (gg ε) (vv ε z) z) ∧
    (∀ z u w : Ch6D N, fderiv ℝ (fderiv ℝ (gg ε)) z u w = hessForm ε z u w) ∧
    (∀ z : Ch6D N, ∑ i : Fin N, fderiv ℝ (fderiv ℝ (gg ε)) z (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) =
        2 * ∑ k : Fin N, ∑ l : Fin N, if k < l then chi2 ε (z l - z k) else 0) ∧
    (∀ z : Ch6D N, ‖vv ε z‖ ≤ (N : ℝ) ^ 2) ∧
    (∀ z : Ch6D N, ‖vv ε z‖ ≤ if (∃ k l : Fin N, k < l ∧
      min (z l - z k) (1 - (z l - z k)) < ε / 2) then (N : ℝ) ^ 2 else 0) ∧
    (∀ d : ℝ, |chi2 ε d| ≤ if min d (1 - d) < ε / 2 then Cz / ε else 0) ∧
    (∀ z : Ch6D N, |2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then chi2 ε (z l - z k) else 0)| ≤
      (N : ℝ) ^ 2 * (Cz / ε)) ∧
    (∀ z : Ch6D N, (∀ k l : Fin N, k < l → 0 ≤ z l - z k ∧ z l - z k ≤ 1) →
      0 ≤ gg ε z ∧ gg ε z ≤ ε * (N : ℝ) ^ 2) :=
  ⟨gg_contDiff ε, vv_contDiff ε, hasGradientAt_gg ε, fderiv_fderiv_gg_apply ε, laplacian_gg ε,
    norm_vv_le ε, norm_vv_le_indicator ε hε, fun d => abs_chi2_le_indicator d hε hε1,
    abs_laplacian_le_sq ε hε hε1, gg_bounds ε hε⟩

end HRS.MC.CepE6D
