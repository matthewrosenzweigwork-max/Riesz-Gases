import Mathlib

/-!
# iid bridge, packet iid5, part A: the positive square root of an operator `0 ≤ M ≤ 1`

Real Hilbert spaces carry no continuous functional calculus in Mathlib, so the square root is built by hand:
with `N = 1 - M`, `‖N‖ ≤ 1`, and `sqrt(1 - t) = 1 - ∑_{n ≥ 1} b_n t^n` where `b_n ≥ 0` solves the Cauchy
recursion `2 b_n = [n = 1] + ∑_{i+j = n} b_i b_j` and `∑ b_n ≤ 1`.
-/

open Finset
open scoped InnerProductSpace

noncomputable section

namespace HRS.MC.IID

/-- Coefficients of `1 - sqrt (1 - t)`. -/
def sqb : ℕ → ℝ
  | 0 => 0
  | (n + 1) => (1 / 2) * ((if n = 0 then 1 else 0) + ∑ i : Fin n, sqb (i.val + 1) * sqb (n - i.val))
decreasing_by all_goals omega

theorem sqb_succ (n : ℕ) :
    sqb (n + 1) = (1 / 2) * ((if n = 0 then 1 else 0) + ∑ i : Fin n, sqb (i.val + 1) * sqb (n - i.val)) := by
  rw [sqb]

theorem sqb_zero : sqb 0 = 0 := by rw [sqb]

theorem sqb_nonneg : ∀ n, 0 ≤ sqb n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [sqb_zero]
    | succ n =>
      rw [sqb_succ]
      refine mul_nonneg (by norm_num) (add_nonneg (by split_ifs <;> norm_num) (sum_nonneg fun i _ => ?_))
      exact mul_nonneg (ih _ (by omega)) (ih _ (by omega))

/-- The Cauchy-product identity of the coefficients. -/
theorem sqb_conv (m : ℕ) :
    ∑ p ∈ antidiagonal m, sqb p.1 * sqb p.2 = 2 * sqb m - if m = 1 then 1 else 0 := by
  cases m with
  | zero => simp [sqb_zero]
  | succ n =>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ', sum_range_succ]
    have h1 : ∑ i : Fin n, sqb (i.val + 1) * sqb (n - i.val) =
        ∑ k ∈ range n, sqb (k + 1) * sqb (n - k) :=
      Fin.sum_univ_eq_sum_range (fun k => sqb (k + 1) * sqb (n - k)) n
    have h2 : ∑ k ∈ range n, sqb (k + 1) * sqb (n + 1 - (k + 1)) =
        ∑ k ∈ range n, sqb (k + 1) * sqb (n - k) := by
      refine sum_congr rfl fun k _ => ?_
      rw [Nat.add_sub_add_right]
    have h3 := sqb_succ n
    simp only [sqb_zero, Nat.sub_self, mul_zero, zero_mul, add_zero, Nat.sub_zero]
    rw [h2, h3, h1]
    have : (n + 1 = 1) ↔ (n = 0) := by omega
    simp only [this]
    ring

theorem sqb_antisum_le (N : ℕ) :
    ∑ m ∈ range (N + 1), ∑ p ∈ antidiagonal m, sqb p.1 * sqb p.2 ≤ (∑ i ∈ range N, sqb i) ^ 2 := by
  rw [sum_sigma' (range (N + 1)) (fun m => antidiagonal m) (fun m p => sqb p.1 * sqb p.2)]
  have hinj : Set.InjOn (fun x : (_ : ℕ) × (ℕ × ℕ) => x.2)
      (((range (N + 1)).sigma fun m => antidiagonal m : Finset ((_ : ℕ) × (ℕ × ℕ))) : Set _) := by
    rintro ⟨m, p⟩ hx ⟨m', p'⟩ hy hxy
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, HasAntidiagonal.mem_antidiagonal, mem_range] at hx hy
    simp only at hxy
    subst hxy
    have : m = m' := by omega
    subst this
    rfl
  rw [← sum_image (f := fun q : ℕ × ℕ => sqb q.1 * sqb q.2) hinj]
  set I := (((range (N + 1)).sigma fun m => antidiagonal m : Finset ((_ : ℕ) × (ℕ × ℕ)))).image
    (fun x => x.2) with hI
  have hz : ∑ q ∈ I ∩ (range N ×ˢ range N), sqb q.1 * sqb q.2 = ∑ q ∈ I, sqb q.1 * sqb q.2 := by
    refine sum_subset inter_subset_left fun q hq hq' => ?_
    have hq0 := hq
    simp only [hI, mem_image, Finset.mem_sigma, mem_range, HasAntidiagonal.mem_antidiagonal] at hq
    obtain ⟨⟨m, p⟩, ⟨hm, hp⟩, rfl⟩ := hq
    dsimp only at hm hp ⊢
    by_cases h1 : p.1 = 0
    · simp [h1, sqb_zero]
    by_cases h2 : p.2 = 0
    · simp [h2, sqb_zero]
    exfalso
    refine hq' (mem_inter.2 ⟨hq0, ?_⟩)
    simp only [mem_product, mem_range]
    omega
  calc _ = ∑ q ∈ I ∩ (range N ×ˢ range N), sqb q.1 * sqb q.2 := hz.symm
    _ ≤ ∑ q ∈ range N ×ˢ range N, sqb q.1 * sqb q.2 :=
        sum_le_sum_of_subset_of_nonneg inter_subset_right fun q _ _ => mul_nonneg (sqb_nonneg _) (sqb_nonneg _)
    _ = _ := by rw [sq, sum_mul_sum, sum_product]

theorem sqb_partial_le (N : ℕ) : ∑ i ∈ range N, sqb i ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h0 : 0 ≤ ∑ i ∈ range N, sqb i := sum_nonneg fun i _ => sqb_nonneg i
    have h1 : 2 * ∑ i ∈ range (N + 1), sqb i =
        ∑ m ∈ range (N + 1), ∑ p ∈ antidiagonal m, sqb p.1 * sqb p.2 +
          ∑ m ∈ range (N + 1), (if m = 1 then (1 : ℝ) else 0) := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun m _ => ?_
      rw [sqb_conv]; ring
    have h2 : ∑ m ∈ range (N + 1), (if m = 1 then (1 : ℝ) else 0) ≤ 1 := by
      rw [sum_ite_eq']
      split_ifs <;> norm_num
    have h3 := sqb_antisum_le N
    nlinarith

theorem sqb_summable : Summable sqb :=
  summable_of_sum_range_le sqb_nonneg sqb_partial_le

theorem sqb_tsum_le : ∑' n, sqb n ≤ 1 :=
  sqb_summable.tsum_le_of_sum_range_le sqb_partial_le

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem norm_one_sub_le (M : E →L[ℝ] E) (hs : ∀ x y, ⟪M x, y⟫_ℝ = ⟪x, M y⟫_ℝ)
    (h0 : ∀ x, 0 ≤ ⟪M x, x⟫_ℝ) (h1 : ∀ x, ⟪M x, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    ‖(1 : E →L[ℝ] E) - M‖ ≤ 1 := by
  have hsym : ((1 : E →L[ℝ] E) - M).IsSymmetric := by
    intro x y
    simp only [ContinuousLinearMap.coe_coe, sub_apply, one_apply_eq_self,
      inner_sub_left, inner_sub_right, hs]
  have hn := ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (𝕜 := ℝ) (T := (1 : E →L[ℝ] E) - M) hsym
  rw [hn]
  refine ciSup_le fun x => ?_
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [sub_apply, one_apply_eq_self, inner_sub_left,
    RCLike.re_to_real]
  by_cases hx : ‖x‖ ^ 2 = 0
  · simp [hx]
  have hx' : 0 < ‖x‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hx)
  rw [abs_div, abs_of_pos hx', div_le_one hx', abs_le]
  have := h0 x
  have := h1 x
  rw [real_inner_self_eq_norm_sq]
  constructor <;> linarith

/-- **Square root of an operator `0 ≤ M ≤ 1` on a real Hilbert space.** -/
theorem exists_sqrt (M : E →L[ℝ] E) (hs : ∀ x y, ⟪M x, y⟫_ℝ = ⟪x, M y⟫_ℝ)
    (h0 : ∀ x, 0 ≤ ⟪M x, x⟫_ℝ) (h1 : ∀ x, ⟪M x, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    ∃ T : E →L[ℝ] E, (∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ) ∧ (∀ x, 0 ≤ ⟪T x, x⟫_ℝ) ∧
      ∀ x, T (T x) = M x := by
  set N : E →L[ℝ] E := 1 - M with hN
  have hNn : ‖N‖ ≤ 1 := norm_one_sub_le M hs h0 h1
  have hNs : ∀ x y, ⟪N x, y⟫_ℝ = ⟪x, N y⟫_ℝ := by
    intro x y
    simp only [hN, sub_apply, one_apply_eq_self, inner_sub_left, inner_sub_right, hs]
  have hpn : ∀ n, ‖N ^ n‖ ≤ 1 := fun n => by
    induction n with
    | zero => rw [pow_zero]; exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (N ^ n), norm_nonneg N])
  have hNp : ∀ n x y, ⟪(N ^ n) x, y⟫_ℝ = ⟪x, (N ^ n) y⟫_ℝ := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      have e1 : (N ^ (n + 1)) x = N ((N ^ n) x) := by rw [pow_succ']; rfl
      have e2 : (N ^ (n + 1)) y = (N ^ n) (N y) := by rw [pow_succ]; rfl
      rw [e1, e2, hNs, ih]
  set f : ℕ → E →L[ℝ] E := fun n => sqb n • N ^ n with hf
  have hfn : Summable fun n => ‖f n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) sqb_summable
    rw [hf, norm_smul, Real.norm_of_nonneg (sqb_nonneg n)]
    exact mul_le_of_le_one_right (sqb_nonneg n) (hpn n)
  have hfs : Summable f := hfn.of_norm
  set P : E →L[ℝ] E := ∑' n, f n with hP
  have hPP : P * P = (2 : ℝ) • P - N := by
    have h1 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hfn
    have h2 : ∀ n, ∑ kl ∈ antidiagonal n, f kl.1 * f kl.2 =
        ((2 : ℝ) * sqb n - if n = 1 then 1 else 0) • N ^ n := by
      intro n
      have : ∀ kl ∈ antidiagonal n, f kl.1 * f kl.2 = (sqb kl.1 * sqb kl.2) • N ^ n := by
        intro kl hkl
        rw [HasAntidiagonal.mem_antidiagonal] at hkl
        simp only [hf, smul_mul_smul_comm, ← pow_add, hkl]
      rw [sum_congr rfl this, ← sum_smul, sqb_conv]
    have h3 : HasSum (fun n => (if n = 1 then (1 : ℝ) else 0) • N ^ n) N := by
      have := hasSum_ite_eq (1 : ℕ) N
      convert this using 1
      funext n
      split_ifs with h
      · subst h; simp
      · simp
    have h4 := (hfs.hasSum.const_smul (2 : ℝ)).sub h3
    have h5 : (fun n => (2 : ℝ) • f n - (if n = 1 then (1 : ℝ) else 0) • N ^ n) =
        fun n => ((2 : ℝ) * sqb n - if n = 1 then 1 else 0) • N ^ n := by
      funext n
      rw [sub_smul, mul_smul]
    rw [h5] at h4
    rw [h1]
    simp_rw [h2]
    exact h4.tsum_eq
  have hPx : ∀ x, HasSum (fun n => sqb n • (N ^ n) x) (P x) := fun x => by
    have := hfs.hasSum.mapL (ContinuousLinearMap.apply ℝ E x)
    simpa [hf] using this
  have hPi : ∀ x y, HasSum (fun n => sqb n * ⟪y, (N ^ n) x⟫_ℝ) ⟪y, P x⟫_ℝ := fun x y => by
    have := (hPx x).mapL (innerSL ℝ y)
    simpa [inner_smul_right] using this
  have hPsym : ∀ x y, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ := by
    intro x y
    have h1 := hPi x y
    have h2 := hPi y x
    have : (fun n => sqb n * ⟪y, (N ^ n) x⟫_ℝ) = fun n => sqb n * ⟪x, (N ^ n) y⟫_ℝ := by
      funext n; rw [real_inner_comm, hNp]
    rw [this] at h1
    rw [real_inner_comm, h1.unique h2]
  refine ⟨1 - P, ?_, ?_, ?_⟩
  · intro x y
    simp only [sub_apply, one_apply_eq_self, inner_sub_left, inner_sub_right, hPsym x y]
  · intro x
    simp only [sub_apply, one_apply_eq_self, inner_sub_left, real_inner_self_eq_norm_sq]
    have h1 := hPi x x
    have h2 : HasSum (fun n => sqb n * ‖x‖ ^ 2) ((∑' n, sqb n) * ‖x‖ ^ 2) :=
      sqb_summable.hasSum.mul_right _
    have h3 : ⟪x, P x⟫_ℝ ≤ (∑' n, sqb n) * ‖x‖ ^ 2 := by
      refine hasSum_le (fun n => ?_) h1 h2
      refine mul_le_mul_of_nonneg_left ?_ (sqb_nonneg n)
      calc ⟪x, (N ^ n) x⟫_ℝ ≤ ‖x‖ * ‖(N ^ n) x‖ := real_inner_le_norm _ _
        _ ≤ ‖x‖ * (1 * ‖x‖) := by
          gcongr
          exact ((N ^ n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hpn n) (norm_nonneg _))
        _ = ‖x‖ ^ 2 := by ring
    rw [real_inner_comm] at h3
    nlinarith [sqb_tsum_le, sq_nonneg ‖x‖]
  · intro x
    have : (1 - P) * (1 - P) = M := by
      have : (1 - P) * (1 - P) = 1 - (2 : ℝ) • P + P * P := by
        rw [two_smul]; noncomm_ring
      rw [this, hPP, hN]; abel
    have h := congrArg (fun A : E →L[ℝ] E => A x) this
    simpa [mul_apply] using h

end Operator

section Factor

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Symmetric positive square-root matrix.**  For an orthonormal sequence `u` and a symmetric operator `R`
with `0 ≤ R ≤ 1`, the Gram matrix `⟪u i, R u j⟫` has a symmetric factor `S`, positive semidefinite on every
finite section, with `∑_k S_ik S_jk = ⟪u i, R u j⟫`. -/
theorem exists_symm_factor (u : ℕ → E) (hu : Orthonormal ℝ u) (R : E →L[ℝ] E)
    (hs : ∀ x y, ⟪R x, y⟫_ℝ = ⟪x, R y⟫_ℝ) (h0 : ∀ x, 0 ≤ ⟪R x, x⟫_ℝ)
    (h1 : ∀ x, ⟪R x, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    ∃ S : ℕ → ℕ → ℝ, (∀ i j, S i j = S j i) ∧
      (∀ i j, HasSum (fun k => S i k * S j k) ⟪u i, R (u j)⟫_ℝ) ∧
      ∀ (n : ℕ) (x : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, x i * x j * S i j := by
  classical
  have hV : OrthogonalFamily ℝ (fun _ : ℕ => ℝ)
      (fun i => LinearIsometry.toSpanSingleton ℝ E (hu.1 i)) := hu.orthogonalFamily
  let U : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] E := hV.linearIsometry.toContinuousLinearMap
  have hUs : ∀ i, U (lp.single 2 i (1 : ℝ)) = u i := fun i => by
    show hV.linearIsometry (lp.single 2 i (1 : ℝ)) = u i
    rw [hV.linearIsometry_apply_single]
    simp
  have hUn : ∀ x, ‖U x‖ = ‖x‖ := fun x => hV.linearIsometry.norm_map x
  let M : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
    (ContinuousLinearMap.adjoint U) ∘L R ∘L U
  have hM : ∀ x y, ⟪M x, y⟫_ℝ = ⟪R (U x), U y⟫_ℝ := fun x y => by
    show ⟪(ContinuousLinearMap.adjoint U) (R (U x)), y⟫_ℝ = _
    rw [ContinuousLinearMap.adjoint_inner_left]
  have hM' : ∀ x y, ⟪x, M y⟫_ℝ = ⟪U x, R (U y)⟫_ℝ := fun x y => by
    rw [real_inner_comm, hM]; exact real_inner_comm _ _
  obtain ⟨T, hTs, hT0, hTT⟩ := exists_sqrt M
    (fun x y => by rw [hM, hM']; exact hs _ _)
    (fun x => by rw [hM]; exact h0 _)
    (fun x => by rw [hM, ← hUn x]; exact h1 _)
  set eV : ℕ → lp (fun _ : ℕ => ℝ) 2 := fun j => lp.single 2 j (1 : ℝ) with heV
  set S : ℕ → ℕ → ℝ := fun i j => (T (eV j)) i with hS
  have hSi : ∀ i j, S i j = ⟪eV i, T (eV j)⟫_ℝ := fun i j => by
    simp [hS, heV, lp.inner_single_left]
  have hsymm : ∀ i j, S i j = S j i := fun i j => by
    rw [hSi, hSi, real_inner_comm, ← hTs, real_inner_comm]
  refine ⟨S, hsymm, fun i j => ?_, fun n x => ?_⟩
  · have h := lp.hasSum_inner (𝕜 := ℝ) (T (eV i)) (T (eV j))
    have hv : ⟪T (eV i), T (eV j)⟫_ℝ = ⟪u i, R (u j)⟫_ℝ := by
      rw [hTs, hTT, hM', hUs, hUs]
    rw [hv] at h
    convert h using 1
    funext k
    have e1 : (T (eV i)) k = S i k := (hsymm i k).symm
    have e2 : (T (eV j)) k = S j k := (hsymm j k).symm
    rw [e1, e2]
    simp [mul_comm]
  · set y : lp (fun _ : ℕ => ℝ) 2 := ∑ i, x i • eV i with hy
    have h := hT0 y
    have : ⟪T y, y⟫_ℝ = ∑ i, ∑ j, x i * x j * S i j := by
      have hTy : T y = ∑ j, x j • T (eV j) := by
        rw [hy, map_sum]
        exact sum_congr rfl fun j _ => map_smul T (x j) (eV j)
      rw [real_inner_comm, hTy]
      simp_rw [inner_sum, real_inner_smul_right]
      rw [hy]
      simp_rw [sum_inner, real_inner_smul_left, ← hSi]
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [← this]; exact h

end Factor

end HRS.MC.IID
