import HRS.MS.MovSchAux12

/-!
# S64 (S6.9), part 8: `s64_H_hasDeriv`

Namespace `HRS.MS.MovSch`, prefix `s64_`.  For a non-collision configuration `Z`: `σ ↦ H_N(ℓ_{ik}(Z,σ))` has derivative
`s64_drift d s q N i k Z` at `0`, where `H_N = HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

lemma s64_H_symm (g V : Euc d → ℝ) (hg : ∀ x, g (-x) = g x) (W : EucConfig d N) :
    HRS.Whole.canonicalHamiltonian g V W = ∑ j, V (W j) +
      (1 / (2 * (N : ℝ))) * ∑ a, ∑ b ∈ Finset.univ.erase a, g (W a - W b) := by
  unfold HRS.Whole.canonicalHamiltonian
  rw [HRS.MS.Canon.cn_sum_erase_eq g hg W]
  congr 1
  rw [one_div, one_div, mul_inv]
  ring

lemma s64_inner_single (x : Euc d) (k : Fin d) : inner ℝ x (EuclideanSpace.single k (1 : ℝ)) = x k := by
  rw [real_inner_comm]
  have := EuclideanSpace.inner_single_left (𝕜 := ℝ) k (1 : ℝ) x
  simpa using this

lemma s64_V_hasDeriv (q : ℝ) (Z : EucConfig d N) (i : Fin N) (k : Fin d) :
    HasDerivAt (fun σ : ℝ => ∑ j, confinement q (s64_ell Z i k σ j)) (q * Z i k) 0 := by
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      HasDerivAt (fun σ : ℝ => confinement q (s64_ell Z i k σ j))
        (q * inner ℝ (Z j) (if j = i then EuclideanSpace.single k (1 : ℝ) else 0)) 0 := by
    intro j _
    set c : Euc d := if j = i then EuclideanSpace.single k (1 : ℝ) else 0 with hc
    have hfun : (fun σ : ℝ => confinement q (s64_ell Z i k σ j)) =
        fun σ : ℝ => q * ‖Z j + σ • c‖ ^ 2 / 2 := by
      funext σ
      rw [s64_ell_apply]
      rfl
    rw [hfun]
    have hline : HasDerivAt (fun σ : ℝ => Z j + σ • c) c 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add (Z j)
      simpa using this
    have h2 := hline.norm_sq
    have h3 := (h2.const_mul q).div_const 2
    refine h3.congr_deriv ?_
    simp only [zero_smul, add_zero]
    ring
  have hs := HasDerivAt.fun_sum hj
  refine hs.congr_deriv ?_
  have : ∀ j : Fin N, q * inner ℝ (Z j) (if j = i then EuclideanSpace.single k (1 : ℝ) else 0) =
      if j = i then q * Z i k else 0 := by
    intro j
    by_cases h : j = i
    · subst h; rw [if_pos rfl, if_pos rfl, s64_inner_single]
    · simp [h]
  simp_rw [this]
  simp

theorem s64_H_hasDeriv (s q : ℝ) {Z : EucConfig d N} (hZ : s64_NC Z) (i : Fin N) (k : Fin d) :
    HasDerivAt (fun σ : ℝ => HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) (s64_ell Z i k σ))
      (s64_drift d s q N i k Z) 0 := by
  have hg : ∀ x : Euc d, rieszKernel d s (-x) = rieszKernel d s x := by
    intro x; unfold rieszKernel; simp [norm_neg]
  have hfun : (fun σ : ℝ => HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) (s64_ell Z i k σ)) =
      fun σ : ℝ => ∑ j, confinement q (s64_ell Z i k σ j) +
        (1 / (2 * (N : ℝ))) * ∑ a, ∑ b ∈ Finset.univ.erase a,
          rieszKernel d s (s64_ell Z i k σ a - s64_ell Z i k σ b) := by
    funext σ
    exact s64_H_symm _ _ hg _
  rw [hfun]
  have hpair : HasDerivAt (fun σ : ℝ => ∑ a, ∑ b ∈ Finset.univ.erase a,
      rieszKernel d s (s64_ell Z i k σ a - s64_ell Z i k σ b))
      (∑ a, ∑ b ∈ Finset.univ.erase a, ((if a = i then rieszKernelGrad d s (Z a - Z b) k else 0) -
        (if b = i then rieszKernelGrad d s (Z a - Z b) k else 0))) 0 := by
    refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b hb => ?_
    exact s64_pair_hasDeriv s (hZ a b (Finset.ne_of_mem_erase hb).symm) i k
  have htot := (s64_V_hasDeriv q Z i k).add (hpair.const_mul (1 / (2 * (N : ℝ))))
  refine htot.congr_deriv ?_
  -- evaluate the pair sum
  set T : Fin N → Fin N → ℝ := fun a b => rieszKernelGrad d s (Z a - Z b) k with hT
  have hS : ∑ a, ∑ b ∈ Finset.univ.erase a, ((if a = i then T a b else 0) - (if b = i then T a b else 0)) =
      2 * ∑ j ∈ Finset.univ.erase i, T i j := by
    have h1 : ∀ a : Fin N, ∑ b ∈ Finset.univ.erase a, ((if a = i then T a b else 0) - (if b = i then T a b else 0)) =
        ∑ b, ((if a = i then T a b else 0) - (if b = i then T a b else 0)) := by
      intro a
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ a)]
      simp
    simp_rw [h1, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h5 : ∑ a ∈ Finset.univ.erase i, T a i = - ∑ a ∈ Finset.univ.erase i, T i a := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hne : Z i - Z a ≠ 0 := sub_ne_zero.2 (hZ i a (Finset.ne_of_mem_erase ha).symm)
      simp only [hT]
      have := s64_G_odd s k hne
      rw [neg_sub] at this
      exact this
    have hA : ∑ b, T i b = T i i + ∑ b ∈ Finset.univ.erase i, T i b :=
      (Finset.add_sum_erase _ (fun b => T i b) (Finset.mem_univ i)).symm
    have hB : ∑ a, T a i = T i i + ∑ a ∈ Finset.univ.erase i, T a i :=
      (Finset.add_sum_erase _ (fun a => T a i) (Finset.mem_univ i)).symm
    have h4 : ∑ x : Fin N, ∑ x_1 : Fin N, (if x = i then T x x_1 else 0) = ∑ b, T i b := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    rw [h4, hA, hB, h5]
    ring
  rw [hS]
  unfold s64_drift
  have hN : (1 / (2 * (N : ℝ))) * (2 * ∑ j ∈ Finset.univ.erase i, T i j) =
      (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, T i j := by
    rw [one_div, one_div, mul_inv]; ring
  rw [hN]

end HRS.MS.MovSch

end
