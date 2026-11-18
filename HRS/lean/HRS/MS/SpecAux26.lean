import HRS.MS.SpecAux13
import HRS.MS.SpecAux25

/-!
# S8P: eigenbasis of a `B`-symmetric compact semigroup (generic, for S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_semigroup_eigenbasis`: a semigroup `T(t)` on an infinite-dimensional
Hilbert space `H` that is symmetric for the equivalent inner product `⟨x, B y⟩` (`BData`), strongly continuous on `[0,∞)`,
with `T(1)` compact, has a `B`-orthonormal, `B`-complete sequence of eigenvectors of `T(1)` with eigenvalues
`μ_n = e^{-ω_n} ∈ (0,1]`-type (positive, antitone, `→ 0`).
-/

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem s8p_semigroup_eigenbasis (D : BData H) (T : ℝ → H →L[ℝ] H)
    (hsymm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, D.B y⟫ = ⟪x, D.B (T t y)⟫)
    (hzero : T 0 = 1) (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t)
    (hcont : ∀ x, ContinuousOn (fun t => T t x) (Ici 0))
    (hcompact : IsCompactOperator (T 1)) (hinf : ¬ FiniteDimensional ℝ H) :
    ∃ (e : ℕ → H) (μ : ℕ → ℝ), (∀ n, 0 < μ n) ∧ Antitone μ ∧ Tendsto μ atTop (𝓝 0) ∧
      (∀ n, T 1 (e n) = μ n • e n) ∧
      (∀ n m, ⟪e n, D.B (e m)⟫ = if n = m then 1 else 0) ∧
      (∀ f, (∀ n, ⟪f, D.B (e n)⟫ = 0) → f = 0) := by
  classical
  have hBinj : ∀ x : H, ⟪x, D.B x⟫ = 0 → x = 0 := by
    intro x hx
    have h1 := D.low x
    rw [hx] at h1
    have : ‖x‖ ^ 2 ≤ 0 := by
      by_contra hne
      push Not at hne
      nlinarith [D.c_pos]
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg x])
  let T' : ℝ → BSp D →L[ℝ] BSp D := T
  have hTs : (T' 1 : BSp D →ₗ[ℝ] BSp D).IsSymmetric := fun x y =>
    hsymm 1 zero_le_one (show H from x) (show H from y)
  have hhalf : T 1 = T (1 / 2) * T (1 / 2) := by
    have := hadd (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    rwa [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at this
  have hTp : ∀ x : BSp D, 0 ≤ ⟪x, T' 1 x⟫ := by
    intro x
    show 0 ≤ ⟪(show H from x), D.B (T 1 (show H from x))⟫
    rw [hhalf, ContinuousLinearMap.mul_apply, ← hsymm (1 / 2) (by norm_num)]
    have := D.low (T (1 / 2) (show H from x))
    exact le_trans (mul_nonneg D.c_pos.le (sq_nonneg _)) this
  have hTi : Function.Injective (T' 1) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    -- injectivity from the semigroup structure in the `B`-inner product
    have hker := s8p_semigroup_ker_trivial (H := BSp D) T'
      (fun t ht x y => hsymm t ht (show H from x) (show H from y)) hzero hadd hcont (x := x) hx
    exact hker
  have hinf' : ¬ FiniteDimensional ℝ (BSp D) := fun h => hinf (show FiniteDimensional ℝ H from h)
  obtain ⟨b, lam, hlam0, hlam, hanti, hlim⟩ :=
    s8p_eigen_sequence (T' 1) hcompact hTs hTp hTi hinf'
  refine ⟨fun n => (show H from b n), lam, hlam0, hanti, hlim, fun n => ?_, fun n m => ?_, fun f hf => ?_⟩
  · exact hlam n
  · have := (orthonormal_iff_ite.1 b.orthonormal) n m
    rw [bsp_inner] at this
    exact this
  · let f' : BSp D := f
    have hfz : ∀ n, ⟪f', b n⟫ = 0 := fun n => by rw [bsp_inner]; exact hf n
    have h := b.hasSum_inner_mul_inner f' f'
    have h0 : ∀ i, ⟪f', b i⟫ * ⟪b i, f'⟫ = 0 := fun i => by rw [hfz i]; simp
    have h' : HasSum (fun _ : ℕ => (0 : ℝ)) ⟪f', f'⟫ := by
      convert h using 1
      funext i; exact (h0 i).symm
    have h2 : ⟪f', f'⟫ = 0 := (hasSum_zero.unique h').symm
    rw [bsp_inner] at h2
    exact hBinj f h2

end HRS.MS.Spec
