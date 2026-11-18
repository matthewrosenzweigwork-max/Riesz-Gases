import HRS.MS.SpecAux12

/-!
# S8P: generalized eigenbasis `G B e = μ e` (generic, for S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_generalized_eigenbasis`: `G` compact, symmetric, positive, injective and
`B` symmetric with `c‖x‖² ≤ ⟨x,Bx⟩` (`BData`) on an infinite-dimensional real Hilbert space.  Then there are `e : ℕ → H`, `μ_n > 0`
antitone, `μ_n → 0`, with `G (B e_n) = μ_n e_n`, `⟨e_n, B e_m⟩ = δ_{nm}` and `{e_n}` complete in the `B`-sense
(`⟨f, B e_n⟩ = 0 ∀ n ⇒ f = 0`).  In S8.7: `G = L⁻¹`, `B = A⁻¹`, `ω_n = 1/μ_n`.
-/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem s8p_generalized_eigenbasis (D : BData H) (G : H →L[ℝ] H) (hG : IsCompactOperator G)
    (hGs : ∀ x y, ⟪G x, y⟫ = ⟪x, G y⟫) (hGp : ∀ x, 0 ≤ ⟪x, G x⟫) (hGi : Function.Injective G)
    (hinf : ¬ FiniteDimensional ℝ H) :
    ∃ (e : ℕ → H) (μ : ℕ → ℝ), (∀ n, 0 < μ n) ∧ Antitone μ ∧ Tendsto μ atTop (𝓝 0) ∧
      (∀ n, G (D.B (e n)) = μ n • e n) ∧
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
  have key1 : ∀ x y : H, ⟪G (D.B x), D.B y⟫ = ⟪x, D.B (G (D.B y))⟫ := by
    intro x y; rw [hGs, D.symm]
  have key2 : ∀ x : H, ⟪x, D.B (G (D.B x))⟫ = ⟪D.B x, G (D.B x)⟫ := fun x => (D.symm _ _).symm
  let T : BSp D →L[ℝ] BSp D := G.comp D.B
  have hTc : IsCompactOperator T := hG.comp_clm D.B
  have hTs : (T : BSp D →ₗ[ℝ] BSp D).IsSymmetric := fun x y =>
    key1 (show H from x) (show H from y)
  have hTp : ∀ x : BSp D, 0 ≤ ⟪x, T x⟫ := by
    intro x
    have := hGp (D.B (show H from x))
    rw [← key2] at this
    exact this
  have hTi : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : G (D.B (show H from x)) = 0 := hx
    have h2 : D.B (show H from x) = 0 := hGi (by rw [h1, map_zero])
    have : ⟪(show H from x), D.B (show H from x)⟫ = 0 := by rw [h2]; exact inner_zero_right _
    exact hBinj _ this
  have hinf' : ¬ FiniteDimensional ℝ (BSp D) := fun h => hinf (show FiniteDimensional ℝ H from h)
  obtain ⟨b, lam, hlam0, hlam, hanti, hlim⟩ := s8p_eigen_sequence T hTc hTs hTp hTi hinf'
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
