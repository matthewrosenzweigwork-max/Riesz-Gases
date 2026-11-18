import HRS.Equilibrium.Parametrix.PX3bAux

/-!
# S8.2 NormalForm packet P05, part 1: Laplacian of `B(z,z) g(|z|²)`

For a symmetric bilinear form `B` on `ℝ^d`: `Δ[B(x,x) g(|x|²)] = B(x,x)(8g' + 4|x|² g'' + 2d g') + 2 tr B · g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.S82N

open HRS

variable {d : ℕ}

/-- The quadratic form `x ↦ B x x` has derivative `2 B x` when `B` is symmetric. -/
lemma s82n_hasFDerivAt_quad (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (y : Euc d) :
    HasFDerivAt (fun x : Euc d => B x x) ((2 : ℝ) • B y) y := by
  have h := B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
  refine h.congr_fderiv ?_
  ext v
  simp [hB v y]
  ring

lemma s82n_laplacian_quad_radial (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (w : Euc d) (g g' g'' : ℝ → ℝ)
    (h1 : ∀ᶠ t in 𝓝 (‖w‖ ^ 2), HasDerivAt g (g' t) t)
    (h2 : HasDerivAt g' (g'' (‖w‖ ^ 2)) (‖w‖ ^ 2)) :
    Laplacian.laplacian (fun x : Euc d => B x x * g (‖x‖ ^ 2)) w =
      B w w * (8 * g' (‖w‖ ^ 2) + 4 * ‖w‖ ^ 2 * g'' (‖w‖ ^ 2) + 2 * d * g' (‖w‖ ^ 2)) +
        2 * (∑ i, B (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i)) *
          g (‖w‖ ^ 2) := by
  set t : ℝ := ‖w‖ ^ 2 with ht
  set f : Euc d → ℝ := fun x => B x x * g (‖x‖ ^ 2) with hf
  have hn : ∀ y : Euc d, HasFDerivAt (fun x : Euc d => ‖x‖ ^ 2)
      ((2 : ℕ) • innerSL ℝ y) y := fun y => (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hcont : Continuous fun x : Euc d => ‖x‖ ^ 2 := by fun_prop
  have h1' : ∀ᶠ x in 𝓝 w, HasDerivAt g (g' (‖x‖ ^ 2)) (‖x‖ ^ 2) :=
    hcont.continuousAt.eventually h1
  have hfd : ∀ᶠ x in 𝓝 w, fderiv ℝ f x =
      (B x x) • (g' (‖x‖ ^ 2) • ((2 : ℕ) • innerSL ℝ x)) + g (‖x‖ ^ 2) • ((2 : ℝ) • B x) := by
    filter_upwards [h1'] with x hx
    have hg := hx.comp_hasFDerivAt x (hn x)
    exact ((s82n_hasFDerivAt_quad B hB x).mul hg).fderiv
  set φ : Euc d → Euc d →L[ℝ] ℝ := fun x =>
    (B x x) • (g' (‖x‖ ^ 2) • ((2 : ℕ) • innerSL ℝ x)) + g (‖x‖ ^ 2) • ((2 : ℝ) • B x) with hφ
  have hfd' : fderiv ℝ f =ᶠ[𝓝 w] φ := hfd
  have ha : HasFDerivAt (fun x : Euc d => g' (‖x‖ ^ 2))
      (g'' (‖w‖ ^ 2) • ((2 : ℕ) • innerSL ℝ w)) w :=
    h2.comp_hasFDerivAt w (hn w)
  have hL : HasFDerivAt (fun x : Euc d => (2 : ℕ) • innerSL ℝ x)
      ((2 : ℕ) • (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) w := by
    have h3 := (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).hasFDerivAt (x := w)
    exact h3.const_smul (2 : ℕ)
  have hg0 : HasFDerivAt (fun x : Euc d => g (‖x‖ ^ 2)) (g' (‖w‖ ^ 2) • ((2 : ℕ) • innerSL ℝ w)) w :=
    h1.self_of_nhds.comp_hasFDerivAt w (hn w)
  have hBd : HasFDerivAt (fun x : Euc d => (2 : ℝ) • B x) ((2 : ℝ) • B) w :=
    (B.hasFDerivAt (x := w)).const_smul (2 : ℝ)
  have hφd : HasFDerivAt φ _ w :=
    ((s82n_hasFDerivAt_quad B hB w).smul (ha.smul hL)).add (hg0.smul hBd)
  have hsec : ∀ v : Euc d, iteratedFDeriv ℝ 2 f w ![v, v] =
      8 * g' t * inner ℝ w v * B w v + 4 * g'' t * B w w * (inner ℝ w v) ^ 2 +
        2 * g' t * B w w * ‖v‖ ^ 2 + 2 * g t * B v v := by
    intro v
    rw [iteratedFDeriv_two_apply, hfd'.fderiv_eq, hφd.fderiv]
    have hv : (innerSL ℝ) v v = ‖v‖ ^ 2 := by simp [innerSL_apply_apply]
    simp [innerSL_apply_apply]
    rw [hv, ht]
    ring
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [hsec]
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  have hsum2 : ∑ i, inner ℝ w (b i) ^ 2 = ‖w‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, Real.norm_eq_abs, sq_abs]
  have hsum1 : ∑ i, inner ℝ w (b i) * B w (b i) = B w w := by
    have h := b.sum_repr' w
    have e : B w w = B w (∑ i, inner ℝ (b i) w • b i) := by rw [h]
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, real_inner_comm]
  have hnorm : ∀ i, ‖b i‖ = 1 := fun i => b.norm_eq_one i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hnorm]
  rw [show ∑ i, 8 * g' t * inner ℝ w (b i) * B w (b i) =
      8 * g' t * ∑ i, inner ℝ w (b i) * B w (b i) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hsum1]
  rw [hsum2]
  simp [ht]
  ring

end HRS.MS.S82N
