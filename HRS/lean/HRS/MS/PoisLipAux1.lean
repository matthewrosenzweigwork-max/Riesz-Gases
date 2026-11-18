import Mathlib
import HRS.MS.PoisMaxAux2

open Filter Topology Set
open scoped RealInnerProductSpace

/-!
# POIS-LIPDEC (part 1): the maximum-point step with a quadratic penalty

`PoissonSpike.poisson_maxpoint` is stated for one function `u` and no penalty.  The penalised maximum
principle `pm_penalized_max` (PoisMaxAux1) is applied to `G = u(x) - u(y) - A e^{-c0 t} f(|x-y|)` on the
doubled space, and its failure hypothesis needs the first and second order conditions at a maximum of
`G - ε(1+|x|²+|y|²)e^{λ t}`.  That function is `a(x) - c(y) - A' f(|x-y|) - const` with
`a = u - ε'|·|²`, `c = u + ε'|·|²`, two DIFFERENT functions, so the spike cannot be applied verbatim.

This file re-proves the maximum-point step for two functions `a, c ∈ C²` (same proof as the spike, which
is reused for the one-variable lemmas `localMax_second`, `line_hasDerivAt(2)`, `norm_line`) and
specialises it to the penalised situation.

Main results.
* `ld_maxpoint`: `Φ(x,y) = a x - c y - A f |x-y|` has a local max at `(x,y)`, `x ≠ y`, `a, c ∈ C²`,
  `f ∈ C²(0,∞)`  ⟹  `Da(x) = Dc(y) = A f'(r)⟪e,·⟫` and
  `Δa(x) - Δc(y) ≤ 4 A f''(r)` (with `Laplacian.laplacian`, `r = |x-y|`, `e = (x-y)/r`).
* `ld_maxpoint_pen`: the same for `u(x) - u(y) - A f|x-y| - κ₁|x|² - κ₂|y|²` (any constant may be added
  to the objective): `Du(x) = A f'⟪e,·⟫ + 2κ₁⟪x,·⟫`, `Du(y) = A f'⟪e,·⟫ - 2κ₂⟪y,·⟫`,
  `Δu(x) - Δu(y) ≤ 4 A f'' + 2d(κ₁+κ₂)`.

Statement adjustments relative to the packet sketch: none in content; the sketch's `pm_poisson_maxpoint`
is generalised to two functions and a penalty because the penalty is unavoidable (PoisMax does not
provide it).  The case `d = 1` is covered uniformly (the orthonormal basis extension of `{e}` has no
`η ⊥ e` vectors).  Helper lemmas carry the prefix `ld_`.
-/

namespace HRS.MS.PoisLip

open HRS HRS.MS.PoissonSpike

variable {d : ℕ}

/-- the doubled-variable function for two functions -/
noncomputable def ldΦ (a c : Euc d → ℝ) (A : ℝ) (f : ℝ → ℝ) (p : Euc d × Euc d) : ℝ :=
  a p.1 - c p.2 - A * f ‖p.1 - p.2‖

section
variable {a c : Euc d → ℝ} {A : ℝ} {f : ℝ → ℝ} {x y : Euc d}

theorem ld_phi_line (ξ ζ : Euc d) (s : ℝ) :
    ldΦ a c A f (x + s • ξ, y + s • ζ) =
      a (x + s • ξ) - c (y + s • ζ) - A * f ‖(x - y) + s • (ξ - ζ)‖ := by
  have : (x + s • ξ) - (y + s • ζ) = (x - y) + s • (ξ - ζ) := by rw [smul_sub]; abel
  simp only [ldΦ, this]

theorem ld_isLocalMax_line (hmax : IsLocalMax (ldΦ a c A f) (x, y)) (ξ ζ : Euc d) :
    IsLocalMax (fun s : ℝ => ldΦ a c A f (x + s • ξ, y + s • ζ)) 0 := by
  have hg : Continuous fun s : ℝ => ((x + s • ξ, y + s • ζ) : Euc d × Euc d) := by fun_prop
  have h0 : IsLocalMax (ldΦ a c A f)
      ((fun s : ℝ => ((x + s • ξ, y + s • ζ) : Euc d × Euc d)) 0) := by
    simpa using hmax
  exact h0.comp_continuous (b := (0:ℝ)) hg.continuousAt

theorem ld_first_order (ha : ContDiff ℝ 2 a) (hc : ContDiff ℝ 2 c)
    (hf : ContDiffOn ℝ 2 f (Set.Ioi 0))
    (hmax : IsLocalMax (ldΦ a c A f) (x, y)) (hxy : x ≠ y) (ξ ζ : Euc d) :
    fderiv ℝ a x ξ - fderiv ℝ c y ζ
      - A * (deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) (ξ - ζ)) = 0 := by
  have hw : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hr : 0 < ‖x - y‖ := norm_pos_iff.2 hw
  have hfd : DifferentiableAt ℝ f ‖x - y‖ :=
    (hf.differentiableOn (by norm_num) _ hr).differentiableAt (Ioi_mem_nhds hr)
  have hN := norm_line (δ := ξ - ζ) hw
  have hfN : HasDerivAt (fun s : ℝ => f ‖(x - y) + s • (ξ - ζ)‖)
      (deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) (ξ - ζ)) 0 := by
    have hfd' : DifferentiableAt ℝ f ((fun s : ℝ => ‖(x - y) + s • (ξ - ζ)‖) 0) := by
      simpa using hfd
    have := hfd'.hasDerivAt.comp (0:ℝ) hN
    simp only [zero_smul, add_zero] at this
    exact this
  have h1 := (line_hasDerivAt ha x ξ 0).sub (line_hasDerivAt hc y ζ 0)
  have h2 := (h1.sub (hfN.const_mul A))
  have hmax' := ld_isLocalMax_line hmax ξ ζ
  simp only [ld_phi_line] at hmax'
  have := hmax'.hasDerivAt_eq_zero (f' := _) (show HasDerivAt (fun s : ℝ => a (x + s • ξ) - c (y + s • ζ)
    - A * f ‖(x - y) + s • (ξ - ζ)‖) _ 0 from h2)
  simpa using this

theorem ld_second_order_diag (ha : ContDiff ℝ 2 a) (hc : ContDiff ℝ 2 c)
    (hmax : IsLocalMax (ldΦ a c A f) (x, y)) (η : Euc d) :
    iteratedFDeriv ℝ 2 a x ![η, η] - iteratedFDeriv ℝ 2 c y ![η, η] ≤ 0 := by
  have hmax' := ld_isLocalMax_line hmax η η
  have e1 : ∀ s : ℝ, ldΦ a c A f (x + s • η, y + s • η) =
      a (x + s • η) - c (y + s • η) - A * f ‖x - y‖ := fun s => by simp [ld_phi_line]
  simp only [e1] at hmax'
  have hh : ∀ s : ℝ, HasDerivAt (fun s : ℝ => a (x + s • η) - c (y + s • η) - A * f ‖x - y‖)
      (fderiv ℝ a (x + s • η) η - fderiv ℝ c (y + s • η) η) s := fun s =>
    ((line_hasDerivAt ha x η s).sub (line_hasDerivAt hc y η s)).sub_const _
  have hG := (line_hasDerivAt2 ha x η 0).sub (line_hasDerivAt2 hc y η 0)
  have := (localMax_second (Filter.Eventually.of_forall hh) (show HasDerivAt
    (fun s : ℝ => fderiv ℝ a (x + s • η) η - fderiv ℝ c (y + s • η) η) _ 0 from hG) hmax').2
  simpa using this

theorem ld_second_order_radial (ha : ContDiff ℝ 2 a) (hc : ContDiff ℝ 2 c)
    (hf : ContDiffOn ℝ 2 f (Set.Ioi 0))
    (hmax : IsLocalMax (ldΦ a c A f) (x, y)) (hxy : x ≠ y) :
    iteratedFDeriv ℝ 2 a x ![‖x - y‖⁻¹ • (x - y), ‖x - y‖⁻¹ • (x - y)]
      - iteratedFDeriv ℝ 2 c y ![‖x - y‖⁻¹ • (x - y), ‖x - y‖⁻¹ • (x - y)]
      ≤ 4 * A * deriv (deriv f) ‖x - y‖ := by
  have hw : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hr : 0 < ‖x - y‖ := norm_pos_iff.2 hw
  generalize hrdef : ‖x - y‖ = r at hr
  generalize hedef : r⁻¹ • (x - y) = e
  have hxe : x - y = r • e := by
    rw [← hedef, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hnorm : ‖e‖ = 1 := by
    rw [← hedef, norm_smul, hrdef, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
      inv_mul_cancel₀ hr.ne']
  have hfd : ∀ t, 0 < t → DifferentiableAt ℝ f t := fun t ht =>
    (hf.differentiableOn (by norm_num) _ ht).differentiableAt (Ioi_mem_nhds ht)
  have hdd : DifferentiableAt ℝ (deriv f) r := by
    have h1 := (hf.contDiffAt (Ioi_mem_nhds hr)).fderiv_right (m := 1) (by norm_num)
    exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have hpos : ∀ᶠ s in 𝓝 (0:ℝ), 0 < r + 2 * s := by
    have : ContinuousAt (fun s : ℝ => r + 2 * s) 0 := by fun_prop
    exact this.eventually (lt_mem_nhds (by simpa using hr))
  have hmax' := ld_isLocalMax_line hmax e (-e)
  have hnm : ∀ s : ℝ, 0 < r + 2 * s → ‖(x - y) + s • (e - -e)‖ = r + 2 * s := fun s hs => by
    have : (x - y) + s • (e - -e) = (r + 2 * s) • e := by rw [hxe]; module
    rw [this, norm_smul, hnorm, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  simp only [ld_phi_line] at hmax'
  have hmax2 : IsLocalMax
      (fun s : ℝ => a (x + s • e) - c (y + s • (-e)) - A * f (r + 2 * s)) 0 := by
    refine hmax'.congr ?_
    filter_upwards [hpos] with s hs
    simp only [hnm s hs]
  have hfs : ∀ s : ℝ, 0 < r + 2 * s →
      HasDerivAt (fun s : ℝ => f (r + 2 * s)) (deriv f (r + 2 * s) * 2) s := fun s hs => by
    have := (hfd _ hs).hasDerivAt.comp s (((hasDerivAt_id s).const_mul 2).const_add r)
    simp only [id, mul_one] at this
    exact this
  have hh : ∀ᶠ s in 𝓝 (0:ℝ), HasDerivAt
      (fun s : ℝ => a (x + s • e) - c (y + s • (-e)) - A * f (r + 2 * s))
      (fderiv ℝ a (x + s • e) e - fderiv ℝ c (y + s • (-e)) (-e)
        - A * (deriv f (r + 2 * s) * 2)) s := by
    filter_upwards [hpos] with s hs
    exact ((line_hasDerivAt ha x e s).sub (line_hasDerivAt hc y (-e) s)).sub
      ((hfs s hs).const_mul A)
  have hG2 : HasDerivAt (fun s : ℝ => deriv f (r + 2 * s)) (deriv (deriv f) r * 2) 0 := by
    have h0 : HasDerivAt (deriv f) (deriv (deriv f) r) (r + 2 * 0) := by
      rw [mul_zero, add_zero]; exact hdd.hasDerivAt
    have := h0.comp (0:ℝ) (((hasDerivAt_id (0:ℝ)).const_mul 2).const_add r)
    simp only [id, mul_one] at this
    exact this
  have hG := (((line_hasDerivAt2 ha x e 0).sub (line_hasDerivAt2 hc y (-e) 0)).sub
      ((hG2.mul_const 2).const_mul A))
  have key := (localMax_second hh (show HasDerivAt (fun s : ℝ => fderiv ℝ a (x + s • e) e
      - fderiv ℝ c (y + s • (-e)) (-e) - A * (deriv f (r + 2 * s) * 2)) _ 0 from hG) hmax2).2
  have hneg : iteratedFDeriv ℝ 2 c y ![-e, -e] = iteratedFDeriv ℝ 2 c y ![e, e] := by
    simp only [iteratedFDeriv_two_apply]; simp
  simp only [zero_smul, add_zero, hneg] at key
  linarith

end

/-- **Maximum-point step for two functions.** -/
theorem ld_maxpoint (hd : 1 ≤ d) (a c : Euc d → ℝ) (ha : ContDiff ℝ 2 a) (hc : ContDiff ℝ 2 c)
    (A : ℝ) (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Ioi 0)) (x y : Euc d)
    (hmax : IsLocalMax (fun p : Euc d × Euc d => a p.1 - c p.2 - A * f ‖p.1 - p.2‖) (x, y))
    (hxy : x ≠ y) :
    (∀ v : Euc d, fderiv ℝ a x v = A * deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) v ∧
      fderiv ℝ c y v = A * deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) v) ∧
    Laplacian.laplacian a x - Laplacian.laplacian c y ≤ 4 * A * deriv (deriv f) ‖x - y‖ := by
  have hmax : IsLocalMax (ldΦ a c A f) (x, y) := hmax
  refine ⟨fun v => ⟨?_, ?_⟩, ?_⟩
  · have := ld_first_order ha hc hf hmax hxy v 0
    simp at this
    linarith
  · have := ld_first_order ha hc hf hmax hxy 0 v
    simp [inner_neg_right] at this
    linarith
  · set e : Euc d := ‖x - y‖⁻¹ • (x - y) with he
    have hnorm : ‖e‖ = 1 := by
      rw [he, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 (sub_ne_zero.2 hxy))]
    let i0 : Fin d := ⟨0, hd⟩
    have hon : Orthonormal ℝ (({i0} : Set (Fin d)).domRestrict (fun _ => e)) := by
      refine ⟨fun i => hnorm, fun i j hij => ?_⟩
      exact absurd (Subtype.ext (by rw [Set.mem_singleton_iff.1 i.2, Set.mem_singleton_iff.1 j.2])) hij
    obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (by simp) hon
    have hb0 : b i0 = e := hb i0 rfl
    rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis a b) x,
      congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis c b) y,
      ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ i : Fin d, (if i = i0 then 4 * A * deriv (deriv f) ‖x - y‖ else 0) := by
          refine Finset.sum_le_sum fun i _ => ?_
          by_cases h : i = i0
          · subst h
            rw [ite_eq_left_iff.2 (fun h => absurd rfl h), hb0]
            exact ld_second_order_radial ha hc hf hmax hxy
          · rw [ite_eq_right_iff.2 (fun h' => absurd h' h)]
            exact ld_second_order_diag ha hc hmax (b i)
      _ = _ := by simp

/-! ### The quadratic penalty -/

theorem ld_fderiv_normsq (x v : Euc d) :
    fderiv ℝ (fun z : Euc d => ‖z‖ ^ 2) x v = 2 * inner ℝ x v := by
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp [two_mul]

theorem ld_D2_normsq (x v : Euc d) :
    iteratedFDeriv ℝ 2 (fun z : Euc d => ‖z‖ ^ 2) x ![v, v] = 2 * ‖v‖ ^ 2 := by
  have hc : ContDiff ℝ 2 (fun z : Euc d => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have h1 := line_hasDerivAt2 hc x v 0
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ (fun z : Euc d => ‖z‖ ^ 2) (x + t • v) v)
      (2 * ‖v‖ ^ 2) 0 := by
    have e : (fun t : ℝ => fderiv ℝ (fun z : Euc d => ‖z‖ ^ 2) (x + t • v) v) =
        fun t => 2 * inner ℝ x v + 2 * ‖v‖ ^ 2 * t := by
      funext t
      rw [ld_fderiv_normsq, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp; ring
    rw [e]
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul (2 * ‖v‖ ^ 2)).const_add (2 * inner ℝ x v)
  have := h1.unique h2
  simpa using this

theorem ld_D2_pen {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (κ : ℝ) (x v : Euc d) :
    iteratedFDeriv ℝ 2 (fun z => u z - κ * ‖z‖ ^ 2) x ![v, v] =
      iteratedFDeriv ℝ 2 u x ![v, v] - 2 * κ * ‖v‖ ^ 2 := by
  have hc : ContDiff ℝ 2 (fun z : Euc d => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have e1 : (fun z => u z - κ * ‖z‖ ^ 2) = u - (fun z => κ • (‖z‖ ^ 2)) := by
    funext z; simp [smul_eq_mul]
  rw [e1, iteratedFDeriv_sub_apply (hu.contDiffAt) ((hc.const_smul κ).contDiffAt),
    iteratedFDeriv_const_smul_apply' hc.contDiffAt]
  simp [ld_D2_normsq]
  ring

theorem ld_fderiv_pen {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (κ : ℝ) (x v : Euc d) :
    fderiv ℝ (fun z => u z - κ * ‖z‖ ^ 2) x v = fderiv ℝ u x v - 2 * κ * inner ℝ x v := by
  have h := ((hu.differentiable (by norm_num) x).hasFDerivAt.sub
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul κ))
  have h' : HasFDerivAt (fun z : Euc d => u z - κ * ‖z‖ ^ 2) _ x := h
  rw [h'.fderiv]
  simp [two_mul]
  ring

/-- **Maximum-point step with a quadratic penalty.** -/
theorem ld_maxpoint_pen (hd : 1 ≤ d) (u : Euc d → ℝ) (hu : ContDiff ℝ 2 u) (A κ₁ κ₂ : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioi 0)) (x y : Euc d) (k : ℝ)
    (hmax : ∀ x' y' : Euc d,
      u x' - u y' - A * f ‖x' - y'‖ - κ₁ * ‖x'‖ ^ 2 - κ₂ * ‖y'‖ ^ 2 + k ≤
      u x - u y - A * f ‖x - y‖ - κ₁ * ‖x‖ ^ 2 - κ₂ * ‖y‖ ^ 2 + k)
    (hxy : x ≠ y) :
    (∀ v : Euc d, fderiv ℝ u x v = A * deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) v
        + 2 * κ₁ * inner ℝ x v ∧
      fderiv ℝ u y v = A * deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) v
        - 2 * κ₂ * inner ℝ y v) ∧
    Laplacian.laplacian u x - Laplacian.laplacian u y ≤
      4 * A * deriv (deriv f) ‖x - y‖ + 2 * d * (κ₁ + κ₂) := by
  set a : Euc d → ℝ := fun z => u z - κ₁ * ‖z‖ ^ 2 with ha
  set c : Euc d → ℝ := fun z => u z + κ₂ * ‖z‖ ^ 2 with hcdef
  have hc2 : ContDiff ℝ 2 (fun z : Euc d => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have haC : ContDiff ℝ 2 a := hu.sub (contDiff_const.mul hc2)
  have hcC : ContDiff ℝ 2 c := hu.add (contDiff_const.mul hc2)
  have hc' : c = fun z => u z - (-κ₂) * ‖z‖ ^ 2 := by funext z; simp [hcdef]
  have hlm : IsLocalMax (fun p : Euc d × Euc d => a p.1 - c p.2 - A * f ‖p.1 - p.2‖) (x, y) := by
    refine IsMaxOn.isLocalMax (s := Set.univ) (fun p _ => ?_) Filter.univ_mem
    have := hmax p.1 p.2
    simp only [Set.mem_ofPred_eq, ha, hcdef]
    linarith
  obtain ⟨h1, h2⟩ := ld_maxpoint hd a c haC hcC A f hf x y hlm hxy
  refine ⟨fun v => ⟨?_, ?_⟩, ?_⟩
  · have := (h1 v).1
    rw [ha, ld_fderiv_pen hu] at this
    linarith
  · have := (h1 v).2
    have e : (fun z : Euc d => u z + κ₂ * ‖z‖ ^ 2) = fun z => u z - (-κ₂) * ‖z‖ ^ 2 := by
      funext z; ring
    rw [hcdef, e, ld_fderiv_pen hu] at this
    linarith
  · have hsum : ∀ (z : Euc d) (κ : ℝ) (b : OrthonormalBasis (Fin d) ℝ (Euc d)),
        ∑ i, iteratedFDeriv ℝ 2 (fun w => u w - κ * ‖w‖ ^ 2) z ![b i, b i] =
          Laplacian.laplacian u z - 2 * κ * d := by
      intro z κ b
      simp only [ld_D2_pen hu, b.norm_eq_one, Finset.sum_sub_distrib]
      rw [← congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b) z]
      simp
      ring
    have hL : ∀ (z : Euc d) (κ : ℝ), Laplacian.laplacian (fun w => u w - κ * ‖w‖ ^ 2) z =
        Laplacian.laplacian u z - 2 * κ * d := by
      intro z κ
      rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
        (EuclideanSpace.basisFun (Fin d) ℝ)) z, hsum z κ (EuclideanSpace.basisFun (Fin d) ℝ)]
    have e1 := hL x κ₁
    have e2 : Laplacian.laplacian c y = Laplacian.laplacian u y + 2 * κ₂ * d := by
      rw [hc', hL y (-κ₂)]; ring
    simp only [ha] at h2
    rw [e1, e2] at h2
    linarith

end HRS.MS.PoisLip
