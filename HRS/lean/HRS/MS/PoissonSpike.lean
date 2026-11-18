import Mathlib
import HRS.Torus.Basic
open Filter Topology
open scoped RealInnerProductSpace

/-!
# Spike: maximum-point step of the doubling-of-variables Lipschitz decay (D2 / D0(a))

If `Φ(x,y) = u x - u y - A f ‖x-y‖` has a local maximum at `(x,y)` with `x ≠ y`, then
`Du(x) = Du(y) = A f'(r) ⟪e, ·⟫` and `Δu(x) - Δu(y) ≤ 4 A f''(r)`, where `r = ‖x-y‖`,
`e = (x-y)/r`.  `lapE` is the trace of `iteratedFDeriv ℝ 2` over the standard orthonormal basis
(equal to `lap` of `HRS/Energy/Commutator/SmearAux.lean`, which is not imported here).
-/

namespace HRS.MS.PoissonSpike

/-- one-variable second-order necessary condition, in `HasDerivAt` form. -/
theorem localMax_second {h G : ℝ → ℝ} {G2 : ℝ}
    (hh : ∀ᶠ s in 𝓝 (0:ℝ), HasDerivAt h (G s) s) (hG : HasDerivAt G G2 0)
    (hmax : IsLocalMax h 0) : G 0 = 0 ∧ G2 ≤ 0 := by
  have h0 : HasDerivAt h (G 0) 0 := hh.self_of_nhds
  have hG0 : G 0 = 0 := hmax.hasDerivAt_eq_zero h0
  refine ⟨hG0, ?_⟩
  by_contra hpos
  push Not at hpos
  have hdh : deriv h =ᶠ[𝓝 0] G := hh.mono fun s hs => hs.deriv
  have h1 : deriv h 0 = 0 := by rw [h0.deriv, hG0]
  have h2 : deriv (deriv h) 0 = G2 := by rw [hdh.deriv_eq, hG.deriv]
  have hmin : IsLocalMin h 0 :=
    isLocalMin_of_deriv_deriv_pos (by rw [h2]; exact hpos) h1 h0.continuousAt
  have hconst : ∀ᶠ s in 𝓝 (0:ℝ), h s = h 0 := by
    filter_upwards [hmax, hmin] with s h1 h2 using le_antisymm h1 h2
  have : deriv h =ᶠ[𝓝 0] fun _ => (0:ℝ) := by
    have := (show h =ᶠ[𝓝 0] fun _ => h 0 from hconst).deriv
    filter_upwards [this] with s hs
    simpa using hs
  have h3 : deriv (deriv h) 0 = 0 := by rw [this.deriv_eq]; simp
  linarith

/-- the line `s ↦ u (z + s ξ)`, first and second derivative. -/
theorem line_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (z ξ : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => u (z + t • ξ)) (fderiv ℝ u (z + s • ξ) ξ) s := by
  have hl : HasDerivAt (fun t : ℝ => z + t • ξ) ξ s := by
    simpa using ((hasDerivAt_id s).smul_const ξ).const_add z
  have := (hu.differentiable (by norm_num) (z + s • ξ)).hasFDerivAt.comp_hasDerivAt s hl
  exact this

theorem line_hasDerivAt2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (z ξ : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ u (z + t • ξ) ξ)
      (iteratedFDeriv ℝ 2 u (z + s • ξ) ![ξ, ξ]) s := by
  have hl : HasDerivAt (fun t : ℝ => z + t • ξ) ξ s := by
    simpa using ((hasDerivAt_id s).smul_const ξ).const_add z
  have hd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 := (hd (z + s • ξ)).hasFDerivAt.comp_hasDerivAt s hl
  have h2 := h1.clm_apply (hasDerivAt_const s ξ)
  rw [iteratedFDeriv_two_apply]
  simpa using h2


/-- trace of a bilinear form is independent of the orthonormal basis (via `LinearMap.trace`). -/
theorem trace_indep {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (b b' : OrthonormalBasis ι ℝ E) :
    ∑ i, B (b i) (b i) = ∑ i, B (b' i) (b' i) := by
  have hfd : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  let T : E →ₗ[ℝ] E :=
    { toFun := fun ξ => (InnerProductSpace.toDual ℝ E).symm (B ξ)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have key : ∀ c : OrthonormalBasis ι ℝ E, T.trace ℝ E = ∑ i, B (c i) (c i) := by
    intro c
    rw [LinearMap.trace_eq_sum_inner T c]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm]
    simp [T]
  rw [← key b, ← key b']

variable {d : ℕ}

/-- Laplacian: trace of the second derivative over the standard orthonormal basis. -/
noncomputable def lapE (u : Euc d → ℝ) (z : Euc d) : ℝ :=
  ∑ i, iteratedFDeriv ℝ 2 u z
    ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]

/-- the doubled-variable function -/
noncomputable def Φ (u : Euc d → ℝ) (A : ℝ) (f : ℝ → ℝ) (p : Euc d × Euc d) : ℝ :=
  u p.1 - u p.2 - A * f ‖p.1 - p.2‖

theorem norm_line {w δ : Euc d} (hw : w ≠ 0) :
    HasDerivAt (fun s : ℝ => ‖w + s • δ‖) (inner ℝ (‖w‖⁻¹ • w) δ) 0 := by
  have hl : HasDerivAt (fun t : ℝ => w + t • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const δ).const_add w
  have hw' : w + (0:ℝ) • δ ≠ 0 := by simpa using hw
  have hd : DifferentiableAt ℝ (fun s : ℝ => ‖w + s • δ‖) 0 :=
    DifferentiableAt.norm ℝ hl.differentiableAt hw'
  have h1 := hd.hasDerivAt.pow 2
  have h2 := hl.norm_sq
  have h3 := h1.unique h2
  have hr : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have : deriv (fun s : ℝ => ‖w + s • δ‖) 0 = inner ℝ (‖w‖⁻¹ • w) δ := by
    simp only [zero_smul, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h3
    rw [real_inner_smul_left]
    field_simp
    linarith
  rw [← this]; exact hd.hasDerivAt


section
variable {u : Euc d → ℝ} {A : ℝ} {f : ℝ → ℝ} {x y : Euc d}

theorem phi_line (ξ ζ : Euc d) (s : ℝ) :
    Φ u A f (x + s • ξ, y + s • ζ) =
      u (x + s • ξ) - u (y + s • ζ) - A * f ‖(x - y) + s • (ξ - ζ)‖ := by
  have : (x + s • ξ) - (y + s • ζ) = (x - y) + s • (ξ - ζ) := by rw [smul_sub]; abel
  simp only [Φ, this]

theorem isLocalMax_line (hmax : IsLocalMax (Φ u A f) (x, y)) (ξ ζ : Euc d) :
    IsLocalMax (fun s : ℝ => Φ u A f (x + s • ξ, y + s • ζ)) 0 := by
  have hg : Continuous fun s : ℝ => ((x + s • ξ, y + s • ζ) : Euc d × Euc d) := by fun_prop
  have h0 : IsLocalMax (Φ u A f) ((fun s : ℝ => ((x + s • ξ, y + s • ζ) : Euc d × Euc d)) 0) := by
    simpa using hmax
  exact h0.comp_continuous (b := (0:ℝ)) hg.continuousAt

theorem first_order (hu : ContDiff ℝ 2 u) (hf : ContDiffOn ℝ 2 f (Set.Ioi 0))
    (hmax : IsLocalMax (Φ u A f) (x, y)) (hxy : x ≠ y) (ξ ζ : Euc d) :
    fderiv ℝ u x ξ - fderiv ℝ u y ζ
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
  have h1 := (line_hasDerivAt hu x ξ 0).sub (line_hasDerivAt hu y ζ 0)
  have h2 := (h1.sub (hfN.const_mul A))
  have hmax' := isLocalMax_line hmax ξ ζ
  simp only [phi_line] at hmax'
  have := hmax'.hasDerivAt_eq_zero (f' := _) (show HasDerivAt (fun s : ℝ => u (x + s • ξ) - u (y + s • ζ) - A * f ‖(x - y) + s • (ξ - ζ)‖) _ 0 from h2)
  simpa using this

theorem second_order_diag (hu : ContDiff ℝ 2 u) (hmax : IsLocalMax (Φ u A f) (x, y)) (η : Euc d) :
    iteratedFDeriv ℝ 2 u x ![η, η] - iteratedFDeriv ℝ 2 u y ![η, η] ≤ 0 := by
  have hmax' := isLocalMax_line hmax η η
  have e1 : ∀ s : ℝ, Φ u A f (x + s • η, y + s • η) =
      u (x + s • η) - u (y + s • η) - A * f ‖x - y‖ := fun s => by simp [phi_line]
  simp only [e1] at hmax'
  have hh : ∀ s : ℝ, HasDerivAt (fun s : ℝ => u (x + s • η) - u (y + s • η) - A * f ‖x - y‖)
      (fderiv ℝ u (x + s • η) η - fderiv ℝ u (y + s • η) η) s := fun s =>
    ((line_hasDerivAt hu x η s).sub (line_hasDerivAt hu y η s)).sub_const _
  have hG := (line_hasDerivAt2 hu x η 0).sub (line_hasDerivAt2 hu y η 0)
  have := (localMax_second (Filter.Eventually.of_forall hh) (show HasDerivAt (fun s : ℝ => fderiv ℝ u (x + s • η) η - fderiv ℝ u (y + s • η) η) _ 0 from hG) hmax').2
  simpa using this


theorem second_order_radial (hu : ContDiff ℝ 2 u) (hf : ContDiffOn ℝ 2 f (Set.Ioi 0))
    (hmax : IsLocalMax (Φ u A f) (x, y)) (hxy : x ≠ y) :
    iteratedFDeriv ℝ 2 u x ![‖x - y‖⁻¹ • (x - y), ‖x - y‖⁻¹ • (x - y)]
      - iteratedFDeriv ℝ 2 u y ![‖x - y‖⁻¹ • (x - y), ‖x - y‖⁻¹ • (x - y)]
      ≤ 4 * A * deriv (deriv f) ‖x - y‖ := by
  have hw : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hr : 0 < ‖x - y‖ := norm_pos_iff.2 hw
  generalize hrdef : ‖x - y‖ = r at hr
  generalize hedef : r⁻¹ • (x - y) = e
  have hxe : x - y = r • e := by
    rw [← hedef, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hnorm : ‖e‖ = 1 := by
    rw [← hedef, norm_smul, hrdef, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_cancel₀ hr.ne']
  have hfd : ∀ t, 0 < t → DifferentiableAt ℝ f t := fun t ht =>
    (hf.differentiableOn (by norm_num) _ ht).differentiableAt (Ioi_mem_nhds ht)
  have hdd : DifferentiableAt ℝ (deriv f) r := by
    have h1 := (hf.contDiffAt (Ioi_mem_nhds hr)).fderiv_right (m := 1) (by norm_num)
    exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have hpos : ∀ᶠ s in 𝓝 (0:ℝ), 0 < r + 2 * s := by
    have : ContinuousAt (fun s : ℝ => r + 2 * s) 0 := by fun_prop
    exact this.eventually (lt_mem_nhds (by simpa using hr))
  have hmax' := isLocalMax_line hmax e (-e)
  have hnm : ∀ s : ℝ, 0 < r + 2 * s → ‖(x - y) + s • (e - -e)‖ = r + 2 * s := fun s hs => by
    have : (x - y) + s • (e - -e) = (r + 2 * s) • e := by rw [hxe]; module
    rw [this, norm_smul, hnorm, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  simp only [phi_line] at hmax'
  have hmax2 : IsLocalMax (fun s : ℝ => u (x + s • e) - u (y + s • (-e)) - A * f (r + 2 * s)) 0 := by
    refine hmax'.congr ?_
    filter_upwards [hpos] with s hs
    simp only [hnm s hs]
  have hfs : ∀ s : ℝ, 0 < r + 2 * s →
      HasDerivAt (fun s : ℝ => f (r + 2 * s)) (deriv f (r + 2 * s) * 2) s := fun s hs => by
    have := (hfd _ hs).hasDerivAt.comp s (((hasDerivAt_id s).const_mul 2).const_add r)
    simp only [id, mul_one] at this
    exact this
  have hh : ∀ᶠ s in 𝓝 (0:ℝ), HasDerivAt
      (fun s : ℝ => u (x + s • e) - u (y + s • (-e)) - A * f (r + 2 * s))
      (fderiv ℝ u (x + s • e) e - fderiv ℝ u (y + s • (-e)) (-e)
        - A * (deriv f (r + 2 * s) * 2)) s := by
    filter_upwards [hpos] with s hs
    exact ((line_hasDerivAt hu x e s).sub (line_hasDerivAt hu y (-e) s)).sub
      ((hfs s hs).const_mul A)
  have hG2 : HasDerivAt (fun s : ℝ => deriv f (r + 2 * s)) (deriv (deriv f) r * 2) 0 := by
    have h0 : HasDerivAt (deriv f) (deriv (deriv f) r) (r + 2 * 0) := by
      rw [mul_zero, add_zero]; exact hdd.hasDerivAt
    have := h0.comp (0:ℝ) (((hasDerivAt_id (0:ℝ)).const_mul 2).const_add r)
    simp only [id, mul_one] at this
    exact this
  have hG := (((line_hasDerivAt2 hu x e 0).sub (line_hasDerivAt2 hu y (-e) 0)).sub
      ((hG2.mul_const 2).const_mul A))
  have key := (localMax_second hh (show HasDerivAt (fun s : ℝ => fderiv ℝ u (x + s • e) e
      - fderiv ℝ u (y + s • (-e)) (-e) - A * (deriv f (r + 2 * s) * 2)) _ 0 from hG) hmax2).2
  have hneg : iteratedFDeriv ℝ 2 u y ![-e, -e] = iteratedFDeriv ℝ 2 u y ![e, e] := by
    simp only [iteratedFDeriv_two_apply]; simp
  simp only [zero_smul, add_zero, hneg] at key
  linarith

end

theorem lapE_eq (u : Euc d → ℝ) (z : Euc d) (b : OrthonormalBasis (Fin d) ℝ (Euc d)) :
    lapE u z = ∑ i, iteratedFDeriv ℝ 2 u z ![b i, b i] := by
  unfold lapE
  simp only [iteratedFDeriv_two_apply]
  simpa using trace_indep (fderiv ℝ (fderiv ℝ u) z) (EuclideanSpace.basisFun (Fin d) ℝ) b

theorem poisson_maxpoint (hd : 1 ≤ d) (u : Euc d → ℝ) (hu : ContDiff ℝ 2 u) (A : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioi 0)) (x y : Euc d)
    (hmax : IsLocalMax (fun p : Euc d × Euc d => u p.1 - u p.2 - A * f ‖p.1 - p.2‖) (x, y))
    (hxy : x ≠ y) :
    (∀ v : Euc d, fderiv ℝ u x v = A * deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) v ∧
      fderiv ℝ u y v = A * deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) v) ∧
    lapE u x - lapE u y ≤ 4 * A * deriv (deriv f) ‖x - y‖ := by
  have hmax : IsLocalMax (Φ u A f) (x, y) := hmax
  refine ⟨fun v => ⟨?_, ?_⟩, ?_⟩
  · have := first_order hu hf hmax hxy v 0
    simp at this
    linarith
  · have := first_order hu hf hmax hxy 0 v
    simp [inner_neg_right] at this
    linarith
  · set e : Euc d := ‖x - y‖⁻¹ • (x - y) with he
    have hnorm : ‖e‖ = 1 := by
      rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (sub_ne_zero.2 hxy))]
    let i0 : Fin d := ⟨0, hd⟩
    have hon : Orthonormal ℝ (({i0} : Set (Fin d)).domRestrict (fun _ => e)) := by
      refine ⟨fun i => hnorm, fun i j hij => ?_⟩
      exact absurd (Subtype.ext (by rw [Set.mem_singleton_iff.1 i.2, Set.mem_singleton_iff.1 j.2])) hij
    obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (by simp) hon
    have hb0 : b i0 = e := hb i0 rfl
    rw [lapE_eq u x b, lapE_eq u y b, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ i : Fin d, (if i = i0 then 4 * A * deriv (deriv f) ‖x - y‖ else 0) := by
          refine Finset.sum_le_sum fun i _ => ?_
          by_cases h : i = i0
          · subst h; rw [ite_eq_left_iff.2 (fun h => absurd rfl h), hb0]; exact second_order_radial hu hf hmax hxy
          · rw [ite_eq_right_iff.2 (fun h' => absurd h' h)]; exact second_order_diag hu hmax (b i)
      _ = _ := by simp

end HRS.MS.PoissonSpike
