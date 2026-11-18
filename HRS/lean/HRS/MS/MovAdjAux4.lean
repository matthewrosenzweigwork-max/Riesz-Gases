import HRS.MS.MovAdjAux3

/-!
# S6.7 (packet P1, part 3): the local part of the duality identity

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

For `ρ = ρ₀` thermal, `ψ0 = √ρ ∈ 𝓢`, `φ ∈ 𝓢`, `z = ψ0 φ`, `u ∈ C_b²`, `ν = β⁻¹`, `ℓ = ∇log ρ`, and the flux field
`W = ρ ∇(ν φ/√ρ) = ν(ψ0 ∇φ - φ ∇ψ0)` (`s67Wv`):

`s67_local`: `∫ z (νΔu + ν⟨ℓ,∇u⟩) = ∫ (div W) u`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovForce HRS.MS.MovOsc

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- The flux field `W = ρ ∇(β⁻¹ φ/√ρ)`. -/
def s67Wv (d : ℕ) (β : ℝ) (ρ : Euc d → ℝ) (φ : Euc d → ℝ) (y : Euc d) : Euc d :=
  ρ y • gradient (fun z => β⁻¹ * (φ z / Real.sqrt (ρ z))) y

/-- Product of two Schwartz functions as a Schwartz function. -/
def s67prod (a b : 𝓢R) : 𝓢R := SchwartzMap.smulLeftCLM ℝ (⇑a : Euc d → ℝ) b

@[simp] theorem s67prod_apply (a b : 𝓢R) (x : Euc d) : s67prod a b x = a x * b x := by
  simp [s67prod, SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth]

/-- Coordinates of the flux field. -/
theorem s67_Wv_comp (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (φ : 𝓢R) (y : Euc d) (i : Fin d) :
    s67Wv d β ρ φ y i = β⁻¹ * (ψ0 y * fderiv ℝ φ y (EuclideanSpace.single i 1) -
      φ y * fderiv ℝ ψ0 y (EuclideanSpace.single i 1)) := by
  have hρ := mnb_rhoData H
  unfold s67Wv
  rw [mov2a_flux hρ.smooth hρ.pos (φ.smooth ⊤) y]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have e1 : gradient (fun z => Real.sqrt (ρ z)) y i = fderiv ℝ ψ0 y (EuclideanSpace.single i 1) := by
    rw [← hψ0, mnc_gradient_apply]
  rw [e1, mnc_gradient_apply]
  have e2 : ψ0 y = Real.sqrt (ρ y) := by rw [hψ0]
  rw [e2]
  ring

/-- Coordinates of the flux field are Schwartz functions. -/
theorem s67_Wv_schwartz (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (φ : 𝓢R) (i : Fin d) : ∃ S : 𝓢R, ∀ y, s67Wv d β ρ φ y i = S y := by
  refine ⟨β⁻¹ • (s67prod ψ0 (mova1_D i φ) - s67prod φ (mova1_D i ψ0)), fun y => ?_⟩
  rw [s67_Wv_comp H ψ0 hψ0 φ y i]
  simp


/-! ### Auxiliary facts on `C_b²` functions -/

theorem s67_grad_norm (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _

theorem s67_grad_cont {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) : Continuous (fun y => gradient u y) := by
  have h := HRS.MS.S98.s98_gL_contDiff (k := 0) (χ := u) (by simpa using hu) 1
  simp only [one_smul] at h
  exact h.continuous

theorem s67_grad_diff {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) : Differentiable ℝ (fun y => gradient u y) := by
  have h := HRS.MS.S98.s98_gL_contDiff (k := 1) (χ := u) (by simpa using hu) 1
  simp only [one_smul] at h
  exact h.differentiable one_ne_zero

theorem s67_grad_comp_abs_le (f : Euc d → ℝ) (x : Euc d) (i : Fin d) :
    |gradient f x i| ≤ ‖fderiv ℝ f x‖ := by
  have := PiLp.norm_apply_le (gradient f x) i
  rw [s67_grad_norm] at this
  simpa [Real.norm_eq_abs] using this

/-- `∑ S_i ∂_i u` is integrable for Schwartz `S_i` and `u ∈ C_b²`. -/
theorem s67_int_sum_grad (S : Fin d → 𝓢R) {u : Euc d → ℝ} (hu : MemCb 2 u) :
    Integrable (fun x => ∑ i, S i x * gradient u x i) := by
  obtain ⟨B, hB0, hBu, hBd, -⟩ := s67_memCb_bounds hu
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by norm_num)
  refine integrable_finsetSum _ fun i _ => ?_
  refine (S i).integrable.mul_bdd (g := fun x => gradient u x i) (c := B) ?_ ?_
  · exact ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp (s67_grad_cont hu1)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact (s67_grad_comp_abs_le u x i).trans (hBd x)

theorem s67_inner_eq (a b : Euc d → ℝ) (x : Euc d) :
    inner ℝ (gradient a x) (gradient b x) =
      ∑ i, fderiv ℝ a x (EuclideanSpace.single i 1) * gradient b x i := by
  rw [mnc_inner_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [mnc_gradient_apply]

/-- **The local part of the duality identity.** -/
theorem s67_local (H : Mov2dTh d s β q ρ) {u : Euc d → ℝ} (hu : MemCb 2 u) (φ ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    ∫ x, (β⁻¹ * Laplacian.laplacian u x +
        β⁻¹ * inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient u x)) * (ψ0 x * φ x) =
      ∫ x, movDiv (s67Wv d β ρ φ) x * u x := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hρ := mnb_rhoData H
  obtain ⟨B, hB0, hBu, hBd, hB2⟩ := s67_memCb_bounds hu
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by norm_num)
  have hρd : Differentiable ℝ ρ := hρ.smooth.differentiable (by simp)
  -- Step 1: integration by parts against the flux field
  have hWrg : ∀ i : Fin d, ∃ c : ℝ, 0 ≤ c ∧
      HRS.MP.RdGen.RgW (s67W d) 1 c (fun y => s67Wv d β ρ φ y i) := by
    intro i
    obtain ⟨S, hS⟩ := s67_Wv_schwartz H ψ0 hψ0 φ i
    obtain ⟨c, hc0, hc⟩ := s67_rgW_schwartz S
    refine ⟨c, hc0, ?_⟩
    have : (fun y => s67Wv d β ρ φ y i) = ⇑S := funext hS
    rw [this]; exact hc
  have h1 := s67_ibp_div_rgW' hd1 hWrg hu1 hBu hBd
  -- the inner product with the flux field
  have hWin : ∀ x, inner ℝ (s67Wv d β ρ φ x) (gradient u x) =
      β⁻¹ * (ψ0 x * inner ℝ (gradient (⇑φ) x) (gradient u x) -
        φ x * inner ℝ (gradient (⇑ψ0) x) (gradient u x)) := by
    intro x
    rw [mnc_inner_eq_sum, mnc_inner_eq_sum, mnc_inner_eq_sum]
    simp_rw [s67_Wv_comp H ψ0 hψ0 φ x, mnc_gradient_apply]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- Step 2: integration by parts for `ψ0 ∇u` against `φ`
  have hY2 : ∀ i : Fin d, ∃ c : ℝ, 0 ≤ c ∧
      HRS.MP.RdGen.RgW (s67W d) 1 c (fun y => (ψ0 y • gradient u y) i) := by
    intro i
    obtain ⟨c1, hc10, hc1⟩ := s67_rgW_schwartz ψ0
    obtain ⟨c2, hc20, hc2⟩ := dc1a_grad_comp_rgW hu i
    refine ⟨2 ^ 1 * c1 * c2, by positivity, ?_⟩
    have := s67_mul_rgW hc10 hc20 hc1 hc2
    simpa [PiLp.smul_apply] using this
  obtain ⟨Bφ, hBφ0, hBφ, hBφd⟩ := s67_schwartz_bounds φ
  have h2 := s67_ibp_div_rgW' hd1 hY2 (φ.smooth 1) hBφ hBφd
  have hdiv2 : ∀ x, movDiv (fun y => ψ0 y • gradient u y) x =
      ψ0 x * Laplacian.laplacian u x + inner ℝ (gradient (⇑ψ0) x) (gradient u x) := by
    intro x
    rw [mv1_movDiv_smul (ψ0.smooth ⊤ |>.differentiable (by simp) x) (s67_grad_diff hu.1 x),
      HRS.MS.S98.s98_movDiv_gradient hu.1 x, mov2a_sum_fderiv_mul]
  -- integrability
  have IJ1 : Integrable (fun x => ψ0 x * inner ℝ (gradient (⇑φ) x) (gradient u x)) := by
    have := s67_int_sum_grad (fun i => s67prod ψ0 (mova1_D i φ)) hu
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [s67prod_apply, mova1_D_apply]
    rw [s67_inner_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have IJ2 : Integrable (fun x => φ x * inner ℝ (gradient (⇑ψ0) x) (gradient u x)) := by
    have := s67_int_sum_grad (fun i => s67prod φ (mova1_D i ψ0)) hu
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [s67prod_apply, mova1_D_apply]
    rw [s67_inner_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have IJ3 : Integrable (fun x => (ψ0 x * φ x) * Laplacian.laplacian u x) := by
    have := (s67prod ψ0 φ).integrable (μ := (volume : Measure (Euc d))) |>.mul_bdd (g := Laplacian.laplacian u) (c := d * B)
      (s67_lap_cont hu.1).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact s67_lap_bound hB2 x)
    simpa using this
  -- assemble
  have hF2 : ∫ x, (ψ0 x * Laplacian.laplacian u x +
        inner ℝ (gradient (⇑ψ0) x) (gradient u x)) * φ x =
      (∫ x, (ψ0 x * φ x) * Laplacian.laplacian u x) + ∫ x, φ x * inner ℝ (gradient (⇑ψ0) x) (gradient u x) := by
    rw [← integral_add IJ3 IJ2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hF1 : -∫ x, inner ℝ (ψ0 x • gradient u x) (gradient (⇑φ) x) =
      -∫ x, ψ0 x * inner ℝ (gradient (⇑φ) x) (gradient u x) := by
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [real_inner_smul_left, real_inner_comm]
  simp_rw [hdiv2] at h2
  rw [hF2, hF1] at h2
  -- h2 : J3 + J2 = - J1
  have hLHS : ∫ x, (β⁻¹ * Laplacian.laplacian u x +
        β⁻¹ * inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient u x)) * (ψ0 x * φ x) =
      β⁻¹ * (∫ x, (ψ0 x * φ x) * Laplacian.laplacian u x) +
        2 * β⁻¹ * ∫ x, φ x * inner ℝ (gradient (⇑ψ0) x) (gradient u x) := by
    have e : (fun x => (β⁻¹ * Laplacian.laplacian u x +
        β⁻¹ * inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient u x)) * (ψ0 x * φ x)) =
        fun x => β⁻¹ * ((ψ0 x * φ x) * Laplacian.laplacian u x) +
          (2 * β⁻¹) * (φ x * inner ℝ (gradient (⇑ψ0) x) (gradient u x)) := by
      funext x
      have hg : gradient (⇑ψ0) x =
          ((1 / 2) * Real.sqrt (ρ x)) • gradient (fun y => Real.log (ρ y)) x := by
        have := mov2a_grad_sqrt hρd hρ.pos x
        rw [hψ0]; exact this
      rw [hg, real_inner_smul_left]
      have e2 : ψ0 x = Real.sqrt (ρ x) := by rw [hψ0]
      rw [e2]
      ring
    rw [e, integral_add (IJ3.const_mul _) (IJ2.const_mul _), integral_const_mul, integral_const_mul]
  have hRHS : ∫ x, movDiv (s67Wv d β ρ φ) x * u x =
      -(β⁻¹ * ((∫ x, ψ0 x * inner ℝ (gradient (⇑φ) x) (gradient u x)) -
        ∫ x, φ x * inner ℝ (gradient (⇑ψ0) x) (gradient u x))) := by
    rw [h1]
    simp_rw [hWin]
    rw [integral_const_mul, integral_sub IJ1 IJ2]
  rw [hLHS, hRHS]
  generalize (∫ x, (ψ0 x * φ x) * Laplacian.laplacian u x) = J3 at h2 ⊢
  generalize (∫ x, φ x * inner ℝ (gradient (⇑ψ0) x) (gradient u x)) = J2 at h2 ⊢
  generalize (∫ x, ψ0 x * inner ℝ (gradient (⇑φ) x) (gradient u x)) = J1 at h2 ⊢
  have hJ1 : J1 = -(J3 + J2) := by linarith
  rw [hJ1]
  ring

end HRS.MS.MovAdj
