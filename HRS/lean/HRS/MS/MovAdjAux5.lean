import HRS.MS.MovAdjAux4

/-!
# S6.7 (packet P1, part 4): the nonlocal part and the duality identity

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67_sqrt_movS`: `√ρ · S φ = -div W - div(ρ F_z)` with `W = ρ∇(νφ/√ρ)`, `F_z = ∇g ⋆ (√ρ φ)`;
* `s67_nonlocal`: `∫ z J u = ∫ div(ρ F_z) u`;
* `s67_duality`: **`∫ (𝓛 u) √ρ φ = -∫ u √ρ S φ`** for `u ∈ C_b²`, `φ ∈ 𝓢`, `𝓛 = generatorW` of the stationary coefficient.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovForce HRS.MS.MovOsc

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- From `cbNormVecE` to pointwise derivative bounds. -/
theorem s67_cbVec_bound {K : ℕ} {v : Euc d → Euc d} {Λ : ℝ} (h : cbNormVecE K v ≤ ENNReal.ofReal Λ)
    {i : ℕ} (hi : i ≤ K) (x : Euc d) : ‖iteratedFDeriv ℝ i v x‖ ≤ max Λ 0 := by
  unfold cbNormVecE at h
  have h1 : (⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i v y‖) ≤ ENNReal.ofReal Λ :=
    (Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j v y‖)
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))).trans h
  have h2 : ENNReal.ofReal ‖iteratedFDeriv ℝ i v x‖ ≤ ENNReal.ofReal Λ := (le_iSup _ x).trans h1
  by_cases hΛ : 0 ≤ Λ
  · exact ((ENNReal.ofReal_le_ofReal_iff hΛ).1 h2).trans (le_max_left _ _)
  · push Not at hΛ
    rw [ENNReal.ofReal_of_nonpos hΛ.le] at h2
    have := ENNReal.ofReal_eq_zero.1 (le_antisymm h2 zero_le)
    exact this.trans (le_max_right _ _)

theorem s67_sqrt_movS (H : Mov2dTh d s β q ρ) (φ : Euc d → ℝ) (x : Euc d) :
    Real.sqrt (ρ x) * movS d s β ρ φ x =
      -movDiv (s67Wv d β ρ φ) x -
        movDiv (fun y => ρ y • movForce d s (fun z => Real.sqrt (ρ z) * φ z) y) x := by
  have hρ := mnb_rhoData H
  have hs : Real.sqrt (ρ x) ≠ 0 := (Real.sqrt_pos.2 (hρ.pos x)).ne'
  unfold movS movP s67Wv
  field_simp
  ring

/-- `RgW` components give an integrable divergence. -/
theorem s67_int_div_rgW (hd : 1 ≤ d) {Y : Euc d → Euc d}
    (hY : ∀ i : Fin d, ∃ c : ℝ, 0 ≤ c ∧ HRS.MP.RdGen.RgW (s67W d) 1 c (fun y => Y y i)) :
    Integrable (fun x => movDiv Y x) := by
  have hYc : ContDiff ℝ 1 Y := by
    refine contDiff_euclidean.2 fun i => ?_
    obtain ⟨c, -, hc⟩ := hY i
    exact hc.1
  have hYd : Differentiable ℝ Y := hYc.differentiable one_ne_zero
  have : (fun x => movDiv Y x) = fun x => ∑ i : Fin d, fderiv ℝ (fun y => Y y i) x (EuclideanSpace.single i 1) := by
    funext x
    unfold movDiv
    exact Finset.sum_congr rfl fun i _ => mnc_comp_fderiv_apply Y hYd x _ i
  rw [this]
  refine integrable_finsetSum _ fun i _ => ?_
  obtain ⟨c, hc0, hc⟩ := hY i
  exact s67_rgW_int_deriv hd hc0 hc _ (by simp)

/-- The components `Y_i = ρ F_i` of the nonlocal flux, with `F = ∇g ⋆ (√ρ φ)`, are in `RgW`. -/
theorem s67_nonlocal_flux (H : Mov2dTh d s β q ρ) (φ : 𝓢R) :
    ∀ i : Fin d, ∃ c : ℝ, 0 ≤ c ∧ HRS.MP.RdGen.RgW (s67W d) 1 c
      (fun y => (ρ y • movForce d s (fun z => Real.sqrt (ρ z) * φ z) y) i) := by
  intro i
  have hd := H.hd
  obtain ⟨Cρ, hCρ, hρW⟩ := mnc_rgW_rho H
  obtain ⟨C, hC0, hC⟩ := mn_force_bound hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ 0 (d + 3)
    (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; push_cast; linarith)
  obtain ⟨-, -, hF1, -, hcb⟩ := hC (⇑φ) φ.continuous (memOsc_schwartz _ φ)
  set F : Euc d → Euc d := movForce d s (fun z => Real.sqrt (ρ z) * φ z) with hF
  have hcbv : cbNormVecE 1 F ≤ ENNReal.ofReal (C * oscNorm ((d + 3 : ℕ) : ℝ) (⇑φ)) := by
    have : cbNormVecE (0 + 1) F ≤ _ := le_trans le_self_add hcb
    simpa using this
  have hFb : ∀ n, n ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ n F x‖ ≤ max (C * oscNorm ((d + 3 : ℕ) : ℝ) (⇑φ)) 0 := by
    intro n hn x
    refine s67_cbVec_bound hcbv hn x
  have hF1' : ContDiff ℝ 1 F := by simpa using hF1
  have hproj : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v i)
  have hFi : HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) 1 (max (C * oscNorm ((d + 3 : ℕ) : ℝ) (⇑φ)) 0)
      (fun y => F y i) := by
    refine ⟨contDiff_euclidean.1 hF1' i, fun n hn x => ?_⟩
    have hn' : (n : WithTop ℕ∞) ≤ 1 := by exact_mod_cast hn
    have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left (f := F) (x := x)
      (N := (1 : WithTop ℕ∞)) hF1'.contDiffAt hn'
    calc ‖iteratedFDeriv ℝ n (fun y => F y i) x‖
        = ‖iteratedFDeriv ℝ n ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) ∘ F) x‖ := rfl
      _ ≤ ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ n F x‖ := this
      _ ≤ 1 * max (C * oscNorm ((d + 3 : ℕ) : ℝ) (⇑φ)) 0 :=
          mul_le_mul hproj (hFb n hn x) (norm_nonneg _) zero_le_one
      _ = max (C * oscNorm ((d + 3 : ℕ) : ℝ) (⇑φ)) 0 * 1 := by ring
  refine ⟨2 ^ 1 * Cρ * max (C * oscNorm ((d + 3 : ℕ) : ℝ) (⇑φ)) 0, by positivity, ?_⟩
  have := s67_mul_rgW hCρ (le_max_right _ _) hρW hFi
  simpa [PiLp.smul_apply] using this

/-- The `RgW` memberships of `ρ ∂_j u`. -/
theorem s67_h_rgW (H : Mov2dTh d s β q ρ) {u : Euc d → ℝ} (hu : MemCb 2 u) (j : Fin d) :
    ∃ c : ℝ, 0 ≤ c ∧ HRS.MP.RdGen.RgW (s67W d) 1 c (fun y => ρ y * gradient u y j) := by
  obtain ⟨Cρ, hCρ, hρW⟩ := mnc_rgW_rho H
  obtain ⟨c, hc0, hc⟩ := dc1a_grad_comp_rgW hu j
  exact ⟨2 ^ 1 * Cρ * c, by positivity, s67_mul_rgW hCρ hc0 hρW hc⟩

/-- The nonlocal term `J u` is bounded and measurable. -/
theorem s67_J_bdd (H : Mov2dTh d s β q ρ) {u : Euc d → ℝ} (hu : MemCb 2 u) :
    (∃ B : ℝ, ∀ x, |s67J d s ρ u x| ≤ B) ∧ Measurable (s67J d s ρ u) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hb : ∀ j : Fin d, ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      ‖(convGradConvW (rieszKernelGrad d s) (fun y => ρ y * gradient u y j) x) j‖ ≤ B := by
    intro j
    obtain ⟨c, hc0, hc⟩ := s67_h_rgW H hu j
    exact dc1a_force_bound' hd1 H.hs0 H.hsd hc0 hc j
  choose B hB0 hB using hb
  refine ⟨⟨∑ j, B j, fun x => ?_⟩, ?_⟩
  · unfold s67J
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    simpa [Real.norm_eq_abs] using hB j x
  · unfold s67J
    refine Finset.measurable_sum _ fun j _ => ?_
    obtain ⟨c, hc0, hc⟩ := s67_h_rgW H hu j
    exact dc1b_conv_meas hd1 H.hs0 H.hsd hc0 hc j

/-- **The nonlocal part of the duality identity.** -/
theorem s67_nonlocal (H : Mov2dTh d s β q ρ) {u : Euc d → ℝ} (hu : MemCb 2 u) (φ ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    ∫ x, (ψ0 x * φ x) * s67J d s ρ u x =
      ∫ x, movDiv (fun y => ρ y • movForce d s (fun z => Real.sqrt (ρ z) * φ z) y) x * u x := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by norm_num)
  obtain ⟨B, hB0, hBu, hBd, hB2⟩ := s67_memCb_bounds hu
  set zS : 𝓢R := s67prod ψ0 φ with hzS
  have hzf : (⇑zS : Euc d → ℝ) = fun x => Real.sqrt (ρ x) * φ x := by
    funext x; rw [hzS, s67prod_apply, hψ0]
  obtain ⟨cz, hcz0, hczW⟩ := s67_rgW_schwartz zS
  -- (1) integration by parts
  have h1 := s67_ibp_div_rgW' hd1 (s67_nonlocal_flux H φ) hu1 hBu hBd
  -- (2) antisymmetry, coordinatewise
  have hanti : ∀ j : Fin d, ∫ x, zS x * (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ y * gradient u y j) x) j =
      -∫ x, (ρ x * gradient u x j) * (movForce d s (fun z => Real.sqrt (ρ z) * φ z) x) j := by
    intro j
    obtain ⟨c, hc0, hc⟩ := s67_h_rgW H hu j
    have := s67_antisym hd1 H.hs0 H.hsd j hcz0 hc0 hczW hc
    rw [this, hzf]
    rfl
  have hint1 : ∀ j : Fin d, Integrable (fun x => zS x * (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ y * gradient u y j) x) j) := by
    intro j
    obtain ⟨c, hc0, hc⟩ := s67_h_rgW H hu j
    obtain ⟨Bj, hBj0, hBj⟩ := dc1a_force_bound' hd1 H.hs0 H.hsd hc0 hc j
    exact zS.integrable (μ := (volume : Measure (Euc d))) |>.mul_bdd (c := Bj)
      (dc1b_conv_meas hd1 H.hs0 H.hsd hc0 hc j).aestronglyMeasurable
      (Filter.Eventually.of_forall hBj)
  have hint2 : ∀ j : Fin d, Integrable (fun x => (ρ x * gradient u x j) *
      (movForce d s (fun z => Real.sqrt (ρ z) * φ z) x) j) := by
    intro j
    obtain ⟨c, hc0, hc⟩ := s67_h_rgW H hu j
    obtain ⟨cF, hcF0, hcF⟩ := s67_rgW_schwartz zS
    obtain ⟨Bj, hBj0, hBj⟩ := dc1a_force_bound' hd1 H.hs0 H.hsd hcF0 hcF j
    have hmeas := dc1b_conv_meas hd1 H.hs0 H.hsd hcF0 hcF j
    rw [hzf] at hmeas hBj
    exact (s67_rgW_int hd1 hc0 hc).mul_bdd (c := Bj) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hBj)
  have hLHS : ∫ x, (ψ0 x * φ x) * s67J d s ρ u x = -∑ j : Fin d, ∫ x, (ρ x * gradient u x j) *
      (movForce d s (fun z => Real.sqrt (ρ z) * φ z) x) j := by
    have e : ∀ x, (ψ0 x * φ x) * s67J d s ρ u x = ∑ j : Fin d, zS x * (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ y * gradient u y j) x) j := by
      intro x
      unfold s67J
      rw [Finset.mul_sum, hzS, s67prod_apply]
    simp_rw [e]
    rw [integral_finsetSum _ (fun j _ => hint1 j)]
    simp_rw [hanti]
    rw [Finset.sum_neg_distrib]
  have hRHS : ∫ x, movDiv (fun y => ρ y • movForce d s (fun z => Real.sqrt (ρ z) * φ z) y) x * u x =
      -∑ j : Fin d, ∫ x, (ρ x * gradient u x j) *
        (movForce d s (fun z => Real.sqrt (ρ z) * φ z) x) j := by
    rw [h1]
    congr 1
    rw [← integral_finsetSum _ (fun j _ => hint2 j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [real_inner_smul_left, mnc_inner_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hLHS, hRHS]

/-- **The duality identity.**  For `u ∈ C_b²`, a Schwartz function `φ`, and the generator `𝓛` of the stationary
coefficient of `quadraticGradientDyn`: `∫ (𝓛 u) √ρ φ = -∫ u √ρ S φ`. -/
theorem s67_duality (H : Mov2dTh d s β q ρ) {u : Euc d → ℝ} (hu : MemCb 2 u) (φ : 𝓢R) (r : ℝ) :
    ∫ x, generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) r u x *
        (Real.sqrt (ρ x) * φ x) =
      -∫ x, u x * (Real.sqrt (ρ x) * movS d s β ρ (⇑φ) x) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hρ := mnb_rhoData H
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  obtain ⟨B, hB0, hBu, hBd, hB2⟩ := s67_memCb_bounds hu
  have hρd : Differentiable ℝ ρ := hρ.smooth.differentiable (by simp)
  have e0 : ∀ x, Real.sqrt (ρ x) = ψ0 x := fun x => by rw [hψ0]
  simp_rw [e0]
  -- the generator in terms of `ℓ`
  have hgen : ∀ x, generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) r u x * (ψ0 x * φ x) =
      (β⁻¹ * Laplacian.laplacian u x +
        β⁻¹ * inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient u x)) * (ψ0 x * φ x) +
      (ψ0 x * φ x) * s67J d s ρ u x := by
    intro x
    rw [s67_gen_eq, s67_drift_eq H.hd H.hs0 H.hsd H.hq H.hβ H.hρ x, real_inner_smul_left]
    ring
  -- integrability of the pieces
  obtain ⟨⟨BJ, hBJ⟩, hJm⟩ := s67_J_bdd H hu
  have IJ2 : Integrable (fun x => φ x * inner ℝ (gradient (⇑ψ0) x) (gradient u x)) := by
    have := s67_int_sum_grad (fun i => s67prod φ (mova1_D i ψ0)) hu
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [s67prod_apply, mova1_D_apply]
    rw [s67_inner_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have IJ3 : Integrable (fun x => (ψ0 x * φ x) * Laplacian.laplacian u x) := by
    have := (s67prod ψ0 φ).integrable (μ := (volume : Measure (Euc d))) |>.mul_bdd
      (g := Laplacian.laplacian u) (c := d * B) (s67_lap_cont hu.1).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact s67_lap_bound hB2 x)
    simpa using this
  have Iloc : Integrable (fun x => (β⁻¹ * Laplacian.laplacian u x +
        β⁻¹ * inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient u x)) * (ψ0 x * φ x)) := by
    have e : (fun x => (β⁻¹ * Laplacian.laplacian u x +
        β⁻¹ * inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient u x)) * (ψ0 x * φ x)) =
        fun x => β⁻¹ * ((ψ0 x * φ x) * Laplacian.laplacian u x) +
          (2 * β⁻¹) * (φ x * inner ℝ (gradient (⇑ψ0) x) (gradient u x)) := by
      funext x
      have hg : gradient (⇑ψ0) x =
          ((1 / 2) * Real.sqrt (ρ x)) • gradient (fun y => Real.log (ρ y)) x := by
        have := mov2a_grad_sqrt hρd hρ.pos x
        rw [hψ0]; exact this
      rw [hg, real_inner_smul_left, ← e0 x]
      ring
    rw [e]
    exact (IJ3.const_mul _).add (IJ2.const_mul _)
  have INL : Integrable (fun x => (ψ0 x * φ x) * s67J d s ρ u x) :=
    (s67prod ψ0 φ).integrable (μ := (volume : Measure (Euc d))) |>.mul_bdd (c := BJ)
      hJm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hBJ x) |>.congr (Filter.Eventually.of_forall fun x => by simp)
  -- the right side
  have hWc := fun i : Fin d => s67_Wv_schwartz H ψ0 hψ0 φ i
  have hWrg : ∀ i : Fin d, ∃ c : ℝ, 0 ≤ c ∧
      HRS.MP.RdGen.RgW (s67W d) 1 c (fun y => s67Wv d β ρ φ y i) := by
    intro i
    obtain ⟨S, hS⟩ := hWc i
    obtain ⟨c, hc0, hc⟩ := s67_rgW_schwartz S
    refine ⟨c, hc0, ?_⟩
    have : (fun y => s67Wv d β ρ φ y i) = ⇑S := funext hS
    rw [this]; exact hc
  have IW := s67_int_div_rgW hd1 hWrg
  have IY := s67_int_div_rgW hd1 (s67_nonlocal_flux H φ)
  have IuW : Integrable (fun x => movDiv (s67Wv d β ρ φ) x * u x) :=
    IW.mul_bdd (c := B) hu.1.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBu x)
  have IuY : Integrable (fun x => movDiv (fun y => ρ y • movForce d s (fun z => Real.sqrt (ρ z) * φ z) y) x * u x) :=
    IY.mul_bdd (c := B) hu.1.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBu x)
  have hE1 := s67_local H hu φ ψ0 hψ0
  have hE2 := s67_nonlocal H hu φ ψ0 hψ0
  have hR : ∫ x, u x * (ψ0 x * movS d s β ρ (⇑φ) x) =
      -((∫ x, movDiv (s67Wv d β ρ φ) x * u x) +
        (∫ x, movDiv (fun y => ρ y • movForce d s (fun z => Real.sqrt (ρ z) * φ z) y) x * u x)) := by
    rw [← integral_add IuW IuY, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have := s67_sqrt_movS H (⇑φ) x
    rw [e0 x] at this
    calc u x * (ψ0 x * movS d s β ρ (⇑φ) x)
        = u x * (-movDiv (s67Wv d β ρ φ) x -
          movDiv (fun y => ρ y • movForce d s (fun z => Real.sqrt (ρ z) * φ z) y) x) := by rw [this]
      _ = _ := by ring
  rw [hR]
  simp_rw [hgen]
  rw [integral_add Iloc INL, hE1, hE2]
  ring

end HRS.MS.MovAdj
