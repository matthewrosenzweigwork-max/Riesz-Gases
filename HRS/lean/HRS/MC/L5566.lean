import HRS.MC.L5566Aux3

/-!
# Packet L5566: the gradient of the bounded negative-exponent kernel is unbounded (`M:@remark:L5566`)

Relocated proof of `HRS.negSpectral_grad_unbounded`.  Route: `G = lift g` is `C¹` off `ℤ^d` (Aux2/3:
`G(y)(cos 2πy_i - 1) = F_i(y)` with `F_i` a `C¹` series), `G(0) - G(τ e_i) ≥ c₁ τ^{-s}` by positivity of
the coefficients (Aux3), so a bound `‖∇G‖ ≤ C` along the axis would give `G(0) - G(τ e_i) ≤ C τ`,
which fails since `-s < 1`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.L5566

open HRS

variable {d : ℕ}

lemma l5566_diffAt_shift (G : Euc d → ℝ) (v y : Euc d) (hper : ∀ z, G (z - v) = G z)
    (h : DifferentiableAt ℝ G y) : DifferentiableAt ℝ G (y + v) := by
  have h2 : DifferentiableAt ℝ G (y + v - v) := by rwa [add_sub_cancel_right]
  have h1 := h2.comp (y + v) (differentiableAt_id.sub_const v)
  have heq : (G ∘ fun x => id x - v) = G := funext fun z => hper z
  rwa [heq] at h1

lemma l5566_lipschitz_step {s c : ℝ} (hs : s < 0) (i : Fin d) (C : ℝ)
    (hC : ∀ τ ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ (Torus.lift (negSpectralKernel d s c)) (l5566_pt i τ) ∧
      ‖fderiv ℝ (Torus.lift (negSpectralKernel d s c)) (l5566_pt i τ)‖ ≤ C)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) :
    Torus.lift (negSpectralKernel d s c) 0 - Torus.lift (negSpectralKernel d s c) (l5566_pt i τ) ≤ C * τ := by
  set G := Torus.lift (negSpectralKernel d s c) with hG
  set v : Euc d := EuclideanSpace.single i (1 : ℝ) with hv
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC τ hτ).2
  set φ : ℝ → ℝ := fun t => G (l5566_pt i t) with hφ
  have hpt : ∀ t : ℝ, HasDerivAt (fun t : ℝ => l5566_pt i t) v t := by
    intro t
    have := (hasDerivAt_id t).smul_const v
    simpa [l5566_pt, hv] using this
  have hder : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (fderiv ℝ G (l5566_pt i t) v) t := by
    intro t ht
    exact (hC t ht).1.hasFDerivAt.comp_hasDerivAt t (hpt t)
  have hbd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖fderiv ℝ G (l5566_pt i t) v‖ ≤ C := by
    intro t ht
    calc ‖fderiv ℝ G (l5566_pt i t) v‖ ≤ ‖fderiv ℝ G (l5566_pt i t)‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * 1 := by
          rw [hv, EuclideanSpace.norm_single]
          simp only [norm_one, mul_one]
          exact (hC t ht).2
      _ = C := mul_one C
  have hmv : ∀ ε ∈ Set.Ioo (0 : ℝ) τ, φ ε - φ τ ≤ C * τ := by
    intro ε hε
    have hε1 : ε ∈ Set.Ioo (0 : ℝ) 1 := ⟨hε.1, hε.2.trans hτ.2⟩
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ)
      (f' := fun t => fderiv ℝ G (l5566_pt i t) v) (s := Set.Ioo (0 : ℝ) 1) (C := C)
      (fun t ht => (hder t ht).hasDerivWithinAt) hbd (convex_Ioo 0 1) hτ hε1
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    have h2 := (abs_le.mp this).2
    have h3 : |ε - τ| = τ - ε := by rw [abs_sub_comm, abs_of_pos (by linarith [hε.2])]
    rw [h3] at h2
    nlinarith [hε.1]
  have hcont : Continuous G := l5566_continuous_lift hs c
  have hlim : Tendsto (fun ε => φ ε - φ τ) (𝓝[>] (0 : ℝ)) (𝓝 (φ 0 - φ τ)) := by
    have hc0 : Continuous φ := hcont.comp (by unfold l5566_pt; fun_prop)
    exact ((hc0.tendsto 0).sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), φ ε - φ τ ≤ C * τ := by
    have : Set.Ioo (0 : ℝ) τ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hτ.1
    filter_upwards [this] with ε hε using hmv ε hε
  have := le_of_tendsto hlim hev
  have h0 : l5566_pt i (0 : ℝ) = 0 := by simp [l5566_pt]
  simpa [hφ, h0] using this

theorem negSpectral_grad_unbounded_proof (hd : 1 ≤ d) {s c : ℝ} (hs1 : -1 < s) (hs0 : s < 0)
    (hc : 0 < c) :
    ∀ C : ℝ, ∃ x : Torus d, x ≠ 0 ∧
      DifferentiableAt ℝ (Torus.lift (negSpectralKernel d s c)) (Torus.rep x) ∧
      C < ‖Torus.grad (negSpectralKernel d s c) x‖ := by
  intro C
  by_contra hcon
  push_neg at hcon
  set G := Torus.lift (negSpectralKernel d s c) with hG
  let i : Fin d := ⟨0, hd⟩
  have hpt : ∀ τ ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ G (l5566_pt i τ) ∧
      ‖fderiv ℝ G (l5566_pt i τ)‖ ≤ C := by
    intro τ hτ
    have hcos : Real.cos (2 * Real.pi * (l5566_pt i τ) i) ≠ 1 := by
      rw [l5566_pt_apply]
      intro h
      have hπ := Real.pi_pos
      have := (Real.cos_eq_one_iff_of_lt_of_lt (x := 2 * Real.pi * τ) (by nlinarith [hτ.1])
        (by nlinarith [hτ.2])).mp h
      nlinarith [hτ.1]
    have hdiff := l5566_differentiableAt hs0 hc i hcos
    refine ⟨hdiff, ?_⟩
    have hx0 : Torus.mk (l5566_pt i τ) ≠ 0 := by
      intro h
      have h1 := congrFun h i
      simp only [Torus.mk, l5566_pt_apply, Pi.zero_apply] at h1
      rw [AddCircle.coe_eq_zero_iff] at h1
      obtain ⟨n, hn⟩ := h1
      simp only [zsmul_eq_mul, mul_one] at hn
      have h2 : (0 : ℝ) < n := by rw [hn]; exact hτ.1
      have h3 : (n : ℝ) < 1 := by rw [hn]; exact hτ.2
      have h4 : (0 : ℤ) < n := by exact_mod_cast h2
      have h5 : n < (1 : ℤ) := by exact_mod_cast h3
      omega
    obtain ⟨n, hn⟩ := Torus.rep_mk (l5566_pt i τ)
    have hdiff' : DifferentiableAt ℝ G (Torus.rep (Torus.mk (l5566_pt i τ))) := by
      rw [hn]
      refine l5566_diffAt_shift G (Lattice.toEuc n) _ (fun z => ?_) hdiff
      have := Torus.lift_periodic (negSpectralKernel d s c) (z - Lattice.toEuc n) n
      simpa [hG] using this.symm
    have h1 := hcon _ hx0 hdiff'
    rw [NegHess.grad_mk_aux] at h1
    have : ‖gradient G (l5566_pt i τ)‖ = ‖fderiv ℝ G (l5566_pt i τ)‖ :=
      LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ (Euc d)).symm _
    rw [this] at h1
    exact h1
  have hlip := l5566_lipschitz_step (c := c) hs0 i C hpt
  -- choose M
  set K : ℝ := c * (4 * Real.pi * d) ^ (s - d) with hK
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hKpos : 0 < K := by
    have := Real.pi_pos
    positivity
  have hlim : Tendsto (fun M : ℕ => (M : ℝ) ^ (s + 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < s + 1)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM1, hM2⟩ := ((eventually_ge_atTop 1).and (hlim.eventually_gt_atTop (C / (4 * K)))).exists
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hτ : (1 / (4 * (M : ℝ))) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; linarith
  have h1 := l5566_lower hs0 hc hd i M hM1
  have h2 := hlip _ hτ
  have h3 : K * (M : ℝ) ^ s ≤ C * (1 / (4 * (M : ℝ))) := h1.trans h2
  have h4 : (M : ℝ) ^ (s + 1) = (M : ℝ) ^ s * M := Real.rpow_add_one hMpos.ne' s
  have h5 : K * (M : ℝ) ^ (s + 1) ≤ C / 4 := by
    rw [h4]
    have := mul_le_mul_of_nonneg_right h3 hMpos.le
    calc K * ((M : ℝ) ^ s * M) = K * (M : ℝ) ^ s * M := by ring
      _ ≤ C * (1 / (4 * (M : ℝ))) * M := this
      _ = C / 4 := by field_simp
  have h6 : C / 4 < K * (M : ℝ) ^ (s + 1) := by
    have := (div_lt_iff₀ (by positivity : 0 < 4 * K)).mp hM2
    nlinarith
  linarith

example := (@negSpectral_grad_unbounded_proof : type_of% @HRS.negSpectral_grad_unbounded)

end HRS.MC.L5566
