import HRS.Whole.Basic

/-!
# S111: S11.1 `r2_tensor_relaxation` and `r2_cross_density_exists` (plan, and the Riesz reduction)

Worker S111, namespace `HRS.MS.TensRel`, helper prefix `s111_`.  The full per-row plan, with the verdicts on truth and the
blocking inputs, is in the report of the worker; this docstring records the part that matters for the next attempt.

## Verdict (STEP 1)

Both frozen statements read as TRUE and non-vacuous, but neither can be proved from the merged library, and neither fits
the 5,000-line stop rule.  No frozen statement was edited.

### `r2_cross_density_exists` (Window.lean:544), startable, estimate 3k-4k lines, high risk

The densities are `χ_i^r = ρ_β · h_i^r`, `h_i^r ∈ L²(μ)` the Riesz representer of
`ψ' ↦ ℓ(ψ') := linearGaussianCov C β⁻¹ (susceptibilityCov .. γ) r (u+τ_i) ψ' φ_i` on the osc tests.  Pieces:
1. (this file, proved) `s111_density_of_l2_bound`: a linear functional on a subspace of `L²(μ)`-functions with
   `|ℓ ψ| ≤ C ‖ψ‖_{L²(μ)}` is `ψ ↦ ∫ ψ χ` with `χ/ρ ∈ L²(μ)` and `ψ χ` integrable (Hahn-Banach + Riesz).
2. linearity of `ψ ↦ propagatorW C 0 r ψ` on osc tests (uniqueness of the classical adjoint solution; `ul_adjoint_fixed_viscosity`
   gives uniqueness only in the `UlClosure` evolution class, the bridge `IsUlBackwardEvolution -> IsClassicalAdjointW` is that of
   `OrbIdTie`/`orbit_maximal_identification`), and of `responseInverse` (uniqueness of `IsResponse`);
   ~600-900 lines.
3. the bound `|Cov(Z^r ψ', Z^t φ)| ≤ C_φ ‖ψ'‖_{L²(μ)}` for osc tests `ψ'`, uniformly in `r ∈ [0,u+T]`: positivity of the two
   forms (`K ≥ 0`: `wr13c_Kmu_nonneg`, `Psd.log_energy_nonneg`) gives Cauchy-Schwarz down to the variance
   `Var Z^r(ψ') = C₀(Uψ',Uψ') + noiseCovW`; the variance is `R_β(ψ',ψ') + C₀-difference(Uψ',Uψ')`, which needs the
   whole-space fluctuation-dissipation (Lyapunov) identity for classical adjoint solutions (differentiate
   `⟨f_s, R f_s⟩`, integration by parts against the Gaussian-type weight `ρ_β`, `euc_thermal_gaussian_bounds_proof`) and an
   `L²(μ)` energy bound for `‖U^{0,r}ψ'‖`; ~2000-3000 lines.  Neither identity is in a proved row
   (S2.1(i) `S21Main` is still open).
4. membership `osc test ∈ L²(μ)`, assembly over `i, r`; ~300 lines.

### `r2_tensor_relaxation` (Window.lean:560), not startable

(a) is true (rate `e^{-2 lam u / β}` from `K ≥ 0`, `ν = β⁻¹`, and the Poincare constant) but needs, beyond item 2-3 above:
the sharp `L²_0(μ)` decay `‖U_t‖ ≤ C e^{-(lam/β) t}` and the same for `∂_t U_t` (`t ≥ 1`) for the classical propagator
(`mov_linear` only gives a non-explicit rate `c` in oscillator norms for the forward semigroup; `mov_global_adjoint_*`
(S6.7) and `weighted_adjoint_decay` (S8.3) are still `stated`), a path-space (`C([0,T];B_m)`) second-moment comparison
of two Gaussian window laws that are given only through finite-dimensional laws (existence of a coupling, or a tensor-level
argument), the identity `C_γ(t) - R_β = U^*(R_γ - R_β)U`, and the Hermite/Sobolev-in-time summation: about 6k-9k lines.
(b) is blocked: `κu, κβ` are arbitrary `projTensor`s pinned only on products of evaluations, so a bound on
`‖κu - κβ‖_π` (a sup over ALL bounded trilinear forms) needs a representation of `κ` by a Bochner/BV integral of
elementary tensors with projective-norm control.  That representation is the content of S10.1-S10.4 / S2.1(iii)
(`r2_path_interpolation`, `r2_window_orbits`, `r2_window_errors` are `stated`), plus the approximation-property argument
that a `projTensor` is determined by its values on `∏ ev_{τ_i}(φ_i)`.  The torus analogue (`docs/MC_E214_TENSOR_PLAN.md`)
costs 10k+ lines with `winJ_compare` alone at 2.5k-5k.

### `r2_two_parameter_edgeworth` (S11.2)

Needs `r2_tensor_relaxation` (the constants `c, C`); only the conditional N3 (`SuppNSpec`) is startable, and it needs a
Banach-valued Gaussian covariance comparison on `C([0,T];B_m)` (the merged A.31 is Euclidean): ~1.5k lines, not started.
-/

noncomputable section

open MeasureTheory

namespace HRS.MS.TensRel

open HRS

variable {d : ℕ}

/-- The linear map `S → L²(μ)`, `ψ ↦ [ψ]`. -/
def s111_toLp {μ : Measure (Euc d)} (S : Submodule ℝ (Euc d → ℝ)) (hS : ∀ ψ ∈ S, MemLp ψ 2 μ) :
    S →ₗ[ℝ] Lp ℝ 2 μ where
  toFun ψ := (hS ψ ψ.2).toLp ψ
  map_add' a b := by
    have h := MemLp.toLp_add (hS a a.2) (hS b b.2)
    refine Eq.trans ?_ h
    exact MemLp.toLp_congr _ _ (by simp)
  map_smul' c a := by
    have h := MemLp.toLp_const_smul (μ := μ) (p := 2) c (hS a a.2)
    refine Eq.trans ?_ h
    exact MemLp.toLp_congr _ _ (by simp)

/-- **Riesz reduction.**  Let `μ = ρ dx` with `ρ > 0` measurable and `μ` finite, `S` a space of `L²(μ)` functions and `ℓ` a linear
functional on `S` bounded by `C ‖ψ‖_{L²(μ)}`.  Then there is a density `χ` with `χ/ρ ∈ L²(μ)` such that `ψ χ` is Lebesgue
integrable and `∫ ψ χ dx = ℓ ψ` for every `ψ ∈ S` (`∫ ψ χ dx = ∫ ψ (χ/ρ) dμ`). -/
theorem s111_density_of_l2_bound {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ : ∀ x, 0 < ρ x)
    (S : Submodule ℝ (Euc d → ℝ)) (hS : ∀ ψ ∈ S, MemLp ψ 2 (HRS.Whole.withDensityReal ρ)) (ℓ : S →ₗ[ℝ] ℝ)
    (C : ℝ) (hℓ : ∀ ψ : S, |ℓ ψ| ≤ C * ‖s111_toLp S hS ψ‖) :
    ∃ χ : Euc d → ℝ, MemLp (fun x => χ x / ρ x) 2 (HRS.Whole.withDensityReal ρ) ∧
      ∀ ψ : S, Integrable (fun x => (ψ : Euc d → ℝ) x * χ x) ∧ ∫ x, (ψ : Euc d → ℝ) x * χ x = ℓ ψ := by
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set T := s111_toLp (μ := μ) S hS with hT
  -- ℓ vanishes on the kernel of T
  have hker : LinearMap.ker T ≤ LinearMap.ker ℓ := by
    intro ψ hψ
    have h0 : T ψ = 0 := hψ
    have := hℓ ψ
    rw [h0, norm_zero, mul_zero] at this
    exact abs_nonpos_iff.mp this
  -- ℓ' on the range of T
  let ℓ' : LinearMap.range T →ₗ[ℝ] ℝ :=
    ((LinearMap.ker T).liftQ ℓ hker).comp (LinearMap.quotKerEquivRange T).symm.toLinearMap
  have hℓ' : ∀ ψ : S, ℓ' ⟨T ψ, ⟨ψ, rfl⟩⟩ = ℓ ψ := by
    intro ψ
    simp only [ℓ', LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image T ψ ⟨ψ, rfl⟩]
    rfl
  have hbd : ∀ y : LinearMap.range T, ‖ℓ' y‖ ≤ |C| * ‖y‖ := by
    rintro ⟨y, ψ, rfl⟩
    rw [Real.norm_eq_abs, hℓ' ψ]
    calc |ℓ ψ| ≤ C * ‖T ψ‖ := hℓ ψ
      _ ≤ |C| * ‖T ψ‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
  let ℓc : StrongDual ℝ (LinearMap.range T) := ℓ'.mkContinuous |C| hbd
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range T) ℓc
  set h : Lp ℝ 2 μ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm g with hh
  have hinner : ∀ ψ : S, ∫ x, (ψ : Euc d → ℝ) x * h x ∂μ = ℓ ψ := by
    intro ψ
    have h1 : inner ℝ h (T ψ) = ℓ ψ := by
      rw [hh, InnerProductSpace.toDual_symm_apply]
      have := hg ⟨T ψ, ⟨ψ, rfl⟩⟩
      rw [this]
      simp only [ℓc, LinearMap.mkContinuous_apply]
      exact hℓ' ψ
    rw [← h1, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    have hae : (T ψ : Euc d → ℝ) =ᵐ[μ] (ψ : Euc d → ℝ) := MemLp.coeFn_toLp (hS ψ ψ.2)
    filter_upwards [hae] with x hx
    rw [hx]
    simp [mul_comm]
  have hfin : ∀ᵐ x ∂(volume : Measure (Euc d)), ENNReal.ofReal (ρ x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hmeas : Measurable fun x => ENNReal.ofReal (ρ x) := hρm.ennreal_ofReal
  refine ⟨fun x => ρ x * h x, ?_, fun ψ => ?_⟩
  · have : (fun x => ρ x * h x / ρ x) = (h : Euc d → ℝ) := by
      funext x
      field_simp [(hρ x).ne']
    rw [this]
    exact Lp.memLp h
  · have hint : Integrable (fun x => (ψ : Euc d → ℝ) x * h x) μ :=
      MemLp.integrable_mul (hS ψ ψ.2) (Lp.memLp h)
    have hint' : Integrable (fun x => (ψ : Euc d → ℝ) x * (ρ x * h x)) volume := by
      have := (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (Euc d))) hmeas hfin
        (g := fun x => (ψ : Euc d → ℝ) x * h x)).1 hint
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ x).le]
      ring
    refine ⟨hint', ?_⟩
    rw [← hinner ψ]
    have e := integral_withDensity_eq_integral_toReal_smul hmeas hfin
      (fun x => (ψ : Euc d → ℝ) x * h x)
    refine Eq.trans ?_ e.symm
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ x).le]
    ring

end HRS.MS.TensRel
