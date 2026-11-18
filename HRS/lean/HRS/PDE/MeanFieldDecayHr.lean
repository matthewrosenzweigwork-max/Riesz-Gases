import HRS.PDE.MeanFieldDecayL2

/-!
# Decay of the finite-regularity mean-field solution, packet P7c (package MF-01)
(plan `MeanFieldDecayPlan.md`, §1 P7c)

* `exists_thermal_hK_bound`: the thermal density inherits the uniform `H^K` bound of the solutions
  (every finite partial sum of `w_K(k) |ρ̂β(k)|²` is a limit, as `t → ∞`, of the same partial sum
  for `ρ^t`, by the `L²` decay of `exists_l2_decay`).
* `finite_reg_decay`: Proposition 5.1, `O:eq:finite-decay`; interpolation between the `L²` decay and
  the bounded `H^K` norm.  The statement is *exactly* the type of `HRS.PDE.finite_reg_decay`
  (`HRS/PDE/MeanField.lean`), so the integrator closes the target by
  `exact HRS.PDE.MFDecay.finite_reg_decay hd s βm βp K V ρ₀ H`.

Statement check (`pp.parens`): neither statement contains an integral, so the `∫`-precedence trap
does not occur; both are proved exactly as in the plan.

Both theorems use `MFGlobal.finite_reg_uniform_bounds` (and `exists_l2_decay`, which uses
`MFGlobal.isRealCoeff_of_isMFSolutionHK`); `MFApriori.mf_apriori_bound_real_on` (AP7) is now proved,
so they are unconditional.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFDecay

open MFApriori

variable {d : ℕ}

/-! ### Section 1: the uniform `H^K` bound of the thermal density -/

/-- (C1) The thermal density inherits the uniform `H^K` bound of the solutions
(lower semicontinuity of finite partial sums along `t → ∞`). -/
theorem exists_thermal_hK_bound (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → Continuous ρβ → (∀ x, 0 < ρβ x) →
      MemSobolev K ρβ → hsNormSq K (coeffOf ρβ) ≤ B := by
  obtain ⟨c, C, hc, hunif⟩ := MFGlobal.finite_reg_uniform_bounds hd s βm βp K V ρ₀ H
  obtain ⟨C₀, κ, hC₀, hκ, hdec⟩ := exists_l2_decay hd s βm βp K V ρ₀ H
  refine ⟨C ^ 2, sq_nonneg _, ?_⟩
  intro β hβ ρβ hρβ hcont hpos hSob
  obtain ⟨ρc, hsol, -⟩ := MFGlobal.finite_reg_exists_unique hd s βm βp K V ρ₀ H β hβ
  have hb := hunif β hβ ρc hsol
  have hdec' := hdec β hβ ρc hsol ρβ hρβ hcont hpos hSob
  refine tsum_le_of_sum_le' (sq_nonneg _) fun S => ?_
  -- `t ↦ ∑_{k∈S} w_K(k) ‖ρc t k‖²` is bounded by `C²` for `t ≥ 0` and tends to the `ρβ`-sum
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ∑ k ∈ S, sobWeight (K : ℝ) k * ‖ρc t k‖ ^ 2 ≤ C ^ 2 := by
    intro t ht
    have hmem : MemHs (K : ℝ) (ρc t) := hsol.cont.1 t (Set.mem_Ici.2 ht)
    have h1 : ∑ k ∈ S, sobWeight (K : ℝ) k * ‖ρc t k‖ ^ 2 ≤ hsNormSq (K : ℝ) (ρc t) :=
      hmem.sum_le_tsum S fun k _ => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)
    have h2 : hsNorm (K : ℝ) (ρc t) ≤ C := (hb t ht).2
    have h3 : hsNorm (K : ℝ) (ρc t) ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    rw [hsNorm_sq'] at h3
    exact h1.trans h3
  have hexp : Tendsto (fun t : ℝ => C₀ * Real.exp (-κ * t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -κ * t) atTop atBot := by
      have := (tendsto_id.const_mul_atTop hκ : Tendsto (fun t : ℝ => κ * t) atTop atTop)
      have h2 := tendsto_neg_atTop_atBot.comp this
      refine h2.congr fun t => ?_
      simp [neg_mul]
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C₀
  have hcoord : ∀ k : Lattice d, Tendsto (fun t : ℝ => ρc t k) atTop (𝓝 (coeffOf ρβ k)) := by
    intro k
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun t : ℝ => Real.sqrt (C₀ * Real.exp (-κ * t))) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hexp
      simpa [Function.comp_def] using h
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hsq
    filter_upwards [eventually_ge_atTop 0] with t ht
    obtain ⟨hm0, hle⟩ := hdec' t ht
    have h1 : sobWeight 0 k * ‖(ρc t - coeffOf ρβ) k‖ ^ 2 ≤ hsNormSq 0 (ρc t - coeffOf ρβ) :=
      sobWeight_mul_sq_le_hsNormSq hm0 k
    rw [Aux.sobWeight_zero_aux, one_mul] at h1
    have h2 : ‖ρc t k - coeffOf ρβ k‖ ^ 2 ≤ C₀ * Real.exp (-κ * t) := by
      simpa using h1.trans hle
    calc ‖ρc t k - coeffOf ρβ k‖ = Real.sqrt (‖ρc t k - coeffOf ρβ k‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt h2
  have hlim : Tendsto (fun t : ℝ => ∑ k ∈ S, sobWeight (K : ℝ) k * ‖ρc t k‖ ^ 2) atTop
      (𝓝 (∑ k ∈ S, sobWeight (K : ℝ) k * ‖coeffOf ρβ k‖ ^ 2)) := by
    refine tendsto_finsetSum S fun k _ => ?_
    exact ((hcoord k).norm.pow 2).const_mul _
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨0, hbound⟩)

/-! ### Section 2: `H^r` decay by interpolation -/

/-- (C2) = the body of `finite_reg_decay` (verbatim conclusion). -/
theorem finite_reg_decay (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) :
    ∀ r : ℝ, 0 ≤ r → r < K → ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧
      ∀ β ∈ Set.Icc βm βp, ∀ ρc : ℝ → Coeff d, IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc →
      ∀ ρβ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρβ → Continuous ρβ →
        (∀ x, 0 < ρβ x) → MemSobolev K ρβ →
      ∀ t, 0 ≤ t → MemHs r (ρc t - coeffOf ρβ) ∧
        hsNorm r (ρc t - coeffOf ρβ) ≤ Cr * Real.exp (-cr * t) := by
  intro r hr0 hrK
  obtain ⟨c, C, hc, hunif⟩ := MFGlobal.finite_reg_uniform_bounds hd s βm βp K V ρ₀ H
  obtain ⟨C₀, κ, hC₀, hκ, hdec⟩ := exists_l2_decay hd s βm βp K V ρ₀ H
  obtain ⟨B, hB0, hB⟩ := exists_thermal_hK_bound hd s βm βp K V ρ₀ H
  have hKpos : (0 : ℝ) < K := lt_of_le_of_lt hr0 hrK
  set θ : ℝ := r / K with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hr0 hKpos.le
  have hθ1 : θ < 1 := (div_lt_one hKpos).2 hrK
  have hθr : (1 - θ) * 0 + θ * (K : ℝ) = r := by
    rw [hθ]; field_simp; ring
  set Cb : ℝ := C + Real.sqrt B with hCb
  set Q : ℝ := C₀ ^ (1 - θ) * (Cb ^ 2) ^ θ with hQ
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ Cb ^ 2 := sq_nonneg _
    positivity
  set cr : ℝ := κ * (1 - θ) / 2 with hcr
  have hcr0 : 0 < cr := by
    have : 0 < 1 - θ := by linarith
    positivity
  refine ⟨Real.sqrt Q + 1, cr, by positivity, hcr0, ?_⟩
  intro β hβ ρc hsol ρβ hρβ hcont hpos hSob t ht
  have hb := hunif β hβ ρc hsol
  obtain ⟨hZ0, hZle⟩ := hdec β hβ ρc hsol ρβ hρβ hcont hpos hSob t ht
  have hmt : MemHs (K : ℝ) (ρc t) := hsol.cont.1 t (Set.mem_Ici.2 ht)
  have hmβ : MemHs (K : ℝ) (coeffOf ρβ) := (ProdAux.memHs_of_memSobolev (K : ℝ) hSob).1
  have hZK : MemHs (K : ℝ) (ρc t - coeffOf ρβ) := Aux.memHs_sub hmt hmβ
  obtain ⟨hmr, hint⟩ := hsNormSq_interpolation 0 (K : ℝ) θ hθ0 hθ1.le (ρc t - coeffOf ρβ) hZ0 hZK
  rw [hθr] at hmr hint
  refine ⟨hmr, ?_⟩
  -- the `H^K` norm of the difference
  have hKd : hsNormSq (K : ℝ) (ρc t - coeffOf ρβ) ≤ Cb ^ 2 := by
    have h1 : hsNorm (K : ℝ) (ρc t - coeffOf ρβ) ≤ hsNorm (K : ℝ) (ρc t) + hsNorm (K : ℝ) (coeffOf ρβ) := by
      rw [sub_eq_add_neg]
      have := (Aux.memHs_add_le (K : ℝ) hmt (Aux.memHs_neg hmβ)).2
      rwa [Aux.hsNorm_neg] at this
    have h2 : hsNorm (K : ℝ) (coeffOf ρβ) ≤ Real.sqrt B :=
      Real.sqrt_le_sqrt (hB β hβ ρβ hρβ hcont hpos hSob)
    have h3 : hsNorm (K : ℝ) (ρc t - coeffOf ρβ) ≤ Cb := by
      have := (hb t ht).2
      linarith
    have h4 : hsNorm (K : ℝ) (ρc t - coeffOf ρβ) ^ 2 ≤ Cb ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
    rwa [hsNorm_sq'] at h4
  have hE0 : 0 ≤ C₀ * Real.exp (-κ * t) := by positivity
  have hZnn : 0 ≤ hsNormSq 0 (ρc t - coeffOf ρβ) := hsNormSq_nonneg' _ _
  have hKnn : 0 ≤ hsNormSq (K : ℝ) (ρc t - coeffOf ρβ) := hsNormSq_nonneg' _ _
  have h1 : hsNormSq 0 (ρc t - coeffOf ρβ) ^ (1 - θ) ≤ (C₀ * Real.exp (-κ * t)) ^ (1 - θ) :=
    Real.rpow_le_rpow hZnn hZle (by linarith)
  have h2 : hsNormSq (K : ℝ) (ρc t - coeffOf ρβ) ^ θ ≤ (Cb ^ 2) ^ θ :=
    Real.rpow_le_rpow hKnn hKd hθ0
  have h3 : hsNormSq r (ρc t - coeffOf ρβ) ≤ (C₀ * Real.exp (-κ * t)) ^ (1 - θ) * (Cb ^ 2) ^ θ :=
    hint.trans (mul_le_mul h1 h2 (Real.rpow_nonneg hKnn _) (Real.rpow_nonneg hE0 _))
  have h4 : (C₀ * Real.exp (-κ * t)) ^ (1 - θ) = C₀ ^ (1 - θ) * Real.exp (-(2 * cr) * t) := by
    rw [Real.mul_rpow hC₀.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    rw [hcr]; ring
  have h5 : hsNormSq r (ρc t - coeffOf ρβ) ≤ Q * Real.exp (-cr * t) ^ 2 := by
    refine h3.trans (le_of_eq ?_)
    rw [h4, hQ, ← Real.exp_nat_mul]
    have : -(2 * cr) * t = ((2 : ℕ) : ℝ) * (-cr * t) := by push_cast; ring
    rw [this]; ring
  have h6 : hsNorm r (ρc t - coeffOf ρβ) ≤ Real.sqrt Q * Real.exp (-cr * t) := by
    unfold hsNorm
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hQ0]
    exact h5
  have h7 : 0 ≤ Real.exp (-cr * t) := (Real.exp_pos _).le
  nlinarith

end HRS.PDE.MFDecay
