import HRS.PDE.MeanFieldDecayHr
import HRS.PDE.MeanFieldAdjointFrozen

/-!
# V-uniform thermal `H^K` bound and frozen data (packet EVE1 of `docs/MAIN_E_EVU_PLAN.md`)

* `thermal_hK_of_bound` is a copy of `HRS.PDE.MFDecay.exists_thermal_hK_bound`
  (`HRS/PDE/MeanFieldDecayHr.lean:38`) with the uniform constant `C` of the `H^K` bound of the
  solutions supplied as the hypothesis `hb` (instead of obtained from
  `MFGlobal.finite_reg_uniform_bounds`). The conclusion is `hsNormSq K (coeffOf ρβ) ≤ C ^ 2`.
  The qualitative per-`V` facts (`finite_reg_exists_unique`, `exists_l2_decay`) are used unchanged.

* `frozenHyp_of_bounds` builds `HRS.PDE.MFAdjoint.FrozenHyp` directly (no dynamics): for fixed
  `d s βm βp` and `n K` with `d/2 + n < K`, there is `Cn ≥ 0` (depending only on `d n K`) such that
  for all `Bv lam B`, `V`, `ρβ` with `Torus.IsCk n V`, `Torus.cbNorm n V ≤ Bv`, a thermal density
  `ρβ` at `β ∈ [βm, βp]` that is continuous, lies in `H^K`, is bounded below by `lam > 0` and has
  `hsNormSq K (coeffOf ρβ) ≤ B`, the frozen data hold with `Λ₀ = max Bv (Cn * √B)`.
  The `C^n` bound for `ρβ` comes from `toFun_isCk_le` applied to `coeffOf ρβ` (the `H^K` bound).
  The original `finiteReg_hypotheses` (`HRS/PDE/MeanFieldAdjointWiring.lean:73`) is bypassed.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

open HRS.PDE
open MFDecay MFApriori

namespace HRS.ME.EVU

variable {d : ℕ}

/-- (C1, hypothesis form) A copy of `HRS.PDE.MFDecay.exists_thermal_hK_bound`: the uniform `H^K`
bound `C` of the solutions (for `t ≥ 0`) is a hypothesis `hb`; the thermal density then satisfies
`hsNormSq K (coeffOf ρβ) ≤ C ^ 2`. -/
theorem thermal_hK_of_bound (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (C : ℝ)
    (hb : ∀ β ∈ Set.Icc βm βp, ∀ ρc : ℝ → Coeff d, IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc →
      ∀ t, 0 ≤ t → HRS.PDE.hsNorm (K : ℝ) (ρc t) ≤ C) :
    ∀ β ∈ Set.Icc βm βp, ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → Continuous ρβ → (∀ x, 0 < ρβ x) →
      MemSobolev K ρβ → hsNormSq (K : ℝ) (coeffOf ρβ) ≤ C ^ 2 := by
  obtain ⟨C₀, κ, hC₀, hκ, hdec⟩ := MFDecay.exists_l2_decay hd s βm βp K V ρ₀ H
  intro β hβ ρβ hρβ hcont hpos hSob
  obtain ⟨ρc, hsol, -⟩ := MFGlobal.finite_reg_exists_unique hd s βm βp K V ρ₀ H β hβ
  have hbC := hb β hβ ρc hsol
  have hdec' := hdec β hβ ρc hsol ρβ hρβ hcont hpos hSob
  refine tsum_le_of_sum_le' (sq_nonneg _) fun S => ?_
  -- `t ↦ ∑_{k∈S} w_K(k) ‖ρc t k‖²` is bounded by `C²` for `t ≥ 0` and tends to the `ρβ`-sum
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ∑ k ∈ S, sobWeight (K : ℝ) k * ‖ρc t k‖ ^ 2 ≤ C ^ 2 := by
    intro t ht
    have hmem : MemHs (K : ℝ) (ρc t) := hsol.cont.1 t (Set.mem_Ici.2 ht)
    have h1 : ∑ k ∈ S, sobWeight (K : ℝ) k * ‖ρc t k‖ ^ 2 ≤ hsNormSq (K : ℝ) (ρc t) :=
      hmem.sum_le_tsum S fun k _ => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)
    have h2 : HRS.PDE.hsNorm (K : ℝ) (ρc t) ≤ C := hbC t ht
    have h3 : HRS.PDE.hsNorm (K : ℝ) (ρc t) ^ 2 ≤ C ^ 2 :=
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

/-- (T2) Frozen data with `ρβ` bounded in `H^K`: `FrozenHyp` is built directly from the
hypotheses, the `C^n` bound of `ρβ` coming from `toFun_isCk_le` (`Cn`, depending only on `d n K`). -/
theorem frozenHyp_of_bounds (s βm βp : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (n K : ℕ) (hnK : (d : ℝ) / 2 + n < K) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ (Bv lam B : ℝ) (V ρβ : Torus d → ℝ) (β : ℝ), β ∈ Set.Icc βm βp →
      Torus.IsCk n V → Torus.cbNorm n V ≤ Bv →
      IsThermalDensity (periodicRiesz d s) V β ρβ → Continuous ρβ → MemSobolev K ρβ →
      0 < lam → (∀ x, lam ≤ ρβ x) → 0 ≤ B → hsNormSq (K : ℝ) (coeffOf ρβ) ≤ B →
      MFAdjoint.FrozenHyp d s n βp⁻¹ βm⁻¹ lam (max Bv (Cn * Real.sqrt B)) β V ρβ := by
  have hKd : (d : ℝ) / 2 < K := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) n (K : ℝ) hnK
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro Bv lam B V ρβ β hβ hV hVB hth hρC hSob hlam0 hlow hB0 hBsq
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hβp : 0 < βp := lt_of_lt_of_le hβpos hβ.2
  have hMK : MemSobolev (K : ℝ) ρβ := hSob
  have hMKc : MemHs (K : ℝ) (coeffOf ρβ) := (hsNormSq_coeffOf (K : ℝ) ρβ hMK).1
  have hreal0 : IsRealCoeff (coeffOf ρβ) := isRealCoeff_coeffOf ρβ (hMK.1.integrable one_le_two)
  have hsumB : Summable fun k => ‖coeffOf ρβ k‖ := summable_norm_of_memHs (K : ℝ) hKd _ hMKc
  have hρβ_eq : toFun (coeffOf ρβ) = ρβ := toFun_coeffOf ρβ hρC hsumB
  obtain ⟨hCK, hCb⟩ := hC (coeffOf ρβ) hMKc hreal0
  rw [hρβ_eq] at hCK hCb
  -- the `H^K` norm of `ρβ` is at most `√B`
  have hsB : HRS.PDE.hsNorm (K : ℝ) (coeffOf ρβ) ≤ Real.sqrt B := Real.sqrt_le_sqrt hBsq
  have hn0 : 0 ≤ HRS.PDE.hsNorm (K : ℝ) (coeffOf ρβ) := Real.sqrt_nonneg _
  have hCn : Torus.cbNorm n ρβ ≤ max C 0 * Real.sqrt B :=
    hCb.trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) hn0).trans
      (mul_le_mul_of_nonneg_left hsB (le_max_right C 0)))
  have hν : β⁻¹ ∈ Set.Icc βp⁻¹ βm⁻¹ := ⟨inv_anti₀ hβpos hβ.2, inv_anti₀ hβm hβ.1⟩
  exact ⟨hs0, hsd, hβpos, inv_pos.mpr hβp, hν, hV, hVB.trans (le_max_left _ _), hth, hCK,
    hCn.trans (le_max_right _ _), hlam0, hlow⟩

end HRS.ME.EVU
