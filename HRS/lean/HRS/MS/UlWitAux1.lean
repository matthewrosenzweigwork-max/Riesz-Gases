import HRS.MS.UlNormAux3
import HRS.MS.UlocCb
import HRS.MS.SuppU4Aux1
import HRS.Whole.Adjoint

/-!
# UL-W (part 1): the non-vacuity witness for `UlAdjointInput`; plan and approximation of the data

## Why S5.1 is not a witness (decision M4)

`UlAdjointInput θ C T j K` (frozen, `HRS/Whole/Adjoint.lean:142`) quantifies over EVERY `φ ∈ C^{j'}`,
`j' = j + 1 + ⌈d/2⌉`, with `ulNormE j' θ φ < ⊤` (for instance `φ = sin x₁`), and asserts
`(∃ f, IsClassicalAdjointW C t φ f) ∧ MemCb j (propagatorW C r t φ) ∧ cbNorm j (propagatorW C r t φ) ≤ K ‖φ‖_{j'}`.
The data class of S5.1 (`ul_adjoint_fixed_viscosity_proof`, UL5) is `UlClosure k θ`, functions tending to a constant at
infinity in the `ul` sense.  Moreover `propagatorW` is `Classical.choose`, so the claim also needs UNIQUENESS of classical
adjoint solutions for the coefficient (F-CAU).

## The witness proved in `UlWitTie.lean`

`ul_adjoint_input_witness` (statement in `UlWitTie.lean`): `d ≥ 2`, `0 ≤ s < d`, `θ` a `IsUlCutoff`.  There is `j₀` such
that for every `j ≥ j₀`, `T ≥ 0`, `ν > 0`, symmetric `Q`, any matrix `M`, any `c₀ ∈ ℝ^d`, any Schwartz probability density
`ρ`, there is `K` with `UlAdjointInput θ ((⟨s, M, quadV Q c₀, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) T j K`.
This is the coefficient `νΔ + (M∇g*ρ - Qx - c₀)·∇ - Div g*(ρ Mᵀ∇·)` along the STATIONARY path `ρ_t ≡ ρ` (the form in which
`UlAdjointInput` is consumed by `WholeSetup.adjoint`, `AdjointDecayHyp.adjoint` and, with `c` constant in `t`, by S5.7).
Honest limits (documented, not hidden): `ν > 0` only (S5.1 needs `ν > 0`; `K` depends on `ν⁻¹`, `T`, `Q`, `M`, `ρ`, so the
uniformity in `ν ∈ [0, ν_*]` required by `WholeSetup` is NOT delivered); autonomous `ρ` (S5.1 is autonomous); `j ≥ j₀`
(for `j = 0` and even `d` the predicate is expected to be false, not proved here: `H^{1+d/2}_ul` does not embed in `C²_b`, so
for some admissible `φ` no classical solution, which needs `D²φ` bounded at `r = t`, exists).  No junk-value trap: `ν > 0`, `d ≥ 2`, `ρ` a Schwartz probability
density (so every Bochner integral of `convGradConvW` is a genuine integral), the solution is constructed (never `0`).

## Plan (cheapest honest route, sizes are the measured ones)

1. (`UlWitAux1`, this file) Approximation of the data: for `φ ∈ C^k` with `ulNormE k θ φ < ⊤`, `k > d/2`, there are
   `ψ_n ∈ C_c^∞` with `ulNormE k θ ψ_n ≤ C ulNormE k θ φ` (C independent of `n`, `φ`) and `ψ_n → φ` pointwise:
   `ψ_n = ζ_n · (η_n ⋆ φ)`, `ζ_n = χ(·/(n+1))`, `η_n` a normalised bump of radius `→ 0`.  Uses `ulocNormE_avg_le`
   (averaging of translates), `ulocNormE_mul_cb` (cutoff), `ul_equiv`, and `uloc_embedding_cb_proof` (boundedness of `φ`).
   `ψ_n ∈ C_c^∞ ⊂ UlClosure k θ` trivially.
2. (`UlWitAux2`) Existence by compactness.  S5.1 gives `u_n` (classical, closure valued) with `ulNormE k θ (u_n r) ≤ C ‖ψ_n‖`,
   hence (by `ulClosure_cb`) uniform bounds in `C_b^{j}` and, from the equation, `|∂_r u_n| ≤ B(1+|x|)` uniformly.  The S55M
   machinery (`s55m_ex`: diagonal extraction, `s55m_dl`: derivative convergence) gives a pointwise limit `g` with `D^i u_n →
   D^i g`, `i ≤ 4`; the equation passes to the limit by dominated convergence (`s55m_gen_tendsto`: the nonlocal term with the
   cancellation convention converges because `ρ` is Schwartz); the result is `IsClassicalAdjointW` with terminal datum `φ`
   (copies of `s55m_cont_gen`, `s55m_limit_ftc`, `s55m_limit` for an explicit coefficient instead of a `WholeSetup`).
3. (`UlWitTie`) Uniqueness: `Fcau.propagatorW_eq` for `D.coeff (fun _ => ρ)` (regime R1 if `s ≤ d-2`, else R3 with `ν₀ = ν`;
   `CoeffHypRd` for a constant Schwartz path; `VHypRd (quadV Q c₀)`), so `propagatorW = g`.  Bound: `ulocNormE_lsc` for the
   pointwise limit, then `uloc_embedding_cb_proof` (the limit is continuous, so it equals the `C_b^j` representative).
   Existence of the S5.1 solutions for the coefficient `fixedViscosityCoeff s M Q ν c ρ`, `c = M∇g*ρ - c₀`
   (`IsSmoothBounded c` from `tail_conv`), which equals `D.coeff (fun _ => ρ)`.

Frozen statements are only used (never restated); the witness is a NEW statement and needs no coverage row.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace HRS.MS.UlW

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.Ul

variable {d : ℕ}

/-! ### Scaled cutoffs -/

/-- `ζ_n = χ(·/(n+1))`. -/
def ulwZ (χ : Euc d → ℝ) (n : ℕ) : Euc d → ℝ := fun x => χ ((((n : ℝ) + 1)⁻¹) • x)

theorem ulw_inv_le_one (n : ℕ) : (((n : ℝ) + 1)⁻¹) ≤ 1 := by
  apply inv_le_one_of_one_le₀
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem ulw_Z_smooth {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (n : ℕ) : ContDiff ℝ ∞ (ulwZ χ n) :=
  hχ.1.comp (contDiff_const_smul _)

theorem ulw_Z_cs {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (n : ℕ) : HasCompactSupport (ulwZ χ n) :=
  hχ.2.1.comp_smul (c := (((n : ℝ) + 1)⁻¹)) (by positivity)

theorem ulw_Z_tendsto {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (x : Euc d) :
    Tendsto (fun n => ulwZ χ n x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
  symm
  apply hχ.2.2.2.2
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ‖x‖ ≤ (n : ℝ) + 1 := by
    have := Nat.le_ceil ‖x‖
    have h2 : (⌈‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

theorem ulw_Z_deriv {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ) (n : ℕ) (i : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (ulwZ χ n) x‖ ≤ ‖iteratedFDeriv ℝ i χ ((((n : ℝ) + 1)⁻¹) • x)‖ := by
  unfold ulwZ
  rw [iteratedFDeriv_comp_const_smul _ (contDiff_infty.1 hχ i), norm_smul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have h0 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ i χ ((((n : ℝ) + 1)⁻¹) • x)‖ := norm_nonneg _
  have h1 : ((((n : ℝ) + 1)⁻¹) ^ i) ≤ 1 := pow_le_one₀ (by positivity) (ulw_inv_le_one n)
  nlinarith

theorem ulw_Z_cb {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (k n : ℕ) :
    MemCb k (ulwZ χ n) ∧ cbNorm k (ulwZ χ n) ≤ cbNorm k χ := by
  have hbd : ∀ j, BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ j χ z‖) := fun j =>
    u4_bdd j ⟨hχ.1, hχ.2.1⟩
  have hle : ∀ j x, ‖iteratedFDeriv ℝ j (ulwZ χ n) x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j χ z‖ := fun j x =>
    (ulw_Z_deriv hχ.1 n j x).trans (le_ciSup (hbd j) _)
  refine ⟨⟨(ulw_Z_smooth hχ n).of_le (by exact_mod_cast le_top), fun j _ => ⟨⨆ z, ‖iteratedFDeriv ℝ j χ z‖, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hle j x
  · unfold cbNorm
    exact Finset.sum_le_sum fun j _ => ciSup_le fun x => hle j x

/-! ### Mollification -/

/-- A sequence of bump functions with radius `1/(n+1)`. -/
def ulwBump (d : ℕ) (n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]
    nlinarith⟩

/-- `η_n ⋆ φ`. -/
def ulwMol (d : ℕ) (n : ℕ) (φ : Euc d → ℝ) : Euc d → ℝ :=
  ((ulwBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ)

theorem ulw_mol_smooth {φ : Euc d → ℝ} (hφ : Continuous φ) (n : ℕ) : ContDiff ℝ ∞ (ulwMol d n φ) :=
  (ulwBump d n).hasCompactSupport_normed.contDiff_convolution_left _ (ulwBump d n).contDiff_normed
    (hφ.locallyIntegrable)

theorem ulw_mol_tendsto {φ : Euc d → ℝ} (hφ : Continuous φ) (x : Euc d) :
    Tendsto (fun n => ulwMol d n φ x) atTop (𝓝 (φ x)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure (Euc d)))
    (φ := ulwBump d) (l := atTop) (g := φ) ?_ hφ x
  · exact h
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The mollifier is an average of translates over a probability measure. -/
theorem ulw_mol_avg {φ : Euc d → ℝ} (hm : Measurable φ) (n : ℕ) :
    ∃ μ : Measure (Euc d), IsProbabilityMeasure μ ∧ ∀ x, ulwMol d n φ x = ∫ y, φ (x + y) ∂μ := by
  set η : Euc d → ℝ := (ulwBump d n).normed volume with hη
  have hη0 : ∀ t, 0 ≤ η t := fun t => (ulwBump d n).nonneg_normed t
  have hηc : Continuous η := ((ulwBump d n).contDiff_normed (n := 0)).continuous
  have hint : Integrable η volume := hηc.integrable_of_hasCompactSupport (ulwBump d n).hasCompactSupport_normed
  set ν : Measure (Euc d) := volume.withDensity (fun t => ENNReal.ofReal (η t)) with hν
  have : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hη0),
      (ulwBump d n).integral_normed, ENNReal.ofReal_one]
  refine ⟨ν.map Neg.neg, inferInstance, fun x => ?_⟩
  rw [integral_map (f := fun y : Euc d => φ (x + y)) measurable_neg.aemeasurable
    ((hm.comp (measurable_const_add x)).aestronglyMeasurable),
    hν, integral_withDensity_eq_integral_toReal_smul₀]
  · unfold ulwMol
    rw [convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, sub_eq_add_neg]
    rw [ENNReal.toReal_ofReal (hη0 t)]
  · exact (ENNReal.measurable_ofReal.comp hηc.measurable).aemeasurable
  · exact Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top


/-! ### Data with finite `ul` norm are bounded -/

theorem ulw_bdd_of_ul {k : ℕ} (hk : (d : ℝ) / 2 < k) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) {φ : Euc d → ℝ}
    (hc : Continuous φ) (hfin : ulNormE k θ φ < ⊤) : ∃ B : ℝ, ∀ x, |φ x| ≤ B := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  have hfin' : ulocNormE k χ φ < ⊤ :=
    lt_of_le_of_lt (hequ φ).2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  obtain ⟨C1, h1⟩ := HRS.MS.UlocCb.uloc_embedding_cb_proof k 0 (by simpa using hk) χ hχ
  obtain ⟨v, hvae, hv, -⟩ := h1 φ hfin'
  have hvφ : v = φ := (Continuous.ae_eq_iff_eq volume hv.1.continuous hc).1 hvae
  subst hvφ
  obtain ⟨B, hB⟩ := hv.2 0 le_rfl
  refine ⟨B, fun x => ?_⟩
  have := hB ⟨x, rfl⟩
  simpa [norm_iteratedFDeriv_zero] using this

/-! ### Approximation of the data by `C_c^∞` functions -/

/-- **Approximation of the data.**  For a continuous `φ` with finite `H^k_ul` norm, `k > d/2`, there are `C_c^∞`
functions `ψ_n`, bounded in `H^k_ul` by `Cap ‖φ‖_{H^k_ul}` (`Cap` independent of `n` and of `φ`), converging pointwise to `φ`. -/
theorem ulw_approx_data (k : ℕ) (hk : (d : ℝ) / 2 < k) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) :
    ∃ Cap : ℝ, 0 < Cap ∧ ∀ φ : Euc d → ℝ, Continuous φ → ulNormE k θ φ < ⊤ →
      ∃ ψ : ℕ → Euc d → ℝ, (∀ n, ContDiff ℝ ∞ (ψ n) ∧ HasCompactSupport (ψ n)) ∧
        (∀ n, ulNormE k θ (ψ n) ≤ ENNReal.ofReal Cap * ulNormE k θ φ) ∧
        ∀ x, Tendsto (fun n => ψ n x) atTop (𝓝 (φ x)) := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨Cm, hCm, hmul⟩ := ulocNormE_mul_cb k χ
  set Kχ : ℝ := cbNorm k χ with hKχ
  have hK0 : 0 ≤ Kχ := u4_cbNorm_nonneg k χ
  refine ⟨Ce * (Cm * Kχ) * Ce + 1, by positivity, fun φ hφ hfin => ?_⟩
  obtain ⟨B, hB⟩ := ulw_bdd_of_ul hk θ hθ hφ hfin
  refine ⟨fun n x => ulwZ χ n x * ulwMol d n φ x, fun n => ⟨(ulw_Z_smooth hχ n).mul (ulw_mol_smooth hφ n), ?_⟩,
    fun n => ?_, fun x => ?_⟩
  · have h : HasCompactSupport (ulwZ χ n * ulwMol d n φ) := (ulw_Z_cs hχ n).mul_right
    exact h
  · obtain ⟨μ, hμ, hmol⟩ := ulw_mol_avg hφ.measurable n
    have havg : ulocNormE k χ (ulwMol d n φ) ≤ ulocNormE k χ φ := by
      have e : ulwMol d n φ = fun x => ∫ y, φ (x + y) ∂μ := funext hmol
      rw [e]
      exact ulocNormE_avg_le k χ hχ μ φ hφ.measurable B hB
    obtain ⟨hZm, hZc⟩ := ulw_Z_cb hχ k n
    have h1 := hmul (ulwZ χ n) hZm (ulwMol d n φ)
    have h2 : ENNReal.ofReal (Cm * cbNorm k (ulwZ χ n)) ≤ ENNReal.ofReal (Cm * Kχ) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hZc hCm.le)
    have h3 : ulocNormE k χ φ ≤ ENNReal.ofReal Ce * ulNormE k θ φ := (hequ φ).2
    calc ulNormE k θ (fun x => ulwZ χ n x * ulwMol d n φ x)
        ≤ ENNReal.ofReal Ce * ulocNormE k χ (fun x => ulwZ χ n x * ulwMol d n φ x) := (hequ _).1
      _ ≤ ENNReal.ofReal Ce * (ENNReal.ofReal (Cm * Kχ) * (ENNReal.ofReal Ce * ulNormE k θ φ)) := by
          gcongr
          exact h1.trans (by gcongr; exact havg.trans h3)
      _ = ENNReal.ofReal (Ce * (Cm * Kχ) * Ce) * ulNormE k θ φ := by
          have e : ENNReal.ofReal (Ce * (Cm * Kχ) * Ce) =
              ENNReal.ofReal Ce * (ENNReal.ofReal Cm * ENNReal.ofReal Kχ) * ENNReal.ofReal Ce := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCe.le,
              ENNReal.ofReal_mul hCm.le]
          rw [e, ENNReal.ofReal_mul hCm.le]
          ring
      _ ≤ ENNReal.ofReal (Ce * (Cm * Kχ) * Ce + 1) * ulNormE k θ φ := by
          gcongr
          linarith
  · have := (ulw_Z_tendsto hχ x).mul (ulw_mol_tendsto hφ x)
    simpa using this

end HRS.MS.UlW
