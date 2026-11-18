import HRS.ME.EVUE2
import HRS.ME.Fourier417A

/-!
# Chunk E, packet F1: V-uniform coefficient decay, the `hsNorm` glue, and `GenHyp` (namespace `HRS.ME.FamU`)

Originals (copied with the convention of `docs/MAIN_E_FAMU_PLAN.md`):
* `HRS.Uniform.Q54.coeff_decay_V` (`HRS/Uniform/Q54Aux21.lean:28`) becomes `coeff_decay_V_unifV`.
  The constant `BV = cbNorm n V * c1 + cbNorm n V` is replaced by `max (Bf n) 0 * (c1 + 1)`.
* New lemma `hsNorm_coeffOf_le_cbNorm` (no original): for every real index `m`,
  `hsNorm m (coeffOf V) ≤ C * cbNorm ⌈m⌉₊ V` for smooth `V`. It combines
  `HRS.PDE.ClassicalPart.memHs_coeffOf_cbNorm` at the integer `⌈m⌉₊` with
  `HRS.ME.fourierTailA_hs_mono` (monotonicity of `hsNorm` in the index, from `m ≤ ⌈m⌉₊`).
* `HRS.MD.EQEvoUnif.eqevo_genhyp_unif` (`HRS/MD/EQEvoUnif.lean:97`) becomes `eqevo_genhyp_unifV`,
  using `HRS.ME.EVU.eqevo_thermal_unifV` with `Bv := Bf (K+2)` and `coeff_decay_V_unifV` at `n := K+1`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.ME.FamU

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.Uniform.Q54

variable {d : ℕ}

/-- **F1a (V-uniform copy of `coeff_decay_V`).** The fixed data are `n` and `Bf`; the constant `BV`
is chosen before `V`, and the bound holds for every smooth `V` with `cbNorm j V ≤ Bf j` for all `j`. -/
theorem coeff_decay_V_unifV (n : ℕ) (Bf : ℕ → ℝ) :
    ∃ BV : ℝ, 0 ≤ BV ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ m : Lattice d, ‖coeffOf V m‖ ≤ BV * Lattice.jp m ^ (-(n : ℝ)) := by
  have hc10 : 0 ≤ ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n := by positivity
  have hB0 : 0 ≤ max (Bf n) 0 := le_max_right _ _
  refine ⟨max (Bf n) 0 * ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n + max (Bf n) 0,
    by positivity, fun V hV hb m => ?_⟩
  have hVn : Torus.IsCk (n : WithTop ℕ∞) V := HRS.MD.EQEvoUnif.eqevo_isCk_nat hV n
  have hc0 : Torus.cbNorm n V ≤ max (Bf n) 0 := (hb n).trans (le_max_left _ _)
  have hc00 : 0 ≤ Torus.cbNorm n V := R2Aux.cbNorm_nonneg' n V
  by_cases hm : m = 0
  · subst hm
    have h1 : ‖coeffOf V 0‖ ≤ Torus.cbNorm n V := by
      rw [coeffOf_eq_fcoef]
      exact Torus.norm_fcoef_le_of_bound (fun x => R2Aux.abs_le_cbNorm hVn x) 0
    rw [jp_zero, Real.one_rpow, mul_one]
    linarith [mul_nonneg hB0 hc10]
  · have h1 := coeffOf_decay V hVn m hm
    have hj := Torus.jp_pos m
    have e : Lattice.jp m ^ (-(n : ℝ)) = (Lattice.jp m ^ n)⁻¹ := by
      rw [Real.rpow_neg hj.le, Real.rpow_natCast]
    rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖coeffOf V m‖ * Lattice.jp m ^ n
        ≤ Torus.cbNorm n V * ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n := h1
      _ ≤ max (Bf n) 0 * ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n :=
          mul_le_mul_of_nonneg_right hc0 hc10
      _ ≤ max (Bf n) 0 * ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n + max (Bf n) 0 := by linarith

/-- **F1b (new).** For every real index `m`, the Sobolev norm of the coefficients of a smooth `V`
is bounded by `C * cbNorm ⌈m⌉₊ V`, with `C` fixed before `V`. -/
theorem hsNorm_coeffOf_le_cbNorm (m : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V →
      HRS.PDE.hsNorm m (coeffOf V) ≤ C * Torus.cbNorm ⌈m⌉₊ V := by
  refine ⟨Real.sqrt (((1 : ℝ) + d) ^ ⌈m⌉₊), Real.sqrt_nonneg _, fun V hV => ?_⟩
  obtain ⟨hmem, hb⟩ := HRS.PDE.ClassicalPart.memHs_coeffOf_cbNorm ⌈m⌉₊ V
    (HRS.MD.EQEvoUnif.eqevo_isCk_nat hV ⌈m⌉₊)
  have h1 : HRS.PDE.hsNorm m (coeffOf V) ≤ HRS.PDE.hsNorm (⌈m⌉₊ : ℝ) (coeffOf V) :=
    (HRS.ME.fourierTailA_hs_mono (Nat.le_ceil m) hmem).2
  have h2 : HRS.PDE.hsNorm (⌈m⌉₊ : ℝ) (coeffOf V) ≤
      Real.sqrt (((1 : ℝ) + d) ^ ⌈m⌉₊) * Torus.cbNorm ⌈m⌉₊ V := by
    unfold HRS.PDE.hsNorm
    calc Real.sqrt (HRS.PDE.hsNormSq (⌈m⌉₊ : ℝ) (coeffOf V))
        ≤ Real.sqrt (((1 : ℝ) + d) ^ ⌈m⌉₊ * Torus.cbNorm ⌈m⌉₊ V ^ 2) := Real.sqrt_le_sqrt hb
      _ = _ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (R2Aux.cbNorm_nonneg' _ V)]
  exact h1.trans h2

/-- **F1c (V-uniform copy of `eqevo_genhyp_unif`).** The fixed data are `d s βm βp hs0 hsd hβm hββ`,
the bound sequence `Bf`, and the level `K` with `6 d + 30 ≤ K`; the constants `Bμ, BV` come before `V`. -/
theorem eqevo_genhyp_unifV (hd : 2 ≤ d) (s βm βp : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) (K : ℕ) (hK : 6 * d + 30 ≤ K) :
    ∃ Bμ BV : ℝ, 0 ≤ Bμ ∧ 0 ≤ BV ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V →
      (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
        IsThermalDensity (periodicRiesz d s) V β ρβ →
          GenHyp d s (K : ℝ) 1 Bμ BV (mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Λ₀, c₀, lam, Lam, B, -, -, hB0, hmain⟩ :=
    HRS.ME.EVU.eqevo_thermal_unifV hd s βm βp hs0 hsd hβm hββ (Bf (K + 2)) 0 K (by omega)
  obtain ⟨BV, hBV0, hBV⟩ := coeff_decay_V_unifV (d := d) (K + 1) Bf
  refine ⟨Real.sqrt B, BV, Real.sqrt_nonneg _, hBV0, fun V hV hb β hβ ρβ hρβ => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hVc : Continuous V :=
    HRS.PDE.continuous_of_isCk (by exact_mod_cast HRS.MD.EQEvoUnif.eqevo_isCk_nat hV 1)
  obtain ⟨hpos, hc⟩ := HRS.Q41.q41_thermal_pos_cont hd hs0 hsd hβ0 hVc hρβ
  have hSob : MemSobolev (K : ℝ) ρβ :=
    HRS.PDE.MFThermalAssembly.thermal_memSobolev_all hd1 s hs0 hsd K V
      (by exact_mod_cast HRS.MD.EQEvoUnif.eqevo_isCk_nat hV (K + 2)) β hβ0 ρβ hρβ hc hpos
  have hHs : MemHs (K : ℝ) (coeffOf ρβ) := (ProdAux.memHs_of_memSobolev (K : ℝ) hSob).1
  have hB' : hsNormSq (K : ℝ) (coeffOf ρβ) ≤ B :=
    (hmain V hV (hb (K + 2)) β hβ ρβ hρβ).2.2
  have hsn : HRS.PDE.hsNorm (K : ℝ) (coeffOf ρβ) ≤ Real.sqrt B := Real.sqrt_le_sqrt hB'
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i j
    show |(-1 : Matrix (Fin d) (Fin d) ℝ) i j| ≤ 1
    rw [Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  · intro m
    have h1 := MFApriori.norm_coeff_le_hsNorm (K : ℝ) hHs m
    rw [sqrt_sobWeight_eq] at h1
    have hj := Torus.jp_pos m
    have e : Lattice.jp m ^ (-(K : ℝ)) = (Lattice.jp m ^ (K : ℝ))⁻¹ := Real.rpow_neg hj.le _
    rw [e, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hj _)]
    exact h1.trans hsn
  · intro m
    have := hBV V hV hb m
    simpa [mfData] using this

end HRS.ME.FamU
