import HRS.PDE.MeanFieldAdjointWiring
import HRS.PDE.MeanFieldAdjointSmoothing
import HRS.PDE.MeanFieldDecayGap
import HRS.PDE.MeanFieldDecayHr
import HRS.PDE.MeanFieldThermal
import HRS.PDE.MeanField
import HRS.PDE.Hadamard
import HRS.Sections.Q41Aux14
import HRS.Uniform.Q54Aux21

/-!
# EQP7C: uniform-in-`β` bounds for the frozen (stationary) data, packets P7.1-P7.3

* `eqevo_thermal_unif` (P7.1): for every level `n` and every `K` large enough, one choice of
  `Λ₀, c₀, lam, Lam, B` (fixed before `β` and `ρβ`) makes every thermal density `ρβ` at `β ∈ [βm, βp]`
  a `FrozenHyp` at level `n`, with `lam ≤ ρβ ≤ Lam` and `‖ρβ‖²_{H^K} ≤ B`.
* `eqevo_genhyp_unif` (P7.2): uniform `GenHyp` constants for the frozen density.
* `eqevo_adjdata_frozen` (P7.3): uniform `AdjointData` at the frozen level for every `T > 0`.

Continuity and positivity of thermal densities come from `HRS.Q41.q41_thermal_pos_cont`, so the
statements quantify over all `IsThermalDensity` solutions.  The reference datum for the
`FiniteRegHyp` is the constant density `ρ₀ ≡ 1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MD.EQEvoUnif

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.Uniform.Q54

variable {d : ℕ}

/-- `C^k` regularity (for a natural `k`) of a smooth potential. -/
theorem eqevo_isCk_nat {V : Torus d → ℝ} (hV : Torus.IsSmooth V) (k : ℕ) :
    Torus.IsCk (k : WithTop ENat) V := by
  have h : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Torus.lift V) := hV
  exact h.of_le (by exact_mod_cast le_top)

/-- The constant density `1` lies in `H^K`. -/
theorem eqevo_memSobolev_one (K : ℕ) : MemSobolev (K : ℝ) (fun _ : Torus d => (1 : ℝ)) := by
  refine memSobolev_of_memHs (K : ℝ) _ (memLp_const 1) ?_
  unfold MemHs
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  have hk0 : k ≠ 0 := by simpa using hk
  simp [HRS.PDE.coeffOf_const, deltaCoeff, hk0]

/-- The constant density `1` is a probability density on the torus. -/
theorem eqevo_isProb_one : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
  ⟨fun _ => zero_le_one, measurable_const, by simp⟩

/-- The reference datum `ρ₀ ≡ 1` satisfies `FiniteRegHyp` at every level `K ≥ 6d + 30`. -/
theorem eqevo_finiteRegHyp_one (hd : 2 ≤ d) (s βm βp : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (K : ℕ)
    (hK : 6 * d + 30 ≤ K) : FiniteRegHyp d s βm βp K V (fun _ : Torus d => (1 : ℝ)) := by
  have hKr : (6 * (d : ℝ) + 30) ≤ K := by exact_mod_cast hK
  have hdr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨hs0, hsd, hβm, hββ, by linarith, by exact_mod_cast eqevo_isCk_nat hV (K + 2),
    eqevo_isProb_one, eqevo_memSobolev_one K, ⟨1, one_pos, fun _ => le_refl _⟩⟩

/-- **P7.1.** Uniform frozen-data bounds: the constants are fixed before `β` and `ρβ`. -/
theorem eqevo_thermal_unif (hd : 2 ≤ d) (s βm βp : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) :
    ∀ (n K : ℕ), 2 * n + 6 * d + 30 ≤ K →
      ∃ Λ₀ c₀ lam Lam B : ℝ, 0 < c₀ ∧ 0 < lam ∧ 0 ≤ B ∧
        ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
          IsThermalDensity (periodicRiesz d s) V β ρβ →
            FrozenHyp d s n βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρβ ∧
              (∀ x, lam ≤ ρβ x ∧ ρβ x ≤ Lam) ∧ hsNormSq (K : ℝ) (coeffOf ρβ) ≤ B := by
  intro n K hK
  have hd1 : 1 ≤ d := by omega
  have hKr : 2 * (n : ℝ) + 6 * (d : ℝ) + 30 ≤ K := by exact_mod_cast hK
  have hdr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hVc : Continuous V := HRS.PDE.continuous_of_isCk (by exact_mod_cast eqevo_isCk_nat hV 1)
  have H0 : FiniteRegHyp d s βm βp K V (fun _ : Torus d => (1 : ℝ)) :=
    eqevo_finiteRegHyp_one hd s βm βp hs0 hsd hβm hββ V hV K (by omega)
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hmain⟩ :=
    finiteReg_hypotheses hd1 s βm βp K V (fun _ : Torus d => (1 : ℝ)) H0 (n + d + 5)
      (by push_cast; linarith) (by omega)
  obtain ⟨lam, Lam, hlam, hbd⟩ := HRS.PDE.MFDecay.exists_thermal_bounds hd1 s hs0 hsd βm βp hβm hββ V hVc
  obtain ⟨B, hB0, hB⟩ := HRS.PDE.MFDecay.exists_thermal_hK_bound hd1 s βm βp K V (fun _ : Torus d => (1 : ℝ)) H0
  refine ⟨Λ₀, c₀, lam, Lam, B, hc₀, hlam, hB0, fun β hβ ρβ hρβ => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨hpos, hc⟩ := HRS.Q41.q41_thermal_pos_cont hd hs0 hsd hβ0 hVc hρβ
  obtain ⟨ρc, hsol, -⟩ :=
    HRS.PDE.finite_reg_exists_unique hd1 s βm βp K V (fun _ : Torus d => (1 : ℝ)) H0 β hβ
  have hF := (hmain β hβ ρc hsol ρβ hρβ hc hpos).1
  have hSob : MemSobolev (K : ℝ) ρβ :=
    HRS.PDE.MFThermalAssembly.thermal_memSobolev_all hd1 s hs0 hsd K V (by exact_mod_cast eqevo_isCk_nat hV (K + 2)) β hβ0 ρβ
      hρβ hc hpos
  exact ⟨FrozenHyp.mono (by omega) hF, fun x => hbd β hβ ρβ hρβ hc hpos x,
    hB β hβ ρβ hρβ hc hpos hSob⟩

/-- **P7.2.** Uniform `GenHyp` constants for every thermal density (`Bμ = sqrt B` from P7.1). -/
theorem eqevo_genhyp_unif (hd : 2 ≤ d) (s βm βp : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) :
    ∀ K : ℕ, 6 * d + 30 ≤ K → ∃ Bμ BV : ℝ, 0 ≤ Bμ ∧ 0 ≤ BV ∧
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
        IsThermalDensity (periodicRiesz d s) V β ρβ →
          GenHyp d s (K : ℝ) 1 Bμ BV (mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ := by
  intro K hK
  obtain ⟨Λ₀, c₀, lam, Lam, B, -, -, hB0, hmain⟩ :=
    eqevo_thermal_unif hd s βm βp hs0 hsd hβm hββ V hV 0 K (by omega)
  have hd1 : 1 ≤ d := by omega
  have hVc : Continuous V := HRS.PDE.continuous_of_isCk (by exact_mod_cast eqevo_isCk_nat hV 1)
  obtain ⟨BV, hBV0, hBV⟩ :=
    coeff_decay_V V (K + 1) (eqevo_isCk_nat hV (K + 1))
  refine ⟨Real.sqrt B, BV, Real.sqrt_nonneg _, hBV0, fun β hβ ρβ hρβ => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨hpos, hc⟩ := HRS.Q41.q41_thermal_pos_cont hd hs0 hsd hβ0 hVc hρβ
  have hSob : MemSobolev (K : ℝ) ρβ :=
    HRS.PDE.MFThermalAssembly.thermal_memSobolev_all hd1 s hs0 hsd K V (by exact_mod_cast eqevo_isCk_nat hV (K + 2)) β hβ0 ρβ
      hρβ hc hpos
  have hHs : MemHs (K : ℝ) (coeffOf ρβ) := (ProdAux.memHs_of_memSobolev (K : ℝ) hSob).1
  have hB' : hsNormSq (K : ℝ) (coeffOf ρβ) ≤ B := (hmain β hβ ρβ hρβ).2.2
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
    have := hBV m
    simpa [mfData] using this

/-- **P7.3.** Uniform frozen `AdjointData` at level `m` (from P7.1 at level `m + 3`). -/
theorem eqevo_adjdata_frozen (hd : 2 ≤ d) (s βm βp : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (m K : ℕ)
    (hK : 2 * (m + 3) + 6 * d + 30 ≤ K) :
    ∃ Λ₀ c₀ : ℝ, 0 < c₀ ∧
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
        IsThermalDensity (periodicRiesz d s) V β ρβ →
          ∀ T : ℝ, 0 < T →
            AdjointData s m (frozenRegime d s c₀) 1 Λ₀ Λ₀
              (mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) βp⁻¹ T (fun _ => ρβ) := by
  obtain ⟨Λ₀, c₀, lam, Lam, B, hc₀, -, -, h⟩ :=
    eqevo_thermal_unif hd s βm βp hs0 hsd hβm hββ V hV (m + 3) K hK
  refine ⟨Λ₀, c₀, hc₀, fun β hβ ρβ hρβ T hT => ?_⟩
  exact adjointData_frozen_level m (h β hβ ρβ hρβ).1 (βp⁻¹) T hT

end HRS.MD.EQEvoUnif
