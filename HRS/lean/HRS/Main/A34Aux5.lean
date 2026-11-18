import HRS.Main.A34Aux4

/-!
# Packet A34, helper 5: coefficient discrepancy facts, density bounds, the functional moment
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

/-- The pieces of the coefficient discrepancy. -/
theorem a34_delta_facts (S : MainData d) (L : LimitCoeffs d) (m N : ℕ) (Rg : Regime)
    (ν₀ MB Λ VB : ℝ)
    (hAN : AdjointData S.s (m + 2) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N))
    (hAL : AdjointData S.s (m + 2) Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ) :
    0 ≤ S.coeffDiscrepancy L m N ∧
    (∀ r ∈ Set.Icc (0 : ℝ) S.T, Torus.cbNorm (m + 2) (S.ρ N r - L.ρ r) ≤ S.coeffDiscrepancy L m N) ∧
    |S.invβ N - L.invβ| ≤ S.coeffDiscrepancy L m N ∧
    |2 * S.qN N - 2 * L.invβstar| ≤ S.coeffDiscrepancy L m N ∧
    |S.AN N - L.A| ≤ S.coeffDiscrepancy L m N := by
  have hbdd : BddAbove (Set.range fun r : Set.Icc (0 : ℝ) S.T =>
      Torus.cbNorm (m + 2) (S.ρ N r - L.ρ r)) := by
    refine ⟨Λ + Λ, ?_⟩
    rintro _ ⟨r, rfl⟩
    have h1 := hAN.hμ.smooth r r.2
    have h2 := hAL.hμ.smooth r r.2
    have h1' : Torus.IsCk (m + 2) (S.ρ N r) := h1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 2 + 3))
    have h2' : Torus.IsCk (m + 2) (L.ρ r) := h2.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 2 + 3))
    refine (cbNorm_sub_le' (m + 2) _ _ h1' h2').trans (add_le_add ?_ ?_)
    · exact (HRS.PDE.cbNorm_mono' (by omega) _).trans (hAN.hμ.bound r r.2)
    · exact (HRS.PDE.cbNorm_mono' (by omega) _).trans (hAL.hμ.bound r r.2)
  have hsup0 : 0 ≤ ⨆ r : Set.Icc (0 : ℝ) S.T, Torus.cbNorm (m + 2) (S.ρ N r - L.ρ r) :=
    Real.iSup_nonneg fun r => Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have e : S.coeffDiscrepancy L m N = |S.invβ N - L.invβ| + |2 * S.qN N - 2 * L.invβstar| +
      |S.AN N - L.A| + ⨆ r : Set.Icc (0 : ℝ) S.T, Torus.cbNorm (m + 2) (S.ρ N r - L.ρ r) := rfl
  have a1 := abs_nonneg (S.invβ N - L.invβ)
  have a2 := abs_nonneg (2 * S.qN N - 2 * L.invβstar)
  have a3 := abs_nonneg (S.AN N - L.A)
  refine ⟨by rw [e]; positivity, fun r hr => ?_, by rw [e]; linarith, by rw [e]; linarith,
    by rw [e]; linarith⟩
  rw [e]
  have := le_ciSup hbdd ⟨r, hr⟩
  linarith

/-- `A33Rho` and the sup bound for a density path with `AdjointData` at a level `J > d/2`. -/
theorem a34_rho (J : ℕ) (hJd : (d : ℝ) / 2 < J) (Rg : Regime) (s MB Λ VB ν₀ T : ℝ)
    (D : DynData d) (ρ : ℝ → Torus d → ℝ) (hA : AdjointData s J Rg MB Λ VB D ν₀ T ρ) :
    A33Rho T ρ ∧ ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ r x| ≤ Λ := by
  refine ⟨⟨a33_rho_cont hA.hμ hJd hA.hT, fun r hr x => (hA.hμ.prob r hr).nonneg x,
    fun r hr => (hA.hμ.prob r hr).integral_one⟩, fun r hr x => ?_⟩
  exact (HRS.PDE.abs_le_cbNorm (J + 3) (ρ r) (hA.hμ.smooth r hr) x).trans (hA.hμ.bound r hr)

/-- First absolute moment of the random functional. -/
theorem a34_moment_abs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → (Torus d → ℝ) → ℝ} {m₀ : ℕ} {Cin : ℝ}
    (hη_meas : ∀ ψ : Torus d → ℝ, Measurable fun ω => η ω ψ)
    (hη_sm : ∀ ψ : Torus d → ℝ, MemSobolev (m₀ : ℝ) ψ → Continuous ψ →
      ∫⁻ ω, ENNReal.ofReal ((η ω ψ) ^ 2) ∂P ≤ ENNReal.ofReal (Cin ^ 2 * sobolevNorm (m₀ : ℝ) ψ ^ 2))
    {ψ : Torus d → ℝ} (hψ : MemSobolev (m₀ : ℝ) ψ) (hψc : Continuous ψ) :
    MemLp (fun ω => η ω ψ) 2 P ∧ ∫ ω, |η ω ψ| ∂P ≤ |Cin| * sobolevNorm (m₀ : ℝ) ψ := by
  have hm : Measurable fun ω => η ω ψ := hη_meas ψ
  have h2 := hη_sm ψ hψ hψc
  have hlt : ∫⁻ ω, ENNReal.ofReal ((η ω ψ) ^ 2) ∂P < ⊤ := h2.trans_lt ENNReal.ofReal_lt_top
  have hmem : MemLp (fun ω => η ω ψ) 2 P := by
    refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
    refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
    exact hlt
  refine ⟨hmem, ?_⟩
  have hint : Integrable (fun ω => (η ω ψ) ^ 2) P := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).1 hmem
  have hI : ∫ ω, (η ω ψ) ^ 2 ∂P ≤ Cin ^ 2 * sobolevNorm (m₀ : ℝ) ψ ^ 2 := by
    have := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => sq_nonneg _)
    rw [← this] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  refine (a33_integral_abs_le _ hmem).trans ?_
  calc Real.sqrt (∫ ω, (η ω ψ) ^ 2 ∂P) ≤ Real.sqrt ((|Cin| * sobolevNorm (m₀ : ℝ) ψ) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow, sq_abs]; exact hI
    _ = |Cin| * sobolevNorm (m₀ : ℝ) ψ :=
        Real.sqrt_sq (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))

theorem a34_isCk2 (J : ℕ) (hJ : mStar d ≤ J) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφ : MemSobolev (J : ℝ) φ) : Torus.IsCk 2 φ := by
  have hcm := (hsNormSq_coeffOf _ φ hφ).1
  have hJ' : (d : ℝ) / 2 + 2 < (J : ℝ) := by
    have h1 := a33_mStar_gt d
    have h2 : (mStar d : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  have hdm : (d : ℝ) / 2 < (J : ℝ) := by linarith [show (0 : ℝ) ≤ 2 by norm_num]
  have hs := summable_norm_of_memHs _ hdm _ hcm
  have hre : IsRealCoeff (coeffOf φ) := isRealCoeff_coeffOf φ (ClassicalAux.integrable_of_continuous hφc)
  obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) 2 (J : ℝ) (by exact_mod_cast hJ')
  have := (hC _ hcm hre).1
  rwa [toFun_coeffOf φ hφc hs] at this

theorem a34_prop_zero (hd : 1 ≤ d) (J : ℕ) (hJ : mStar d ≤ J) (Rg : Regime) (s MB Λ VB ν₀ T : ℝ)
    (D : DynData d) (ρ : ℝ → Torus d → ℝ) (hA : AdjointData s J Rg MB Λ VB D ν₀ T ρ)
    {φ : Torus d → ℝ} (hφc : Continuous φ) (hφ : MemSobolev (J : ℝ) φ) :
    propagator D ρ 0 0 φ = φ := by
  have hK : ClassicalAux.ConvKernelFacts d D.s := ClassicalAux.convKernelFacts hd D
  have hJ3 := ClassicalPart.three_le_mStar d
  have hV1 : Torus.IsCk 1 D.V :=
    ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ J + 3)) hA.hV.1
  have hμ1 : Torus.IsCk 1 (ρ 0) := ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ J + 3))
    (hA.hμ.smooth 0 ⟨le_rfl, hA.hT.le⟩)
  exact MFSemigroup.propagator_zero D hK hV1 ρ hμ1 (a34_isCk2 J hJ hφc hφ)

end HRS.A34
