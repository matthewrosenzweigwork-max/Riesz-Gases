import HRS.PDE.MeanField
import HRS.PDE.MeanFieldDecayGap
import HRS.PDE.MeanFieldVelocity

/-!
# Q48b, part 1: the thermal density is a stationary solution of the mean-field equation

For a smooth positive thermal density `ρβ` (and smooth `V`), the constant path `ρ^t ≡ ρβ` is a global solution of
`O:eq:mf-finite` in `C([0,∞);H^K)` for every `K` (`IsMFSolutionHK`), the hypotheses `FiniteRegHyp` of Proposition 5.1 hold
with `ρ⁰ = ρβ`, `β₋ = β₊ = β`, and the density path `mfPath` of the constant coefficient path is the constant `ρβ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q48b

open HRS HRS.PDE

variable {d : ℕ}

theorem q48b_isCk_of_isSmooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (n : ℕ) :
    Torus.IsCk (n : WithTop ℕ∞) f :=
  HRS.PDE.MFSemigroup.isCk_nat_of_isSmooth hf n

theorem q48b_continuous_of_isSmooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  HRS.PDE.MFAux.continuous_of_isCk (q48b_isCk_of_isSmooth hf 1)

/-- The coefficient sequence of a smooth function is real and absolutely summable, and the function is recovered. -/
theorem q48b_toFun_coeffOf {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    IsRealCoeff (coeffOf f) ∧ (Summable fun k => ‖coeffOf f k‖) ∧ toFun (coeffOf f) = f := by
  have hc := q48b_continuous_of_isSmooth hf
  have hmem := HRS.PDE.MFSemigroup.memHs_of_isSmooth hf ((d : ℝ) / 2 + 3)
  have hsum : Summable fun k => ‖coeffOf f k‖ :=
    summable_norm_of_memHs _ (by linarith) _ hmem
  exact ⟨isRealCoeff_coeffOf f (HRS.PDE.MFThermalReg.integrable_of_cont hc), hsum,
    HRS.PDE.MFThermalReg.toFun_coeffOf hc hsum⟩

/-- Stationarity at the coefficient level: `ν Δρβ + Div(ρβ ∇(V + g*ρβ)) = 0` for the thermal density. -/
theorem q48b_rhs_zero (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hth : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρ : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) :
    mfRhsCoeff d s V β⁻¹ (coeffOf ρβ) = 0 := by
  set K : ℝ := (d : ℝ) / 2 + 3 with hK
  have hKd : (d : ℝ) / 2 + 2 < K := by rw [hK]; linarith
  have hKd0 : (d : ℝ) / 2 < K - 2 := by rw [hK]; linarith
  obtain ⟨hreal, hsum, heq⟩ := q48b_toFun_coeffOf hρ
  have hcont := q48b_continuous_of_isSmooth hρ
  have hmem : MemHs K (coeffOf ρβ) := HRS.PDE.MFSemigroup.memHs_of_isSmooth hρ K
  have hVK : MemHs K (coeffOf V) := HRS.PDE.MFSemigroup.memHs_of_isSmooth hV K
  have hV2 : Torus.IsCk 2 V := q48b_isCk_of_isSmooth hV 2
  have hρ1 : Torus.IsCk 1 ρβ := q48b_isCk_of_isSmooth hρ 1
  have hρ2 : Torus.IsCk 2 ρβ := q48b_isCk_of_isSmooth hρ 2
  -- the Gibbs relation
  have hW := HRS.PDE.MFApriori.isCk_two_Wpot hd s hs0 hsd K hKd V hV2 (coeffOf ρβ) hmem hreal
  have hW1 : Torus.IsCk 1 (HRS.PDE.MFApriori.Wpot d s V (coeffOf ρβ)) := hW.of_le (by norm_num)
  obtain ⟨hφ1, hder⟩ := HRS.PDE.MFAux.gibbs_partialDeriv V ρβ (convFun (periodicRiesz d s) ρβ) β
    hβ.ne' _ hρ1 (hV2.of_le (by norm_num)) hpos hth.2
  have hRiesz := HRS.PDE.MFDecay.riesz_coeffOf_eq_convFun hd s hs0 hsd K (by linarith) ρβ hcont hmem
  have hWeq : HRS.PDE.MFApriori.Wpot d s V (coeffOf ρβ) = fun y => V y + convFun (periodicRiesz d s) ρβ y := by
    funext y
    unfold HRS.PDE.MFApriori.Wpot
    rw [congrFun hRiesz y]
  have hdW : ∀ j y, Torus.partialDeriv j (HRS.PDE.MFApriori.Wpot d s V (coeffOf ρβ)) y =
      -β⁻¹ * (Torus.partialDeriv j ρβ y / ρβ y) := by
    intro j y
    rw [hWeq, HRS.PDE.MFApriori.partialDeriv_add j V _ (hV2.of_le (by norm_num)) hφ1 y, hder j y]
    ring
  have hflux : ∀ j, (fun y => ρβ y *
      Torus.partialDeriv j (HRS.PDE.MFApriori.Wpot d s V (coeffOf ρβ)) y) =
      fun y => (-β⁻¹) * Torus.partialDeriv j ρβ y := by
    intro j
    funext y
    rw [hdW j y]
    have := (hpos y).ne'
    field_simp
  have hF : ∀ x, toFun (mfRhsCoeff d s V β⁻¹ (coeffOf ρβ)) x = 0 := by
    intro x
    rw [HRS.PDE.MFApriori.toFun_mfRhsCoeff_eq' hd s hs0 hsd K hKd V hV2 hVK β⁻¹ _ hmem hreal x,
      heq, laplacian_eq_sum _ hρ2 x]
    simp_rw [hflux]
    have hpd : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j ρβ) := fun j => isCk_one_partialDeriv j _ hρ2
    have : ∀ j, Torus.partialDeriv j (fun y => (-β⁻¹) * Torus.partialDeriv j ρβ y) x =
        (-β⁻¹) * Torus.partialDeriv j (Torus.partialDeriv j ρβ) x := fun j =>
      HRS.PDE.MFApriori.partialDeriv_const_mul_of_isCk1 j (hpd j) _ x
    simp_rw [this]
    rw [← Finset.mul_sum]
    ring
  -- recover the coefficients
  obtain ⟨Cb, -, hCb⟩ := HRS.PDE.MFApriori.exists_rhs_bound hd s hs0 hsd K (by linarith) V hVK β⁻¹
  have hmemR := (hCb _ hmem).1
  have hsumR : Summable fun k => ‖mfRhsCoeff d s V β⁻¹ (coeffOf ρβ) k‖ :=
    summable_norm_of_memHs _ hKd0 _ hmemR
  have hrealR : IsRealCoeff (mfRhsCoeff d s V β⁻¹ (coeffOf ρβ)) :=
    HRS.PDE.MFApriori.isRealCoeff_mfRhsCoeff s V (HRS.PDE.MFThermalReg.integrable_of_cont
      (q48b_continuous_of_isSmooth hV)) _ _ hreal
  have h1 := coeffOf_toFun _ hrealR hsumR
  have h0 : toFun (mfRhsCoeff d s V β⁻¹ (coeffOf ρβ)) = fun _ => 0 := funext hF
  rw [h0] at h1
  rw [← h1]
  funext k
  simp [coeffOf, Torus.funFourierCoeff, UnitAddTorus.mFourierCoeff]


theorem q48b_mfPath_const (ρβ : Torus d → ℝ) (hρ : Torus.IsSmooth ρβ) :
    mfPath (fun _ : ℝ => coeffOf ρβ) = fun _ => ρβ := by
  funext t
  exact (q48b_toFun_coeffOf hρ).2.2

/-- The constant path `ρ^t ≡ ρβ` is a global `H^K` solution of the mean-field equation. -/
theorem q48b_isMFSolutionHK (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hth : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρ : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (K : ℕ) :
    IsMFSolutionHK d s V β⁻¹ K ρβ (fun _ => coeffOf ρβ) := by
  have h0 := q48b_rhs_zero hd s hs0 hsd β hβ V hV ρβ hth hρ hpos
  have hmem : MemHs (K : ℝ) (coeffOf ρβ) := HRS.PDE.MFSemigroup.memHs_of_isSmooth hρ K
  refine ⟨rfl, ⟨fun τ _ => hmem, fun τ₀ _ => ?_⟩, fun k t _ => ?_, fun k t _ => ?_⟩
  · simp only [sub_self]
    have : HRS.PDE.hsNorm (K : ℝ) (0 : Coeff d) = 0 := by
      unfold HRS.PDE.hsNorm HRS.PDE.hsNormSq
      simp
    simp only [this]
    exact tendsto_const_nhds
  · simp [h0]
  · simp [h0]

/-- `FiniteRegHyp` for the thermal density as initial datum (`β₋ = β₊ = β`). -/
theorem q48b_finiteRegHyp (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hth : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρ : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (K : ℕ) (hK : (d : ℝ) / 2 + 6 < K) :
    FiniteRegHyp d s β β K V ρβ := by
  have hcont := q48b_continuous_of_isSmooth hρ
  obtain ⟨x₀, -, hx₀⟩ := (isCompact_univ (X := Torus d)).exists_isMinOn Set.univ_nonempty
    hcont.continuousOn
  refine ⟨hs0, hsd, hβ, le_rfl, hK, q48b_isCk_of_isSmooth hV (K + 2), hth.1,
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hρ K, ρβ x₀, hpos x₀, fun x => hx₀ (Set.mem_univ x)⟩

end HRS.Uniform.Q48b
