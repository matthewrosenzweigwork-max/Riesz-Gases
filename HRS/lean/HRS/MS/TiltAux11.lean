import HRS.MS.TiltAux10

/-!
# S4.7 packet P6c: the uniform setup and the bias of the first marginal

`s47_setup`: one set of constants `(Cs, C, c, B_U, B_B, K_R, K_T)` for all `a ∈ [am,ap]`, `β ∈ [βm,βp]`, `γ ∈ [γm,γp]` and all `ε`
with `IsTiltData d s a β ψ ε`: the density `ρ₀ = (1+εψ) ρ_*` satisfies `S47Setup` (reference data `TRef` with `q = a β`
(`s47_tref`), static bundle, `R` and `T` bounds).  `s47_bias`: `|ν(f) - μ(f)| ≤ ‖f‖_∞ C_s δ_N` for the first marginal `ν`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

/-- ED15R: the uniform setup, with constants depending on `ε_*` but not on `(ε, ψ)`. -/
theorem s47_setup_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp γm γp : ℝ}
    (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm) (hap : am ≤ ap) (hβp : βm ≤ βp) (hγp : γm ≤ γp)
    (εstar : ℝ) :
    ∃ Cs C c BU BB KR KT : ℝ, 0 ≤ Cs ∧ 0 ≤ KR ∧ 0 ≤ KT ∧ ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp,
      ∀ γ ∈ Set.Icc γm γp, ∀ (ε : ℝ) (ψ : Euc d → ℝ), IsTiltData d s a β ψ ε →
        cbNorm (100 * d + 1001) (fun x => ε * ψ x) ≤ εstar →
        ∃ Bd : Euc d → Euc d, S47Setup d s (perturbedDensity (thermalDensity d s a β) ε ψ) (a * β) γ
          Cs C c BU BB KR KT Bd := by
  obtain ⟨C, c, BU, BB, hC0, hc0, hT⟩ := s47_tref_unif hd hs0 hsd ham hβm hap hβp εstar
  obtain ⟨Cs, hCs, hS⟩ := s47_static_all hd hs0 hsd hγm hγp hC0 hc0
  obtain ⟨KR, hKR, hR⟩ := s47_R_bound hd hs0 hsd C Cs hCs
  obtain ⟨KT, hKT, hTb⟩ := s47_T_bound hd hs0 hsd Cs hCs
  refine ⟨Cs, C, c, BU, BB, KR, KT, hCs, hKR, hKT, fun a ha β hβ γ hγ ε ψ hε hcb => ?_⟩
  obtain ⟨Bd, hTR⟩ := hT a β ha.1 ha.2 hβ.1 hβ.2 _ (Or.inr ⟨ε, ψ, hε, hcb, rfl⟩)
  refine ⟨Bd, hTR, hCs, fun N hN => hS hTR γ hγ N hN, hKR,
    fun N hN _ hχ _ hB2 => hR hTR (fun N hN => hS hTR γ hγ N hN) N hN hχ hB2, hKT,
    fun N hN _ hf _ hbd => hTb hTR (fun N hN => hS hTR γ hγ N hN) N hN hf hbd⟩

theorem s47_setup (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp γm γp : ℝ}
    (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm) (hap : am ≤ ap) (hβp : βm ≤ βp) (hγp : γm ≤ γp)
    (ψ : Euc d → ℝ) :
    ∃ Cs C c BU BB KR KT : ℝ, 0 ≤ Cs ∧ 0 ≤ KR ∧ 0 ≤ KT ∧ ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp,
      ∀ γ ∈ Set.Icc γm γp, ∀ ε : ℝ, IsTiltData d s a β ψ ε →
        ∃ Bd : Euc d → Euc d, S47Setup d s (perturbedDensity (thermalDensity d s a β) ε ψ) (a * β) γ
          Cs C c BU BB KR KT Bd := by
  obtain ⟨εstar, hε⟩ := HRS.MS.S48.s48_tilt_cb_star (d := d) ψ
  obtain ⟨Cs, C, c, BU, BB, KR, KT, h1, h2, h3, h⟩ :=
    s47_setup_unif hd hs0 hsd ham hβm hγm hap hβp hγp εstar
  exact ⟨Cs, C, c, BU, BB, KR, KT, h1, h2, h3, fun a ha β hβ γ hγ ε hε' =>
    h a ha β hβ γ hγ ε ψ hε' (hε s a β ε hε')⟩

/-- `|ν(f) - μ(f)| ≤ ‖f‖_∞ C_s δ_N`: the bias of the first marginal (the `L²(μ)` bound `‖dν/dμ - 1‖ ≤ C_s δ_N`). -/
theorem s47_bias {s : ℝ} {ρ : Euc d → ℝ} {γ Cs : ℝ} {N : ℕ} (hρ : IsProbDensity ρ)
    (hS : S47Static d s ρ γ Cs N) {f : Euc d → ℝ} (hf : Measurable f) {Bf : ℝ}
    (hBf : ∀ x, |f x| ≤ Bf) :
    |pair (s47_nu d s ρ γ N) f - pair (withDensityReal ρ) f| ≤ Bf * (Cs * HRS.deltaN d s N) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0)
  obtain ⟨φN, hφNm, hνeq, hφNb, hφN2, hφNn⟩ := hS.marg
  have hCs : 0 ≤ Cs := (hφNb 0).1.trans (hφNb 0).2
  set μ := withDensityReal ρ with hμdef
  have hf2 : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable Bf
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBf x)
  have hνf : pair (s47_nu d s ρ γ N) f = ∫ x, φN x * f x ∂μ := by
    have hνeq' : s47_nu d s ρ γ N = μ.withDensity (fun x => ENNReal.ofReal (φN x)) := hνeq
    unfold pair
    rw [hνeq', integral_withDensity_eq_integral_toReal_smul hφNm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hφNb _).1]
  have hφf : Integrable (fun x => φN x * f x) μ :=
    Integrable.of_bound ((hφNm.mul hf).aestronglyMeasurable) (Cs * Bf)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφNb x).1]
        exact mul_le_mul (hφNb x).2 (hBf x) (abs_nonneg _) hCs)
  have hfi : Integrable f μ := hf2.integrable one_le_two
  have hd0 : pair (s47_nu d s ρ γ N) f - pair μ f = ∫ x, (φN x - 1) * f x ∂μ := by
    rw [hνf]; unfold pair
    rw [← integral_sub hφf hfi]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hd0]
  have hg1 : Integrable (fun x => |φN x - 1|) μ := (hφN2.integrable one_le_two).abs
  calc |∫ x, (φN x - 1) * f x ∂μ| ≤ ∫ x, |(φN x - 1) * f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, Bf * |φN x - 1| ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) (hg1.const_mul _)
          (Filter.Eventually.of_forall fun x => by
            show |(φN x - 1) * f x| ≤ Bf * |φN x - 1|
            rw [abs_mul]; nlinarith [abs_nonneg (φN x - 1), hBf x])
    _ = Bf * ∫ x, |φN x - 1| ∂μ := integral_const_mul _ _
    _ ≤ Bf * (Cs * HRS.deltaN d s N) :=
        mul_le_mul_of_nonneg_left ((s45_l1_le_l2 hφN2).trans hφNn) hBf0

end S47

end
