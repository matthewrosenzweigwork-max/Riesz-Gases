import HRS.MC.S7FCW2Aux
import HRS.MC.L2C6a
import HRS.MC.L2C7
import HRS.MC.L2C0
import HRS.Sections.Sec7Setting
import HRS.MC.SEdgeVocab
import HRS.MC.Sec7Vocab

/-!
# S7FCW2: relocated proofs of `s7_FC_C1_coeffs` and `s7_FC_C3_version` (FC-C1, FC-C3)

Relocated proofs of the frozen statements of `HRS/MC/S7FCPlan.lean` (namespace `HRS.MC.Sec7.FCPlan`); the statements
are copied verbatim here, the tie file is `HRS/MC/S7FCW2Tie.lean`.

* C1 (`s7_FC_C1_coeffs_proof`): `K := max C 0` with `C` from `HRS.MC.L2C6a.l2c6a_proof` (uniform `L²` bound of
  `η^t(φ)`); `ModeCovBound` from `HRS.MC.L2C7.l2c7_proof`; `HasFiniteGaussianCoeffs` from the Gaussian noise
  decomposition (`S7FCW2_fgc`).
* C3 (`s7_FC_C3_version_proof`): the a.s. continuity of `η` on every `[0,n]` gives a measurable full-measure set
  `Bad`-complement `G` on which all paths are continuous; `η' t ω := 1_G(ω) η(t ∨ 0, ω)` is continuous in `t` for
  every `ω` and measurable in `ω` for every `t`, hence jointly measurable by
  `measurable_uncurry_of_continuous_of_measurable`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7FCW2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec

variable {d : ℕ}

theorem s7_FC_C1_coeffs_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (η : ℝ → Ω' → NegSobolev d r),
        IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η → ∀ t : ℝ, 0 ≤ t →
          HasFiniteGaussianCoeffs P' (η t) ∧ ModeCovBound P' (η t) K := by
  obtain ⟨C, hC⟩ := HRS.MC.L2C6a.l2c6a_proof R r hr
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro Ω' _ P' _ η hη t ht
  obtain ⟨Y₀, hY, hLin⟩ := hη
  have hcov : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      MemLp (fun ω => NegSobolev.eval (η t ω) φ) 2 P' ∧
        ∫ ω, NegSobolev.eval (η t ω) φ ^ 2 ∂P' ≤ max C 0 * HRS.PDE.l2NormSq φ := by
    intro φ hφ
    obtain ⟨h1, h2⟩ := hC P' Y₀ η hY hLin t ht φ hφ
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (integral_nonneg fun x => sq_nonneg _))⟩
  refine ⟨?_, HRS.MC.L2C7.l2c7_proof P' r (η t) (max C 0) hcov⟩
  exact S7FCW2_fgc P' R.D R.ρ r R.D.invβ t _ Y₀ η hY (hLin t) ht
    (fun φ hφ => (HRS.MC.L2C0.l2c0_proof R φ hφ 0 t le_rfl ht).1)

theorem s7_FC_C3_version_proof (R : Regime d) (r : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    ∃ η' : ℝ → Ω' → NegSobolev d r, Measurable (Function.uncurry η') ∧
      (∀ t : ℝ, 0 ≤ t → η' t =ᵐ[P'] η t) ∧
      ∀ (ω : Ω') (T : ℝ), ContinuousOn (fun t => η' t ω) (Set.Icc 0 T) := by
  obtain ⟨Y₀, -, hLin⟩ := hη
  have hae : ∀ᵐ ω ∂P', ∀ n : ℕ, ContinuousOn (fun t => η t ω) (Set.Icc 0 (n : ℝ)) :=
    ae_all_iff.2 fun n => (hLin (n : ℝ)).cont
  obtain ⟨Bad, hBadm, hsub, hBad0⟩ : ∃ Bad : Set Ω', MeasurableSet Bad ∧
      {ω | ¬ ∀ n : ℕ, ContinuousOn (fun t => η t ω) (Set.Icc 0 (n : ℝ))} ⊆ Bad ∧ P' Bad = 0 :=
    ⟨toMeasurable P' _, measurableSet_toMeasurable _ _, subset_toMeasurable _ _,
      by rw [measure_toMeasurable]; exact ae_iff.1 hae⟩
  have hGae : ∀ᵐ ω ∂P', ω ∈ Badᶜ :=
    ae_iff.2 (measure_mono_null (fun ω hω => by simpa using hω) hBad0)
  have hgood : ∀ ω ∈ Badᶜ, ∀ n : ℕ, ContinuousOn (fun t => η t ω) (Set.Icc 0 (n : ℝ)) :=
    fun ω hω => by
      by_contra h
      exact hω (hsub h)
  have hcontω : ∀ ω : Ω', Continuous fun t : ℝ => Badᶜ.indicator (fun ω => η (max t 0) ω) ω := by
    intro ω
    by_cases hω : ω ∈ Badᶜ
    · simp only [Set.indicator_of_mem hω]
      have hC : ContinuousOn (fun t => η t ω) (Set.Ici 0) := by
        refine continuousOn_of_locally_continuousOn fun x hx => ?_
        refine ⟨Set.Iio ((⌈x⌉₊ + 1 : ℕ) : ℝ), isOpen_Iio, ?_, ?_⟩
        · refine Set.mem_Iio.2 ?_
          have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
          have h2 : ((⌈x⌉₊ : ℕ) : ℝ) < ((⌈x⌉₊ + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.lt_succ_self _
          linarith
        · refine (hgood ω hω (⌈x⌉₊ + 1)).mono ?_
          intro t ht
          exact ⟨ht.1, le_of_lt ht.2⟩
      exact hC.comp_continuous (continuous_id.max continuous_const)
        fun t => Set.mem_Ici.2 (le_max_right t 0)
    · simp only [Set.indicator_of_notMem hω]
      exact continuous_const
  refine ⟨fun t ω => Badᶜ.indicator (fun ω => η (max t 0) ω) ω, ?_, ?_, ?_⟩
  · refine measurable_uncurry_of_continuous_of_measurable (u := fun t ω =>
      Badᶜ.indicator (fun ω => η (max t 0) ω) ω) (fun ω => hcontω ω) (fun t => ?_)
    exact ((hLin 0).meas (max t 0)).indicator hBadm.compl
  · intro t ht
    filter_upwards [hGae] with ω hω
    simp only [Set.indicator_of_mem hω, max_eq_left ht]
  · intro ω T
    exact (hcontω ω).continuousOn

end HRS.MC.Sec7.S7FCW2

end
