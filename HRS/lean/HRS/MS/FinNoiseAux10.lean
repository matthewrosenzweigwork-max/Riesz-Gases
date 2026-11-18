import HRS.MS.FinNoiseAux9

/-!
# S8.6 `finite_noise`, packet P6b (S86): the polar-coupling integrands are Hilbert-Schmidt on every horizon

* `s86_hs_S`: `r ↦ 1_{r ≤ t} S_r(π ·)` (`S_r` the symmetric root of `hsCovForm (Φ_r)`) is `IsHSIntegrand P' ℱ' T` for
  every `T`, because `∑_j ‖S_r e_j‖² = ∑_k ‖Φ_r k‖²`.
* `s86_hs_Sb`: the same for the deterministic integrand `1_{r ≤ t} Sb_r` of a `PCDetData`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem s86_tsum_enorm_sq {κ : Type*} (f : κ → H) (hf : Summable fun k => ‖f k‖ ^ 2) :
    ∑' k, ‖f k‖ₑ ^ 2 = ENNReal.ofReal (∑' k, ‖f k‖ ^ 2) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hf]
  refine tsum_congr fun k => ?_
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem s86_sum_sq_root {ι κ : Type*} [Countable ι] [Countable κ] (e : HilbertBasis ι ℝ H)
    {Φ : κ → H} (hΦ : Summable fun k => ‖Φ k‖ ^ 2) {S : H →L[ℝ] H}
    (hS : IsSqrtOfForm S (hsCovForm Φ)) :
    ∑' j, ‖S (e j)‖ ^ 2 = ∑' k, ‖Φ k‖ ^ 2 := by
  classical
  have hs := HRS.Uniform.RelCov.summable_sqrt_diag e hS (isTraceClassCov_hsCovForm hΦ)
  have h1 := HRS.Uniform.Q07c.hsCovForm_sqrt_cols e hS hs
  rw [← HRS.Uniform.Q07c.traceNormForm_hsCovForm_eq hΦ, ← h1,
    HRS.Uniform.Q07c.traceNormForm_hsCovForm_eq hs]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}

theorem s86_hs_S (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {ℱ : Filtration ℝ mΩ} {ℱ' : Filtration ℝ mΩ'} (π : Ω' → Ω) (hπp : MeasurePreserving π P' P)
    (hπm : ∀ s, Measurable[ℱ' s, ℱ s] π) {κ : Type*} [Countable κ] {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ H) (Φ : ℝ → Ω → κ → H) (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ)
    (S : ℝ → Ω → H →L[ℝ] H) (hSsq : ∀ r w, IsSqrtOfForm (S r w) (hsCovForm (Φ r w)))
    (hSprog : ∀ x y, IsProgressive ℱ (fun r w => inner ℝ (S r w x) y)) (t T : ℝ) :
    IsHSIntegrand P' ℱ' T (fun r w (j : ι) => if r ≤ t then S r (π w) (e j) else 0) := by
  classical
  refine ⟨fun j => ?_, fun r w => ?_, ?_⟩
  · obtain ⟨ι₀, hι₀, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
    have := hι₀
    intro τ
    letI : MeasurableSpace (Set.Iic τ × Ω') := Subtype.instMeasurableSpace.prod (ℱ' τ)
    refine measurable_of_inner_basis b fun i => ?_
    have h1 : Measurable fun p : Set.Iic τ × Ω' => inner ℝ (S p.1.1 (π p.2) (e j)) (b i) :=
      isProgressive_comp_π hπm (hSprog (e j) (b i)) τ
    have h2 : Measurable fun p : Set.Iic τ × Ω' =>
        inner ℝ (b i) (if p.1.1 ≤ t then S p.1.1 (π p.2) (e j) else 0) := by
      have : (fun p : Set.Iic τ × Ω' => inner ℝ (b i) (if p.1.1 ≤ t then S p.1.1 (π p.2) (e j) else 0)) =
          fun p => if p.1.1 ≤ t then inner ℝ (S p.1.1 (π p.2) (e j)) (b i) else 0 := by
        funext p; by_cases h : p.1.1 ≤ t <;> simp [h, real_inner_comm]
      rw [this]
      exact Measurable.ite (measurableSet_le (measurable_subtype_coe.comp measurable_fst)
        measurable_const) h1 measurable_const
    exact h2
  · by_cases hr : r ≤ t
    · simp only [hr, ite_true]
      exact HRS.Uniform.RelCov.summable_sqrt_diag e (hSsq r (π w))
        (isTraceClassCov_hsCovForm ((hΦ 0).summable r (π w)))
    · simp [hr]
  · have hpt : ∀ r w, ∑' j : ι, ‖(if r ≤ t then S r (π w) (e j) else 0 : H)‖ₑ ^ 2 ≤
        ∑' k, ‖Φ r (π w) k‖ₑ ^ 2 := by
      intro r w
      by_cases hr : r ≤ t
      · simp only [hr, ite_true]
        have hs := HRS.Uniform.RelCov.summable_sqrt_diag e (hSsq r (π w))
          (isTraceClassCov_hsCovForm ((hΦ 0).summable r (π w)))
        rw [s86_tsum_enorm_sq _ hs, s86_tsum_enorm_sq _ ((hΦ 0).summable r (π w)),
          s86_sum_sq_root e ((hΦ 0).summable r (π w)) (hSsq r (π w))]
      · simp [hr]
    unfold hsSqIntegralOn
    calc ∫⁻ w, (∫⁻ r in Icc 0 T, ∑' j : ι, ‖(if r ≤ t then S r (π w) (e j) else 0 : H)‖ₑ ^ 2) ∂P'
        ≤ ∫⁻ w, (∫⁻ r in Icc 0 T, ∑' k, ‖Φ r (π w) k‖ₑ ^ 2) ∂P' :=
          lintegral_mono fun w => lintegral_mono fun r => hpt r w
      _ = ∫⁻ w, (∫⁻ r in Icc 0 T, ∑' k, ‖Φ r w k‖ₑ ^ 2) ∂P :=
          hπp.lintegral_comp (hdsum_measurable_hsSq Φ (fun k => (hΦ 0).prog k) T)
      _ < ⊤ := (hΦ T).sq

theorem s86_hs_Sb (P' : Measure Ω') [IsProbabilityMeasure P'] {ℱ' : Filtration ℝ mΩ'}
    {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ H) (t : ℝ) (Sb : ℝ → H →L[ℝ] H)
    (Tf : ℝ → ℝ) (hD : PCDetData e t Sb Tf) (T : ℝ) :
    IsHSIntegrand P' ℱ' T (fun r (_ : Ω') (j : ι) => if r ≤ t then Sb r (e j) else 0) := by
  classical
  have hsum : ∀ r, Summable fun j : ι => ‖(if r ≤ t then Sb r (e j) else 0 : H)‖ ^ 2 := by
    intro r
    by_cases hr : r ∈ Icc 0 t
    · simpa [hr.2] using (hD.trace r hr).summable
    · have : Sb r = 0 := hD.zero r hr
      simp [this]
  refine ⟨fun j => ?_, fun r w => hsum r, ?_⟩
  · intro τ
    have hm : Measurable fun r : ℝ => (if r ≤ t then Sb r (e j) else 0 : H) :=
      Measurable.ite measurableSet_Iic (hD.meas (e j)) measurable_const
    exact hm.comp (measurable_subtype_coe.comp measurable_fst)
  · have hpt : ∀ r (w : Ω'), ∑' j : ι, ‖(if r ≤ t then Sb r (e j) else 0 : H)‖ₑ ^ 2 ≤
        (Icc (0 : ℝ) t).indicator (fun r => ENNReal.ofReal (Tf r)) r := by
      intro r w
      by_cases hr : r ∈ Icc 0 t
      · rw [Set.indicator_of_mem hr]
        simp only [hr.2, ite_true]
        rw [s86_tsum_enorm_sq _ (by simpa [hr.2] using hsum r)]
        have := (hD.trace r hr).tsum_eq
        rw [this]
      · have : Sb r = 0 := hD.zero r hr
        simp [this, hr]
    unfold hsSqIntegralOn
    calc ∫⁻ w, (∫⁻ r in Icc 0 T, ∑' j : ι, ‖(if r ≤ t then Sb r (e j) else 0 : H)‖ₑ ^ 2) ∂P'
        ≤ ∫⁻ w, (∫⁻ r in Icc 0 T, (Icc (0 : ℝ) t).indicator (fun r => ENNReal.ofReal (Tf r)) r) ∂P' :=
          lintegral_mono fun w => lintegral_mono fun r => hpt r w
      _ ≤ ∫⁻ w, (∫⁻ r, (Icc (0 : ℝ) t).indicator (fun r => ENNReal.ofReal (Tf r)) r) ∂P' :=
          lintegral_mono fun w => lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ r in Icc (0 : ℝ) t, ENNReal.ofReal (Tf r) := by
          rw [lintegral_const, lintegral_indicator measurableSet_Icc]
          simp
      _ < ⊤ := hD.Tint.lintegral_lt_top

end Gen

end HRS.MS.FinNoise
