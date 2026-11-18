import HRS.MS.GenPathAux19
import HRS.Main.GFB3Aux7

/-!
# S5.6 packet P5b: the `𝒦`-valued Hilbert-Schmidt integrand of the empirical noise

`s56Phi C m T q X r ζ (i,a) = √(2q/N) Γ_{clamp r,a}(x_i^r) ∈ 𝒦` (the integrand of `empiricalNoiseIntegrand`, with the time clamped to
`[0,T]`: it coincides with it for `r ∈ [0,T]`, and the clamp makes it provably progressive on `ℝ`; the frozen integrand contains the
`Classical.choose` of `propagatorW`, arbitrary for `r < 0`).  `s56_phi_isHS`: it is a progressive Hilbert-Schmidt integrand on every
horizon.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

/-- The clamped `𝒦`-valued noise integrand. -/
def s56Phi {Ω : Type*} {N : ℕ} (C : WholeCoeff d) (m T q : ℝ) (X : ℝ≥0 → Ω → EucConfig d N) :
    ℝ → Ω → Fin N × Fin d → KSpace d m T :=
  fun r ζ ia => Real.sqrt (2 * q / N) • gradFeature C m T ia.2 (mrrClamp T r) (X (Real.toNNReal r) ζ ia.1)

theorem s56Phi_eq {Ω : Type*} {N : ℕ} (C : WholeCoeff d) (m T q : ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (ζ : Ω) (ia : Fin N × Fin d) :
    s56Phi C m T q X r ζ ia = HRS.Whole.empiricalNoiseIntegrand C m T q X r ζ ia := by
  unfold s56Phi HRS.Whole.empiricalNoiseIntegrand
  rw [mrrClamp_of_mem hr]

theorem s56_meas_comp {σ κ : Type*} (mσ : MeasurableSpace σ) {ι : Type*} [MeasurableSpace ι]
    [MeasurableSpace κ] {E : Type*} [MeasurableSpace E] {F : ι × κ → E} (hF : Measurable F)
    {f1 : σ → ι} {f2 : σ → κ} (h1 : Measurable f1) (h2 : Measurable f2) :
    Measurable fun s => F (f1 s, f2 s) :=
  hF.comp (h1.prodMk h2)

theorem s56_phi_isHS (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (q : ℝ) {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hprog : IsProgressive ℱ (ofNNRealTime X)) (τ : ℝ) :
    IsHSIntegrand P ℱ τ (s56Phi (S.coeff N) b.m b.T q X) := by
  obtain ⟨Cf, hCf⟩ := HRS.MS.Star.general_orbits_features_proof b hbv
  refine ⟨?_, fun r ζ => Summable.of_finite, ?_⟩
  · intro k i
    have hp : Measurable fun p : ℝ × EucConfig d N => ((p.1, p.2 k.1) : ℝ × Euc d) :=
      measurable_fst.prodMk ((measurable_pi_apply k.1).comp measurable_snd)
    have hf : Measurable fun p : ℝ × EucConfig d N =>
        gradFeature (S.coeff N) b.m b.T k.2 (mrrClamp b.T p.1) (p.2 k.1) :=
      Measurable.comp (g := fun p : ℝ × Euc d => gradFeature (S.coeff N) b.m b.T k.2 (mrrClamp b.T p.1) p.2)
        (f := fun p : ℝ × EucConfig d N => ((p.1, p.2 k.1) : ℝ × Euc d))
        (s56_feat_meas b hbv S N hC k.2) hp
    have hg : Measurable fun p : ℝ × EucConfig d N => Real.sqrt (2 * q / N) •
        gradFeature (S.coeff N) b.m b.T k.2 (mrrClamp b.T p.1) (p.2 k.1) :=
      hf.const_smul (Real.sqrt (2 * q / N))
    have hX := hprog i
    have h1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ i)]
        fun p : Set.Iic i × Ω => (p.1 : ℝ) :=
      measurable_subtype_coe.comp measurable_fst
    exact s56_meas_comp (Subtype.instMeasurableSpace.prod (ℱ i)) hg h1 hX
  · set B : ℝ := |Real.sqrt (2 * q / N)| * |Cf| with hB
    have hnorm : ∀ r ζ (k : Fin N × Fin d), ‖s56Phi (S.coeff N) b.m b.T q X r ζ k‖ ≤ B := by
      intro r ζ k
      unfold s56Phi
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := (hCf S N k.2 _ (mrrClamp_mem hbv.hT.le r)).2 0 (Nat.zero_le _) (X (Real.toNNReal r) ζ k.1)
      rw [norm_iteratedFDeriv_zero] at this
      exact this.trans (le_abs_self _)
    have hpt : ∀ r ζ, ∑' k : Fin N × Fin d, ‖s56Phi (S.coeff N) b.m b.T q X r ζ k‖ₑ ^ 2 ≤
        ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
      intro r ζ
      rw [tsum_fintype]
      calc ∑ k : Fin N × Fin d, ‖s56Phi (S.coeff N) b.m b.T q X r ζ k‖ₑ ^ 2
          ≤ ∑ _k : Fin N × Fin d, ENNReal.ofReal B ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            refine pow_le_pow_left' ?_ 2
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hnorm r ζ k)
        _ = ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ]
    unfold hsSqIntegralOn
    refine lt_of_le_of_lt (lintegral_mono fun ζ => lintegral_mono fun r => hpt r ζ) ?_
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, measure_univ, mul_one]
    refine ENNReal.mul_lt_top ?_ ?_
    · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    · exact ENNReal.ofReal_lt_top

end HRS.MS.GenPath
