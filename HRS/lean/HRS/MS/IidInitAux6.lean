import HRS.MS.IidInitAux5

/-!
# SA27, part 6: finite-dimensional convergence of the transported field paths

For every finite family of times `t_a ∈ [0,T]` and smooth tests `φ_a ∈ H^q`, the laws of the vectors
`(⟨φ_a, Zη_N^{t_a}⟩)_a` and `(⟨φ_a, Zemp_N^{t_a}⟩)_a` converge in `W₁` on `ℝ^p` to the law of
`(⟨φ_a, J^{t_a}⟩)_a = (A η'(U_∞^{0,t_a}φ_a))_a`:

* `sa27_w1_map_lip`: a Lipschitz map multiplies `W₁` by at most its constant;
* `sa27_pathLaw_fdd`: the finite-dimensional marginals of a path law;
* `sa27_fdd_w1`: the convergence (the Gaussian part by the scalar `L²` coupling on the space of the limit bridge, the
  empirical part by the multi-time S.B.2 and the Lipschitz pairing map `H^p → ℝ^p`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

noncomputable section

namespace HRS.MS.IidInit

open HRS HRS.Whole HRS.MP.HNegInfra HRS.MP.RdProp HRS.U5 HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open HRS.Whole.AppendixALemmas (AdjointInputOneD AdjointDerivInput)

variable {d : ℕ}

/-- A Lipschitz map multiplies `W₁` by at most its constant. -/
theorem sa27_w1_map_lip {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (f : E → F) (Lc : ℝ≥0)
    (hL : Lc ≠ 0) (hf : LipschitzWith Lc f) (P Q : Measure E) :
    wassersteinE 1 (P.map f) (Q.map f) ≤ (Lc : ℝ≥0∞) * wassersteinE 1 P Q := by
  conv_rhs => unfold wassersteinE
  rw [ENNReal.mul_iInf_of_ne (by simpa using hL) ENNReal.coe_ne_top]
  refine le_iInf fun π => ?_
  have hm : Measurable (Prod.map f f : E × E → F × F) :=
    (hf.continuous.prodMap hf.continuous).measurable
  have hcpl : IsCoupling (π.1.map (Prod.map f f)) (P.map f) (Q.map f) := by
    obtain ⟨h1, h2⟩ := π.2
    constructor
    · rw [Measure.map_map measurable_fst hm]
      have : (Prod.fst ∘ Prod.map f f : E × E → F) = f ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map hf.continuous.measurable measurable_fst, h1]
    · rw [Measure.map_map measurable_snd hm]
      have : (Prod.snd ∘ Prod.map f f : E × E → F) = f ∘ Prod.snd := rfl
      rw [this, ← Measure.map_map hf.continuous.measurable measurable_snd, h2]
  refine (wassersteinE_le_cost hcpl).trans ?_
  have hmeas : Measurable fun z : F × F => ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm.pow_const _)
  rw [lintegral_map hmeas hm]
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  calc ∫⁻ z, ENNReal.ofReal ‖(Prod.map f f z).1 - (Prod.map f f z).2‖ ∂π.1
      ≤ ∫⁻ z, (Lc : ℝ≥0∞) * ENNReal.ofReal ‖z.1 - z.2‖ ∂π.1 := by
        refine lintegral_mono fun z => ?_
        have h := hf.dist_le_mul z.1 z.2
        rw [dist_eq_norm, dist_eq_norm] at h
        simp only [Prod.map_fst, Prod.map_snd]
        calc ENNReal.ofReal ‖f z.1 - f z.2‖ ≤ ENNReal.ofReal (Lc * ‖z.1 - z.2‖) :=
              ENNReal.ofReal_le_ofReal h
          _ = (Lc : ℝ≥0∞) * ENNReal.ofReal ‖z.1 - z.2‖ := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    _ = (Lc : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π.1 :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top

/-- The vector of pairings `(⟨φ_a, F_a⟩)_a` on the Hilbert direct sum. -/
def sa27_pairVec {q : ℝ} {p : ℕ} (φ : Fin p → sa27_Tst d q)
    (F : PiLp 2 (fun _ : Fin p => HNeg d q)) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => HNeg.pairing (φ a).1 (F a)

theorem sa27_pairVec_lip {q : ℝ} {p : ℕ} (φ : Fin p → sa27_Tst d q) :
    ∃ Lc : ℝ≥0, Lc ≠ 0 ∧ LipschitzWith Lc (sa27_pairVec φ) := by
  set c : ℝ := Real.sqrt (∑ a, HRS.Whole.sobolevNorm q (φ a).1 ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  refine ⟨Real.toNNReal (c + 1), by simp; linarith, LipschitzWith.of_dist_le_mul fun F F' => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
  have hsub : sa27_pairVec φ F - sa27_pairVec φ F' =
      WithLp.toLp 2 fun a => HNeg.pairing (φ a).1 (F a - F' a) := by
    ext a
    simp [sa27_pairVec, mhn_pairing_sub (φ a).2]
  rw [hsub, EuclideanSpace.norm_eq]
  have hbd : ∀ a, ‖HNeg.pairing (φ a).1 (F a - F' a)‖ ^ 2 ≤
      ‖F - F'‖ ^ 2 * HRS.Whole.sobolevNorm q (φ a).1 ^ 2 := by
    intro a
    have h1 : |HNeg.pairing (φ a).1 (F a - F' a)| ≤
        ‖F a - F' a‖ * HRS.Whole.sobolevNorm q (φ a).1 := hneg_pairing_le (φ a).2 _
    have h2 : ‖F a - F' a‖ ≤ ‖F - F'‖ := by simpa using PiLp.norm_apply_le (F - F') a
    have h3 : |HNeg.pairing (φ a).1 (F a - F' a)| ≤ ‖F - F'‖ * HRS.Whole.sobolevNorm q (φ a).1 :=
      h1.trans (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _))
    rw [Real.norm_eq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  calc Real.sqrt (∑ a, ‖HNeg.pairing (φ a).1 (F a - F' a)‖ ^ 2)
      ≤ Real.sqrt (∑ a, ‖F - F'‖ ^ 2 * HRS.Whole.sobolevNorm q (φ a).1 ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ => hbd a)
    _ = ‖F - F'‖ * c := by
        rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ (c + 1) * ‖F - F'‖ := by nlinarith [norm_nonneg (F - F')]

theorem sa27_contPathOf_apply {E : Type*} [NormedAddCommGroup E] (T : ℝ) (z : ℝ → E)
    (hz : Continuous fun t : Set.Icc (0 : ℝ) T => z t) (t : Set.Icc (0 : ℝ) T) :
    contPathOf T z t = z t := by
  unfold contPathOf
  rw [dif_pos hz]
  rfl

/-- The finite-dimensional marginals of the law of a continuous `H^{-q}`-valued process. -/
theorem sa27_pathLaw_fdd {q : ℝ} (T : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → Ω → HNeg d q) (hcont : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Z t ζ) (Set.Icc 0 T))
    (hΦ : Measurable fun ζ => contPathOf T fun t => Z t ζ) {p : ℕ}
    (g : Fin p → Set.Icc (0 : ℝ) T × sa27_Tst d q) :
    (pathLaw T P Z).map (sa27_fd (sa27_pathF T (sa27_pf d q)) g) =
      P.map (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (g a).2.1 (Z (g a).1.1 ζ) :
        EuclideanSpace ℝ (Fin p))) := by
  have hF : Measurable (sa27_fd (sa27_pathF T (sa27_pf d q)) g) :=
    (sa27_fd_continuous _ (sa27_pathF_continuous T (sa27_pf d q) (sa27_pf_continuous q)) g).measurable
  unfold pathLaw
  rw [Measure.map_map hF hΦ]
  refine Measure.map_congr ?_
  filter_upwards [hcont] with ζ hζ
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Z t ζ := continuousOn_iff_continuous_restrict.1 hζ
  ext a
  simp [sa27_fd, sa27_pathF, sa27_pf, sa27_contPathOf_apply T (fun t => Z t ζ) hc]

/-- The constant `c_φ = (∑ ‖φ_a‖²)^{1/2}`. -/
def sa27_cphi {q : ℝ} {p : ℕ} (φ : Fin p → sa27_Tst d q) : ℝ :=
  Real.sqrt (∑ a, HRS.Whole.sobolevNorm q (φ a).1 ^ 2)

end HRS.MS.IidInit
