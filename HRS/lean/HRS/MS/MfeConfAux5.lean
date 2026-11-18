import HRS.MS.MfeConfAux4
import HRS.MS.WrEnt
import HRS.MS.WrPress

/-!
# S.B.1, packet F2: the whole-space entropy split `H(ν | Q_N) = H(ν | μ^{⊗N}) + βN ∫ F_N dν + log K_N`

Whole-space version of the torus `HRS.movT_relEntropy_split` (`HRS/PDE/MovFFinal.lean`), for `d ≥ 2` (S3.1 is proved for `2 ≤ d`).

* `sb1_measurable_modulatedEnergy`: `X ↦ F_N^g(X, μ)` is Borel for a Borel kernel and `σ`-finite `μ`.
* `sb1_kl_tilted`: for `f` measurable with `e^f` `P`-integrable and `ν`-integrable `f`: `H(ν | P^f) < ∞ ↔ H(ν | P) < ∞` and
  the entropy identity.  (Unlike the torus, `f = -βN F_N` is NOT bounded above for the logarithmic kernel, so the proof uses the
  `ν`-integrability of `f`, which comes from `euclidean_pair_entropy_self`.)
* `sb1_gibbsWellDefined`: S3.1 at `θ = 0`, `h = 0` for one `b > 0`.
* `sb1_modGibbs_eq_tilted`: `Q_{N,b}(μ) = (μ^{⊗N}).tilted (-bN F_N)`.
* `sb1_relEntropy_split`: the split, with the finiteness equivalence `H(ν|Q) < ∞ ↔ MFEFiniteW`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-! ### Measurability of the modulated energy -/

theorem sb1_measurable_convMeasure {g : Euc d → ℝ} (hg : Measurable g) (μ : Measure (Euc d))
    [SFinite μ] : Measurable (Whole.convMeasure g μ) := by
  have h : StronglyMeasurable (fun p : Euc d × Euc d => g (p.1 - p.2)) :=
    (hg.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := μ)).measurable

theorem sb1_measurable_modulatedEnergy {g : Euc d → ℝ} (hg : Measurable g) (μ : Measure (Euc d))
    [SFinite μ] : Measurable (fun X : Whole.EucConfig d N => Whole.modulatedEnergy g X μ) := by
  unfold Whole.modulatedEnergy
  have h1 : ∀ i j : Fin N, Measurable fun X : Whole.EucConfig d N => g (X i - X j) := fun i j =>
    hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  have h2 : ∀ i : Fin N, Measurable fun X : Whole.EucConfig d N => Whole.convMeasure g μ (X i) :=
    fun i => (sb1_measurable_convMeasure hg μ).comp (measurable_pi_apply i)
  refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
  · exact Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => h1 i j) _
  · exact Measurable.const_mul (Finset.measurable_sum _ fun i _ => h2 i) _

theorem sb1_measurable_rieszKernel (s : ℝ) : Measurable (Whole.rieszKernel d s) := by
  unfold Whole.rieszKernel
  by_cases hs : s = 0
  · simp only [hs, ite_true]
    exact (Real.measurable_log.comp measurable_norm).neg
  · simp only [hs, ite_false]
    exact measurable_norm.pow_const _

/-! ### The tilted relative entropy -/

theorem sb1_kl_tilted {α : Type*} [MeasurableSpace α] (P ν : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] {f : α → ℝ} (hexp : Integrable (fun x => Real.exp (f x)) P)
    (hfν : Integrable f ν) :
    (klDiv ν (P.tilted f) ≠ ⊤ ↔ klDiv ν P ≠ ⊤) ∧
    (klDiv ν P ≠ ⊤ →
      (klDiv ν (P.tilted f)).toReal =
        (klDiv ν P).toReal - ∫ x, f x ∂ν + Real.log (∫ x, Real.exp (f x) ∂P)) := by
  have : IsProbabilityMeasure (P.tilted f) := isProbabilityMeasure_tilted hexp
  have hPQ : P ≪ P.tilted f := absolutelyContinuous_tilted hexp
  have hQP : P.tilted f ≪ P := tilted_absolutelyContinuous P f
  refine ⟨⟨fun h => ?_, fun h1 => ?_⟩, fun h1 => ?_⟩
  · obtain ⟨hνQ, hint⟩ := klDiv_ne_top_iff.1 h
    have hνP : ν ≪ P := hνQ.trans hQP
    have e := llr_tilted_right hνP hexp
    have hllr : Integrable (llr ν P) ν := by
      have : Integrable (fun x => llr ν (P.tilted f) x + f x -
          Real.log (∫ z, Real.exp (f z) ∂P)) ν :=
        (hint.add hfν).sub (integrable_const _)
      refine this.congr ?_
      filter_upwards [e] with x hx
      rw [hx]; ring
    exact klDiv_ne_top hνP hllr
  · obtain ⟨hνP, hint⟩ := klDiv_ne_top_iff.1 h1
    exact klDiv_ne_top (hνP.trans hPQ) (integrable_llr_tilted_right hνP hfν hint hexp)
  · obtain ⟨hνP, hint⟩ := klDiv_ne_top_iff.1 h1
    rw [toReal_klDiv (hνP.trans hPQ) (integrable_llr_tilted_right hνP hfν hint hexp),
      toReal_klDiv hνP hint, integral_llr_tilted_right hνP hfν hexp hint]
    simp [probReal_univ]

/-! ### Well-definedness of the Gibbs law (S3.1 at `θ = 0`) -/

/-- S3.1 at `h = 0`, `θ = 0`: for a bounded probability density (with the log moment when `s = 0`), `d ≥ 2`, `N ≥ 2`, `b > 0`,
the modulated Gibbs law is well defined. -/
theorem sb1_gibbsWellDefined (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M L : ℝ}
    {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (hρM : ∀ x, ρ x ≤ M)
    (hlog : s = 0 → Whole.HasLogMoment (Whole.withDensityReal ρ) L) (hN : 2 ≤ N) {b : ℝ}
    (hb : 0 < b) :
    Whole.GibbsWellDefined (fun x y => Whole.rieszKernel d s (x - y)) N b (Whole.withDensityReal ρ) := by
  obtain ⟨θ0, hθ0, C0, hP⟩ := HRS.MS.Wr.euclidean_pressure_proof hd hs0 hsd M L b (2 * b) 0 hb
    (by linarith)
  have hhz : Whole.IsBoundedPairKernel s 0 (fun _ _ : Euc d => (0 : ℝ)) :=
    ⟨measurable_const, fun _ _ => rfl, fun x y _ => by simp⟩
  have := (hP ρ hρ hρM hlog (fun _ _ => 0) hhz N hN b ⟨le_rfl, by linarith⟩ 0
    (by rw [abs_zero]; exact hθ0.le)).1
  simpa only [zero_mul, sub_zero] using this

/-- The Gibbs weight is integrable, the normaliser is positive, and `Q_{N,b} = (μ^{⊗N}).tilted (-bN F_N)`. -/
theorem sb1_modGibbs_eq_tilted (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M L : ℝ}
    {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (hρM : ∀ x, ρ x ≤ M)
    (hlog : s = 0 → Whole.HasLogMoment (Whole.withDensityReal ρ) L) (hN : 2 ≤ N) {b : ℝ}
    (hb : 0 < b) :
    Integrable (fun X : Whole.EucConfig d N =>
      Real.exp (-b * N * Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ)))
      (Measure.pi fun _ => Whole.withDensityReal ρ) ∧
    0 < Whole.gibbsNormalizer (Whole.rieszKernel d s) N b (Whole.withDensityReal ρ) ∧
    Whole.modulatedGibbs (Whole.rieszKernel d s) N b (Whole.withDensityReal ρ) =
      (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ).tilted
        (fun X => -b * N * Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ)) := by
  have hW := sb1_gibbsWellDefined hd hs0 hsd hρ hρM hlog hN hb
  have hexp : Integrable (fun X : Whole.EucConfig d N =>
      Real.exp (-b * N * Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ)))
      (Measure.pi fun _ => Whole.withDensityReal ρ) := hW.weight_integrable
  have hK : 0 < Whole.gibbsNormalizer (Whole.rieszKernel d s) N b (Whole.withDensityReal ρ) :=
    hW.normalizer_pos
  refine ⟨hexp, hK, ?_⟩
  unfold Whole.modulatedGibbs Measure.tilted
  have hKdef : Whole.gibbsNormalizer (Whole.rieszKernel d s) N b (Whole.withDensityReal ρ) =
      ∫ x, Real.exp (-b * N * Whole.rieszModulatedEnergy d s x (Whole.withDensityReal ρ))
        ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ) := rfl
  rw [hKdef] at hK ⊢
  set K := ∫ x, Real.exp (-b * N * Whole.rieszModulatedEnergy d s x (Whole.withDensityReal ρ))
    ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ) with hKK
  have e : (fun x : Whole.EucConfig d N => ENNReal.ofReal
      (Real.exp (-b * N * Whole.rieszModulatedEnergy d s x (Whole.withDensityReal ρ)) / K)) =
      (ENNReal.ofReal K)⁻¹ • fun x => ENNReal.ofReal
        (Real.exp (-b * N * Whole.rieszModulatedEnergy d s x (Whole.withDensityReal ρ))) := by
    funext x
    rw [ENNReal.ofReal_div_of_pos hK]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.div_eq_inv_mul]
  rw [e, withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK).ne')]
  rfl

/-! ### The entropy split -/

/-- **F2** (whole-space `movT_relEntropy_split`).  For `d ≥ 2`, a bounded probability density `ρ` (log moment when `s = 0`),
`N ≥ 2`, `b > 0` and a probability law `ν` on `(ℝ^d)^N`: `H(ν | Q_{N,b}(μ)) < ∞ ↔ 𝖤_N-finite` (`MFEFiniteW`), and then
`H(ν|Q) = H(ν|μ^{⊗N}) + b N ∫ F_N dν + log K_{N,b}(μ)`. -/
theorem sb1_relEntropy_split (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M L : ℝ}
    {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (hρM : ∀ x, ρ x ≤ M)
    (hlog : s = 0 → Whole.HasLogMoment (Whole.withDensityReal ρ) L) (hN : 2 ≤ N) {b : ℝ}
    (hb : 0 < b) {ν : Measure (Whole.EucConfig d N)} [IsProbabilityMeasure ν] :
    (relEntropy ν (Whole.modulatedGibbs (Whole.rieszKernel d s) N b (Whole.withDensityReal ρ)) ≠ ⊤ ↔
      Whole.MFEFiniteW d s ν (Whole.withDensityReal ρ)) ∧
    (Whole.MFEFiniteW d s ν (Whole.withDensityReal ρ) →
      (relEntropy ν (Whole.modulatedGibbs (Whole.rieszKernel d s) N b
          (Whole.withDensityReal ρ))).toReal =
        (relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ)).toReal +
          b * N * ∫ X, Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ) ∂ν +
          Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d s) N b (Whole.withDensityReal ρ))) := by
  have hN0 : 0 < N := by omega
  have : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  obtain ⟨hexp, hK, hQ⟩ := sb1_modGibbs_eq_tilted hd hs0 hsd hρ hρM hlog hN hb
  set μ := Whole.withDensityReal ρ with hμ
  set P := Measure.pi fun _ : Fin N => μ with hP
  set f : Whole.EucConfig d N → ℝ := fun X => -b * N * Whole.rieszModulatedEnergy d s X μ with hf
  have hNne : -b * (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN0
    have := mul_pos hb this
    intro h; linarith
  have hint : ∀ {ν' : Measure (Whole.EucConfig d N)}, Integrable f ν' ↔
      Integrable (fun X => Whole.rieszModulatedEnergy d s X μ) ν' := fun {ν'} =>
    integrable_const_mul_iff (isUnit_iff_ne_zero.2 hNne) _
  -- finiteness of the entropy forces integrability of the energy (S3.1, pair entropy with `h = g`)
  have hfin : relEntropy ν (Whole.modulatedGibbs (Whole.rieszKernel d s) N b μ) ≠ ⊤ →
      Integrable (fun X => Whole.rieszModulatedEnergy d s X μ) ν := by
    intro hne
    obtain ⟨c, hc, C, hC⟩ := HRS.MS.Wr.euclidean_pair_entropy_self_proof hd hs0 hsd M L b (2 * b) hb
      (by linarith)
    have h2 := (hC ρ hρ hρM hlog N hN b ⟨le_rfl, by linarith⟩).2 ν inferInstance (lt_top_iff_ne_top.2 hne)
    have h3 := h2.1
    have h4 : Integrable (fun X => Whole.modulatedEnergy (Whole.rieszKernel d s) X μ) ν := by
      have := h3.const_mul (1 / (N : ℝ))
      refine (this.mono' ?_ ?_)
      · exact (sb1_measurable_modulatedEnergy (sb1_measurable_rieszKernel s) μ).aestronglyMeasurable
      · refine Eventually.of_forall fun X => ?_
        have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
        have : 1 / (N : ℝ) * ((N : ℝ) * |Whole.modulatedEnergy (Whole.rieszKernel d s) X μ|) =
            |Whole.modulatedEnergy (Whole.rieszKernel d s) X μ| := by field_simp
        rw [Real.norm_eq_abs, this]
    exact h4
  have hfm : Measurable f := measurable_const.mul
    (sb1_measurable_modulatedEnergy (sb1_measurable_rieszKernel s) μ)
  unfold Whole.MFEFiniteW relEntropy
  rw [hQ]
  refine ⟨⟨fun h => ?_, fun hh => ?_⟩, fun hh => ?_⟩
  · have hI : Integrable (fun X => Whole.rieszModulatedEnergy d s X μ) ν := by
      apply hfin
      rw [hQ]; exact h
    have := (sb1_kl_tilted P ν hexp (hint.2 hI)).1.1 h
    exact ⟨this, hI⟩
  · exact (sb1_kl_tilted P ν hexp (hint.2 hh.2)).1.2 hh.1
  · have key := (sb1_kl_tilted P ν hexp (hint.2 hh.2)).2 hh.1
    rw [key]
    have hi : ∫ X, f X ∂ν = -b * N * ∫ X, Whole.rieszModulatedEnergy d s X μ ∂ν :=
      integral_const_mul _ _
    rw [hi]
    show _ = _ + _ + Real.log (∫ x, Real.exp (f x) ∂P)
    ring

end HRS.MS.MfeConf
