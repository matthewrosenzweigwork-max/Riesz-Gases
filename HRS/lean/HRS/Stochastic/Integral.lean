import HRS.Stochastic.Simple

/-!
# The Itô integral against finitely many Brownian motions

Package SI-01, part 3.  For a progressively measurable integrand `Φ : ℝ → Ω → ι → ℝ` with
`E ∫_0^T ∑_k |Φ^k_s|² ds < ∞` for every `T` (`IsProgressiveL2`), the Itô integral
`M_t = ∫_0^t Φ_s · dW_s = ∑_k ∫_0^t Φ^k_s dW^k_s` is *characterised* (`IsItoIntegral`) as the
process with everywhere continuous paths, adapted, vanishing on `(-∞, 0]`, which at every time
`t ≥ 0` is the `L²(P)`-limit of the elementary integrals of *every* sequence of simple integrands
converging to `Φ` in `L²([0,t] × Ω)`.  This determines `M` up to indistinguishability
(`IsItoIntegral.ae_eq_forall`); existence (`exists_isItoIntegral`) is the construction of the
integral.  `itoIntegral` is the chosen such process (`0` if none exists, which never happens under
`IsBrownianFiltration` and `IsProgressiveL2`; cf. the `propagator` convention of `Setup.lean`).

Main statements: martingale property, Itô isometry (incl. cross terms and increments), linearity,
Doob's `L²` maximal inequality (`lintegral_iSup_itoIntegral_sq_le`, M L10583, L4984, L9415),
the stopping identity `∫ 1_{s ≤ τ} Φ dW = (∫ Φ dW)_{· ∧ τ}` (`itoIntegral_stopIntegrand`), and the
extension to integrands with `∫_0^T |Φ|² < ∞` a.s. by localisation (`localItoIntegral`), which is
a continuous local martingale (`IsContLocalMartingale`).  The local integral is what Itô's formula
produces in general (M L10791-10860 "continuous local martingale", localisation at L10858;
Cépa–Lépingle coordinate equations M L1650-1651 need only the additive-noise form).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

/-! ### Integrand classes -/

/-- Progressively measurable integrands with `E ∫_0^T ∑_k |Φ^k|² < ∞` for every `T`
(square-integrable on every bounded time interval). -/
structure IsProgressiveL2 (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (Φ : ℝ → Ω → ι → ℝ) : Prop where
  prog : IsProgressive ℱ Φ
  sq : ∀ T : ℝ, sqIntegralOn P Φ T < ∞

/-- Progressively measurable integrands with `∫_0^T ∑_k |Φ^k_s|² ds < ∞` a.s. for every `T`. -/
structure IsProgressiveLocL2 (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (Φ : ℝ → Ω → ι → ℝ) :
    Prop where
  prog : IsProgressive ℱ Φ
  sq : ∀ T : ℝ, ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2 < ∞

/-! ### Auxiliary lemmas on the `L²` size of progressive integrands -/

section Aux
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {Φ Φ' : ℝ → Ω → ι → ℝ}

theorem measurable_clamp {β : Type*} [MeasurableSpace β] {Φ : ℝ → Ω → β} (h : IsProgressive ℱ Φ)
    (T : ℝ) : Measurable (fun p : ℝ × Ω => Φ (min p.1 T) p.2) := by
  have hT := h T
  have hg : @Measurable (ℝ × Ω) (Set.Iic T × Ω) inferInstance
      (Subtype.instMeasurableSpace.prod (ℱ T))
      (fun p : ℝ × Ω => ((⟨min p.1 T, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic T), p.2)) := by
    refine @Measurable.prodMk _ _ _ _ Subtype.instMeasurableSpace (ℱ T) _ _ ?_ ?_
    · exact Measurable.subtype_mk (measurable_fst.min measurable_const)
    · exact measurable_snd.mono le_rfl (ℱ.le T)
  exact hT.comp hg

theorem measurable_sqSum_clamp (h : IsProgressive ℱ Φ) (T : ℝ) :
    Measurable (fun p : ℝ × Ω => ∑ k, ‖Φ (min p.1 T) p.2 k‖ₑ ^ 2) := by
  have := measurable_clamp h T
  refine Finset.measurable_sum _ fun k _ => ?_
  exact ((measurable_pi_apply k).comp this).enorm.pow_const 2

theorem measurable_lintegral_sqSum (h : IsProgressive ℱ Φ) (T : ℝ) :
    Measurable (fun ω => ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ (min s T) ω k‖ₑ ^ 2) := by
  have := (measurable_sqSum_clamp h T).comp (measurable_swap (α := Ω) (β := ℝ))
  exact this.lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 T))

theorem lintegral_sqSum_clamp (Φ : ℝ → Ω → ι → ℝ) (T : ℝ) (ω : Ω) :
    ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ (min s T) ω k‖ₑ ^ 2 = ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2 := by
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [min_eq_left hs.2]

theorem measurable_lintegral_sqSum' (h : IsProgressive ℱ Φ) (T : ℝ) :
    Measurable (fun ω => ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) := by
  simp_rw [← lintegral_sqSum_clamp Φ T]
  exact measurable_lintegral_sqSum h T


theorem sqIntegralOn_eq_clamp (P : Measure Ω) (Φ : ℝ → Ω → ι → ℝ) (T : ℝ) :
    sqIntegralOn P Φ T = ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ (min s T) ω k‖ₑ ^ 2) ∂P := by
  unfold sqIntegralOn
  simp_rw [lintegral_sqSum_clamp Φ T]

theorem enorm_add_sq_le (a b : ℝ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  simp only [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
  have h : |a + b| ^ 2 ≤ 2 * |a| ^ 2 + 2 * |b| ^ 2 := by
    rw [sq_abs, sq_abs, sq_abs]; nlinarith [sq_nonneg (a - b)]
  calc ENNReal.ofReal (|a + b| ^ 2) ≤ ENNReal.ofReal (2 * |a| ^ 2 + 2 * |b| ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp

theorem sqIntegralOn_add_le {f g : ℝ → Ω → ι → ℝ} (hf : IsProgressive ℱ f) (hg : IsProgressive ℱ g)
    (T : ℝ) : sqIntegralOn P (fun s ω => f s ω + g s ω) T ≤
      2 * sqIntegralOn P f T + 2 * sqIntegralOn P g T := by
  rw [sqIntegralOn_eq_clamp, sqIntegralOn_eq_clamp P f, sqIntegralOn_eq_clamp P g]
  have h1 := measurable_lintegral_sqSum hf T
  have h2 := measurable_sqSum_clamp hf T
  have h3 := measurable_sqSum_clamp hg T
  calc _ ≤ ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, (2 * ∑ k, ‖f (min s T) ω k‖ₑ ^ 2 + 2 * ∑ k, ‖g (min s T) ω k‖ₑ ^ 2)) ∂P := by
        refine lintegral_mono fun ω => lintegral_mono fun s => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun k _ => enorm_add_sq_le _ _
    _ = _ := by
        have hm1 : ∀ ω, Measurable fun s : ℝ => ∑ k, ‖f (min s T) ω k‖ₑ ^ 2 := fun ω => by
          have := h2.comp (measurable_prodMk_right (y := ω))
          exact this
        have hm2 : ∀ ω, Measurable fun s : ℝ => ∑ k, ‖g (min s T) ω k‖ₑ ^ 2 := fun ω => by
          have := h3.comp (measurable_prodMk_right (y := ω))
          exact this
        have e1 : ∀ ω, (∫⁻ s in Set.Icc 0 T, (2 * ∑ k, ‖f (min s T) ω k‖ₑ ^ 2 + 2 * ∑ k, ‖g (min s T) ω k‖ₑ ^ 2))
            = 2 * (∫⁻ s in Set.Icc 0 T, ∑ k, ‖f (min s T) ω k‖ₑ ^ 2)
              + 2 * (∫⁻ s in Set.Icc 0 T, ∑ k, ‖g (min s T) ω k‖ₑ ^ 2) := by
          intro ω
          rw [lintegral_add_left ((hm1 ω).const_mul 2), lintegral_const_mul _ (hm1 ω),
            lintegral_const_mul _ (hm2 ω)]
        simp_rw [e1]
        rw [lintegral_add_left (h1.const_mul 2), lintegral_const_mul _ h1,
          lintegral_const_mul _ (measurable_lintegral_sqSum hg T)]

theorem sqIntegralOn_mono_of_enorm_le {f g : ℝ → Ω → ι → ℝ} (h : ∀ s ω k, ‖f s ω k‖ₑ ≤ ‖g s ω k‖ₑ)
    (T : ℝ) : sqIntegralOn P f T ≤ sqIntegralOn P g T := by
  unfold sqIntegralOn
  refine lintegral_mono fun ω => lintegral_mono fun s => ?_
  exact Finset.sum_le_sum fun k _ => pow_le_pow_left' (h s ω k) 2

theorem sqIntegralOn_smul (c : ℝ) (f : ℝ → Ω → ι → ℝ) (T : ℝ) :
    sqIntegralOn P (fun s ω => c • f s ω) T = ENNReal.ofReal (c ^ 2) * sqIntegralOn P f T := by
  unfold sqIntegralOn
  have e : ∀ s ω, ∑ k, ‖(c • f s ω) k‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ∑ k, ‖f s ω k‖ₑ ^ 2 := by
    intro s ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [e]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem sqIntegralOn_sub_comm (f g : ℝ → Ω → ι → ℝ) (T : ℝ) :
    sqIntegralOn P (fun s ω => f s ω - g s ω) T = sqIntegralOn P (fun s ω => g s ω - f s ω) T := by
  unfold sqIntegralOn
  refine lintegral_congr fun ω => lintegral_congr fun s => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  show ‖f s ω k - g s ω k‖ₑ ^ 2 = ‖g s ω k - f s ω k‖ₑ ^ 2
  rw [enorm_sub_rev]

theorem isProgressive_add {f g : ℝ → Ω → ι → ℝ} (hf : IsProgressive ℱ f) (hg : IsProgressive ℱ g) :
    IsProgressive ℱ (fun s ω => f s ω + g s ω) := fun i => (hf i).add (hg i)

theorem isProgressive_sub {f g : ℝ → Ω → ι → ℝ} (hf : IsProgressive ℱ f) (hg : IsProgressive ℱ g) :
    IsProgressive ℱ (fun s ω => f s ω - g s ω) := fun i => (hf i).sub (hg i)

theorem isProgressive_smul {f : ℝ → Ω → ι → ℝ} (hf : IsProgressive ℱ f) (c : ℝ) :
    IsProgressive ℱ (fun s ω => c • f s ω) := fun i => (hf i).const_smul c


theorem lintegral_enorm_sq_eq_eLpNorm_sq {α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast ((∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂μ) ^ (2⁻¹ : ℝ)) 2, ← ENNReal.rpow_mul]
  simp

theorem norm_toLp_sq {α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  rw [Lp.norm_toLp, lintegral_enorm_sq_eq_eLpNorm_sq hf.aestronglyMeasurable, ENNReal.toReal_pow]

theorem enorm_toLp_sq (x : ι → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ₑ ^ 2 = ∑ k, ‖x k‖ₑ ^ 2 := by
  have h : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖₊ ^ 2 = ∑ k, ‖x k‖₊ ^ 2 := by
    rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt]
  simp only [enorm_eq_nnnorm]
  rw [← ENNReal.coe_pow, h]
  push_cast
  rfl

/-- the time-space measure on `[0, T] × Ω` -/
def tsMeasure (P : Measure Ω) (T : ℝ) : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Icc (0 : ℝ) T)).prod P

/-- the clamped Euclidean-valued version of an integrand -/
def eclamp (Φ : ℝ → Ω → ι → ℝ) (T : ℝ) : ℝ × Ω → EuclideanSpace ℝ ι :=
  fun p => WithLp.toLp 2 (Φ (min p.1 T) p.2)

theorem measurable_eclamp (h : IsProgressive ℱ Φ) (T : ℝ) : Measurable (eclamp Φ T) :=
  (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).measurable.comp (measurable_clamp h T)

theorem lintegral_enorm_sq_eclamp [SFinite P] (h : IsProgressive ℱ Φ) (T : ℝ) :
    ∫⁻ p, ‖eclamp Φ T p‖ₑ ^ 2 ∂tsMeasure P T = sqIntegralOn P Φ T := by
  rw [tsMeasure, lintegral_prod_symm _ ((measurable_eclamp h T).enorm.pow_const 2).aemeasurable,
    sqIntegralOn_eq_clamp]
  simp [eclamp, enorm_toLp_sq]

theorem memLp_eclamp [SFinite P] (hΦ : IsProgressiveL2 P ℱ Φ) (T : ℝ) :
    MemLp (eclamp Φ T) 2 (tsMeasure P T) := by
  rw [memLp_iff]
  have h1 := lintegral_enorm_sq_eq_eLpNorm_sq (μ := tsMeasure P T)
    (measurable_eclamp hΦ.prog T).aestronglyMeasurable
  rw [lintegral_enorm_sq_eclamp hΦ.prog] at h1
  have h2 := hΦ.sq T
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at h1
  simp at h1
  rw [h1] at h2
  exact lt_irrefl _ h2

/-- the embedding of a progressive `L²` integrand on `[0, T]` into the Hilbert space
`L²([0, T] × Ω; ℝ^ι)` -/
def embL2 [SFinite P] (hΦ : IsProgressiveL2 P ℱ Φ) (T : ℝ) :
    Lp (EuclideanSpace ℝ ι) 2 (tsMeasure P T) :=
  (memLp_eclamp hΦ T).toLp _

theorem norm_embL2_sq [SFinite P] (hΦ : IsProgressiveL2 P ℱ Φ) (T : ℝ) :
    ‖embL2 hΦ T‖ ^ 2 = (sqIntegralOn P Φ T).toReal := by
  rw [embL2, norm_toLp_sq, lintegral_enorm_sq_eclamp hΦ.prog]

theorem inner_embL2 [IsProbabilityMeasure P] {Ψ : ℝ → Ω → ι → ℝ} (hΦ : IsProgressiveL2 P ℱ Φ)
    (hΨ : IsProgressiveL2 P ℱ Ψ) (T : ℝ) :
    inner ℝ (embL2 hΦ T) (embL2 hΨ T) = ∫ ω, (∫ s in Set.Icc 0 T, ∑ k, Φ s ω k * Ψ s ω k) ∂P := by
  rw [MeasureTheory.L2.inner_def]
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (embL2 hΦ T) (embL2 hΨ T)
  have hae : ∀ᵐ p ∂tsMeasure P T, inner ℝ ((embL2 hΦ T) p) ((embL2 hΨ T) p) =
      inner ℝ (eclamp Φ T p) (eclamp Ψ T p) := by
    filter_upwards [MemLp.coeFn_toLp (memLp_eclamp hΦ T), MemLp.coeFn_toLp (memLp_eclamp hΨ T)]
      with p h1 h2
    rw [embL2, embL2, h1, h2]
  rw [integral_congr_ae hae]
  have hint' := hint.congr hae
  rw [tsMeasure, integral_prod_symm _ (by rw [← tsMeasure]; exact hint')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp only [eclamp, min_eq_left hs.2, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_comm]

end Aux

theorem IsProgressiveL2.locL2 {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {Φ : ℝ → Ω → ι → ℝ}
    (h : IsProgressiveL2 P ℱ Φ) : IsProgressiveLocL2 P ℱ Φ := by
  refine ⟨h.prog, fun T => ?_⟩
  have h2 := h.sq T
  unfold sqIntegralOn at h2
  exact ae_lt_top (measurable_lintegral_sqSum' h.prog T) h2.ne

theorem IsProgressiveL2.add {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {Φ Φ' : ℝ → Ω → ι → ℝ}
    (h : IsProgressiveL2 P ℱ Φ) (h' : IsProgressiveL2 P ℱ Φ') :
    IsProgressiveL2 P ℱ (fun s ω => Φ s ω + Φ' s ω) := by
  refine ⟨isProgressive_add h.prog h'.prog, fun T => ?_⟩
  refine lt_of_le_of_lt (sqIntegralOn_add_le h.prog h'.prog T) ?_
  have := h.sq T
  have := h'.sq T
  finiteness

theorem IsProgressiveL2.smul {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {Φ : ℝ → Ω → ι → ℝ}
    (h : IsProgressiveL2 P ℱ Φ) (c : ℝ) : IsProgressiveL2 P ℱ (fun s ω => c • Φ s ω) := by
  refine ⟨isProgressive_smul h.prog c, fun T => ?_⟩
  rw [sqIntegralOn_smul]
  have := h.sq T
  finiteness

theorem IsProgressiveL2.sub {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {Φ Φ' : ℝ → Ω → ι → ℝ}
    (h : IsProgressiveL2 P ℱ Φ) (h' : IsProgressiveL2 P ℱ Φ') :
    IsProgressiveL2 P ℱ (fun s ω => Φ s ω - Φ' s ω) := by
  have := h.add (h'.smul (-1))
  convert this using 3
  simp [sub_eq_add_neg]

/-- A progressive integrand bounded by a constant is in the `L²` class. -/
theorem IsProgressiveL2.of_bounded (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {Φ : ℝ → Ω → ι → ℝ} (hΦ : IsProgressive ℱ Φ) (C : ℝ)
    (hC : ∀ s ω k, |Φ s ω k| ≤ C) : IsProgressiveL2 P ℱ Φ := by
  refine ⟨hΦ, fun T => ?_⟩
  calc sqIntegralOn P Φ T
      ≤ ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal C ^ 2) ∂P := by
        refine lintegral_mono fun ω => lintegral_mono fun s => ?_
        calc ∑ k, ‖Φ s ω k‖ₑ ^ 2 ≤ ∑ _k : ι, ENNReal.ofReal C ^ 2 := by
              refine Finset.sum_le_sum fun k _ => ?_
              refine pow_le_pow_left' ?_ 2
              rw [Real.enorm_eq_ofReal_abs]
              exact ENNReal.ofReal_le_ofReal (hC s ω k)
          _ = _ := by simp
    _ < ⊤ := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          measure_univ, mul_one, Real.volume_Icc]
        finiteness

theorem IsProgressiveL2.simple (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (Ψ : SimpleIntegrand ℱ ι) : IsProgressiveL2 P ℱ Ψ.toFun :=
  ⟨Ψ.isProgressive_toFun, fun T => Ψ.sqIntegralOn_toFun_lt_top P T⟩

/-- A constant (deterministic, time-independent) integrand. -/
theorem IsProgressiveL2.const (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (σ : ι → ℝ) : IsProgressiveL2 P ℱ (fun _ _ => σ) :=
  IsProgressiveL2.of_bounded P (isProgressive_const ℱ σ) (∑ j, |σ j|) fun _ _ k =>
    Finset.single_le_sum (f := fun j => |σ j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)

theorem sum_enorm_sq_eq_ofReal (x : ι → ℝ) :
    ∑ k, ‖x k‖ₑ ^ 2 = ENNReal.ofReal (∑ k, x k ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem isProgressive_comp_continuous {ℱ : Filtration ℝ mΩ}
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [TopologicalSpace.PseudoMetrizableSpace E] (X : ℝ → Ω → E) (hX : Adapted ℱ X)
    (hXc : ∀ ω, Continuous fun t => X t ω) (g : ℝ → E → ι → ℝ)
    (hg : Continuous (Function.uncurry g)) :
    IsProgressive ℱ (fun s ω => g s (X s ω)) := by
  have hprog : IsProgressive ℱ X :=
    ((hX.stronglyAdapted).isStronglyProgressive_of_continuous hXc).isProgressive
  intro i
  have h1 := hprog i
  have h2 : Measurable[Subtype.instMeasurableSpace.prod (ℱ i)]
      (fun p : Set.Iic i × Ω => ((p.1 : ℝ), X p.1 p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk h1
  exact hg.measurable.comp h2

theorem integrable_sq_aux {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {Φ : ℝ → Ω → ι → ℝ} (hΦ : IsProgressiveL2 P ℱ Φ) (t : ℝ) :
    (∀ᵐ ω ∂P, IntegrableOn (fun s => ∑ k, Φ s ω k ^ 2) (Set.Icc 0 t)) ∧
      Integrable (fun ω => ∫ s in Set.Icc 0 t, ∑ k, Φ s ω k ^ 2) P ∧
      ∫ ω, (∫ s in Set.Icc 0 t, ∑ k, Φ s ω k ^ 2) ∂P = (sqIntegralOn P Φ t).toReal := by
  have hm := measurable_clamp hΦ.prog t
  have hG : Measurable fun p : ℝ × Ω => ∑ k, Φ (min p.1 t) p.2 k ^ 2 :=
    Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).comp hm).pow_const 2
  have hF := measurable_lintegral_sqSum' hΦ.prog t
  have hfin : ∫⁻ ω, (∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P < ⊤ := hΦ.sq t
  have hae : ∀ᵐ ω ∂P, (∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k‖ₑ ^ 2) < ⊤ := ae_lt_top hF hfin.ne
  -- clamped section is measurable
  have hGs : ∀ ω, Measurable fun s : ℝ => ∑ k, Φ (min s t) ω k ^ 2 := fun ω => by
    have := hG.comp (measurable_prodMk_right (y := ω))
    exact this
  have hint : ∀ᵐ ω ∂P, IntegrableOn (fun s => ∑ k, Φ s ω k ^ 2) (Set.Icc 0 t) := by
    filter_upwards [hae] with ω hω
    have h1 : IntegrableOn (fun s => ∑ k, Φ (min s t) ω k ^ 2) (Set.Icc 0 t) := by
      refine ⟨(hGs ω).aestronglyMeasurable, ?_⟩
      have : ∀ s, ‖∑ k, Φ (min s t) ω k ^ 2‖ₑ = ∑ k, ‖Φ (min s t) ω k‖ₑ ^ 2 := fun s => by
        rw [sum_enorm_sq_eq_ofReal, Real.enorm_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
      simp_rw [HasFiniteIntegral, this, lintegral_sqSum_clamp Φ t]
      exact hω
    refine h1.congr_fun (fun s hs => ?_) measurableSet_Icc
    simp only [min_eq_left hs.2]
  have hsm : StronglyMeasurable fun ω => ∫ s in Set.Icc 0 t, ∑ k, Φ (min s t) ω k ^ 2 := by
    have := (hG.comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable
    exact this.integral_prod_right' (ν := volume.restrict (Set.Icc 0 t))
  have hsm' : StronglyMeasurable fun ω => ∫ s in Set.Icc 0 t, ∑ k, Φ s ω k ^ 2 := by
    convert hsm using 2 with ω
    exact setIntegral_congr_fun measurableSet_Icc fun s hs => by simp only [min_eq_left hs.2]
  refine ⟨hint, ?_, ?_⟩
  · refine ⟨hsm'.aestronglyMeasurable, ?_⟩
    calc ∫⁻ ω, ‖∫ s in Set.Icc 0 t, ∑ k, Φ s ω k ^ 2‖ₑ ∂P
        ≤ ∫⁻ ω, (∫⁻ s in Set.Icc 0 t, ‖∑ k, Φ s ω k ^ 2‖ₑ) ∂P :=
          lintegral_mono fun ω => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ ω, (∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P := by
          refine lintegral_congr fun ω => lintegral_congr fun s => ?_
          rw [sum_enorm_sq_eq_ofReal, Real.enorm_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
      _ < ⊤ := hfin
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
      setIntegral_nonneg measurableSet_Icc fun s _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
      hsm'.aestronglyMeasurable]
    unfold sqIntegralOn
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hint] with ω hω
    rw [ofReal_integral_eq_lintegral_ofReal hω
      (Filter.Eventually.of_forall fun s => Finset.sum_nonneg fun k _ => sq_nonneg _)]
    refine lintegral_congr fun s => ?_
    rw [sum_enorm_sq_eq_ofReal]

/-- An integrand of the form `Φ_s = g (s, X_s)` with `X` continuous and adapted (values in a
second-countable Borel space) and `g` continuous is progressive and locally square-integrable
pathwise. This is the class of integrands produced by Itô's formula. -/
theorem IsProgressiveLocL2.of_continuous (P : Measure Ω) {ℱ : Filtration ℝ mΩ}
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [TopologicalSpace.PseudoMetrizableSpace E] (X : ℝ → Ω → E) (hX : Adapted ℱ X)
    (hXc : ∀ ω, Continuous fun t => X t ω) (g : ℝ → E → ι → ℝ)
    (hg : Continuous (Function.uncurry g)) :
    IsProgressiveLocL2 P ℱ (fun s ω => g s (X s ω)) := by
  refine ⟨isProgressive_comp_continuous X hX hXc g hg, fun T => Filter.Eventually.of_forall fun ω => ?_⟩
  have hc : Continuous fun s => ∑ k, g s (X s ω) k ^ 2 := by
    refine continuous_finsetSum _ fun k _ => ?_
    have : Continuous fun s => g s (X s ω) k :=
      (continuous_apply k).comp (hg.comp (continuous_id.prodMk (hXc ω)))
    exact this.pow 2
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hc.continuousOn
  calc ∫⁻ s in Set.Icc 0 T, ∑ k, ‖g s (X s ω) k‖ₑ ^ 2
      ≤ ∫⁻ s in Set.Icc 0 T, ENNReal.ofReal C := by
        refine lintegral_mono_ae ?_
        refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
        rw [sum_enorm_sq_eq_ofReal]
        exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC s hs))
    _ < ⊤ := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Icc]
        finiteness

/-- The continuous adapted integrand `g (s, X_s)` with `g` bounded is in the `L²` class. -/
theorem IsProgressiveL2.of_continuous_bounded (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [TopologicalSpace.PseudoMetrizableSpace E] (X : ℝ → Ω → E) (hX : Adapted ℱ X)
    (hXc : ∀ ω, Continuous fun t => X t ω) (g : ℝ → E → ι → ℝ)
    (hg : Continuous (Function.uncurry g)) (C : ℝ) (hC : ∀ s x k, |g s x k| ≤ C) :
    IsProgressiveL2 P ℱ (fun s ω => g s (X s ω)) :=
  IsProgressiveL2.of_bounded P (isProgressive_comp_continuous X hX hXc g hg) C fun s ω k =>
    hC s (X s ω) k

/-! ### The integral in the `L²` class -/

/-- `M` is the Itô integral `∫_0^· Φ · dW`: continuous adapted, zero on `(-∞, 0]`, and at every
`t ≥ 0` the `L²`-limit of the elementary integrals along every sequence of simple integrands
converging to `Φ` in `L²([0, t] × Ω)`. -/
structure IsItoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) (M : ℝ → Ω → ℝ) : Prop where
  cont : ∀ ω, Continuous fun t => M t ω
  adapted : Adapted ℱ M
  zero : ∀ t : ℝ, t ≤ 0 → ∀ ω, M t ω = 0
  approx : ∀ t : ℝ, 0 ≤ t → ∀ Ψ : ℕ → SimpleIntegrand ℱ ι,
    Tendsto (fun n => sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t) atTop (𝓝 0) →
    Tendsto (fun n => ∫⁻ ω, ‖(Ψ n).elemIntegral W t ω - M t ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)

open Classical in
/-- The Itô integral `t ↦ ∫_0^t Φ_s · dW_s` (a process indexed by `ℝ`, vanishing for `t ≤ 0`):
the process characterised by `IsItoIntegral` when it exists, `0` otherwise. -/
def itoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) : ℝ → Ω → ℝ :=
  if h : ∃ M, IsItoIntegral P ℱ W Φ M then h.choose else 0

/-! ### Hilbert space bookkeeping -/

section Hilbert

theorem norm_sub_eq_of_inner_eq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {a b : E} {a' b' : F}
    (haa : inner ℝ a a = inner ℝ a' a') (hab : inner ℝ a b = inner ℝ a' b')
    (hbb : inner ℝ b b = inner ℝ b' b') : ‖a - b‖ = ‖a' - b'‖ := by
  have h1 : ‖a - b‖ ^ 2 = ‖a' - b'‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm a b, real_inner_comm a' b', haa, hab,
      hbb]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

theorem eq_add_of_inner_eq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {a b c : E} {a' b' c' : F}
    (haa : inner ℝ a a = inner ℝ a' a') (hbb : inner ℝ b b = inner ℝ b' b')
    (hcc : inner ℝ c c = inner ℝ c' c') (hab : inner ℝ a b = inner ℝ a' b')
    (hac : inner ℝ a c = inner ℝ a' c') (hbc : inner ℝ b c = inner ℝ b' c')
    (h' : a' = b' + c') : a = b + c := by
  have h1 : inner ℝ (a - (b + c)) (a - (b + c)) = inner ℝ (a' - (b' + c')) (a' - (b' + c')) := by
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_comm a b, real_inner_comm a' b', real_inner_comm a c, real_inner_comm a' c',
      real_inner_comm b c, real_inner_comm b' c', haa, hbb, hcc, hab, hac, hbc]
  rw [h', sub_self, inner_zero_left, inner_self_eq_zero] at h1
  rw [sub_eq_zero] at h1
  exact h1

theorem eq_smul_of_inner_eq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {a b : E} {a' b' : F} (r : ℝ)
    (haa : inner ℝ a a = inner ℝ a' a') (hbb : inner ℝ b b = inner ℝ b' b')
    (hab : inner ℝ a b = inner ℝ a' b') (h' : a' = r • b') : a = r • b := by
  have h1 : inner ℝ (a - r • b) (a - r • b) = inner ℝ (a' - r • b') (a' - r • b') := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      real_inner_comm a b, real_inner_comm a' b', haa, hbb, hab]
  rw [h', sub_self, inner_zero_left, inner_self_eq_zero] at h1
  rwa [sub_eq_zero] at h1

theorem tendsto_norm_of_sq {E : Type*} [NormedAddCommGroup E] {x : ℕ → E}
    (h : Tendsto (fun n => ‖x n‖ ^ 2) atTop (𝓝 0)) : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).comp h
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

end Hilbert

section Bridge

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

theorem norm_sub_toLp_sq {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    ‖hX.toLp X - hY.toLp Y‖ ^ 2 = (∫⁻ ω, ‖X ω - Y ω‖ₑ ^ 2 ∂P).toReal := by
  rw [← MemLp.toLp_sub hX hY, norm_toLp_sq]
  rfl

theorem inner_toLp {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    inner ℝ (hX.toLp X) (hY.toLp Y) = ∫ ω, X ω * Y ω ∂P := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem lintegral_enorm_sq_lt_top {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂P < ⊤ := by
  rw [lintegral_enorm_sq_eq_eLpNorm_sq hX.aestronglyMeasurable]
  exact ENNReal.pow_lt_top hX.eLpNorm_lt_top

end Bridge

section Simple

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} {Φ : ℝ → Ω → ι → ℝ}

theorem embL2_sub [IsProbabilityMeasure P] {Φ' : ℝ → Ω → ι → ℝ} (hΦ : IsProgressiveL2 P ℱ Φ)
    (hΦ' : IsProgressiveL2 P ℱ Φ') (T : ℝ) :
    embL2 (hΦ.sub hΦ') T = embL2 hΦ T - embL2 hΦ' T := by
  unfold embL2
  rw [← MemLp.toLp_sub (memLp_eclamp hΦ T) (memLp_eclamp hΦ' T)]
  refine MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq ?_)
  funext p
  simp [eclamp]

theorem embL2_add [IsProbabilityMeasure P] {Φ' : ℝ → Ω → ι → ℝ} (hΦ : IsProgressiveL2 P ℱ Φ)
    (hΦ' : IsProgressiveL2 P ℱ Φ') (T : ℝ) :
    embL2 (hΦ.add hΦ') T = embL2 hΦ T + embL2 hΦ' T := by
  unfold embL2
  rw [← MemLp.toLp_add (memLp_eclamp hΦ T) (memLp_eclamp hΦ' T)]
  refine MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq ?_)
  funext p
  simp [eclamp]

theorem embL2_smul [IsProbabilityMeasure P] (hΦ : IsProgressiveL2 P ℱ Φ) (c : ℝ) (T : ℝ) :
    embL2 (hΦ.smul c) T = c • embL2 hΦ T := by
  unfold embL2
  rw [← MemLp.toLp_const_smul c (memLp_eclamp hΦ T)]
  refine MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq ?_)
  funext p
  simp [eclamp]

/-- A sequence of simple integrands converging to `Φ` in `L²([0, t] × Ω)`. -/
def IsApprox (P : Measure Ω) (Φ : ℝ → Ω → ι → ℝ) (Ψ : ℕ → SimpleIntegrand ℱ ι) (t : ℝ) : Prop :=
  Tendsto (fun n => sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t) atTop (𝓝 0)

theorem IsApprox.mono {Ψ : ℕ → SimpleIntegrand ℱ ι} {t t' : ℝ} (h : IsApprox P Φ Ψ t')
    (htt : t ≤ t') : IsApprox P Φ Ψ t :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    (fun _ => sqIntegralOn_mono P _ htt)

theorem tendsto_embL2_of_isApprox [IsProbabilityMeasure P] (hΦ : IsProgressiveL2 P ℱ Φ)
    {Ψ : ℕ → SimpleIntegrand ℱ ι} {t : ℝ} (h : IsApprox P Φ Ψ t) :
    Tendsto (fun n => embL2 (IsProgressiveL2.simple P (Ψ n)) t) atTop (𝓝 (embL2 hΦ t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ n, ‖embL2 (IsProgressiveL2.simple P (Ψ n)) t - embL2 hΦ t‖ ^ 2 =
      (sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t).toReal := fun n => by
    rw [← embL2_sub (IsProgressiveL2.simple P (Ψ n)) hΦ t,
      norm_embL2_sq (IsProgressiveL2.simple P (Ψ n) |>.sub hΦ)]
  refine tendsto_norm_of_sq ?_
  simp_rw [key]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def] using this

variable [IsProbabilityMeasure P]

theorem inner_elemIntegral_eq (hW : IsBrownianFiltration P ℱ W) (Ψ Ψ' : SimpleIntegrand ℱ ι)
    (t : ℝ) :
    inner ℝ ((SimpleIntegrand.memLp_elemIntegral hW Ψ t 2 (by norm_num)).toLp _)
      ((SimpleIntegrand.memLp_elemIntegral hW Ψ' t 2 (by norm_num)).toLp _) =
    inner ℝ (embL2 (IsProgressiveL2.simple P Ψ) t) (embL2 (IsProgressiveL2.simple P Ψ') t) := by
  rw [inner_toLp, inner_embL2, SimpleIntegrand.integral_elemIntegral_mul hW]

/-- **Isometry for differences of elementary integrals.** -/
theorem lintegral_elemIntegral_sub_sq (hW : IsBrownianFiltration P ℱ W)
    (Ψ Ψ' : SimpleIntegrand ℱ ι) (t : ℝ) :
    ∫⁻ ω, ‖Ψ.elemIntegral W t ω - Ψ'.elemIntegral W t ω‖ₑ ^ 2 ∂P =
      sqIntegralOn P (fun s ω => Ψ.toFun s ω - Ψ'.toFun s ω) t := by
  have hA := SimpleIntegrand.memLp_elemIntegral hW Ψ t 2 (by norm_num)
  have hA' := SimpleIntegrand.memLp_elemIntegral hW Ψ' t 2 (by norm_num)
  have hn := norm_sub_eq_of_inner_eq (inner_elemIntegral_eq hW Ψ Ψ t)
    (inner_elemIntegral_eq hW Ψ Ψ' t) (inner_elemIntegral_eq hW Ψ' Ψ' t)
  have h2 : ‖(hA.toLp _) - (hA'.toLp _)‖ ^ 2 =
      ‖embL2 (IsProgressiveL2.simple P Ψ) t - embL2 (IsProgressiveL2.simple P Ψ') t‖ ^ 2 := by
    rw [hn]
  rw [norm_sub_toLp_sq hA hA', ← embL2_sub (IsProgressiveL2.simple P Ψ) (IsProgressiveL2.simple P Ψ'),
    norm_embL2_sq (IsProgressiveL2.simple P Ψ |>.sub (IsProgressiveL2.simple P Ψ'))] at h2
  rw [ENNReal.toReal_eq_toReal_iff'] at h2
  · exact h2
  · exact (lintegral_enorm_sq_lt_top (hA.sub hA')).ne
  · exact ((IsProgressiveL2.simple P Ψ |>.sub (IsProgressiveL2.simple P Ψ')).sq t).ne

end Simple


section Characterisation

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} {Φ Φ' : ℝ → Ω → ι → ℝ}

theorem lintegral_enorm_sq_add_le {X Y : Ω → ℝ} (hX : AEMeasurable X P) :
    ∫⁻ ω, ‖X ω + Y ω‖ₑ ^ 2 ∂P ≤ 2 * ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂P + 2 * ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂P := by
  calc ∫⁻ ω, ‖X ω + Y ω‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, (2 * ‖X ω‖ₑ ^ 2 + 2 * ‖Y ω‖ₑ ^ 2) ∂P :=
        lintegral_mono fun ω => enorm_add_sq_le _ _
    _ = _ := by
        rw [lintegral_add_left' ((hX.enorm.pow_const 2).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

theorem tendsto_two_mul_add {a b : ℕ → ℝ≥0∞} (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) : Tendsto (fun n => 2 * a n + 2 * b n) atTop (𝓝 0) := by
  have h1 := ENNReal.Tendsto.const_mul ha (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have h2 := ENNReal.Tendsto.const_mul hb (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  simpa using h1.add h2


theorem memLp_of_tendsto_lintegral {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P)
    (hX : ∀ n, MemLp (X n) 2 P)
    (h : Tendsto (fun n => ∫⁻ ω, ‖X n ω - Y ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) : MemLp Y 2 P := by
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have hm : AEStronglyMeasurable (fun ω => X n ω - Y ω) P := (hX n).aestronglyMeasurable.sub hY
  rw [lintegral_enorm_sq_eq_eLpNorm_sq hm] at hn
  have h1 : MemLp (fun ω => X n ω - Y ω) 2 P := by
    rw [memLp_iff]
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at hn
    simp at hn
  have := (hX n).sub h1
  convert this using 1
  funext ω
  simp

theorem tendsto_toLp_of_tendsto_lintegral {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hY : MemLp Y 2 P)
    (h : Tendsto (fun n => ∫⁻ ω, ‖X n ω - Y ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hY.toLp Y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_norm_of_sq ?_
  simp_rw [norm_sub_toLp_sq (hX _) hY]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def] using this

end Characterisation


section Characterisation2

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}
  {Φ Φ' : ℝ → Ω → ι → ℝ}

/-- It suffices to check the `L²`-limit property along one approximating sequence per time. -/
theorem isItoIntegral_of_exists_seq (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {M : ℝ → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => M t ω)
    (hadapted : Adapted ℱ M) (hzero : ∀ t : ℝ, t ≤ 0 → ∀ ω, M t ω = 0)
    (hseq : ∀ t : ℝ, 0 ≤ t → ∃ Ξ : ℕ → SimpleIntegrand ℱ ι, IsApprox P Φ Ξ t ∧
      Tendsto (fun n => ∫⁻ ω, ‖(Ξ n).elemIntegral W t ω - M t ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    IsItoIntegral P ℱ W Φ M := by
  refine ⟨hcont, hadapted, hzero, fun t ht Ψ hΨ => ?_⟩
  obtain ⟨Ξ, hΞ, hΞM⟩ := hseq t ht
  have hb : ∀ n, sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - (Ξ n).toFun s ω) t ≤
      2 * sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t +
        2 * sqIntegralOn P (fun s ω => Φ s ω - (Ξ n).toFun s ω) t := fun n => by
    have := sqIntegralOn_add_le (P := P) (isProgressive_sub (Ψ n).isProgressive_toFun hΦ.prog)
      (isProgressive_sub hΦ.prog (Ξ n).isProgressive_toFun) t
    convert this using 3
    simp
  have hΞ' : Tendsto (fun n => sqIntegralOn P (fun s ω => Φ s ω - (Ξ n).toFun s ω) t) atTop
      (𝓝 0) := by
    simp_rw [sqIntegralOn_sub_comm Φ]
    exact hΞ
  have hbound : Tendsto (fun n => 2 * (2 * sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t +
        2 * sqIntegralOn P (fun s ω => Φ s ω - (Ξ n).toFun s ω) t) +
        2 * ∫⁻ ω, ‖(Ξ n).elemIntegral W t ω - M t ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) :=
    tendsto_two_mul_add (tendsto_two_mul_add hΨ hΞ') hΞM
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun _ => bot_le)
    (fun n => ?_)
  have hI : AEMeasurable (fun ω => (Ψ n).elemIntegral W t ω - (Ξ n).elemIntegral W t ω) P :=
    ((SimpleIntegrand.memLp_elemIntegral hW (Ψ n) t 2 (by norm_num)).aestronglyMeasurable.sub
      (SimpleIntegrand.memLp_elemIntegral hW (Ξ n) t 2 (by norm_num)).aestronglyMeasurable).aemeasurable
  calc ∫⁻ ω, ‖(Ψ n).elemIntegral W t ω - M t ω‖ₑ ^ 2 ∂P
      = ∫⁻ ω, ‖((Ψ n).elemIntegral W t ω - (Ξ n).elemIntegral W t ω) +
          ((Ξ n).elemIntegral W t ω - M t ω)‖ₑ ^ 2 ∂P := by simp
    _ ≤ 2 * ∫⁻ ω, ‖(Ψ n).elemIntegral W t ω - (Ξ n).elemIntegral W t ω‖ₑ ^ 2 ∂P +
          2 * ∫⁻ ω, ‖(Ξ n).elemIntegral W t ω - M t ω‖ₑ ^ 2 ∂P := lintegral_enorm_sq_add_le hI
    _ ≤ _ := by
        rw [lintegral_elemIntegral_sub_sq hW]
        gcongr
        exact hb n

theorem sqIntegralOn_of_neg (P : Measure Ω) (Φ : ℝ → Ω → ι → ℝ) {T : ℝ} (hT : T < 0) :
    sqIntegralOn P Φ T = 0 := by
  simp [sqIntegralOn, Set.Icc_eq_empty (not_le.2 hT)]

theorem IsItoIntegral.memLp (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    {M : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M) (t : ℝ) : MemLp (M t) 2 P := by
  rcases lt_or_ge t 0 with ht | ht
  · have : M t = fun _ => 0 := funext fun ω => hM.zero t ht.le ω
    rw [this]
    exact MemLp.zero'
  · obtain ⟨Ψ, hΨ⟩ := exists_simple_approx P ℱ Φ hΦ.prog t (hΦ.sq t)
    exact memLp_of_tendsto_lintegral
      ((hM.adapted t).mono (ℱ.le t) le_rfl).aestronglyMeasurable
      (fun n => SimpleIntegrand.memLp_elemIntegral hW (Ψ n) t 2 (by norm_num)) (hM.approx t ht Ψ hΨ)

theorem IsItoIntegral.inner_eq (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    (hΦ' : IsProgressiveL2 P ℱ Φ') {M M' : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M)
    (hM' : IsItoIntegral P ℱ W Φ' M') {t : ℝ} (ht : 0 ≤ t) :
    inner ℝ ((hM.memLp hW hΦ t).toLp _) ((hM'.memLp hW hΦ' t).toLp _) =
      inner ℝ (embL2 hΦ t) (embL2 hΦ' t) := by
  obtain ⟨Ψ, hΨ⟩ := exists_simple_approx P ℱ Φ hΦ.prog t (hΦ.sq t)
  obtain ⟨Ψ', hΨ'⟩ := exists_simple_approx P ℱ Φ' hΦ'.prog t (hΦ'.sq t)
  have h1 := tendsto_toLp_of_tendsto_lintegral
    (fun n => SimpleIntegrand.memLp_elemIntegral hW (Ψ n) t 2 (by norm_num)) (hM.memLp hW hΦ t)
    (hM.approx t ht Ψ hΨ)
  have h2 := tendsto_toLp_of_tendsto_lintegral
    (fun n => SimpleIntegrand.memLp_elemIntegral hW (Ψ' n) t 2 (by norm_num)) (hM'.memLp hW hΦ' t)
    (hM'.approx t ht Ψ' hΨ')
  have h3 := tendsto_embL2_of_isApprox hΦ hΨ
  have h4 := tendsto_embL2_of_isApprox hΦ' hΨ'
  refine tendsto_nhds_unique (h1.inner h2) ?_
  convert h3.inner h4 using 1
  funext n
  exact inner_elemIntegral_eq hW (Ψ n) (Ψ' n) t

theorem IsItoIntegral.integral_mul (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    (hΦ' : IsProgressiveL2 P ℱ Φ') {M M' : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M)
    (hM' : IsItoIntegral P ℱ W Φ' M') (t : ℝ) :
    ∫ ω, M t ω * M' t ω ∂P = ∫ ω, (∫ s in Set.Icc 0 t, ∑ k, Φ s ω k * Φ' s ω k) ∂P := by
  rcases lt_or_ge t 0 with ht | ht
  · simp [hM.zero t ht.le, Set.Icc_eq_empty (not_le.2 ht)]
  · rw [← inner_embL2 hΦ hΦ' t, ← hM.inner_eq hW hΦ hΦ' hM' ht, inner_toLp]

theorem IsItoIntegral.lintegral_sub_sq (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (hΦ' : IsProgressiveL2 P ℱ Φ') {M M' : ℝ → Ω → ℝ}
    (hM : IsItoIntegral P ℱ W Φ M) (hM' : IsItoIntegral P ℱ W Φ' M') (t : ℝ) :
    ∫⁻ ω, ‖M t ω - M' t ω‖ₑ ^ 2 ∂P = sqIntegralOn P (fun s ω => Φ s ω - Φ' s ω) t := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [sqIntegralOn_of_neg P _ ht]
    simp [hM.zero t ht.le, hM'.zero t ht.le]
  · have hn := norm_sub_eq_of_inner_eq (hM.inner_eq hW hΦ hΦ hM ht)
      (hM.inner_eq hW hΦ hΦ' hM' ht) (hM'.inner_eq hW hΦ' hΦ' hM' ht)
    have h2 : ‖((hM.memLp hW hΦ t).toLp _) - ((hM'.memLp hW hΦ' t).toLp _)‖ ^ 2 =
        ‖embL2 hΦ t - embL2 hΦ' t‖ ^ 2 := by rw [hn]
    rw [norm_sub_toLp_sq, ← embL2_sub hΦ hΦ', norm_embL2_sq (hΦ.sub hΦ')] at h2
    rw [ENNReal.toReal_eq_toReal_iff'] at h2
    · exact h2
    · exact (lintegral_enorm_sq_lt_top ((hM.memLp hW hΦ t).sub (hM'.memLp hW hΦ' t))).ne
    · exact ((hΦ.sub hΦ').sq t).ne

theorem ae_eq_zero_of_lintegral_enorm_sq_eq_zero {X : Ω → ℝ} (hX : AEMeasurable X P)
    (h : ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂P = 0) : X =ᵐ[P] 0 := by
  rw [lintegral_eq_zero_iff' (hX.enorm.pow_const 2)] at h
  filter_upwards [h] with ω hω
  simpa using hω

/-- Two Itô integrals of the same integrand are indistinguishable (this version assumes that
`W` is a Brownian filtration, which is needed for the measurability of the elementary integrals;
see the report on `IsItoIntegral.ae_eq_forall`). -/
theorem IsItoIntegral.ae_eq_forall_of_brownian (hW : IsBrownianFiltration P ℱ W)
    {M M' : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M) (hM' : IsItoIntegral P ℱ W Φ M')
    (hΦ : IsProgressiveL2 P ℱ Φ) : ∀ᵐ ω ∂P, ∀ t, M t ω = M' t ω := by
  refine ae_forall_eq_of_continuous P M M' hM.cont hM'.cont fun t => ?_
  have h := hM.lintegral_sub_sq hW hΦ hΦ hM' t
  have h0 : sqIntegralOn P (fun s ω => Φ s ω - Φ s ω) t = 0 := by simp [sqIntegralOn]
  rw [h0] at h
  have hmeas : AEMeasurable (fun ω => M t ω - M' t ω) P :=
    (((hM.adapted t).mono (ℱ.le t) le_rfl).sub ((hM'.adapted t).mono (ℱ.le t) le_rfl)).aemeasurable
  have := ae_eq_zero_of_lintegral_enorm_sq_eq_zero hmeas h
  filter_upwards [this] with ω hω
  simpa [sub_eq_zero] using hω

end Characterisation2

/-! ### Kolmogorov--Doob weak-type maximal inequality for continuous `L²` martingales -/

theorem kolmogorov_discrete {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {X : ℝ → Ω → ℝ} (hX : Martingale X ℱ P) (hL2 : ∀ t, MemLp (X t) 2 P) (u : ℕ → ℝ)
    (hu : Monotone u) (n : ℕ) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) ^ 2 * P {ω | ∃ k ≤ n, (ε : ℝ) < |X (u k) ω|} ≤ ∫⁻ ω, ‖X (u n) ω‖ₑ ^ 2 ∂P := by
  let 𝒢 : Filtration ℕ mΩ := ⟨fun k => ℱ (u k), fun i j hij => ℱ.mono (hu hij), fun k => ℱ.le _⟩
  have hsub : Submartingale (fun k ω => X (u k) ω ^ 2) 𝒢 P := by
    refine ⟨fun k => ?_, fun i j hij => ?_, fun k => (hL2 _).integrable_sq⟩
    · exact (hX.1 (u k)).pow 2
    · have hm := ℱ.le (u i)
      have h1 := condVar_ae_eq_condExp_sq_sub_sq_condExp hm (hL2 (u j))
      have h2 := hX.2 (u i) (u j) (hu hij)
      have h3 : 0 ≤ᵐ[P] Var[X (u j); P | ℱ (u i)] := by
        unfold condVar
        exact condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      filter_upwards [h1, h2, h3] with ω a b c
      simp only [Pi.sub_apply, Pi.pow_apply] at a
      simp only [Pi.zero_apply] at c
      have : (P[X (u j) | ℱ (u i)]) ω = X (u i) ω := b
      show X (u i) ω ^ 2 ≤ (P[fun ω => X (u j) ω ^ 2 | ℱ (u i)]) ω
      rw [← this]
      have : (P[X (u j) ^ 2 | ℱ (u i)]) ω = (P[fun ω => X (u j) ω ^ 2 | ℱ (u i)]) ω := rfl
      linarith
  have key := maximal_ineq hsub (fun k ω => sq_nonneg _) (ε := ε ^ 2) n
  have hint : Integrable (fun ω => X (u n) ω ^ 2) P := (hL2 _).integrable_sq
  have hsubset : {ω | ∃ k ≤ n, (ε : ℝ) < |X (u k) ω|} ⊆ {ω | ((ε ^ 2 : ℝ≥0) : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => X (u k) ω ^ 2} := by
    rintro ω ⟨k, hk, hlt⟩
    have hk' : k ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
    have h1 : (ε : ℝ) ^ 2 ≤ X (u k) ω ^ 2 := by
      have h0 : (0 : ℝ) ≤ ε := ε.2
      have := pow_le_pow_left₀ h0 hlt.le 2
      rwa [sq_abs] at this
    exact h1.trans (Finset.le_sup' (fun k => X (u k) ω ^ 2) hk')
  calc (ε : ℝ≥0∞) ^ 2 * P {ω | ∃ k ≤ n, (ε : ℝ) < |X (u k) ω|}
      ≤ ((ε ^ 2 : ℝ≥0) : ℝ≥0∞) * P {ω | ((ε ^ 2 : ℝ≥0) : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => X (u k) ω ^ 2} := by
        push_cast
        exact mul_le_mul_right (measure_mono hsubset) _
    _ ≤ _ := key
    _ ≤ ENNReal.ofReal (∫ ω, X (u n) ω ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal (setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun ω => sq_nonneg _))
    _ = ∫⁻ ω, ‖X (u n) ω‖ₑ ^ 2 ∂P := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
        refine lintegral_congr fun ω => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]


/-- the dyadic grid of `[0, N]` of mesh `N / 2^m` -/
def dyadicGrid (N : ℝ) (m : ℕ) (k : ℕ) : ℝ := N * (min k (2 ^ m) : ℕ) / 2 ^ m

theorem dyadicGrid_mono (N : ℝ) (hN : 0 ≤ N) (m : ℕ) : Monotone (dyadicGrid N m) := by
  intro i j hij
  unfold dyadicGrid
  have : ((min i (2 ^ m) : ℕ) : ℝ) ≤ ((min j (2 ^ m) : ℕ) : ℝ) := by exact_mod_cast min_le_min_right _ hij
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_le_div_iff_of_pos_right h2]
  exact mul_le_mul_of_nonneg_left this hN

theorem dyadicGrid_top (N : ℝ) (m : ℕ) : dyadicGrid N m (2 ^ m) = N := by
  unfold dyadicGrid
  have h2 : (2 : ℝ) ^ m ≠ 0 := by positivity
  simp [h2]

theorem dyadicGrid_succ (N : ℝ) (m k : ℕ) (hk : k ≤ 2 ^ m) :
    dyadicGrid N (m + 1) (2 * k) = dyadicGrid N m k := by
  unfold dyadicGrid
  have h1 : min (2 * k) (2 ^ (m + 1)) = 2 * k := min_eq_left (by rw [pow_succ]; omega)
  have h2 : min k (2 ^ m) = k := min_eq_left hk
  rw [h1, h2]
  push_cast
  rw [pow_succ]
  field_simp

theorem exists_dyadicGrid_near (N : ℝ) (hN : 0 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc 0 N) {δ : ℝ}
    (hδ : 0 < δ) : ∃ m k : ℕ, k ≤ 2 ^ m ∧ |dyadicGrid N m k - t| < δ := by
  rcases hN.eq_or_lt with h0 | hpos
  · subst h0
    have : t = 0 := le_antisymm ht.2 ht.1
    exact ⟨0, 0, by simp, by simp [dyadicGrid, this, hδ]⟩
  · obtain ⟨m, hm⟩ := exists_nat_gt (N / δ)
    have hm2 : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have hNm : N < δ * 2 ^ m := by
      have h : N / δ < 2 ^ m := hm.trans_le hm2
      rwa [div_lt_iff₀ hδ, mul_comm] at h
    set x : ℝ := t * 2 ^ m / N with hx
    have hx0 : 0 ≤ x := div_nonneg (mul_nonneg ht.1 h2.le) hpos.le
    have hxle : x ≤ 2 ^ m := by
      rw [hx, div_le_iff₀ hpos]
      nlinarith [ht.2]
    have hk : ⌊x⌋₊ ≤ 2 ^ m := by
      have : (⌊x⌋₊ : ℝ) ≤ 2 ^ m := (Nat.floor_le hx0).trans hxle
      exact_mod_cast this
    refine ⟨m, ⌊x⌋₊, hk, ?_⟩
    have hgrid : dyadicGrid N m ⌊x⌋₊ = N * ⌊x⌋₊ / 2 ^ m := by
      unfold dyadicGrid; rw [min_eq_left hk]
    have htx : t = N * x / 2 ^ m := by
      rw [hx]; field_simp
    have e : t - dyadicGrid N m ⌊x⌋₊ = N * (x - ⌊x⌋₊) / 2 ^ m := by
      rw [hgrid]; nth_rewrite 1 [htx]; ring
    have h3 := Nat.lt_floor_add_one x
    have h4 := Nat.floor_le hx0
    rw [abs_sub_comm, abs_of_nonneg (by rw [e]; exact div_nonneg (mul_nonneg hpos.le (by linarith)) h2.le),
      e, div_lt_iff₀ h2]
    nlinarith

theorem kolmogorov_cont {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {X : ℝ → Ω → ℝ} (hX : Martingale X ℱ P) (hL2 : ∀ t, MemLp (X t) 2 P)
    (hcont : ∀ ω, Continuous fun t => X t ω) {N : ℝ} (hN : 0 ≤ N) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) ^ 2 * P {ω | ∃ t ∈ Set.Icc 0 N, (ε : ℝ) < |X t ω|} ≤ ∫⁻ ω, ‖X N ω‖ₑ ^ 2 ∂P := by
  set A : ℕ → Set Ω := fun m => {ω | ∃ k ≤ 2 ^ m, (ε : ℝ) < |X (dyadicGrid N m k) ω|} with hAdef
  have hA : ∀ m, (ε : ℝ≥0∞) ^ 2 * P (A m) ≤ ∫⁻ ω, ‖X N ω‖ₑ ^ 2 ∂P := fun m => by
    have := kolmogorov_discrete hX hL2 (dyadicGrid N m) (dyadicGrid_mono N hN m) (2 ^ m) ε
    rwa [dyadicGrid_top] at this
  have hmono : Monotone A := by
    refine monotone_nat_of_le_succ fun m ω hω => ?_
    obtain ⟨k, hk, h⟩ := hω
    refine ⟨2 * k, by rw [pow_succ]; omega, ?_⟩
    rw [dyadicGrid_succ N m k hk]
    exact h
  have hsub : {ω | ∃ t ∈ Set.Icc 0 N, (ε : ℝ) < |X t ω|} ⊆ ⋃ m, A m := by
    rintro ω ⟨t, ht, hlt⟩
    have hopen : IsOpen {s : ℝ | (ε : ℝ) < |X s ω|} :=
      isOpen_lt continuous_const (continuous_abs.comp (hcont ω))
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen t hlt
    obtain ⟨m, k, hk, hnear⟩ := exists_dyadicGrid_near N hN ht hδ
    refine Set.mem_iUnion.2 ⟨m, k, hk, ?_⟩
    exact hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hnear)
  calc (ε : ℝ≥0∞) ^ 2 * P {ω | ∃ t ∈ Set.Icc 0 N, (ε : ℝ) < |X t ω|}
      ≤ (ε : ℝ≥0∞) ^ 2 * P (⋃ m, A m) := mul_le_mul_right (measure_mono hsub) _
    _ = (ε : ℝ≥0∞) ^ 2 * ⨆ m, P (A m) := by rw [hmono.measure_iUnion]
    _ = ⨆ m, (ε : ℝ≥0∞) ^ 2 * P (A m) := ENNReal.mul_iSup _ _
    _ ≤ _ := iSup_le hA


/-! ### Construction of the integral: fast approximation and uniform convergence -/

theorem exists_continuous_limit (f : ℕ → ℝ → ℝ) (hf : ∀ n, Continuous (f n))
    (hz : ∀ n t, t ≤ 0 → f n t = 0)
    (h : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Set.Icc (0 : ℝ) N,
      |f (n + 1) t - f n t| ≤ (2⁻¹ : ℝ) ^ n) :
    ∃ L : ℝ → ℝ, Continuous L ∧ ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (L t)) := by
  have h' : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ≤ (N : ℝ), |f (n + 1) t - f n t| ≤ (2⁻¹ : ℝ) ^ n := by
    intro N
    obtain ⟨n0, hn0⟩ := h N
    refine ⟨n0, fun n hn t ht => ?_⟩
    rcases le_or_gt t 0 with ht0 | ht0
    · rw [hz _ _ ht0, hz _ _ ht0]; simp
    · exact hn0 n hn t ⟨ht0.le, ht⟩
  -- pointwise limits
  have hlim : ∀ t : ℝ, ∃ ℓ, Tendsto (fun n => f n t) atTop (𝓝 ℓ) := by
    intro t
    obtain ⟨n0, hn0⟩ := h' ⌈t⌉₊
    have htN : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have hc : CauchySeq (fun j => f (n0 + j) t) := by
      refine cauchySeq_of_le_geometric_two (C := 2 * 2⁻¹ ^ n0) ?_
      intro j
      rw [Real.dist_eq, abs_sub_comm]
      refine (hn0 (n0 + j) (by omega) t htN).trans (le_of_eq ?_)
      rw [pow_add, inv_pow, inv_pow]; field_simp
    obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨ℓ, (tendsto_add_atTop_iff_nat (f := fun n => f n t) n0).1 ?_⟩
    simpa [add_comm] using hℓ
  choose L hL using hlim
  have hunif : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ≤ (N : ℝ), |f n t - L t| ≤ 2 * 2⁻¹ ^ n := by
    intro N
    obtain ⟨n0, hn0⟩ := h' N
    refine ⟨n0, fun n hn t ht => ?_⟩
    have := dist_le_of_le_geometric_two_of_tendsto (f := fun j => f (n + j) t)
      (C := 2 * 2⁻¹ ^ n) (a := L t) ?_ ?_ 0
    · simpa [Real.dist_eq] using this
    · intro j
      rw [Real.dist_eq, abs_sub_comm]
      refine (hn0 (n + j) (by omega) t ht).trans (le_of_eq ?_)
      rw [pow_add, inv_pow, inv_pow]; field_simp
    · have := (tendsto_add_atTop_iff_nat (f := fun m => f m t) n).2 (hL t)
      simpa [add_comm] using this
  refine ⟨L, ?_, hL⟩
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n0, hn0⟩ := hunif (⌈t⌉₊ + 1)
  have htN : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil t]
  have hU : TendstoUniformlyOn f L atTop (Set.Iic ((⌈t⌉₊ + 1 : ℕ) : ℝ)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim0 : Tendsto (fun n : ℕ => 2 * (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
        (by norm_num)).const_mul 2
    filter_upwards [eventually_ge_atTop n0, hlim0.eventually (gt_mem_nhds hε)] with n hn hlt x hx
    rw [Real.dist_eq, abs_sub_comm]
    exact (hn0 n hn x hx).trans_lt hlt
  have hcon : ContinuousOn L (Set.Iic ((⌈t⌉₊ + 1 : ℕ) : ℝ)) :=
    hU.continuousOn (Filter.Eventually.of_forall fun n => (hf n).continuousOn).frequently
  exact hcon.continuousAt (Iic_mem_nhds htN)


section Construction

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}
  {Φ : ℝ → Ω → ι → ℝ}

theorem exists_fast_approx (hΦ : IsProgressiveL2 P ℱ Φ) :
    ∃ Ψ : ℕ → SimpleIntegrand ℱ ι, ∀ n : ℕ,
      sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
  have : ∀ n : ℕ, ∃ Ψ : SimpleIntegrand ℱ ι,
      sqIntegralOn P (fun s ω => Ψ.toFun s ω - Φ s ω) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
    intro n
    obtain ⟨Ψ, hΨ⟩ := exists_simple_approx P ℱ Φ hΦ.prog n (hΦ.sq n)
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
      exact ENNReal.pow_pos (by simp) _
    obtain ⟨k, hk⟩ := (hΨ.eventually (gt_mem_nhds hpos)).exists
    exact ⟨Ψ k, hk.le⟩
  choose Ψ hΨ using this
  exact ⟨Ψ, hΨ⟩


theorem sq_diff_le (hΦ : IsProgressiveL2 P ℱ Φ)
    (Ψ : ℕ → SimpleIntegrand ℱ ι)
    (hΨ : ∀ n : ℕ, sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) n ≤
      ((2 : ℝ≥0∞)⁻¹) ^ (3 * n)) (N n : ℕ) (hNn : N ≤ n) :
    sqIntegralOn P (fun s ω => (Ψ (n + 1)).toFun s ω - (Ψ n).toFun s ω) N ≤
      4 * ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
  have h1 : sqIntegralOn P (fun s ω => (Ψ (n + 1)).toFun s ω - (Ψ n).toFun s ω) N ≤
      2 * sqIntegralOn P (fun s ω => (Ψ (n + 1)).toFun s ω - Φ s ω) N +
        2 * sqIntegralOn P (fun s ω => Φ s ω - (Ψ n).toFun s ω) N := by
    have := sqIntegralOn_add_le (P := P) (isProgressive_sub (Ψ (n + 1)).isProgressive_toFun hΦ.prog)
      (isProgressive_sub hΦ.prog (Ψ n).isProgressive_toFun) N
    convert this using 3
    simp
  have h2 : sqIntegralOn P (fun s ω => (Ψ (n + 1)).toFun s ω - Φ s ω) N ≤
      ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
    refine (sqIntegralOn_mono P _ (by exact_mod_cast hNn.trans n.le_succ)).trans ((hΨ (n + 1)).trans ?_)
    exact pow_le_pow_right_of_le_one' (by simp) (by omega)
  have h3 : sqIntegralOn P (fun s ω => Φ s ω - (Ψ n).toFun s ω) N ≤ ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
    rw [sqIntegralOn_sub_comm]
    exact (sqIntegralOn_mono P _ (by exact_mod_cast hNn)).trans (hΨ n)
  calc _ ≤ _ := h1
    _ ≤ 2 * ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) + 2 * ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by gcongr
    _ = 4 * ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
        rw [← two_mul, ← mul_assoc]; norm_num


theorem ae_small_increments (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    (Ψ : ℕ → SimpleIntegrand ℱ ι)
    (hΨ : ∀ n : ℕ, sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) n ≤
      ((2 : ℝ≥0∞)⁻¹) ^ (3 * n)) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Set.Icc (0 : ℝ) N,
      |(Ψ (n + 1)).elemIntegral W t ω - (Ψ n).elemIntegral W t ω| ≤ (2⁻¹ : ℝ) ^ n := by
  rw [ae_all_iff]
  intro N
  set D : ℕ → ℝ → Ω → ℝ := fun n => (Ψ (n + 1)).elemIntegral W - (Ψ n).elemIntegral W with hD
  have hDm : ∀ n, Martingale (D n) ℱ P := fun n =>
    (SimpleIntegrand.martingale_elemIntegral hW (Ψ (n + 1))).sub
      (SimpleIntegrand.martingale_elemIntegral hW (Ψ n))
  have hDL2 : ∀ n t, MemLp (D n t) 2 P := fun n t =>
    (SimpleIntegrand.memLp_elemIntegral hW (Ψ (n + 1)) t 2 (by norm_num)).sub
      (SimpleIntegrand.memLp_elemIntegral hW (Ψ n) t 2 (by norm_num))
  have hDc : ∀ n ω, Continuous fun t => D n t ω := fun n ω =>
    (SimpleIntegrand.continuous_elemIntegral hW.cont (Ψ (n + 1)) ω).sub
      (SimpleIntegrand.continuous_elemIntegral hW.cont (Ψ n) ω)
  set ε : ℕ → ℝ≥0 := fun n => (2⁻¹ : ℝ≥0) ^ n with hε
  set B : ℕ → Set Ω := fun n => if N ≤ n then
    {ω | ∃ t ∈ Set.Icc (0 : ℝ) N, (ε n : ℝ) < |D n t ω|} else ∅ with hB
  have hBle : ∀ n, P (B n) ≤ 4 * ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    by_cases hNn : N ≤ n
    · simp only [hB, hNn, ↓reduceIte]
      have hk := kolmogorov_cont (hDm n) (hDL2 n) (hDc n) (N := (N : ℝ)) (by positivity) (ε n)
      have hsq : ∫⁻ ω, ‖D n (N : ℝ) ω‖ₑ ^ 2 ∂P ≤ 4 * ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
        have := lintegral_elemIntegral_sub_sq hW (Ψ (n + 1)) (Ψ n) (N : ℝ)
        simp only [hD, Pi.sub_apply]
        rw [this]
        exact sq_diff_le hΦ Ψ hΨ N n hNn
      have hcoe : ((ε n : ℝ≥0) : ℝ≥0∞) = ((2 : ℝ≥0∞)⁻¹) ^ n := by
        simp [hε, ENNReal.inv_pow]
      rw [hcoe] at hk
      have h1 : ((2 : ℝ≥0∞)⁻¹ ^ n) ^ 2 * P {ω | ∃ t ∈ Set.Icc (0 : ℝ) N, (ε n : ℝ) < |D n t ω|} ≤
          ((2 : ℝ≥0∞)⁻¹ ^ n) ^ 2 * (4 * ((2 : ℝ≥0∞)⁻¹) ^ n) := by
        refine hk.trans (hsq.trans (le_of_eq ?_))
        rw [pow_mul]; ring
      have hne0 : ((2 : ℝ≥0∞)⁻¹ ^ n) ^ 2 ≠ 0 := by simp
      have hneT : ((2 : ℝ≥0∞)⁻¹ ^ n) ^ 2 ≠ ⊤ := by simp
      exact (ENNReal.mul_le_mul_iff_right hne0 hneT).1 h1
    · simp [hB, hNn]
  have hsum : ∑' n, P (B n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hBle)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    norm_num
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hω
  refine ⟨max n0 N, fun n hn t ht => ?_⟩
  have h1 := hn0 n (le_trans (le_max_left _ _) hn)
  have hNn : N ≤ n := (le_max_right _ _).trans hn
  simp only [hB, hNn, ↓reduceIte, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at h1
  have := h1 t ht
  simpa [hD, hε] using this

end Construction
section Construction2

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}
  {Φ : ℝ → Ω → ι → ℝ}

theorem isApprox_of_fast (Ψ : ℕ → SimpleIntegrand ℱ ι)
    (hΨ : ∀ n : ℕ, sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) n ≤
      ((2 : ℝ≥0∞)⁻¹) ^ (3 * n)) (t : ℝ) : IsApprox P Φ Ψ t := by
  have hlim : Tendsto (fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ (3 * n)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((2 : ℝ≥0∞)⁻¹) ^ 3) (by
      rw [← ENNReal.inv_pow]; norm_num)
    simpa [pow_mul] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop ⌈t⌉₊] with n hn
  exact (sqIntegralOn_mono P _ ((Nat.le_ceil t).trans (by exact_mod_cast hn))).trans (hΨ n)

theorem lintegral_enorm_sq_le_liminf {X : ℕ → Ω → ℝ} {Y Z : Ω → ℝ} (hX : ∀ m, AEMeasurable (X m) P)
    (hZ : AEMeasurable Z P) (hlim : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop (𝓝 (Y ω))) :
    ∫⁻ ω, ‖Z ω - Y ω‖ₑ ^ 2 ∂P ≤ liminf (fun m => ∫⁻ ω, ‖Z ω - X m ω‖ₑ ^ 2 ∂P) atTop := by
  refine le_trans ?_ (lintegral_liminf_le' (fun m => ((hZ.sub (hX m)).enorm.pow_const 2)))
  refine lintegral_mono_ae ?_
  filter_upwards [hlim] with ω hω
  have h1 : Tendsto (fun m => ‖Z ω - X m ω‖ₑ ^ 2) atTop (𝓝 (‖Z ω - Y ω‖ₑ ^ 2)) := by
    have := ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (continuous_const (y := Z ω) |>.sub continuous_id))).tendsto (Y ω)
    have h2 := this.comp hω
    simpa [Function.comp_def] using h2
  exact le_of_eq h1.liminf_eq.symm


theorem exists_isItoIntegral_aux (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) :
    ∃ (Ψ : ℕ → SimpleIntegrand ℱ ι) (M : ℝ → Ω → ℝ) (C : Set Ω),
      IsItoIntegral P ℱ W Φ M ∧ MeasurableSet C ∧ P Cᶜ = 0 ∧
      (∀ ω ∈ C, ∀ t, Tendsto (fun n => (Ψ n).elemIntegral W t ω) atTop (𝓝 (M t ω))) ∧
      (∀ t, IsApprox P Φ Ψ t) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := exists_fast_approx hΦ
  have happ : ∀ t, IsApprox P Φ Ψ t := isApprox_of_fast Ψ hΨ
  have hae := ae_small_increments hW hΦ Ψ hΨ
  obtain ⟨C, hCm, hC0, hCG⟩ : ∃ C : Set Ω, MeasurableSet C ∧ P Cᶜ = 0 ∧ ∀ ω ∈ C, ∀ N : ℕ,
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Set.Icc (0 : ℝ) N,
        |(Ψ (n + 1)).elemIntegral W t ω - (Ψ n).elemIntegral W t ω| ≤ (2⁻¹ : ℝ) ^ n := by
    refine ⟨(toMeasurable P {ω | ¬ (∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Set.Icc (0 : ℝ) N,
        |(Ψ (n + 1)).elemIntegral W t ω - (Ψ n).elemIntegral W t ω| ≤ (2⁻¹ : ℝ) ^ n)})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · intro ω hω
      by_contra hcon
      exact hω (subset_toMeasurable _ _ hcon)
  have hLim : ∀ ω ∈ C, ∃ L : ℝ → ℝ, Continuous L ∧
      ∀ t, Tendsto (fun n => (Ψ n).elemIntegral W t ω) atTop (𝓝 (L t)) := fun ω hω =>
    exists_continuous_limit (fun n t => (Ψ n).elemIntegral W t ω)
      (fun n => SimpleIntegrand.continuous_elemIntegral hW.cont (Ψ n) ω)
      (fun n t ht => SimpleIntegrand.elemIntegral_of_nonpos W (Ψ n) ht ω) (hCG ω hω)
  let M : ℝ → Ω → ℝ := fun t ω =>
    if ω ∈ C then limUnder atTop (fun n => (Ψ n).elemIntegral W t ω) else 0
  have hMlim : ∀ ω ∈ C, ∀ t, Tendsto (fun n => (Ψ n).elemIntegral W t ω) atTop (𝓝 (M t ω)) := by
    intro ω hω t
    obtain ⟨L, _, hL⟩ := hLim ω hω
    have : M t ω = L t := by simp only [M, hω, ↓reduceIte]; exact (hL t).limUnder_eq
    rw [this]; exact hL t
  have hMcont : ∀ ω, Continuous fun t => M t ω := by
    intro ω
    by_cases hω : ω ∈ C
    · obtain ⟨L, hLc, hL⟩ := hLim ω hω
      have : (fun t => M t ω) = L := by
        funext t; simp only [M, hω, ↓reduceIte]; exact (hL t).limUnder_eq
      rw [this]; exact hLc
    · have : (fun t => M t ω) = fun _ => 0 := by funext t; simp [M, hω]
      rw [this]; exact continuous_const
  have hMzero : ∀ t : ℝ, t ≤ 0 → ∀ ω, M t ω = 0 := by
    intro t ht ω
    by_cases hω : ω ∈ C
    · have := hMlim ω hω t
      simp only [SimpleIntegrand.elemIntegral_of_nonpos W _ ht ω] at this
      exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
    · simp [M, hω]
  have hMad : Adapted ℱ M := by
    intro t
    have hCt : MeasurableSet[ℱ t] C := by
      have := hW.complete t Cᶜ hCm.compl hC0
      simpa using this.compl
    have hf : ∀ n, Measurable[ℱ t] (C.indicator ((Ψ n).elemIntegral W t)) := fun n =>
      (SimpleIntegrand.adapted_elemIntegral hW (Ψ n) t).indicator hCt
    refine @measurable_of_tendsto_metrizable Ω ℝ (ℱ t) _ _ _ _ _ _ hf ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ C
    · simpa [Set.indicator_of_mem hω] using hMlim ω hω t
    · simp [M, hω]
  have hmeasI : ∀ n s, AEMeasurable ((Ψ n).elemIntegral W s) P := fun n s =>
    (SimpleIntegrand.memLp_elemIntegral hW (Ψ n) s 2 (by norm_num)).aestronglyMeasurable.aemeasurable
  have hMI : ∀ t : ℝ, 0 ≤ t → ∀ n, ∫⁻ ω, ‖(Ψ n).elemIntegral W t ω - M t ω‖ₑ ^ 2 ∂P ≤
      2 * sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t := by
    intro t ht n
    have h1 := lintegral_enorm_sq_le_liminf (P := P) (X := fun m => (Ψ m).elemIntegral W t)
      (Y := M t) (Z := (Ψ n).elemIntegral W t) (fun m => hmeasI m t) (hmeasI n t)
      (by filter_upwards [(ae_iff.2 hC0 : ∀ᵐ ω ∂P, ω ∈ C)] with ω hω using hMlim ω hω t)
    refine h1.trans ?_
    have hb : Tendsto (fun m => 2 * sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t +
        2 * sqIntegralOn P (fun s ω => Φ s ω - (Ψ m).toFun s ω) t) atTop
        (𝓝 (2 * sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t)) := by
      have hΞ' : Tendsto (fun m => sqIntegralOn P (fun s ω => Φ s ω - (Ψ m).toFun s ω) t) atTop
          (𝓝 0) := by
        simp_rw [sqIntegralOn_sub_comm Φ]
        exact happ t
      have := ENNReal.Tendsto.const_mul hΞ' (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      simpa using (tendsto_const_nhds (x := 2 * sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t)).add this
    refine le_trans ?_ (le_of_eq hb.liminf_eq)
    refine liminf_le_liminf (Filter.Eventually.of_forall fun m => ?_)
    rw [lintegral_elemIntegral_sub_sq hW]
    have := sqIntegralOn_add_le (P := P) (isProgressive_sub (Ψ n).isProgressive_toFun hΦ.prog)
      (isProgressive_sub hΦ.prog (Ψ m).isProgressive_toFun) t
    convert this using 3
    simp
  have hseq : ∀ t : ℝ, 0 ≤ t → ∃ Ξ : ℕ → SimpleIntegrand ℱ ι, IsApprox P Φ Ξ t ∧
      Tendsto (fun n => ∫⁻ ω, ‖(Ξ n).elemIntegral W t ω - M t ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    intro t ht
    refine ⟨Ψ, happ t, ?_⟩
    have := ENNReal.Tendsto.const_mul (happ t) (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    rw [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le)
      (fun n => hMI t ht n)
  exact ⟨Ψ, M, C, isItoIntegral_of_exists_seq hW hΦ hMcont hMad hMzero hseq, hCm, hC0, hMlim, happ⟩

end Construction2

section Char3

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}
  {Φ Φ' : ℝ → Ω → ι → ℝ}

theorem tendsto_setIntegral_of_tendsto_lintegral {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hY : MemLp Y 2 P)
    (h : Tendsto (fun n => ∫⁻ ω, ‖X n ω - Y ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) {s : Set Ω}
    (hs : MeasurableSet s) :
    Tendsto (fun n => ∫ ω in s, X n ω ∂P) atTop (𝓝 (∫ ω in s, Y ω ∂P)) := by
  have hg : MemLp (s.indicator fun _ => (1 : ℝ)) 2 P :=
    memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top P s))
  have h1 := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_toLp_of_tendsto_lintegral hX hY h)
    (tendsto_const_nhds (x := hg.toLp (s.indicator fun _ => (1 : ℝ))))
  have e : ∀ Z : Ω → ℝ, ∀ hZ : MemLp Z 2 P,
      inner ℝ (hZ.toLp Z) (hg.toLp (s.indicator fun _ => (1 : ℝ))) = ∫ ω in s, Z ω ∂P := by
    intro Z hZ
    rw [inner_toLp, ← integral_indicator hs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ s <;> simp [hω]
  simp only [e] at h1
  exact h1

theorem IsItoIntegral.tendsto_of_le {M : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M)
    {Ψ : ℕ → SimpleIntegrand ℱ ι} {j u : ℝ} (hΨ : IsApprox P Φ Ψ j) (hu : u ≤ j) :
    Tendsto (fun n => ∫⁻ ω, ‖(Ψ n).elemIntegral W u ω - M u ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  rcases lt_or_ge u 0 with hu0 | hu0
  · simp [SimpleIntegrand.elemIntegral_of_nonpos W _ hu0.le, hM.zero u hu0.le]
  · exact hM.approx u hu0 Ψ (hΨ.mono hu)

theorem IsItoIntegral.martingale (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    {M : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M) : Martingale M ℱ P := by
  have hsa : StronglyAdapted ℱ M := hM.adapted.stronglyAdapted
  refine ⟨hsa, fun i j hij => ?_⟩
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i) ((hM.memLp hW hΦ j).integrable one_le_two)
    (fun s _ _ => ((hM.memLp hW hΦ i).integrable one_le_two).integrableOn) (fun s hs _ => ?_)
    (hsa i).aestronglyMeasurable
  have hsm : MeasurableSet s := ℱ.le i s hs
  rcases lt_or_ge j 0 with hj | hj
  · have hi : i < 0 := lt_of_le_of_lt hij hj
    have e1 : M i = fun _ => 0 := funext fun ω => hM.zero i hi.le ω
    have e2 : M j = fun _ => 0 := funext fun ω => hM.zero j hj.le ω
    simp [e1, e2]
  · obtain ⟨Ψ, hΨ⟩ := exists_simple_approx P ℱ Φ hΦ.prog j (hΦ.sq j)
    have h1 := tendsto_setIntegral_of_tendsto_lintegral
      (fun n => SimpleIntegrand.memLp_elemIntegral hW (Ψ n) i 2 (by norm_num)) (hM.memLp hW hΦ i)
      (hM.tendsto_of_le hΨ hij) hsm
    have h2 := tendsto_setIntegral_of_tendsto_lintegral
      (fun n => SimpleIntegrand.memLp_elemIntegral hW (Ψ n) j 2 (by norm_num)) (hM.memLp hW hΦ j)
      (hM.tendsto_of_le hΨ le_rfl) hsm
    have h3 : ∀ n, ∫ ω in s, (Ψ n).elemIntegral W i ω ∂P = ∫ ω in s, (Ψ n).elemIntegral W j ω ∂P :=
      fun n => (SimpleIntegrand.martingale_elemIntegral hW (Ψ n)).setIntegral_eq hij hs
    simp_rw [h3] at h1
    exact tendsto_nhds_unique h1 h2

theorem IsItoIntegral.lintegral_sq (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    {M : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M) (t : ℝ) :
    ∫⁻ ω, ‖M t ω‖ₑ ^ 2 ∂P = sqIntegralOn P Φ t := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [sqIntegralOn_of_neg P _ ht]
    simp [hM.zero t ht.le]
  · have hn := hM.inner_eq hW hΦ hΦ hM ht
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_embL2_sq, norm_toLp_sq] at hn
    rwa [ENNReal.toReal_eq_toReal_iff' (lintegral_enorm_sq_lt_top (hM.memLp hW hΦ t)).ne
      (hΦ.sq t).ne] at hn

end Char3


section Char4

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}
  {Φ Φ' : ℝ → Ω → ι → ℝ}

theorem IsItoIntegral.ae_eq_add (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    (hΦ' : IsProgressiveL2 P ℱ Φ') {M M' Θ : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M)
    (hM' : IsItoIntegral P ℱ W Φ' M')
    (hΘ : IsItoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) Θ) (t : ℝ) :
    Θ t =ᵐ[P] fun ω => M t ω + M' t ω := by
  rcases lt_or_ge t 0 with ht | ht
  · exact Filter.Eventually.of_forall fun ω => by simp [hΘ.zero t ht.le, hM.zero t ht.le,
      hM'.zero t ht.le]
  · have hS := hΦ.add hΦ'
    have key := eq_add_of_inner_eq (hΘ.inner_eq hW hS hS hΘ ht) (hM.inner_eq hW hΦ hΦ hM ht)
      (hM'.inner_eq hW hΦ' hΦ' hM' ht) (hΘ.inner_eq hW hS hΦ hM ht) (hΘ.inner_eq hW hS hΦ' hM' ht)
      (hM.inner_eq hW hΦ hΦ' hM' ht) (embL2_add hΦ hΦ' t)
    rw [← MemLp.toLp_add] at key
    exact (MemLp.toLp_eq_toLp_iff _ ((hM.memLp hW hΦ t).add (hM'.memLp hW hΦ' t))).1 key

theorem IsItoIntegral.ae_eq_smul (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    {M Θ : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M) (c : ℝ)
    (hΘ : IsItoIntegral P ℱ W (fun s ω => c • Φ s ω) Θ) (t : ℝ) :
    Θ t =ᵐ[P] fun ω => c * M t ω := by
  rcases lt_or_ge t 0 with ht | ht
  · exact Filter.Eventually.of_forall fun ω => by simp [hΘ.zero t ht.le, hM.zero t ht.le]
  · have hS := hΦ.smul c
    have key := eq_smul_of_inner_eq c (hΘ.inner_eq hW hS hS hΘ ht) (hM.inner_eq hW hΦ hΦ hM ht)
      (hΘ.inner_eq hW hS hΦ hM ht) (embL2_smul hΦ c t)
    have := (MemLp.toLp_const_smul c (hM.memLp hW hΦ t))
    rw [← this] at key
    exact (MemLp.toLp_eq_toLp_iff _ ((hM.memLp hW hΦ t).const_smul c)).1 key

end Char4

section Char5

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

theorem isItoIntegral_elemIntegral (hW : IsBrownianFiltration P ℱ W) (Ψ : SimpleIntegrand ℱ ι) :
    IsItoIntegral P ℱ W Ψ.toFun (Ψ.elemIntegral W) := by
  refine isItoIntegral_of_exists_seq hW (IsProgressiveL2.simple P Ψ)
    (fun ω => SimpleIntegrand.continuous_elemIntegral hW.cont Ψ ω)
    (SimpleIntegrand.adapted_elemIntegral hW Ψ)
    (fun t ht ω => SimpleIntegrand.elemIntegral_of_nonpos W Ψ ht ω) (fun t ht => ⟨fun _ => Ψ, ?_, ?_⟩)
  · simp [IsApprox, sqIntegralOn]
  · simp

/-- The one-step simple integrand `σ 1_{(0, T]}`. -/
def constStep (ℱ : Filtration ℝ mΩ) (σ : ι → ℝ) (T : ℝ) (hT : 0 ≤ T) : SimpleIntegrand ℱ ι where
  n := 1
  t := ![0, T]
  mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hT]
    exact absurd hij (by decide)
  nonneg := by simp
  ξ := fun _ _ => σ
  meas := fun _ => measurable_const
  bdd := ⟨∑ j, |σ j|, fun _ _ k => Finset.single_le_sum (f := fun j => |σ j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ k)⟩


theorem constStep_toFun (σ : ι → ℝ) (T : ℝ) (hT : 0 ≤ T) (s : ℝ) (ω : Ω) :
    (constStep ℱ σ T hT).toFun s ω = Set.indicator (Set.Ioc 0 T) (fun _ => σ) s := by
  simp only [SimpleIntegrand.toFun, constStep]
  erw [Fin.sum_univ_one]
  simp

theorem constStep_elemIntegral (σ : ι → ℝ) (T : ℝ) (hT : 0 ≤ T) (s : ℝ) (ω : Ω) :
    (constStep ℱ σ T hT).elemIntegral W s ω =
      ∑ k, σ k * (W (Real.toNNReal (min T s)) ω k - W (Real.toNNReal (min 0 s)) ω k) := by
  simp only [SimpleIntegrand.elemIntegral, constStep]
  erw [Fin.sum_univ_one]
  simp

theorem isItoIntegral_const (hW : IsBrownianFiltration P ℱ W) (σ : ι → ℝ) :
    IsItoIntegral P ℱ W (fun _ _ => σ) (fun t ω => ∑ k, σ k * ofNNRealTime W t ω k) := by
  refine isItoIntegral_of_exists_seq hW (IsProgressiveL2.const P ℱ σ) ?_ ?_ ?_ ?_
  · intro ω
    refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
    exact (continuous_apply k).comp (continuous_ofNNRealTime W ω (hW.cont ω))
  · intro t
    rcases le_or_gt t 0 with ht | ht
    · have : (fun ω => ∑ k, σ k * ofNNRealTime W t ω k) = fun _ => 0 := by
        funext ω
        simp [ofNNRealTime, Real.toNNReal_of_nonpos ht, hW.zero]
      change Measurable[ℱ t] (fun ω => ∑ k, σ k * ofNNRealTime W t ω k)
      rw [this]; exact measurable_const
    · change Measurable[ℱ t] (fun ω => ∑ k, σ k * ofNNRealTime W t ω k)
      refine Finset.measurable_sum _ fun k _ => Measurable.const_mul ?_ _
      have h1 : Measurable[ℱ t] (W (Real.toNNReal t)) :=
        (hW.adapted (Real.toNNReal t)).mono (ℱ.mono (le_of_eq (Real.coe_toNNReal t ht.le))) le_rfl
      exact (measurable_pi_apply k).comp h1
  · intro t ht ω
    simp [ofNNRealTime, Real.toNNReal_of_nonpos ht, hW.zero]
  · intro t ht
    refine ⟨fun _ => constStep ℱ σ t ht, ?_, ?_⟩
    · have : ∀ ω, (∫⁻ s in Set.Icc (0 : ℝ) t, ∑ k, ‖(constStep ℱ σ t ht).toFun s ω k - σ k‖ₑ ^ 2) = 0 := by
        intro ω
        rw [← setLIntegral_congr Ioc_ae_eq_Icc]
        refine (setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0) fun s hs => ?_).trans
          (by simp)
        simp [constStep_toFun, Set.indicator_of_mem hs]
      simp [IsApprox, sqIntegralOn, this]
    · have : ∀ ω, (constStep ℱ σ t ht).elemIntegral W t ω = ∑ k, σ k * ofNNRealTime W t ω k := by
        intro ω
        rw [constStep_elemIntegral]
        simp [ofNNRealTime, hW.zero, ht]
      simp [this]

end Char5

section L2

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} {Φ Φ' : ℝ → Ω → ι → ℝ}

/-- Two Itô integrals of the same integrand are indistinguishable. -/
theorem IsItoIntegral.ae_eq_forall [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {M M' : ℝ → Ω → ℝ}
    (hM : IsItoIntegral P ℱ W Φ M) (hM' : IsItoIntegral P ℱ W Φ M') (hΦ : IsProgressiveL2 P ℱ Φ) :
    ∀ᵐ ω ∂P, ∀ t, M t ω = M' t ω :=
  IsItoIntegral.ae_eq_forall_of_brownian hW hM hM' hΦ

/-- **Existence of the Itô integral** for progressive `L²` integrands. -/
theorem exists_isItoIntegral [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) : ∃ M, IsItoIntegral P ℱ W Φ M := by
  obtain ⟨Ψ, M, C, h, -⟩ := exists_isItoIntegral_aux hW hΦ
  exact ⟨M, h⟩

theorem isItoIntegral_itoIntegral [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) : IsItoIntegral P ℱ W Φ (itoIntegral P ℱ W Φ) := by
  unfold itoIntegral
  split_ifs with h
  · exact h.choose_spec
  · exact absurd (exists_isItoIntegral hW hΦ) h

/-- Unconditionally, `itoIntegral` has everywhere continuous paths (it is either a chosen
integral or `0`). -/
theorem continuous_itoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) (ω : Ω) : Continuous fun t => itoIntegral P ℱ W Φ t ω := by
  unfold itoIntegral
  split_ifs with h
  · exact h.choose_spec.cont ω
  · exact continuous_const

theorem adapted_itoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) : Adapted ℱ (itoIntegral P ℱ W Φ) := by
  unfold itoIntegral
  split_ifs with h
  · exact h.choose_spec.adapted
  · exact fun t => measurable_const

theorem itoIntegral_of_nonpos (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) {t : ℝ} (ht : t ≤ 0) (ω : Ω) : itoIntegral P ℱ W Φ t ω = 0 := by
  unfold itoIntegral
  split_ifs with h
  · exact h.choose_spec.zero t ht ω
  · rfl

theorem isProgressive_itoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) : IsProgressive ℱ (itoIntegral P ℱ W Φ) :=
  ((adapted_itoIntegral P ℱ W Φ).stronglyAdapted.isStronglyProgressive_of_continuous
    (continuous_itoIntegral P ℱ W Φ)).isProgressive

/-- The integral of a simple integrand is the elementary integral. -/
theorem itoIntegral_simple [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (Ψ : SimpleIntegrand ℱ ι) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W Ψ.toFun t ω = Ψ.elemIntegral W t ω :=
  (isItoIntegral_itoIntegral hW (IsProgressiveL2.simple P Ψ)).ae_eq_forall_of_brownian hW
    (isItoIntegral_elemIntegral hW Ψ) (IsProgressiveL2.simple P Ψ)

/-- The Itô integral is a martingale over real time. -/
theorem martingale_itoIntegral [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) : Martingale (itoIntegral P ℱ W Φ) ℱ P :=
  (isItoIntegral_itoIntegral hW hΦ).martingale hW hΦ

theorem memLp_two_itoIntegral [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (t : ℝ) : MemLp (itoIntegral P ℱ W Φ t) 2 P :=
  (isItoIntegral_itoIntegral hW hΦ).memLp hW hΦ t

theorem integral_itoIntegral [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (t : ℝ) : ∫ ω, itoIntegral P ℱ W Φ t ω ∂P = 0 := by
  rcases le_total t 0 with ht | ht
  · simp [itoIntegral_of_nonpos P ℱ W Φ ht]
  · have := (martingale_itoIntegral hW hΦ).setIntegral_eq ht (MeasurableSet.univ (α := Ω))
    simpa [itoIntegral_of_nonpos P ℱ W Φ (le_refl (0 : ℝ))] using this.symm

/-- **Itô isometry**: `E[M_t²] = E ∫_0^t ∑_k |Φ^k_s|² ds` (in `ℝ≥0∞`). -/
theorem lintegral_itoIntegral_sq [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (t : ℝ) :
    ∫⁻ ω, ‖itoIntegral P ℱ W Φ t ω‖ₑ ^ 2 ∂P = sqIntegralOn P Φ t :=
  (isItoIntegral_itoIntegral hW hΦ).lintegral_sq hW hΦ t

/-- Itô isometry, real form: `E[M_t²] = E ∫_0^t ∑_k (Φ^k_s)² ds` (the right-hand side is the
finite number `sqIntegralOn P Φ t`, so no Bochner junk value is involved). -/
theorem integral_itoIntegral_sq [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (t : ℝ) :
    ∫ ω, itoIntegral P ℱ W Φ t ω ^ 2 ∂P = (sqIntegralOn P Φ t).toReal := by
  have h := (isItoIntegral_itoIntegral hW hΦ).integral_mul hW hΦ hΦ (isItoIntegral_itoIntegral hW hΦ) t
  simp only [← pow_two] at h
  rw [h]
  exact (integrable_sq_aux hΦ t).2.2

/-- Under `IsProgressiveL2`, the pathwise integrals `∫_0^t ∑_k (Φ^k_s)² ds` exist a.s. and their
expectation is `sqIntegralOn P Φ t`; this is what makes the Bochner forms below meaningful. -/
theorem integrable_sq_of_isProgressiveL2 [IsProbabilityMeasure P] (hΦ : IsProgressiveL2 P ℱ Φ)
    (t : ℝ) :
    (∀ᵐ ω ∂P, IntegrableOn (fun s => ∑ k, Φ s ω k ^ 2) (Set.Icc 0 t)) ∧
      Integrable (fun ω => ∫ s in Set.Icc 0 t, ∑ k, Φ s ω k ^ 2) P ∧
      ∫ ω, (∫ s in Set.Icc 0 t, ∑ k, Φ s ω k ^ 2) ∂P = (sqIntegralOn P Φ t).toReal :=
  integrable_sq_aux hΦ t

/-- Polarised isometry: `E[M_t M'_t] = E ∫_0^t ∑_k Φ^k_s Φ'^k_s ds`; in particular the integrals
against *different* coordinates are orthogonal.  (All integrands are integrable under the `L²`
hypotheses, by `integrable_sq_of_isProgressiveL2` and Cauchy–Schwarz, so the Bochner integrals are
the genuine ones.) -/
theorem integral_itoIntegral_mul [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (hΦ' : IsProgressiveL2 P ℱ Φ') (t : ℝ) :
    ∫ ω, itoIntegral P ℱ W Φ t ω * itoIntegral P ℱ W Φ' t ω ∂P =
      ∫ ω, (∫ s in Set.Icc 0 t, ∑ k, Φ s ω k * Φ' s ω k) ∂P :=
  (isItoIntegral_itoIntegral hW hΦ).integral_mul hW hΦ hΦ' (isItoIntegral_itoIntegral hW hΦ') t

section Restrict

variable {ℱ : Filtration ℝ mΩ}

open Classical in
/-- Restriction of a simple integrand to `(a, b] × A` for `A ∈ ℱ_a`. -/
def SimpleIntegrand.restrict (Ψ : SimpleIntegrand ℱ ι) (a b : ℝ) (ha : 0 ≤ a)
    {A : Set Ω} (hA : MeasurableSet[ℱ a] A) : SimpleIntegrand ℱ ι where
  n := Ψ.n
  t := fun i => max a (min b (Ψ.t i))
  mono := fun i j hij => max_le_max le_rfl (min_le_min le_rfl (Ψ.mono hij))
  nonneg := ha.trans (le_max_left _ _)
  ξ := fun i ω => if Ψ.t i.castSucc ≤ b ∧ ω ∈ A then Ψ.ξ i ω else 0
  meas := fun i => by
    by_cases hc : Ψ.t i.castSucc ≤ b
    · have h1 : max a (min b (Ψ.t i.castSucc)) = max a (Ψ.t i.castSucc) := by rw [min_eq_right hc]
      simp only [hc, true_and]
      rw [h1]
      refine Measurable.ite (ℱ.mono (le_max_left _ _) _ hA) ?_ measurable_const
      exact (Ψ.meas i).mono (ℱ.mono (le_max_right _ _)) le_rfl
    · simp [hc]
  bdd := by
    obtain ⟨C, hC⟩ := Ψ.bdd
    refine ⟨max C 0, fun i ω k => ?_⟩
    by_cases h : Ψ.t i.castSucc ≤ b ∧ ω ∈ A
    · simp only [h, and_self, ite_true]; exact (hC i ω k).trans (le_max_left _ _)
    · simp [h]

theorem mem_Ioc_clamp_iff {a b x y s : ℝ} :
    s ∈ Set.Ioc (max a (min b x)) (max a (min b y)) ↔ s ∈ Set.Ioc a b ∧ s ∈ Set.Ioc x y := by
  simp only [Set.mem_Ioc, max_def, min_def]
  split_ifs <;> grind

open Classical in
theorem restrict_toFun_aux (Ψ : SimpleIntegrand ℱ ι) (a b : ℝ) {A : Set Ω} (ω : Ω) (s : ℝ)
    (i : Fin Ψ.n) :
    Set.indicator (Set.Ioc (max a (min b (Ψ.t i.castSucc))) (max a (min b (Ψ.t i.succ))))
      (fun _ => if Ψ.t i.castSucc ≤ b ∧ ω ∈ A then Ψ.ξ i ω else 0) s =
      if ω ∈ A ∧ s ∈ Set.Ioc a b then
        Set.indicator (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)) (fun _ => Ψ.ξ i ω) s else 0 := by
  by_cases hω : ω ∈ A
  · by_cases hs : s ∈ Set.Ioc a b
    · simp only [hω, hs, and_self, ite_true]
      by_cases hi : s ∈ Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)
      · have h1 : s ∈ Set.Ioc (max a (min b (Ψ.t i.castSucc))) (max a (min b (Ψ.t i.succ))) :=
          mem_Ioc_clamp_iff.2 ⟨hs, hi⟩
        have h2 : Ψ.t i.castSucc ≤ b := by
          have := hi.1; have := hs.2; linarith
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem hi]
        simp [h2, hω]
      · have h1 : s ∉ Set.Ioc (max a (min b (Ψ.t i.castSucc))) (max a (min b (Ψ.t i.succ))) :=
          fun h' => hi (mem_Ioc_clamp_iff.1 h').2
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hi]
    · have h1 : s ∉ Set.Ioc (max a (min b (Ψ.t i.castSucc))) (max a (min b (Ψ.t i.succ))) :=
        fun h' => hs (mem_Ioc_clamp_iff.1 h').1
      simp [hs, Set.indicator_of_notMem h1]
  · simp [hω]

open Classical in
theorem SimpleIntegrand.restrict_toFun (Ψ : SimpleIntegrand ℱ ι) (a b : ℝ) (ha : 0 ≤ a)
    {A : Set Ω} (hA : MeasurableSet[ℱ a] A) (s : ℝ) (ω : Ω) :
    (Ψ.restrict a b ha hA).toFun s ω = if ω ∈ A ∧ s ∈ Set.Ioc a b then Ψ.toFun s ω else 0 := by
  have : (Ψ.restrict a b ha hA).toFun s ω = ∑ i : Fin Ψ.n,
      Set.indicator (Set.Ioc (max a (min b (Ψ.t i.castSucc))) (max a (min b (Ψ.t i.succ))))
      (fun _ => if Ψ.t i.castSucc ≤ b ∧ ω ∈ A then Ψ.ξ i ω else 0) s := rfl
  rw [this]
  simp_rw [restrict_toFun_aux]
  unfold SimpleIntegrand.toFun
  by_cases h : ω ∈ A ∧ s ∈ Set.Ioc a b <;> simp [h]

theorem clamp_id (G : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    G (max a (min b x)) = G (min x b) - G (min x a) + G a := by
  rcases le_total x a with h | h
  · have e1 : max a (min b x) = a := by grind
    have e2 : min x b = x := by grind
    have e3 : min x a = x := by grind
    rw [e1, e2, e3]; ring
  · rcases le_total x b with h' | h'
    · have e1 : max a (min b x) = x := by grind
      have e2 : min x b = x := by grind
      have e3 : min x a = a := by grind
      rw [e1, e2, e3]; ring
    · have e1 : max a (min b x) = b := by grind
      have e2 : min x b = b := by grind
      have e3 : min x a = a := by grind
      rw [e1, e2, e3]; ring

open Classical in
theorem restrict_elem_aux (W : ℝ≥0 → Ω → ι → ℝ) (Ψ : SimpleIntegrand ℱ ι) {a b : ℝ}
    (hab : a ≤ b) (A : Set Ω) (ω : Ω) (s : ℝ) (i : Fin Ψ.n) :
    ∑ k, (if Ψ.t i.castSucc ≤ b ∧ ω ∈ A then Ψ.ξ i ω else 0) k *
      (W (Real.toNNReal (min (max a (min b (Ψ.t i.succ))) s)) ω k -
        W (Real.toNNReal (min (max a (min b (Ψ.t i.castSucc))) s)) ω k) =
    if ω ∈ A then
      (∑ k, Ψ.ξ i ω k * (W (Real.toNNReal (min (Ψ.t i.succ) (min s b))) ω k -
        W (Real.toNNReal (min (Ψ.t i.castSucc) (min s b))) ω k)) -
      (∑ k, Ψ.ξ i ω k * (W (Real.toNNReal (min (Ψ.t i.succ) (min s a))) ω k -
        W (Real.toNNReal (min (Ψ.t i.castSucc) (min s a))) ω k)) else 0 := by
  by_cases hω : ω ∈ A
  · by_cases hc : Ψ.t i.castSucc ≤ b
    · simp only [hc, hω, and_self, ite_true]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hG := fun x => clamp_id (fun u => W (Real.toNNReal (min u s)) ω k) hab x
      have e : ∀ x c : ℝ, min x (min s c) = min (min x c) s := fun x c => by
        rw [min_assoc, min_comm c s]
      rw [hG, hG, e, e, e, e]
      ring
    · simp only [hc, hω, false_and, and_false, ite_false, ite_true, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero]
      have h1 : b < Ψ.t i.castSucc := not_le.1 hc
      have h2 : Ψ.t i.castSucc ≤ Ψ.t i.succ := Ψ.mono (Fin.castSucc_le_succ i)
      have e1 : min (Ψ.t i.succ) (min s b) = min s b := min_eq_right (by grind)
      have e2 : min (Ψ.t i.castSucc) (min s b) = min s b := min_eq_right (by grind)
      have e3 : min (Ψ.t i.succ) (min s a) = min s a := min_eq_right (by grind)
      have e4 : min (Ψ.t i.castSucc) (min s a) = min s a := min_eq_right (by grind)
      simp [e1, e2, e3, e4]
  · simp [hω]

open Classical in
theorem SimpleIntegrand.restrict_elemIntegral (Ψ : SimpleIntegrand ℱ ι) (W : ℝ≥0 → Ω → ι → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Set Ω} (hA : MeasurableSet[ℱ a] A) (s : ℝ) (ω : Ω) :
    (Ψ.restrict a b ha hA).elemIntegral W s ω =
      if ω ∈ A then Ψ.elemIntegral W (min s b) ω - Ψ.elemIntegral W (min s a) ω else 0 := by
  have : (Ψ.restrict a b ha hA).elemIntegral W s ω = ∑ i : Fin Ψ.n, ∑ k,
      (if Ψ.t i.castSucc ≤ b ∧ ω ∈ A then Ψ.ξ i ω else 0) k *
      (W (Real.toNNReal (min (max a (min b (Ψ.t i.succ))) s)) ω k -
        W (Real.toNNReal (min (max a (min b (Ψ.t i.castSucc))) s)) ω k) := rfl
  rw [this]
  simp_rw [restrict_elem_aux W Ψ hab]
  unfold SimpleIntegrand.elemIntegral
  by_cases hω : ω ∈ A
  · simp [hω, Finset.sum_sub_distrib]
  · simp [hω]

end Restrict

section ClaimA

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}
  {Φ : ℝ → Ω → ι → ℝ}

open Classical in
/-- The integrand `1_A 1_{(a, b]} Φ`. -/
def restrictFun (Φ : ℝ → Ω → ι → ℝ) (a b : ℝ) (A : Set Ω) : ℝ → Ω → ι → ℝ :=
  fun s ω => if ω ∈ A ∧ s ∈ Set.Ioc a b then Φ s ω else 0

theorem enorm_restrictFun_le (Φ : ℝ → Ω → ι → ℝ) (a b : ℝ) (A : Set Ω) (s : ℝ) (ω : Ω) (k : ι) :
    ‖restrictFun Φ a b A s ω k‖ₑ ≤ ‖Φ s ω k‖ₑ := by
  unfold restrictFun
  split_ifs <;> simp

theorem isProgressive_restrictFun (hΦ : IsProgressive ℱ Φ) {a b : ℝ}
    {A : Set Ω} (hA : MeasurableSet[ℱ a] A) : IsProgressive ℱ (restrictFun Φ a b A) := by
  intro i
  by_cases hi : a ≤ i
  · have hA' : MeasurableSet[ℱ i] A := ℱ.mono hi _ hA
    have hset : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)]
        {p : Set.Iic i × Ω | p.2 ∈ A ∧ (p.1 : ℝ) ∈ Set.Ioc a b} := by
      have : {p : Set.Iic i × Ω | p.2 ∈ A ∧ (p.1 : ℝ) ∈ Set.Ioc a b} =
          {u : Set.Iic i | (u : ℝ) ∈ Set.Ioc a b} ×ˢ A := by
        ext p; simp [and_comm]
      rw [this]
      exact MeasurableSet.prod (measurable_subtype_coe measurableSet_Ioc) hA'
    exact Measurable.ite hset (hΦ i) measurable_const
  · have : (fun p : Set.Iic i × Ω => restrictFun Φ a b A p.1 p.2) = fun _ => 0 := by
      funext p
      have h1 : (p.1 : ℝ) ≤ i := p.1.2
      have h2 : ¬ (p.1 : ℝ) ∈ Set.Ioc a b := fun h => by
        have := h.1; linarith [not_le.1 hi]
      simp [restrictFun, h2]
    rw [this]
    exact measurable_const

theorem IsProgressiveL2.restrictFun (hΦ : IsProgressiveL2 P ℱ Φ) {a b : ℝ} {A : Set Ω}
    (hA : MeasurableSet[ℱ a] A) : IsProgressiveL2 P ℱ (restrictFun Φ a b A) :=
  ⟨isProgressive_restrictFun hΦ.prog hA, fun T =>
    lt_of_le_of_lt (sqIntegralOn_mono_of_enorm_le (enorm_restrictFun_le Φ a b A) T) (hΦ.sq T)⟩

open Classical in
/-- **Restriction of the Itô integral**: the integral of `1_A 1_{(a, b]} Φ` (`A ∈ ℱ_a`) is
`1_A (M_{t ∧ b} - M_{t ∧ a})`. -/
theorem IsItoIntegral.restrict (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    {M : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {A : Set Ω} (hA : MeasurableSet[ℱ a] A) :
    IsItoIntegral P ℱ W (restrictFun Φ a b A)
      (fun t ω => if ω ∈ A then M (min t b) ω - M (min t a) ω else 0) := by
  refine isItoIntegral_of_exists_seq hW (hΦ.restrictFun hA) ?_ ?_ ?_ ?_
  · intro ω
    by_cases hω : ω ∈ A
    · simp only [hω, ite_true]
      exact ((hM.cont ω).comp (continuous_id.min continuous_const)).sub
        ((hM.cont ω).comp (continuous_id.min continuous_const))
    · simp [hω]; exact continuous_const
  · intro t
    by_cases hta : a ≤ t
    · have hAt : MeasurableSet[ℱ t] A := ℱ.mono hta _ hA
      refine Measurable.ite hAt ?_ measurable_const
      exact ((hM.adapted (min t b)).mono (ℱ.mono (min_le_left _ _)) le_rfl).sub
        ((hM.adapted (min t a)).mono (ℱ.mono (min_le_left _ _)) le_rfl)
    · have h1 : min t b = t := min_eq_left (by linarith [not_le.1 hta])
      have h2 : min t a = t := min_eq_left (not_le.1 hta).le
      have : (fun ω => if ω ∈ A then M (min t b) ω - M (min t a) ω else 0) = fun _ => 0 := by
        funext ω; simp [h1, h2]
      show Measurable[ℱ t] (fun ω => if ω ∈ A then M (min t b) ω - M (min t a) ω else 0)
      rw [this]; exact measurable_const
  · intro t ht ω
    have h1 : min t b = t := min_eq_left (by linarith)
    have h2 : min t a = t := min_eq_left (by linarith)
    simp [h1, h2]
  · intro t ht
    obtain ⟨Ψ, hΨ⟩ := exists_simple_approx P ℱ Φ hΦ.prog t (hΦ.sq t)
    refine ⟨fun n => (Ψ n).restrict a b ha hA, ?_, ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hΨ (fun _ => bot_le)
        (fun n => sqIntegralOn_mono_of_enorm_le (fun s ω k => ?_) t)
      simp only [SimpleIntegrand.restrict_toFun, restrictFun]
      split_ifs <;> simp
    · have htb : 0 ≤ min t b := le_min ht (ha.trans hab)
      have hta : 0 ≤ min t a := le_min ht ha
      have h1 := hM.approx _ htb Ψ (IsApprox.mono (P := P) hΨ (min_le_left _ _))
      have h2 := hM.approx _ hta Ψ (IsApprox.mono (P := P) hΨ (min_le_left _ _))
      have hmeas : ∀ u, 0 ≤ u → ∀ n, AEMeasurable (fun ω => (Ψ n).elemIntegral W u ω - M u ω) P :=
        fun u hu n => ((((Ψ n).adapted_elemIntegral hW u).mono (ℱ.le u) le_rfl).sub
          ((hM.adapted u).mono (ℱ.le u) le_rfl)).aemeasurable
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_two_mul_add h1 h2) (fun _ => bot_le) (fun n => ?_)
      calc ∫⁻ ω, ‖((Ψ n).restrict a b ha hA).elemIntegral W t ω -
              (if ω ∈ A then M (min t b) ω - M (min t a) ω else 0)‖ₑ ^ 2 ∂P
          ≤ ∫⁻ ω, ‖((Ψ n).elemIntegral W (min t b) ω - M (min t b) ω) +
              (-((Ψ n).elemIntegral W (min t a) ω - M (min t a) ω))‖ₑ ^ 2 ∂P := by
            refine lintegral_mono fun ω => ?_
            rw [SimpleIntegrand.restrict_elemIntegral _ W ha hab hA]
            by_cases hω : ω ∈ A
            · simp only [hω, ite_true]
              refine le_of_eq ?_
              congr 2
              ring
            · simp [hω]
        _ ≤ 2 * ∫⁻ ω, ‖(Ψ n).elemIntegral W (min t b) ω - M (min t b) ω‖ₑ ^ 2 ∂P +
              2 * ∫⁻ ω, ‖-((Ψ n).elemIntegral W (min t a) ω - M (min t a) ω)‖ₑ ^ 2 ∂P :=
            lintegral_enorm_sq_add_le (hmeas _ htb n)
        _ = _ := by simp only [enorm_neg]

open Classical in
theorem integral_Icc_restrictFun_sq (Φ : ℝ → Ω → ι → ℝ) {a b : ℝ} (ha : 0 ≤ a) (A : Set Ω) (ω : Ω) :
    ∫ r in Set.Icc 0 b, ∑ k, restrictFun Φ a b A r ω k * restrictFun Φ a b A r ω k =
      if ω ∈ A then ∫ r in Set.Ioc a b, ∑ k, Φ r ω k ^ 2 else 0 := by
  classical
  by_cases hω : ω ∈ A
  · rw [if_pos hω]
    have : ∀ r, ∑ k, restrictFun Φ a b A r ω k * restrictFun Φ a b A r ω k =
        Set.indicator (Set.Ioc a b) (fun r => ∑ k, Φ r ω k ^ 2) r := fun r => by
      by_cases hr : r ∈ Set.Ioc a b
      · simp [restrictFun, hω, hr, sq]
      · simp [restrictFun, hω, hr]
    simp_rw [this]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hI : Set.Icc 0 b ∩ Set.Ioc a b = Set.Ioc a b := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨⟨ha.trans h1.le, h2⟩, h1, h2⟩
    rw [hI]
  · rw [if_neg hω]
    simp [restrictFun, hω]

open Classical in
theorem IsItoIntegral.setIntegral_sub_sq (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {M : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, (M t ω - M s ω) ^ 2 ∂P = ∫ ω in A, (∫ r in Set.Ioc s t, ∑ k, Φ r ω k ^ 2) ∂P := by
  have hMA := hM.restrict hW hΦ hs hst hA
  have h := hMA.integral_mul hW (hΦ.restrictFun hA) (hΦ.restrictFun hA) hMA t
  have hA' : MeasurableSet A := ℱ.le s _ hA
  simp_rw [integral_Icc_restrictFun_sq Φ hs A] at h
  beta_reduce at h
  rw [← integral_indicator hA', ← integral_indicator hA']
  have e1 : ∀ ω, (if ω ∈ A then M (min t t) ω - M (min t s) ω else 0) *
      (if ω ∈ A then M (min t t) ω - M (min t s) ω else 0) =
      A.indicator (fun ω => (M t ω - M s ω) ^ 2) ω := fun ω => by
    by_cases hω : ω ∈ A <;> simp [hω, min_self, min_eq_right hst, sq]
  have e2 : ∀ ω, (if ω ∈ A then ∫ r in Set.Ioc s t, ∑ k, Φ r ω k ^ 2 else 0) =
      A.indicator (fun ω => ∫ r in Set.Ioc s t, ∑ k, Φ r ω k ^ 2) ω := fun ω => by
    by_cases hω : ω ∈ A <;> simp [hω]
  simp only [e1, e2] at h
  exact h

theorem integrable_Ioc_sq (hΦ : IsProgressiveL2 P ℱ Φ) {s t : ℝ} (hs : 0 ≤ s) :
    Integrable (fun ω => ∫ r in Set.Ioc s t, ∑ k, Φ r ω k ^ 2) P := by
  classical
  have hU : MeasurableSet[ℱ s] (Set.univ : Set Ω) := MeasurableSet.univ
  have := (integrable_sq_aux (hΦ.restrictFun (b := t) hU) t).2.1
  refine this.congr (Eventually.of_forall fun ω => ?_)
  have h := integral_Icc_restrictFun_sq Φ hs (Set.univ : Set Ω) ω (b := t)
  simp only [Set.mem_univ, ite_true] at h
  beta_reduce
  rw [← h]
  simp_rw [sq]

end ClaimA

/-- Isometry for increments: `E[(M_t - M_s)²] = E ∫_s^t ∑_k |Φ^k|²` (M L7001, L10848). -/
theorem integral_itoIntegral_sub_sq [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ s ω) ^ 2 ∂P =
      ∫ ω, (∫ r in Set.Ioc s t, ∑ k, Φ r ω k ^ 2) ∂P := by
  have := (isItoIntegral_itoIntegral hW hΦ).setIntegral_sub_sq hW hΦ hs hst
    (MeasurableSet.univ : MeasurableSet[ℱ s] (Set.univ : Set Ω))
  simpa using this

/-- Conditional isometry: `E[(M_t - M_s)² | ℱ_s] = E[∫_s^t ∑_k |Φ^k|² | ℱ_s]`. -/
theorem condExp_itoIntegral_sub_sq [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P[fun ω => (itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ s ω) ^ 2 | ℱ s] =ᵐ[P]
      P[fun ω => ∫ r in Set.Ioc s t, ∑ k, Φ r ω k ^ 2 | ℱ s] := by
  have hM := isItoIntegral_itoIntegral hW hΦ
  have hXint : Integrable (fun ω => (itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ s ω) ^ 2) P :=
    ((memLp_two_itoIntegral hW hΦ t).sub (memLp_two_itoIntegral hW hΦ s)).integrable_sq
  have hYint := integrable_Ioc_sq (t := t) hΦ hs
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hXint
    (g := P[fun ω => ∫ r in Set.Ioc s t, ∑ k, Φ r ω k ^ 2 | ℱ s])
    (fun A _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp (ℱ.le s) hYint hA]
  exact (hM.setIntegral_sub_sq hW hΦ hs hst hA).symm

/-- Linearity: `∫ (Φ + Φ') dW = ∫ Φ dW + ∫ Φ' dW` (indistinguishable). -/
theorem itoIntegral_add [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (hΦ' : IsProgressiveL2 P ℱ Φ') :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) t ω =
      itoIntegral P ℱ W Φ t ω + itoIntegral P ℱ W Φ' t ω := by
  refine ae_forall_eq_of_continuous P _ (fun t ω => itoIntegral P ℱ W Φ t ω + itoIntegral P ℱ W Φ' t ω)
    (continuous_itoIntegral P ℱ W _) (fun ω => (continuous_itoIntegral P ℱ W Φ ω).add
      (continuous_itoIntegral P ℱ W Φ' ω)) fun t => ?_
  exact (isItoIntegral_itoIntegral hW hΦ).ae_eq_add hW hΦ hΦ'
    (isItoIntegral_itoIntegral hW hΦ') (isItoIntegral_itoIntegral hW (hΦ.add hΦ')) t

theorem itoIntegral_smul [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (fun s ω => c • Φ s ω) t ω = c * itoIntegral P ℱ W Φ t ω := by
  refine ae_forall_eq_of_continuous P _ (fun t ω => c * itoIntegral P ℱ W Φ t ω)
    (continuous_itoIntegral P ℱ W _) (fun ω => (continuous_itoIntegral P ℱ W Φ ω).const_mul c)
    fun t => ?_
  exact (isItoIntegral_itoIntegral hW hΦ).ae_eq_smul hW hΦ c (isItoIntegral_itoIntegral hW (hΦ.smul c)) t

/-- Integrands that agree `dt ⊗ P`-a.e. on every `[0, T]` have indistinguishable integrals. -/
theorem itoIntegral_congr [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (hΦ' : IsProgressiveL2 P ℱ Φ')
    (h : ∀ T, sqIntegralOn P (fun s ω => Φ s ω - Φ' s ω) T = 0) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W Φ t ω = itoIntegral P ℱ W Φ' t ω := by
  refine ae_forall_eq_of_continuous P _ _ (continuous_itoIntegral P ℱ W _)
    (continuous_itoIntegral P ℱ W _) fun t => ?_
  have h1 := (isItoIntegral_itoIntegral hW hΦ).lintegral_sub_sq hW hΦ hΦ'
    (isItoIntegral_itoIntegral hW hΦ') t
  rw [h t] at h1
  have hmeas : AEMeasurable (fun ω => itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ' t ω) P :=
    (((adapted_itoIntegral P ℱ W Φ t).mono (ℱ.le t) le_rfl).sub
      ((adapted_itoIntegral P ℱ W Φ' t).mono (ℱ.le t) le_rfl)).aemeasurable
  filter_upwards [ae_eq_zero_of_lintegral_enorm_sq_eq_zero hmeas h1] with ω hω
  simpa [sub_eq_zero] using hω

/-- The integral of a constant integrand `σ` is `∑_k σ_k W^k_t` (for `t ≥ 0`): this is the
additive-noise term `√(2/β) W_t` of the particle system. -/
theorem itoIntegral_const [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (σ : ι → ℝ) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (fun _ _ => σ) t ω = ∑ k, σ k * ofNNRealTime W t ω k :=
  (isItoIntegral_itoIntegral hW (IsProgressiveL2.const P ℱ σ)).ae_eq_forall_of_brownian hW
    (isItoIntegral_const hW σ) (IsProgressiveL2.const P ℱ σ)

/-- The integral of `1_{(a, b]} Φ` is `M_{t ∧ b} - M_{t ∧ a}` (`0 ≤ a ≤ b`): integrals over
subintervals are increments of the integral process. -/
theorem itoIntegral_indicator_Ioc [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (fun s ω => Set.indicator (Set.Ioc a b) (fun _ => Φ s ω) s) t ω =
      itoIntegral P ℱ W Φ (min t b) ω - itoIntegral P ℱ W Φ (min t a) ω := by
  classical
  have hΨ : (fun s ω => Set.indicator (Set.Ioc a b) (fun _ => Φ s ω) s) =
      restrictFun Φ a b Set.univ := by
    funext s ω; simp [restrictFun, Set.indicator]
  rw [hΨ]
  have hU : MeasurableSet[ℱ a] (Set.univ : Set Ω) := MeasurableSet.univ
  have hM := isItoIntegral_itoIntegral hW hΦ
  have hMA := hM.restrict hW hΦ ha hab hU
  have hΨ' := hΦ.restrictFun (b := b) hU
  filter_upwards [(isItoIntegral_itoIntegral hW hΨ').ae_eq_forall_of_brownian hW hMA hΨ']
    with ω hω t
  rw [hω t]; simp

section Doob

theorem iSup_Icc_enorm_eq_of_dense {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ} {D : Set ℝ}
    (hDs : D ⊆ Set.Icc 0 T) (hDc : Set.Icc 0 T ⊆ closure D) :
    (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ₑ) = ⨆ d ∈ D, ‖f d‖ₑ := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (iSup₂_le fun d hd => le_iSup₂ (f := fun t _ => ‖f t‖ₑ) d (hDs hd))
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.1 (hDc ht)
  have h1 : Tendsto (fun n => ‖f (u n)‖ₑ) atTop (𝓝 ‖f t‖ₑ) :=
    (continuous_enorm.comp hf).continuousAt.tendsto.comp hut
  exact le_of_tendsto' h1 fun n => le_iSup₂ (f := fun d _ => ‖f d‖ₑ) (u n) (hu n)

theorem measurable_iSup_Icc_enorm {X : ℝ → Ω → ℝ} (hX : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω) (T : ℝ) :
    Measurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖X t ω‖ₑ) := by
  obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ) T)
  have : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖X t ω‖ₑ) = ⨆ d ∈ D, ‖X d ω‖ₑ := fun ω =>
    iSup_Icc_enorm_eq_of_dense (hc ω) hDs hDd
  simp_rw [this]
  exact Measurable.biSup D hDc fun d _ => (hX d).enorm

theorem iSup_Icc_abs_eq {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) :
    (⨆ t ∈ Set.Icc (0 : ℝ) T, |f t|) = (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ₑ).toReal := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image hf.abs.continuousOn
  have hC' : ∀ t ∈ Set.Icc (0 : ℝ) T, |f t| ≤ C := fun t ht => hC ⟨t, ht, rfl⟩
  have hSfin : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ₑ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup₂_le fun t ht => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hC' t ht)
  have hg : ∀ t, 0 ≤ ⨆ (_ : t ∈ Set.Icc (0 : ℝ) T), |f t| := fun t => Real.iSup_nonneg fun _ => abs_nonneg _
  have hgle : ∀ t, (⨆ (_ : t ∈ Set.Icc (0 : ℝ) T), |f t|) ≤ max C 0 := fun t =>
    Real.iSup_le (fun ht => (hC' t ht).trans (le_max_left _ _)) (le_max_right _ _)
  have hbdd : BddAbove (Set.range fun t => ⨆ (_ : t ∈ Set.Icc (0 : ℝ) T), |f t|) :=
    ⟨max C 0, by rintro _ ⟨t, rfl⟩; exact hgle t⟩
  apply le_antisymm
  · refine Real.iSup_le (fun t => Real.iSup_le (fun ht => ?_) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    have := ENNReal.toReal_mono hSfin (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => ‖f t‖ₑ) t ht)
    simpa using this
  · have hL : 0 ≤ ⨆ t, ⨆ (_ : t ∈ Set.Icc (0 : ℝ) T), |f t| := Real.iSup_nonneg hg
    have : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ₑ) ≤ ENNReal.ofReal (⨆ t, ⨆ (_ : t ∈ Set.Icc (0 : ℝ) T), |f t|) := by
      refine iSup₂_le fun t ht => ?_
      rw [Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      refine le_trans ?_ (le_ciSup hbdd t)
      exact le_ciSup (f := fun _ : t ∈ Set.Icc (0 : ℝ) T => |f t|) (⟨|f t|, by rintro _ ⟨h', rfl⟩; exact le_rfl⟩) ht
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    rwa [ENNReal.toReal_ofReal hL] at this

end Doob

section Doob2

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}
  {Φ : ℝ → Ω → ι → ℝ}

theorem tendsto_sqIntegralOn_of_isApprox (hΦ : IsProgressiveL2 P ℱ Φ)
    {Ψ : ℕ → SimpleIntegrand ℱ ι} {t : ℝ} (h : IsApprox P Φ Ψ t) :
    Tendsto (fun n => sqIntegralOn P (Ψ n).toFun t) atTop (𝓝 (sqIntegralOn P Φ t)) := by
  have h1 := ((tendsto_embL2_of_isApprox hΦ h).norm).pow 2
  simp_rw [norm_embL2_sq] at h1
  exact (ENNReal.tendsto_toReal_iff (fun n => ((IsProgressiveL2.simple P (Ψ n)).sq t).ne)
    (hΦ.sq t).ne).1 h1

theorem lintegral_iSup_isItoIntegral_sq_le (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {M : ℝ → Ω → ℝ} (hM : IsItoIntegral P ℱ W Φ M) (T : ℝ)
    (Ψ : ℕ → SimpleIntegrand ℱ ι) (C : Set Ω) (hC0 : P Cᶜ = 0)
    (hlim : ∀ ω ∈ C, ∀ t, Tendsto (fun n => (Ψ n).elemIntegral W t ω) atTop (𝓝 (M t ω)))
    (happ : IsApprox P Φ Ψ T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ 2 ∂P ≤ 4 * sqIntegralOn P Φ T := by
  set S : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖(Ψ n).elemIntegral W t ω‖ₑ with hS
  have hSm : ∀ n, Measurable (S n) := fun n =>
    measurable_iSup_Icc_enorm (fun t => ((Ψ n).adapted_elemIntegral hW t).mono (ℱ.le t) le_rfl)
      (fun ω => (Ψ n).continuous_elemIntegral hW.cont ω) T
  have hpt : ∀ ω ∈ C, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ 2 ≤ liminf (fun n => S n ω ^ 2) atTop := by
    intro ω hω
    have hmono : Monotone fun x : ℝ≥0∞ => x ^ 2 := fun a b hab => pow_le_pow_left' hab 2
    have hcont : ∀ x : ℝ≥0∞, ContinuousAt (fun x : ℝ≥0∞ => x ^ 2) x := fun x =>
      (ENNReal.continuous_pow 2).continuousAt
    have e1 : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ 2 = ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ ^ 2 := by
      rw [Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ 2) (hcont _) hmono (by simp)]
      refine iSup_congr fun t => ?_
      rw [Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ 2) (hcont _) hmono (by simp)]
    rw [e1]
    refine iSup₂_le fun t ht => ?_
    have h1 : Tendsto (fun n => ‖(Ψ n).elemIntegral W t ω‖ₑ ^ 2) atTop (𝓝 (‖M t ω‖ₑ ^ 2)) := by
      have := ((ENNReal.continuous_pow 2).comp continuous_enorm).tendsto (M t ω)
      simpa [Function.comp_def] using this.comp (hlim ω hω t)
    rw [← h1.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    exact pow_le_pow_left' (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
      ‖(Ψ n).elemIntegral W t ω‖ₑ) t ht) 2
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ 2 ∂P
      ≤ ∫⁻ ω, liminf (fun n => S n ω ^ 2) atTop ∂P := by
        refine lintegral_mono_ae ?_
        have : ∀ᵐ ω ∂P, ω ∈ C := by
          rw [ae_iff]; exact hC0
        filter_upwards [this] with ω hω using hpt ω hω
    _ ≤ liminf (fun n => ∫⁻ ω, S n ω ^ 2 ∂P) atTop :=
        lintegral_liminf_le' fun n => ((hSm n).pow_const 2).aemeasurable
    _ ≤ liminf (fun n => 4 * sqIntegralOn P (Ψ n).toFun T) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n =>
          SimpleIntegrand.lintegral_iSup_elemIntegral_sq_le hW (Ψ n) T)
    _ = 4 * sqIntegralOn P Φ T := by
        have := ENNReal.Tendsto.const_mul (tendsto_sqIntegralOn_of_isApprox hΦ happ)
          (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))
        exact this.liminf_eq

end Doob2

/-- **Doob's `L²` maximal inequality** for the Itô integral:
`E sup_{t ≤ T} M_t² ≤ 4 E ∫_0^T ∑_k |Φ^k|²` (pathwise supremum; M L4984, L10583, L9415). -/
theorem lintegral_iSup_itoIntegral_sq_le [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) (T : ℝ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ) ^ 2 ∂P ≤
      4 * sqIntegralOn P Φ T := by
  obtain ⟨Ψ, M, C, hM, hCm, hC0, hlim, happ⟩ := exists_isItoIntegral_aux hW hΦ
  have hae := (isItoIntegral_itoIntegral hW hΦ).ae_eq_forall_of_brownian hW hM hΦ
  calc _ = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ 2 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with ω hω
        simp_rw [hω]
    _ ≤ _ := lintegral_iSup_isItoIntegral_sq_le hW hΦ hM T Ψ C hC0 hlim (happ T)

/-- The pathwise supremum of the integral over `[0, T]` is in `L²`. -/
theorem memLp_two_iSup_itoIntegral [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (T : ℝ) :
    MemLp (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, |itoIntegral P ℱ W Φ t ω|) 2 P := by
  have hZ : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, |itoIntegral P ℱ W Φ t ω|) =
      fun ω => (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ).toReal := funext fun ω =>
    iSup_Icc_abs_eq (continuous_itoIntegral P ℱ W Φ ω) T
  have hmeas := measurable_iSup_Icc_enorm (X := itoIntegral P ℱ W Φ)
    (fun t => (adapted_itoIntegral P ℱ W Φ t).mono (ℱ.le t) le_rfl)
    (continuous_itoIntegral P ℱ W Φ) T
  rw [hZ]
  have hsm : AEStronglyMeasurable (fun ω =>
      (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ).toReal) P :=
    hmeas.ennreal_toReal.aestronglyMeasurable
  rw [memLp_iff]
  have h1 : eLpNorm (fun ω => (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ).toReal) 2 P ^ 2
      ≤ 4 * sqIntegralOn P Φ T := by
    rw [← lintegral_enorm_sq_eq_eLpNorm_sq hsm]
    refine le_trans (lintegral_mono fun ω => ?_) (lintegral_iSup_itoIntegral_sq_le hW hΦ T)
    refine pow_le_pow_left' ?_ 2
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at h1
  simp at h1
  exact (ENNReal.mul_lt_top (by norm_num) (hΦ.sq T)).ne h1

/-! ### Stopping -/

/-- The integrand stopped at `τ`: `1_{s ≤ τ} Φ_s`. -/
def stopIntegrand (Φ : ℝ → Ω → ι → ℝ) (τ : Ω → WithTop ℝ) : ℝ → Ω → ι → ℝ :=
  fun s ω => Set.indicator {ω | (s : WithTop ℝ) ≤ τ ω} (Φ s) ω

theorem isProgressive_stopIntegrand {Φ : ℝ → Ω → ι → ℝ} (hΦ : IsProgressive ℱ Φ) {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) : IsProgressive ℱ (HRS.stopIntegrand Φ τ) := by
  intro i
  have h := (isProgressive_indicator_le_stoppingTime ℱ hτ i).smul (hΦ i)
  convert h using 1
  funext p
  by_cases hp : (p.1 : WithTop ℝ) ≤ τ p.2 <;> simp [HRS.stopIntegrand, Set.indicator, hp]

theorem enorm_stopIntegrand_le (Φ : ℝ → Ω → ι → ℝ) (τ : Ω → WithTop ℝ) (s : ℝ) (ω : Ω) (k : ι) :
    ‖HRS.stopIntegrand Φ τ s ω k‖ₑ ≤ ‖Φ s ω k‖ₑ := by
  by_cases hp : (s : WithTop ℝ) ≤ τ ω <;> simp [HRS.stopIntegrand, Set.indicator, hp]

theorem IsProgressiveL2.stopIntegrand (hΦ : IsProgressiveL2 P ℱ Φ) {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) : IsProgressiveL2 P ℱ (HRS.stopIntegrand Φ τ) :=
  ⟨isProgressive_stopIntegrand hΦ.prog hτ, fun T =>
    lt_of_le_of_lt (sqIntegralOn_mono_of_enorm_le (enorm_stopIntegrand_le Φ τ) T) (hΦ.sq T)⟩

theorem IsProgressiveLocL2.stopIntegrand (hΦ : IsProgressiveLocL2 P ℱ Φ) {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) : IsProgressiveLocL2 P ℱ (HRS.stopIntegrand Φ τ) :=
  ⟨isProgressive_stopIntegrand hΦ.prog hτ, fun T => by
    filter_upwards [hΦ.sq T] with ω hω
    refine lt_of_le_of_lt (lintegral_mono fun s => ?_) hω
    exact Finset.sum_le_sum fun k _ => pow_le_pow_left' (enorm_stopIntegrand_le Φ τ s ω k) 2⟩

section Stop

/-- dyadic grid point -/
def dy (m j : ℕ) : ℝ := (j : ℝ) / 2 ^ m

theorem dy_nonneg (m j : ℕ) : 0 ≤ dy m j := by unfold dy; positivity

theorem dy_mono (m : ℕ) : Monotone (dy m) := fun i j h => by
  unfold dy
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem mem_Ioc_dy_iff (m j : ℕ) (s : ℝ) :
    s ∈ Set.Ioc (dy m j) (dy m (j + 1)) ↔ j + 1 = ⌈(2 : ℝ) ^ m * s⌉₊ := by
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  simp only [Set.mem_Ioc, dy, div_lt_iff₀ hpos, le_div_iff₀ hpos]
  rw [mul_comm s, ← Nat.lt_ceil, ← Nat.ceil_le]
  omega

theorem le_dyadic_iff (m j : ℕ) {s : ℝ} (hs : 0 < s) (hj : j + 1 = ⌈(2 : ℝ) ^ m * s⌉₊)
    (x : WithTop ℝ) :
    (s : WithTop ℝ) ≤ x.map (fun a => (⌈(2 : ℝ) ^ m * a⌉ : ℝ) / 2 ^ m) ↔ ((dy m j : ℝ) : WithTop ℝ) < x := by
  cases x with
  | top => simp
  | coe a =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe, WithTop.coe_lt_coe]
    have hpos : (0 : ℝ) < 2 ^ m := by positivity
    have hnn : 0 ≤ (2 : ℝ) ^ m * s := by positivity
    have hk : ⌈(2 : ℝ) ^ m * s⌉ = ((j + 1 : ℕ) : ℤ) := by
      rw [hj]; exact (Int.natCast_ceil_eq_ceil hnn).symm
    rw [le_div_iff₀ hpos, mul_comm s, ← Int.ceil_le, hk, dy, div_lt_iff₀ hpos, mul_comm a,
      show (j : ℝ) = ((j : ℤ) : ℝ) by simp, ← Int.lt_ceil]
    push_cast
    omega

variable {ℱ : Filtration ℝ mΩ} {Φ : ℝ → Ω → ι → ℝ}

/-- `∑_{j < J} 1_{τ > j/2^m} 1_{(j/2^m, (j+1)/2^m]} Φ`. -/
def pieceSum (Φ : ℝ → Ω → ι → ℝ) (τ : Ω → WithTop ℝ) (m J : ℕ) : ℝ → Ω → ι → ℝ :=
  fun s ω => ∑ j ∈ Finset.range J,
    restrictFun Φ (dy m j) (dy m (j + 1)) {ω | ((dy m j : ℝ) : WithTop ℝ) < τ ω} s ω

theorem pieceSum_eq (τ : Ω → WithTop ℝ) (m J : ℕ) {s : ℝ} (hs : 0 < s) (hsJ : s ≤ dy m J)
    (ω : Ω) : pieceSum Φ τ m J s ω = stopIntegrand Φ (dyadicUp m τ) s ω := by
  classical
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  set k := ⌈(2 : ℝ) ^ m * s⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hkJ : k ≤ J := by
    rw [hk, Nat.ceil_le]
    have : (2 : ℝ) ^ m * s ≤ 2 ^ m * dy m J := mul_le_mul_of_nonneg_left hsJ hpos.le
    refine this.trans (le_of_eq ?_)
    unfold dy; field_simp
  have hj0 : (k - 1) + 1 = k := by omega
  unfold pieceSum
  rw [Finset.sum_eq_single (k - 1)]
  · have hmem : s ∈ Set.Ioc (dy m (k - 1)) (dy m (k - 1 + 1)) := (mem_Ioc_dy_iff m (k - 1) s).2 hj0
    have hiff := le_dyadic_iff m (k - 1) hs hj0.symm.symm (τ ω)
    simp only [restrictFun, stopIntegrand, Set.indicator, Set.mem_setOf_eq, hmem, and_true]
    have : (s : WithTop ℝ) ≤ dyadicUp m τ ω ↔ ((dy m (k - 1) : ℝ) : WithTop ℝ) < τ ω := hiff
    simp only [this]
  · intro j _ hj
    have : s ∉ Set.Ioc (dy m j) (dy m (j + 1)) := fun h => hj (by
      have := (mem_Ioc_dy_iff m j s).1 h; omega)
    simp [restrictFun, this]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

section Stop2

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → ι → ℝ} {τ : Ω → WithTop ℝ}

theorem measurableSet_dy_lt (hτ : IsStoppingTime ℱ τ) (m j : ℕ) :
    MeasurableSet[ℱ (dy m j)] {ω | ((dy m j : ℝ) : WithTop ℝ) < τ ω} := by
  have := (hτ (dy m j)).compl
  convert this using 1
  ext ω
  simp

open Classical in
theorem pieceSum_spec (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    (hτ : IsStoppingTime ℱ τ) (m J : ℕ) :
    IsProgressiveL2 P ℱ (pieceSum Φ τ m J) ∧ ∀ᵐ ω ∂P, ∀ t,
      itoIntegral P ℱ W (pieceSum Φ τ m J) t ω =
        ∑ j ∈ Finset.range J, (if ((dy m j : ℝ) : WithTop ℝ) < τ ω then
          itoIntegral P ℱ W Φ (min t (dy m (j + 1))) ω - itoIntegral P ℱ W Φ (min t (dy m j)) ω
          else 0) := by
  induction J with
  | zero =>
    have h0 : pieceSum Φ τ m 0 = fun _ _ => (0 : ι → ℝ) := by
      funext s ω; simp [pieceSum]
    rw [h0]
    refine ⟨IsProgressiveL2.const P ℱ 0, ?_⟩
    filter_upwards [itoIntegral_const hW (0 : ι → ℝ)] with ω hω t
    simp [hω t]
  | succ J ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpc : IsProgressiveL2 P ℱ (restrictFun Φ (dy m J) (dy m (J + 1))
        {ω | ((dy m J : ℝ) : WithTop ℝ) < τ ω}) := hΦ.restrictFun (measurableSet_dy_lt hτ m J)
    have hsum : pieceSum Φ τ m (J + 1) = fun s ω => pieceSum Φ τ m J s ω +
        restrictFun Φ (dy m J) (dy m (J + 1)) {ω | ((dy m J : ℝ) : WithTop ℝ) < τ ω} s ω := by
      funext s ω; simp [pieceSum, Finset.sum_range_succ]
    rw [hsum]
    refine ⟨ih1.add hpc, ?_⟩
    have hM := isItoIntegral_itoIntegral hW hΦ
    have hMA := hM.restrict hW hΦ (dy_nonneg m J) (dy_mono m (Nat.le_succ J))
      (measurableSet_dy_lt hτ m J)
    have h3 := (isItoIntegral_itoIntegral hW hpc).ae_eq_forall_of_brownian hW hMA hpc
    filter_upwards [itoIntegral_add hW ih1 hpc, ih2, h3] with ω h1 h2 h3 t
    rw [h1 t, h2 t, h3 t, Finset.sum_range_succ]
    congr 1
    split_ifs <;> rfl

theorem telescope_aux (f : ℕ → ℝ) (k J : ℕ) :
    ∑ j ∈ Finset.range J, (if j < k then f (j + 1) - f j else 0) = f (min J k) - f 0 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : J < k
    · rw [if_pos h, min_eq_left (by omega : J + 1 ≤ k), min_eq_left (by omega : J ≤ k)]
      ring
    · rw [if_neg h, min_eq_right (by omega : k ≤ J + 1), min_eq_right (by omega : k ≤ J)]
      ring

theorem sum_eq_stopped_top (M : ℝ → ℝ) (hM0 : ∀ s ≤ 0, M s = 0) (m J : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (htJ : t ≤ dy m J) :
    ∑ j ∈ Finset.range J, (if ((dy m j : ℝ) : WithTop ℝ) < (⊤ : WithTop ℝ) then
      M (min t (dy m (j + 1))) - M (min t (dy m j)) else 0) = M t := by
  have := telescope_aux (fun j => M (min t (dy m j))) J J
  simp only [WithTop.coe_lt_top, if_true]
  have h2 : ∑ j ∈ Finset.range J, (M (min t (dy m (j + 1))) - M (min t (dy m j))) =
      ∑ j ∈ Finset.range J, (if j < J then M (min t (dy m (j + 1))) - M (min t (dy m j)) else 0) :=
    Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.1 hj)]
  rw [h2, this, min_self]
  have h0 : dy m 0 = 0 := by simp [dy]
  rw [min_eq_left htJ, h0, min_eq_right ht, hM0 0 le_rfl]
  ring

theorem sum_eq_stopped_coe (M : ℝ → ℝ) (hM0 : ∀ s ≤ 0, M s = 0) (m J : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (htJ : t ≤ dy m J) (a : ℝ) :
    ∑ j ∈ Finset.range J, (if ((dy m j : ℝ) : WithTop ℝ) < ((a : ℝ) : WithTop ℝ) then
      M (min t (dy m (j + 1))) - M (min t (dy m j)) else 0) =
      M (min t ((⌈(2 : ℝ) ^ m * a⌉ : ℝ) / 2 ^ m)) := by
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  rcases le_or_gt a 0 with ha | ha
  · have h1 : ∀ j ∈ Finset.range J, (if ((dy m j : ℝ) : WithTop ℝ) < ((a : ℝ) : WithTop ℝ) then
        M (min t (dy m (j + 1))) - M (min t (dy m j)) else 0) = 0 := fun j _ => by
      rw [if_neg]
      rw [WithTop.coe_lt_coe, not_lt]
      exact ha.trans (dy_nonneg m j)
    rw [Finset.sum_eq_zero h1]
    symm
    apply hM0
    refine (min_le_right _ _).trans ?_
    rw [div_nonpos_iff]
    right
    refine ⟨?_, hpos.le⟩
    have : ⌈(2 : ℝ) ^ m * a⌉ ≤ 0 := Int.ceil_le.2 (by simpa using mul_nonpos_of_nonneg_of_nonpos hpos.le ha)
    exact_mod_cast this
  · set K := ⌈(2 : ℝ) ^ m * a⌉ with hK
    have hK1 : 0 < K := Int.ceil_pos.2 (by positivity)
    set kn := K.toNat with hkn
    have hKk : (K : ℝ) = (kn : ℝ) := by
      have : (kn : ℤ) = K := Int.toNat_of_nonneg hK1.le
      rw [← this]; simp
    have hcond : ∀ j : ℕ, (((dy m j : ℝ) : WithTop ℝ) < ((a : ℝ) : WithTop ℝ)) ↔ j < kn := fun j => by
      rw [WithTop.coe_lt_coe, dy, div_lt_iff₀ hpos, mul_comm a, show (j : ℝ) = ((j : ℤ) : ℝ) by simp,
        ← Int.lt_ceil]
      omega
    have h2 : ∑ j ∈ Finset.range J, (if ((dy m j : ℝ) : WithTop ℝ) < ((a : ℝ) : WithTop ℝ) then
        M (min t (dy m (j + 1))) - M (min t (dy m j)) else 0) =
        ∑ j ∈ Finset.range J, (if j < kn then M (min t (dy m (j + 1))) - M (min t (dy m j)) else 0) :=
      Finset.sum_congr rfl fun j _ => by simp only [hcond j]
    rw [h2, telescope_aux (fun j => M (min t (dy m j))) kn J]
    have h0 : dy m 0 = 0 := by simp [dy]
    simp only [h0, min_eq_right ht, hM0 0 le_rfl, sub_zero]
    have hdy : (K : ℝ) / 2 ^ m = dy m kn := by rw [hKk]; rfl
    rw [hdy]
    rcases le_total J kn with hJ | hJ
    · rw [min_eq_left hJ]
      have : min t (dy m kn) = t := min_eq_left (htJ.trans (dy_mono m hJ))
      rw [this, min_eq_left htJ]
    · rw [min_eq_right hJ]

theorem itoIntegral_pieceSum_ae (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    (hτ : IsStoppingTime ℱ τ) (m J : ℕ) {t : ℝ} (ht : 0 ≤ t) (htJ : t ≤ dy m J) :
    ∀ᵐ ω ∂P, itoIntegral P ℱ W (pieceSum Φ τ m J) t ω =
      stoppedProcess (itoIntegral P ℱ W Φ) (dyadicUp m τ) t ω := by
  filter_upwards [(pieceSum_spec hW hΦ hτ m J).2] with ω hω
  rw [hω t]
  have hM0 : ∀ s ≤ 0, itoIntegral P ℱ W Φ s ω = 0 := fun s hs => itoIntegral_of_nonpos P ℱ W Φ hs ω
  cases h : τ ω with
  | top =>
    rw [stoppedProcess_apply_top ((dyadicUp_eq_top_iff m τ ω).2 h)]
    exact sum_eq_stopped_top (fun s => itoIntegral P ℱ W Φ s ω) hM0 m J ht htJ
  | coe a =>
    have hd : dyadicUp m τ ω = (((⌈(2 : ℝ) ^ m * a⌉ : ℝ) / 2 ^ m : ℝ) : WithTop ℝ) := by
      simp [dyadicUp, h]
    rw [stoppedProcess_apply_coe hd]
    exact sum_eq_stopped_coe (fun s => itoIntegral P ℱ W Φ s ω) hM0 m J ht htJ a

theorem sqIntegralOn_pieceSum_sub (τ : Ω → WithTop ℝ) (m J : ℕ) {t : ℝ} (htJ : t ≤ dy m J) :
    sqIntegralOn P (fun s ω => pieceSum Φ τ m J s ω - stopIntegrand Φ (dyadicUp m τ) s ω) t = 0 := by
  unfold sqIntegralOn
  have : ∀ ω, ∫⁻ s in Set.Icc 0 t, ∑ k, ‖pieceSum Φ τ m J s ω k -
      stopIntegrand Φ (dyadicUp m τ) s ω k‖ₑ ^ 2 = 0 := fun ω => by
    rw [← setLIntegral_congr Ioc_ae_eq_Icc]
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0)]
    · simp
    · intro s hs
      simp [pieceSum_eq τ m J hs.1 (hs.2.trans htJ) ω]
  simp [this]

theorem enorm_stop_sub_le (Φ : ℝ → Ω → ι → ℝ) (σ σ' : Ω → WithTop ℝ) (s : ℝ) (ω : Ω) (k : ι) :
    ‖stopIntegrand Φ σ s ω k - stopIntegrand Φ σ' s ω k‖ₑ ≤ ‖Φ s ω k‖ₑ := by
  by_cases h1 : (s : WithTop ℝ) ≤ σ ω <;> by_cases h2 : (s : WithTop ℝ) ≤ σ' ω <;>
    simp [stopIntegrand, Set.indicator, h1, h2]

theorem eventually_stop_dyadic_eq (τ : Ω → WithTop ℝ) (s : ℝ) (ω : Ω) :
    ∀ᶠ m : ℕ in atTop, stopIntegrand Φ (dyadicUp m τ) s ω = stopIntegrand Φ τ s ω := by
  cases h : τ ω with
  | top =>
    refine Eventually.of_forall fun m => ?_
    simp [stopIntegrand, Set.indicator, (dyadicUp_eq_top_iff m τ ω).2 h, h]
  | coe a =>
    by_cases hs : s ≤ a
    · refine Eventually.of_forall fun m => ?_
      have h1 : (s : WithTop ℝ) ≤ τ ω := by rw [h]; exact_mod_cast hs
      have h2 : (s : WithTop ℝ) ≤ dyadicUp m τ ω := h1.trans (le_dyadicUp m τ ω)
      simp [stopIntegrand, Set.indicator, h1, h2]
    · have hlt : a < s := not_le.1 hs
      have hT : Tendsto (fun m : ℕ => a + (1 / 2 : ℝ) ^ m) atTop (𝓝 (a + 0)) :=
        tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      rw [add_zero] at hT
      filter_upwards [hT.eventually_lt_const hlt] with m hm
      obtain ⟨c, hc1, hc2, hc3⟩ := dyadicUp_lt_add (m := m) (τ := τ) (ω := ω) h
      have h1 : ¬ (s : WithTop ℝ) ≤ τ ω := by rw [h]; exact_mod_cast hs
      have h2 : ¬ (s : WithTop ℝ) ≤ dyadicUp m τ ω := by
        rw [hc1]; exact_mod_cast not_le.2 (hc3.trans hm)
      simp [stopIntegrand, Set.indicator, h1, h2]

theorem tendsto_sqIntegralOn_stop_dyadic (hΦ : IsProgressiveL2 P ℱ Φ) {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) (t : ℝ) :
    Tendsto (fun m : ℕ => sqIntegralOn P (fun s ω => stopIntegrand Φ (dyadicUp m τ) s ω -
      stopIntegrand Φ τ s ω) t) atTop (𝓝 0) := by
  have hprog : ∀ m : ℕ, IsProgressive ℱ (fun s ω => stopIntegrand Φ (dyadicUp m τ) s ω -
      stopIntegrand Φ τ s ω) := fun m =>
    isProgressive_sub (isProgressive_stopIntegrand hΦ.prog (isStoppingTime_dyadicUp ℱ hτ m))
      (isProgressive_stopIntegrand hΦ.prog hτ)
  simp_rw [← lintegral_enorm_sq_eclamp (P := P) (hprog _)]
  have key := tendsto_lintegral_of_dominated_convergence (μ := tsMeasure P t)
    (F := fun m p => ‖eclamp (fun s ω => stopIntegrand Φ (dyadicUp m τ) s ω -
      stopIntegrand Φ τ s ω) t p‖ₑ ^ 2) (f := fun _ => 0)
    (fun p => ‖eclamp Φ t p‖ₑ ^ 2)
    (fun m => ((measurable_eclamp (hprog m) t).enorm.pow_const 2))
    (fun m => Eventually.of_forall fun p => ?_)
    (by rw [lintegral_enorm_sq_eclamp hΦ.prog]; exact (hΦ.sq t).ne)
    (Eventually.of_forall fun p => ?_)
  · simpa using key
  · simp only [eclamp, enorm_toLp_sq]
    exact Finset.sum_le_sum fun k _ => pow_le_pow_left' (enorm_stop_sub_le Φ _ _ _ _ k) 2
  · have := eventually_stop_dyadic_eq (Φ := Φ) τ (min p.1 t) p.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [this] with m hm
    simp [eclamp, hm]

theorem stoppedProcess_itoIntegral_of_nonpos (P : Measure Ω) (ℱ : Filtration ℝ mΩ)
    (W : ℝ≥0 → Ω → ι → ℝ) (Φ : ℝ → Ω → ι → ℝ) (τ : Ω → WithTop ℝ) {u : ℝ} (hu : u ≤ 0) (ω : Ω) :
    stoppedProcess (itoIntegral P ℱ W Φ) τ u ω = 0 := by
  cases h : τ ω with
  | top => rw [stoppedProcess_apply_top h]; exact itoIntegral_of_nonpos P ℱ W Φ hu ω
  | coe c =>
    rw [stoppedProcess_apply_coe h]
    exact itoIntegral_of_nonpos P ℱ W Φ ((min_le_left _ _).trans hu) ω

theorem continuous_stoppedProcess_itoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ)
    (W : ℝ≥0 → Ω → ι → ℝ) (Φ : ℝ → Ω → ι → ℝ) (τ : Ω → WithTop ℝ) (ω : Ω) :
    Continuous fun t => stoppedProcess (itoIntegral P ℱ W Φ) τ t ω := by
  cases h : τ ω with
  | top =>
    have : (fun t => stoppedProcess (itoIntegral P ℱ W Φ) τ t ω) = fun t => itoIntegral P ℱ W Φ t ω :=
      funext fun t => stoppedProcess_apply_top h t
    rw [this]; exact continuous_itoIntegral P ℱ W Φ ω
  | coe c =>
    have : (fun t => stoppedProcess (itoIntegral P ℱ W Φ) τ t ω) =
        fun t => itoIntegral P ℱ W Φ (min t c) ω := funext fun t => stoppedProcess_apply_coe h t
    rw [this]
    exact (continuous_itoIntegral P ℱ W Φ ω).comp (continuous_id.min continuous_const)

end Stop2
end Stop

/-- **Localisation identity**: `∫_0^t 1_{s ≤ τ} Φ_s dW_s = M_{t ∧ τ}` for every stopping time `τ`
(M L10573 "first stopped when |M| reaches R", L11875-11879, L3137). -/
theorem itoIntegral_stopIntegrand [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (stopIntegrand Φ τ) t ω =
      stoppedProcess (itoIntegral P ℱ W Φ) τ t ω := by
  have hΦS : IsProgressiveL2 P ℱ (stopIntegrand Φ τ) := hΦ.stopIntegrand hτ
  refine ae_forall_eq_of_continuous P _ _ (continuous_itoIntegral P ℱ W _)
    (continuous_stoppedProcess_itoIntegral P ℱ W Φ τ) fun t => ?_
  rcases le_total t 0 with ht | ht
  · refine Eventually.of_forall fun ω => ?_
    rw [itoIntegral_of_nonpos P ℱ W _ ht, stoppedProcess_itoIntegral_of_nonpos P ℱ W Φ τ ht]
  -- the main case
  set J : ℕ → ℕ := fun m => ⌈(2 : ℝ) ^ m * t⌉₊ with hJ
  have htJ : ∀ m, t ≤ dy m (J m) := fun m => by
    have hpos : (0 : ℝ) < 2 ^ m := by positivity
    unfold dy
    rw [le_div_iff₀ hpos, mul_comm]
    exact Nat.le_ceil _
  set X : ℕ → Ω → ℝ := fun m => stoppedProcess (itoIntegral P ℱ W Φ) (dyadicUp m τ) t with hX
  set Z : Ω → ℝ := itoIntegral P ℱ W (stopIntegrand Φ τ) t with hZ
  have hZm : AEMeasurable Z P := ((adapted_itoIntegral P ℱ W _ t).mono (ℱ.le t) le_rfl).aemeasurable
  have hXae : ∀ m, X m =ᵐ[P] itoIntegral P ℱ W (pieceSum Φ τ m (J m)) t := fun m => by
    filter_upwards [itoIntegral_pieceSum_ae hW hΦ hτ m (J m) ht (htJ m)] with ω hω
    exact hω.symm
  have hXm : ∀ m, AEMeasurable (X m) P := fun m =>
    (((adapted_itoIntegral P ℱ W _ t).mono (ℱ.le t) le_rfl).aemeasurable).congr (hXae m).symm
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop
      (𝓝 (stoppedProcess (itoIntegral P ℱ W Φ) τ t ω)) :=
    Eventually.of_forall fun ω =>
      tendsto_stoppedProcess_dyadicUp (itoIntegral P ℱ W Φ) ω (continuous_itoIntegral P ℱ W Φ ω) τ t
  -- L² convergence of X m to Z
  have hconv : Tendsto (fun m => ∫⁻ ω, ‖Z ω - X m ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    have hpieceL2 : ∀ m, IsProgressiveL2 P ℱ (pieceSum Φ τ m (J m)) := fun m =>
      (pieceSum_spec hW hΦ hτ m (J m)).1
    have hD : ∀ m, IsProgressiveL2 P ℱ (stopIntegrand Φ (dyadicUp m τ)) := fun m =>
      hΦ.stopIntegrand (isStoppingTime_dyadicUp ℱ hτ m)
    have h1 : ∀ m, ∫⁻ ω, ‖Z ω - X m ω‖ₑ ^ 2 ∂P ≤
        2 * sqIntegralOn P (fun s ω => stopIntegrand Φ (dyadicUp m τ) s ω -
          stopIntegrand Φ τ s ω) t := fun m => by
      have e1 : ∫⁻ ω, ‖Z ω - X m ω‖ₑ ^ 2 ∂P =
          ∫⁻ ω, ‖Z ω - itoIntegral P ℱ W (pieceSum Φ τ m (J m)) t ω‖ₑ ^ 2 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hXae m] with ω hω
        rw [hω]
      rw [e1, (isItoIntegral_itoIntegral hW hΦS).lintegral_sub_sq hW hΦS (hpieceL2 m)
        (isItoIntegral_itoIntegral hW (hpieceL2 m)) t]
      have hadd := sqIntegralOn_add_le (P := P)
        (isProgressive_sub hΦS.prog (hD m).prog)
        (isProgressive_sub (hD m).prog (hpieceL2 m).prog) t
      have e2 : (fun s ω => (stopIntegrand Φ τ s ω - stopIntegrand Φ (dyadicUp m τ) s ω) +
          (stopIntegrand Φ (dyadicUp m τ) s ω - pieceSum Φ τ m (J m) s ω)) =
          fun s ω => stopIntegrand Φ τ s ω - pieceSum Φ τ m (J m) s ω := by
        funext s ω; ring
      rw [e2] at hadd
      have e3 : sqIntegralOn P (fun s ω => stopIntegrand Φ (dyadicUp m τ) s ω -
          pieceSum Φ τ m (J m) s ω) t = 0 := by
        rw [sqIntegralOn_sub_comm]; exact sqIntegralOn_pieceSum_sub τ m (J m) (htJ m)
      rw [e3, mul_zero, add_zero, sqIntegralOn_sub_comm (stopIntegrand Φ τ)
        (stopIntegrand Φ (dyadicUp m τ))] at hadd
      exact hadd
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) h1
    have := ENNReal.Tendsto.const_mul (tendsto_sqIntegralOn_stop_dyadic hΦ hτ t)
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    simpa using this
  have hYm : AEMeasurable (stoppedProcess (itoIntegral P ℱ W Φ) τ t) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop hXm hlim
  have hle := lintegral_enorm_sq_le_liminf hXm hZm hlim
  rw [hconv.liminf_eq] at hle
  have h0 : ∫⁻ ω, ‖Z ω - stoppedProcess (itoIntegral P ℱ W Φ) τ t ω‖ₑ ^ 2 ∂P = 0 := le_antisymm hle bot_le
  filter_upwards [ae_eq_zero_of_lintegral_enorm_sq_eq_zero (hZm.sub hYm) h0] with ω hω
  simpa [sub_eq_zero] using hω

/-- The stopped Itô integral is a martingale (optional stopping for stochastic integrals). -/
theorem martingale_stoppedProcess_itoIntegral [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) : Martingale (stoppedProcess (itoIntegral P ℱ W Φ) τ) ℱ P :=
  Martingale.stoppedProcess_of_continuous P ℱ _ (martingale_itoIntegral hW hΦ)
    (continuous_itoIntegral P ℱ W Φ) hτ

/-- The stopped Itô integral has mean zero: `E[M_{t ∧ τ}] = 0` ("the stopped martingale is
integrable, and therefore ...", M L11879). -/
theorem integral_stoppedProcess_itoIntegral [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) (t : ℝ) :
    ∫ ω, stoppedProcess (itoIntegral P ℱ W Φ) τ t ω ∂P = 0 := by
  have hz : ∀ u : ℝ, u ≤ 0 → ∀ ω, stoppedProcess (itoIntegral P ℱ W Φ) τ u ω = 0 := fun u hu ω => by
    cases h : τ ω with
    | top => rw [stoppedProcess_apply_top h]; exact itoIntegral_of_nonpos P ℱ W Φ hu ω
    | coe c =>
      rw [stoppedProcess_apply_coe h]
      exact itoIntegral_of_nonpos P ℱ W Φ ((min_le_left _ _).trans hu) ω
  rcases le_total t 0 with ht | ht
  · simp [hz t ht]
  · rw [Martingale.integral_stoppedProcess_of_continuous P ℱ _ (martingale_itoIntegral hW hΦ)
      (continuous_itoIntegral P ℱ W Φ) hτ 0 t ht]
    simp [hz 0 le_rfl]

end L2

/-! ### The integral in the locally square-integrable class -/

/-- The running squared `L²` norm `t ↦ ∫_0^t ∑_k |Φ^k_s|² ds` (as a real number; `0` when infinite). -/
def sqIntegralProcess (Φ : ℝ → Ω → ι → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => (∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k‖ₑ ^ 2).toReal

/-- The (measurable) set of `ω` on which `∫_0^T |Φ|² < ∞` for every integer `T`. -/
def finiteSet (Φ : ℝ → Ω → ι → ℝ) : Set Ω :=
  {ω | ∀ T : ℕ, ∫⁻ s in Set.Icc 0 (T : ℝ), ∑ k, ‖Φ s ω k‖ₑ ^ 2 < ∞}

open Classical in
/-- The running squared norm with the paths outside `finiteSet Φ` replaced by `0`, so that it has
everywhere continuous nondecreasing paths. -/
def sqIntegralProcess' (Φ : ℝ → Ω → ι → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => if ω ∈ finiteSet Φ then sqIntegralProcess Φ t ω else 0

/-- The localising stopping times `τ_n = inf {t ≥ 0 : ∫_0^t |Φ|² ≥ n}`. -/
def locTime (Φ : ℝ → Ω → ι → ℝ) (n : ℕ) : Ω → WithTop ℝ :=
  hittingAfter (sqIntegralProcess' Φ) (Set.Ici (n : ℝ)) 0

section Loc

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} {Φ Φ' : ℝ → Ω → ι → ℝ}

theorem measurableSet_finiteSet (hΦ : IsProgressive ℱ Φ) : MeasurableSet (finiteSet Φ) := by
  have : finiteSet Φ = ⋂ T : ℕ, {ω | ∫⁻ s in Set.Icc 0 (T : ℝ), ∑ k, ‖Φ s ω k‖ₑ ^ 2 < ∞} := by
    ext ω; simp [finiteSet]
  rw [this]
  exact MeasurableSet.iInter fun T =>
    measurableSet_lt (measurable_lintegral_sqSum' hΦ (T : ℝ)) measurable_const

theorem lintegral_Icc_eq_kernel (g : ℝ → ℝ≥0∞) (N : ℕ)
    (hg : ∫⁻ s in Set.Icc 0 (N : ℝ), g s < ∞) :
    ∃ h : ℝ → ℝ≥0∞, Measurable h ∧ ∀ t : ℝ, 0 ≤ t → t ≤ N →
      ∫⁻ s in Set.Icc 0 t, g s = ∫⁻ s in Set.Icc 0 t, h s := by
  obtain ⟨h, hm, hle, heq⟩ := exists_measurable_le_lintegral_eq (μ := volume.restrict (Set.Icc 0 (N : ℝ))) g
  refine ⟨h, hm, fun t ht0 htN => ?_⟩
  -- split `[0, N] = [0, t] ∪ (t, N]`
  have hsplit : ∀ f : ℝ → ℝ≥0∞, ∫⁻ s in Set.Icc 0 (N : ℝ), f s =
      (∫⁻ s in Set.Icc 0 t, f s) + ∫⁻ s in Set.Ioc t (N : ℝ), f s := fun f => by
    have hdisj : Disjoint (Set.Icc (0 : ℝ) t) (Set.Ioc t (N : ℝ)) :=
      Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
    have := lintegral_union (μ := volume) (f := f) measurableSet_Ioc hdisj
    rw [Set.Icc_union_Ioc_eq_Icc ht0 htN] at this
    exact this
  have h1 : ∫⁻ s in Set.Icc 0 t, h s ≤ ∫⁻ s in Set.Icc 0 t, g s := lintegral_mono hle
  have h2 : ∫⁻ s in Set.Ioc t (N : ℝ), h s ≤ ∫⁻ s in Set.Ioc t (N : ℝ), g s := lintegral_mono hle
  have h3 : (∫⁻ s in Set.Icc 0 t, g s) + ∫⁻ s in Set.Ioc t (N : ℝ), g s =
      (∫⁻ s in Set.Icc 0 t, h s) + ∫⁻ s in Set.Ioc t (N : ℝ), h s := by
    rw [← hsplit, ← hsplit]; exact heq
  by_contra hne
  have hlt : ∫⁻ s in Set.Icc 0 t, h s < ∫⁻ s in Set.Icc 0 t, g s := lt_of_le_of_ne h1 (Ne.symm hne)
  have hfin : ∫⁻ s in Set.Ioc t (N : ℝ), h s ≠ ∞ := by
    refine ne_top_of_le_ne_top (heq ▸ hg.ne) ?_
    exact lintegral_mono_set (fun x hx => ⟨ht0.trans hx.1.le, hx.2⟩)
  have := ENNReal.add_lt_add_of_lt_of_le hfin hlt h2
  exact this.ne h3.symm

theorem continuous_lintegral_Icc_toReal (g : ℝ → ℝ≥0∞)
    (hg : ∀ N : ℕ, ∫⁻ s in Set.Icc 0 (N : ℝ), g s < ∞) :
    Continuous fun t : ℝ => (∫⁻ s in Set.Icc 0 t, g s).toReal := by
  rw [continuous_iff_continuousAt]
  intro t0
  obtain ⟨N, hN⟩ := exists_nat_gt t0
  obtain ⟨h, hm, hgh⟩ := lintegral_Icc_eq_kernel g N (hg N)
  have hfinN : ∫⁻ s in Set.Icc 0 (N : ℝ), h s < ∞ := by
    rw [← hgh N (Nat.cast_nonneg N) le_rfl]; exact hg N
  have hint : IntegrableOn (fun s => (h s).toReal) (Set.Icc 0 (N : ℝ)) :=
    integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfinN.ne
  have hcont := intervalIntegral.continuousOn_primitive_Icc (a := 0) (b := (N : ℝ)) (μ := volume) hint
  have hcl : Continuous (fun x : ℝ => ∫ s in Set.Icc 0 (min (max x 0) (N : ℝ)), (h s).toReal) :=
    hcont.comp_continuous ((continuous_id.max continuous_const).min continuous_const)
      (fun x => ⟨le_min (le_max_right _ _) (Nat.cast_nonneg N), min_le_right _ _⟩)
  have heq : ∀ x : ℝ, x ≤ N → (∫⁻ s in Set.Icc 0 x, g s).toReal =
      ∫ s in Set.Icc 0 (min (max x 0) (N : ℝ)), (h s).toReal := fun x hx => by
    rcases lt_or_ge x 0 with hx0 | hx0
    · have : min (max x 0) (N : ℝ) = 0 := by
        rw [max_eq_right hx0.le]; exact min_eq_left (Nat.cast_nonneg N)
      rw [this, Set.Icc_eq_empty (not_le.2 hx0)]
      simp
    · rw [hgh x hx0 hx, min_eq_left (by simpa [max_eq_left hx0] using hx), max_eq_left hx0,
        integral_toReal hm.aemeasurable]
      refine ae_lt_top hm (ne_top_of_le_ne_top hfinN.ne (lintegral_mono_set ?_))
      exact Set.Icc_subset_Icc le_rfl hx
  refine hcl.continuousAt.congr ?_
  filter_upwards [Iio_mem_nhds hN] with x hx
  exact (heq x hx.le).symm


theorem continuous_sqIntegralProcess' (Φ : ℝ → Ω → ι → ℝ) (ω : Ω) :
    Continuous fun t => sqIntegralProcess' Φ t ω := by
  by_cases hω : ω ∈ finiteSet Φ
  · have : (fun t => sqIntegralProcess' Φ t ω) =
        fun t => (∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k‖ₑ ^ 2).toReal := by
      funext t; simp [sqIntegralProcess', sqIntegralProcess, hω]
    rw [this]
    exact continuous_lintegral_Icc_toReal (fun s => ∑ k, ‖Φ s ω k‖ₑ ^ 2) hω
  · have : (fun t => sqIntegralProcess' Φ t ω) = fun _ => 0 := by
      funext t; simp [sqIntegralProcess', hω]
    rw [this]; exact continuous_const

theorem measurable_lintegral_sqSum_gen {Ω' : Type*} [m : MeasurableSpace Ω'] {Ψ : ℝ → Ω' → ι → ℝ}
    (T : ℝ) (h : Measurable[Subtype.instMeasurableSpace.prod m] fun p : Set.Iic T × Ω' => Ψ p.1 p.2) :
    Measurable fun ω => ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Ψ s ω k‖ₑ ^ 2 := by
  have hg : Measurable (fun p : ℝ × Ω' =>
      ((⟨min p.1 T, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic T), p.2)) :=
    Measurable.prodMk (Measurable.subtype_mk (measurable_fst.min measurable_const)) measurable_snd
  have hm : Measurable (fun p : ℝ × Ω' => Ψ (min p.1 T) p.2) := h.comp hg
  have hG : Measurable (fun p : ℝ × Ω' => ∑ k, ‖Ψ (min p.1 T) p.2 k‖ₑ ^ 2) :=
    Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).comp hm).enorm.pow_const 2
  have := (hG.comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 T))
  simp_rw [← lintegral_sqSum_clamp Ψ T]
  exact this

theorem measurable_lintegral_sqSum_filtration (hΦ : IsProgressive ℱ Φ) (t : ℝ) :
    Measurable[ℱ t] fun ω => ∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k‖ₑ ^ 2 :=
  measurable_lintegral_sqSum_gen (m := ℱ t) t (hΦ t)

theorem ae_mem_finiteSet (hΦ : IsProgressiveLocL2 P ℱ Φ) : ∀ᵐ ω ∂P, ω ∈ finiteSet Φ := by
  have : ∀ᵐ ω ∂P, ∀ T : ℕ, ∫⁻ s in Set.Icc 0 (T : ℝ), ∑ k, ‖Φ s ω k‖ₑ ^ 2 < ∞ :=
    ae_all_iff.2 fun T => hΦ.sq (T : ℝ)
  filter_upwards [this] with ω hω
  exact hω


theorem adapted_sqIntegralProcess' (hℱ : IsCompleteFiltration P ℱ) (hΦ : IsProgressiveLocL2 P ℱ Φ) :
    Adapted ℱ (sqIntegralProcess' Φ) := by
  classical
  intro t
  have hX : Measurable[ℱ t] (sqIntegralProcess Φ t) := by
    unfold sqIntegralProcess
    exact (measurable_lintegral_sqSum_filtration hΦ.prog t).ennreal_toReal
  have hY : Measurable (sqIntegralProcess' Φ t) := by
    have hX' : Measurable (sqIntegralProcess Φ t) := hX.mono (ℱ.le t) le_rfl
    have hfs := measurableSet_finiteSet hΦ.prog
    exact Measurable.ite hfs hX' measurable_const
  refine hℱ.measurable_of_ae_eq t hX hY ?_
  filter_upwards [ae_mem_finiteSet hΦ] with ω hω
  simp [sqIntegralProcess', hω]

theorem isStoppingTime_locTime (hℱ : IsCompleteFiltration P ℱ) (hΦ : IsProgressiveLocL2 P ℱ Φ)
    (n : ℕ) : IsStoppingTime ℱ (locTime Φ n) :=
  isStoppingTime_hittingAfter_Ici ℱ _ (adapted_sqIntegralProcess' hℱ hΦ)
    (continuous_sqIntegralProcess' Φ) n

/-- The localising times exhaust time a.s.: for every `T` some `τ_n ≥ T`. -/
theorem locTime_exhaust (hΦ : IsProgressiveLocL2 P ℱ Φ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∃ n : ℕ, (T : WithTop ℝ) ≤ locTime Φ n ω :=
  Eventually.of_forall fun ω T =>
    hittingAfter_Ici_tendsto_top (sqIntegralProcess' Φ) ω (continuous_sqIntegralProcess' Φ ω) T

theorem locTime_mono (Φ : ℝ → Ω → ι → ℝ) : Monotone fun n => locTime Φ n := fun a b hab ω =>
  hittingAfter_anti (sqIntegralProcess' Φ) 0 (Set.Ici_subset_Ici.2 (Nat.cast_le.2 hab)) ω

theorem le_of_le_hittingAfter {X : ℝ → Ω → ℝ} {ω : Ω} (hX : Continuous fun t => X t ω) (n : ℝ)
    (h0 : X 0 ω ≤ n) {c : ℝ} (hc : hittingAfter X (Set.Ici n) 0 ω = (c : WithTop ℝ)) {t : ℝ}
    (ht0 : 0 ≤ t) (htc : t ≤ c) : X t ω ≤ n := by
  have hlt_aux : ∀ x : ℝ, 0 ≤ x → x < c → X x ω < n := fun x hx0 hxc => by
    have := notMem_of_lt_hittingAfter (u := X) (s := Set.Ici n) (n := 0) (ω := ω) (k := x)
      (by rw [hc]; exact_mod_cast hxc) hx0
    exact not_le.1 this
  rcases lt_or_eq_of_le htc with hlt | heq
  · exact (hlt_aux t ht0 hlt).le
  · subst heq
    by_contra hgt
    rw [not_le] at hgt
    rcases eq_or_lt_of_le ht0 with h | hpos
    · subst h; exact absurd h0 (not_le.2 hgt)
    · have hev : ∀ᶠ x in 𝓝 t, n < X x ω := hX.continuousAt.eventually (lt_mem_nhds hgt)
      have hev' : ∀ᶠ x in 𝓝[<] t, n < X x ω := hev.filter_mono nhdsWithin_le_nhds
      obtain ⟨x, hx1, hx2⟩ := (hev'.and (Ioo_mem_nhdsLT hpos)).exists
      exact absurd (hlt_aux x hx2.1.le hx2.2) (not_lt.2 hx1.le)

theorem inner_stop_le (g : ℝ → ℝ≥0∞) (X : ℝ → Ω → ℝ) (ω : Ω) (n : ℕ)
    (hX : Continuous fun t => X t ω)
    (hfin : ∀ t : ℝ, 0 ≤ t → ∫⁻ s in Set.Icc 0 t, g s = ENNReal.ofReal (X t ω)) (T : ℝ) :
    ∫⁻ s in Set.Icc 0 T, Set.indicator {s : ℝ | (s : WithTop ℝ) ≤ hittingAfter X (Set.Ici (n : ℝ)) 0 ω} g s
      ≤ ENNReal.ofReal n := by
  have h0 : X 0 ω ≤ n := by
    have := hfin 0 le_rfl
    rw [setLIntegral_measure_zero _ _ (by simp)] at this
    have h' := ENNReal.ofReal_eq_zero.1 this.symm
    exact h'.trans (Nat.cast_nonneg n)
  rcases lt_or_ge T 0 with hT | hT
  · rw [Set.Icc_eq_empty (not_le.2 hT)]; simp
  cases hσ : hittingAfter X (Set.Ici (n : ℝ)) 0 ω with
  | top =>
    have hset : {s : ℝ | (s : WithTop ℝ) ≤ (⊤ : WithTop ℝ)} = Set.univ := by
      ext s; simp
    rw [hset, Set.indicator_univ, hfin T hT]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (hittingAfter_eq_top_iff (u := X) (s := Set.Ici (n : ℝ)) (n := 0) (ω := ω)).1 hσ T hT
    exact (not_le.1 this).le
  | coe c =>
    have hc0 : 0 ≤ c := by
      have := le_hittingAfter (u := X) (s := Set.Ici (n : ℝ)) (n := (0 : ℝ)) ω
      rw [hσ] at this
      exact_mod_cast this
    have hset : {s : ℝ | (s : WithTop ℝ) ≤ (c : WithTop ℝ)} = Set.Iic c := by
      ext s; simp
    rw [hset, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hI : Set.Iic c ∩ Set.Icc 0 T = Set.Icc 0 (min c T) := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
      tauto
    rw [hI, hfin _ (le_min hc0 hT)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact le_of_le_hittingAfter hX n h0 hσ (le_min hc0 hT) (min_le_left _ _)

theorem lintegral_Icc_lt_top_of_mem_finiteSet {ω : Ω} (hω : ω ∈ finiteSet Φ) (t : ℝ) :
    ∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k‖ₑ ^ 2 < ∞ := by
  obtain ⟨N, hN⟩ := exists_nat_ge t
  exact lt_of_le_of_lt (lintegral_mono_set (Set.Icc_subset_Icc le_rfl hN)) (hω N)

theorem sqIntegralProcess'_of_mem {ω : Ω} (hω : ω ∈ finiteSet Φ) (t : ℝ) :
    ENNReal.ofReal (sqIntegralProcess' Φ t ω) = ∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k‖ₑ ^ 2 := by
  simp only [sqIntegralProcess', sqIntegralProcess, hω, if_true]
  exact ENNReal.ofReal_toReal (lintegral_Icc_lt_top_of_mem_finiteSet hω t).ne

theorem sum_enorm_stop_sq (Φ : ℝ → Ω → ι → ℝ) (τ : Ω → WithTop ℝ) (s : ℝ) (ω : Ω) :
    ∑ k, ‖stopIntegrand Φ τ s ω k‖ₑ ^ 2 =
      Set.indicator {s : ℝ | (s : WithTop ℝ) ≤ τ ω} (fun s => ∑ k, ‖Φ s ω k‖ₑ ^ 2) s := by
  by_cases h : (s : WithTop ℝ) ≤ τ ω <;> simp [stopIntegrand, Set.indicator, h]


/-- The integrand stopped at `τ_n` is in the `L²` class (`∫_0^{τ_n} |Φ|² ≤ n`). -/
theorem isProgressiveL2_stopIntegrand_locTime [IsProbabilityMeasure P]
    (hℱ : IsCompleteFiltration P ℱ) (hΦ : IsProgressiveLocL2 P ℱ Φ) (n : ℕ) :
    IsProgressiveL2 P ℱ (stopIntegrand Φ (locTime Φ n)) := by
  refine ⟨isProgressive_stopIntegrand hΦ.prog (isStoppingTime_locTime hℱ hΦ n), fun T => ?_⟩
  unfold sqIntegralOn
  calc ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ∑ k, ‖stopIntegrand Φ (locTime Φ n) s ω k‖ₑ ^ 2) ∂P
      ≤ ∫⁻ _ω, ENNReal.ofReal n ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem_finiteSet hΦ] with ω hω
        simp_rw [sum_enorm_stop_sq]
        exact inner_stop_le (fun s => ∑ k, ‖Φ s ω k‖ₑ ^ 2) (sqIntegralProcess' Φ) ω n
          (continuous_sqIntegralProcess' Φ ω)
          (fun t _ => (sqIntegralProcess'_of_mem hω t).symm) T
    _ < ⊤ := by simp

/-- `M` is the local Itô integral of `Φ`: continuous adapted, zero on `(-∞, 0]`, and for every
stopping time `τ` for which `1_{s ≤ τ} Φ` is in the `L²` class, `M_{· ∧ τ} = ∫ 1_{s ≤ τ} Φ dW`. -/
structure IsLocalItoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) (M : ℝ → Ω → ℝ) : Prop where
  cont : ∀ ω, Continuous fun t => M t ω
  adapted : Adapted ℱ M
  zero : ∀ t : ℝ, t ≤ 0 → ∀ ω, M t ω = 0
  stopped : ∀ τ : Ω → WithTop ℝ, IsStoppingTime ℱ τ → IsProgressiveL2 P ℱ (stopIntegrand Φ τ) →
    ∀ᵐ ω ∂P, ∀ t, stoppedProcess M τ t ω = itoIntegral P ℱ W (stopIntegrand Φ τ) t ω

open Classical in
/-- The local Itô integral `t ↦ ∫_0^t Φ_s · dW_s` for integrands with `∫_0^T |Φ|² < ∞` a.s.
(`0` when no process satisfies `IsLocalItoIntegral`). -/
def localItoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) : ℝ → Ω → ℝ :=
  if h : ∃ M, IsLocalItoIntegral P ℱ W Φ M then h.choose else 0

theorem stoppedProcess_eq_of_le {M : ℝ → Ω → ℝ} {σ : Ω → WithTop ℝ} {ω : Ω} {t : ℝ}
    (h : (t : WithTop ℝ) ≤ σ ω) : stoppedProcess M σ t ω = M t ω := by
  cases hσ : σ ω with
  | top => exact stoppedProcess_apply_top hσ t
  | coe c =>
    rw [stoppedProcess_apply_coe hσ]
    rw [hσ] at h
    rw [min_eq_left (by exact_mod_cast h)]

theorem IsLocalItoIntegral.ae_eq_forall [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2 P ℱ Φ) {M M' : ℝ → Ω → ℝ} (hM : IsLocalItoIntegral P ℱ W Φ M)
    (hM' : IsLocalItoIntegral P ℱ W Φ M') : ∀ᵐ ω ∂P, ∀ t, M t ω = M' t ω := by
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t, stoppedProcess M (locTime Φ n) t ω =
      stoppedProcess M' (locTime Φ n) t ω := fun n => by
    have hτ := isStoppingTime_locTime hW.complete hΦ n
    have hL2 := isProgressiveL2_stopIntegrand_locTime hW.complete hΦ n
    filter_upwards [hM.stopped _ hτ hL2, hM'.stopped _ hτ hL2] with ω h1 h2 t
    rw [h1 t, h2 t]
  filter_upwards [ae_all_iff.2 hn, locTime_exhaust hΦ] with ω h1 h2 t
  obtain ⟨n, hn⟩ := h2 t
  have := h1 n t
  rwa [stoppedProcess_eq_of_le hn, stoppedProcess_eq_of_le hn] at this

section LocC

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}
  {Φ Φ' : ℝ → Ω → ι → ℝ}

theorem stopIntegrand_stopIntegrand_of_le (Φ : ℝ → Ω → ι → ℝ) {σ τ : Ω → WithTop ℝ}
    (h : ∀ ω, σ ω ≤ τ ω) : stopIntegrand (stopIntegrand Φ τ) σ = stopIntegrand Φ σ := by
  funext s ω
  by_cases h1 : (s : WithTop ℝ) ≤ σ ω
  · have h2 : (s : WithTop ℝ) ≤ τ ω := h1.trans (h ω)
    simp [stopIntegrand, Set.indicator, h1, h2]
  · simp [stopIntegrand, Set.indicator, h1]

theorem locTime_consistent (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveLocL2 P ℱ Φ)
    (n : ℕ) : ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ n)) t ω =
      stoppedProcess (itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ (n + 1)))) (locTime Φ n) t ω := by
  have h := itoIntegral_stopIntegrand hW (isProgressiveL2_stopIntegrand_locTime hW.complete hΦ (n + 1))
    (isStoppingTime_locTime hW.complete hΦ n)
  rw [stopIntegrand_stopIntegrand_of_le Φ (fun ω => locTime_mono Φ (Nat.le_succ n) ω)] at h
  exact h

/-- The "good" event for gluing. -/
def LocGood (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ) (Φ : ℝ → Ω → ι → ℝ)
    (ω : Ω) : Prop :=
  (∀ n : ℕ, ∀ t, itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ n)) t ω =
      stoppedProcess (itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ (n + 1)))) (locTime Φ n) t ω) ∧
    ∀ T : ℝ, ∃ n : ℕ, (T : WithTop ℝ) ≤ locTime Φ n ω

theorem ae_locGood (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveLocL2 P ℱ Φ) :
    ∀ᵐ ω ∂P, LocGood P ℱ W Φ ω := by
  filter_upwards [ae_all_iff.2 (locTime_consistent hW hΦ), locTime_exhaust hΦ] with ω h1 h2
  exact ⟨h1, h2⟩

theorem LocGood.const {ω : Ω} (h : LocGood P ℱ W Φ ω) {k k' : ℕ} (hkk : k ≤ k') {u : ℝ}
    (hu : (u : WithTop ℝ) ≤ locTime Φ k ω) :
    itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ k')) u ω =
      itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ k)) u ω := by
  induction k', hkk using Nat.le_induction with
  | base => rfl
  | succ k' hk ih =>
    have hle : (u : WithTop ℝ) ≤ locTime Φ k' ω := hu.trans (locTime_mono Φ hk ω)
    have := h.1 k' u
    rw [stoppedProcess_eq_of_le hle] at this
    rw [← this, ih]

open Classical in
/-- The glued local integral. -/
def gluedLocal (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ) (Φ : ℝ → Ω → ι → ℝ)
    (G : Set Ω) : ℝ → Ω → ℝ := fun t ω =>
  if ω ∈ G then
    (if h : ∃ n : ℕ, (t : WithTop ℝ) ≤ locTime Φ n ω then
      itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ (Nat.find h))) t ω else 0)
  else 0

theorem gluedLocal_eq {G : Set Ω} (hG : ∀ ω ∈ G, LocGood P ℱ W Φ ω) {ω : Ω} (hω : ω ∈ G) {u : ℝ}
    {n : ℕ} (hu : (u : WithTop ℝ) ≤ locTime Φ n ω) :
    gluedLocal P ℱ W Φ G u ω = itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ n)) u ω := by
  classical
  have hex : ∃ n : ℕ, (u : WithTop ℝ) ≤ locTime Φ n ω := ⟨n, hu⟩
  simp only [gluedLocal, hω, if_true, dif_pos hex]
  exact ((hG ω hω).const (Nat.find_min' hex hu) (Nat.find_spec hex)).symm

theorem exists_locGood_set (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveLocL2 P ℱ Φ) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, LocGood P ℱ W Φ ω := by
  have hae := ae_locGood hW hΦ
  refine ⟨(toMeasurable P {ω | ¬ LocGood P ℱ W Φ ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · intro ω hω
    by_contra h
    exact hω (subset_toMeasurable _ _ h)

theorem stopIntegrand_comm (Φ : ℝ → Ω → ι → ℝ) (σ τ : Ω → WithTop ℝ) :
    stopIntegrand (stopIntegrand Φ σ) τ = stopIntegrand (stopIntegrand Φ τ) σ := by
  funext s ω
  by_cases h1 : (s : WithTop ℝ) ≤ σ ω <;> by_cases h2 : (s : WithTop ℝ) ≤ τ ω <;>
    simp [stopIntegrand, Set.indicator, h1, h2]

end LocC

theorem exists_isLocalItoIntegral [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2 P ℱ Φ) : ∃ M, IsLocalItoIntegral P ℱ W Φ M := by
  classical
  obtain ⟨G, hGm, hG0, hG⟩ := exists_locGood_set hW hΦ
  refine ⟨gluedLocal P ℱ W Φ G, ?_, ?_, ?_, ?_⟩
  · -- continuity
    intro ω
    by_cases hω : ω ∈ G
    · rw [continuous_iff_continuousAt]
      intro t0
      obtain ⟨n, hn⟩ := (hG ω hω).2 (t0 + 1)
      refine ((continuous_itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ n)) ω).continuousAt).congr ?_
      filter_upwards [Iio_mem_nhds (show t0 < t0 + 1 by linarith)] with u hu
      refine (gluedLocal_eq hG hω ?_).symm
      exact (by exact_mod_cast hu.le : (u : WithTop ℝ) ≤ ((t0 + 1 : ℝ) : WithTop ℝ)).trans hn
    · have : (fun t => gluedLocal P ℱ W Φ G t ω) = fun _ => 0 := by
        funext t; simp [gluedLocal, hω]
      rw [this]; exact continuous_const
  · -- adaptedness
    intro u
    have hGu : MeasurableSet[ℱ u] G := by
      have := hW.complete u Gᶜ hGm.compl hG0
      simpa using this.compl
    have hf : ∀ k : ℕ, Measurable[ℱ u] (G.indicator
        (itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ k)) u)) := fun k =>
      (adapted_itoIntegral P ℱ W _ u).indicator hGu
    refine @measurable_of_tendsto_metrizable Ω ℝ (ℱ u) _ _ _ _ _ _ hf ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ G
    · obtain ⟨n, hn⟩ := (hG ω hω).2 u
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with k hk
      rw [Set.indicator_of_mem hω]
      have hk' : (u : WithTop ℝ) ≤ locTime Φ k ω := hn.trans (locTime_mono Φ hk ω)
      rw [gluedLocal_eq hG hω hk']
    · simp [gluedLocal, hω]
  · -- zero
    intro u hu ω
    by_cases hω : ω ∈ G
    · obtain ⟨n, hn⟩ := (hG ω hω).2 0
      have hu' : (u : WithTop ℝ) ≤ locTime Φ n ω := by
        refine le_trans ?_ hn
        exact_mod_cast hu
      rw [gluedLocal_eq hG hω hu']
      exact itoIntegral_of_nonpos P ℱ W _ hu ω
    · simp [gluedLocal, hω]
  · -- stopped
    intro σ hσ hL2
    have hτ := isStoppingTime_locTime hW.complete hΦ
    have hΦn := isProgressiveL2_stopIntegrand_locTime hW.complete hΦ
    have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t, stoppedProcess (itoIntegral P ℱ W (stopIntegrand Φ σ))
        (locTime Φ n) t ω = stoppedProcess (itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ n))) σ t ω :=
      fun n => by
      have h1 := itoIntegral_stopIntegrand hW hL2 (hτ n)
      have h2 := itoIntegral_stopIntegrand hW (hΦn n) hσ
      rw [stopIntegrand_comm] at h1
      filter_upwards [h1, h2] with ω h1 h2 t
      rw [← h1 t, ← h2 t]
    filter_upwards [ae_all_iff.2 hn, (ae_iff.2 hG0 : ∀ᵐ ω ∂P, ω ∈ G)] with ω h1 hω t
    obtain ⟨n, hn⟩ := (hG ω hω).2 t
    have := h1 n t
    rw [stoppedProcess_eq_of_le hn] at this
    rw [this]
    cases hs : σ ω with
    | top =>
      rw [stoppedProcess_apply_top hs, stoppedProcess_apply_top hs]
      exact gluedLocal_eq hG hω hn
    | coe c =>
      rw [stoppedProcess_apply_coe hs, stoppedProcess_apply_coe hs]
      refine gluedLocal_eq hG hω ?_
      exact (by exact_mod_cast min_le_left t c : ((min t c : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ)).trans hn

theorem isLocalItoIntegral_localItoIntegral [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveLocL2 P ℱ Φ) :
    IsLocalItoIntegral P ℱ W Φ (localItoIntegral P ℱ W Φ) := by
  unfold localItoIntegral
  split_ifs with h
  · exact h.choose_spec
  · exact absurd (exists_isLocalItoIntegral hW hΦ) h

theorem continuous_localItoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) (ω : Ω) : Continuous fun t => localItoIntegral P ℱ W Φ t ω := by
  unfold localItoIntegral
  split_ifs with h
  · exact h.choose_spec.cont ω
  · exact continuous_const

theorem adapted_localItoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) : Adapted ℱ (localItoIntegral P ℱ W Φ) := by
  unfold localItoIntegral
  split_ifs with h
  · exact h.choose_spec.adapted
  · exact fun t => measurable_const

theorem localItoIntegral_of_nonpos (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → ℝ) {t : ℝ} (ht : t ≤ 0) (ω : Ω) : localItoIntegral P ℱ W Φ t ω = 0 := by
  unfold localItoIntegral
  split_ifs with h
  · exact h.choose_spec.zero t ht ω
  · rfl

theorem isLocalItoIntegral_itoIntegral [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) : IsLocalItoIntegral P ℱ W Φ (itoIntegral P ℱ W Φ) where
  cont := continuous_itoIntegral P ℱ W Φ
  adapted := adapted_itoIntegral P ℱ W Φ
  zero := fun t ht ω => itoIntegral_of_nonpos P ℱ W Φ ht ω
  stopped := fun τ hτ _ => by
    filter_upwards [itoIntegral_stopIntegrand hW hΦ hτ] with ω hω t
    exact (hω t).symm

/-- On the `L²` class the local integral is the Itô integral. -/
theorem localItoIntegral_eq_itoIntegral [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) :
    ∀ᵐ ω ∂P, ∀ t, localItoIntegral P ℱ W Φ t ω = itoIntegral P ℱ W Φ t ω := by
  have hex : ∃ M, IsLocalItoIntegral P ℱ W Φ M := ⟨_, isLocalItoIntegral_itoIntegral hW hΦ⟩
  have hspec : IsLocalItoIntegral P ℱ W Φ (localItoIntegral P ℱ W Φ) := by
    unfold localItoIntegral
    rw [dif_pos hex]
    exact hex.choose_spec
  exact IsLocalItoIntegral.ae_eq_forall hW hΦ.locL2 hspec (isLocalItoIntegral_itoIntegral hW hΦ)

/-- A continuous local martingale: continuous adapted, and there are stopping times `τ_n`
exhausting time a.s. such that every `M_{· ∧ τ_n}` is a martingale. -/
structure IsContLocalMartingale (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (M : ℝ → Ω → ℝ) :
    Prop where
  cont : ∀ ω, Continuous fun t => M t ω
  adapted : Adapted ℱ M
  localizing : ∃ τ : ℕ → Ω → WithTop ℝ, (∀ n, IsStoppingTime ℱ (τ n)) ∧
    (∀ᵐ ω ∂P, ∀ T : ℝ, ∃ n, (T : WithTop ℝ) ≤ τ n ω) ∧
    ∀ n, Martingale (stoppedProcess M (τ n)) ℱ P

theorem isContLocalMartingale_localItoIntegral [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveLocL2 P ℱ Φ) :
    IsContLocalMartingale P ℱ (localItoIntegral P ℱ W Φ) := by
  have hL := isLocalItoIntegral_localItoIntegral hW hΦ
  refine ⟨hL.cont, hL.adapted, locTime Φ, isStoppingTime_locTime hW.complete hΦ,
    locTime_exhaust hΦ, fun n => ?_⟩
  have hτ := isStoppingTime_locTime hW.complete hΦ n
  have hL2 := isProgressiveL2_stopIntegrand_locTime hW.complete hΦ n
  have hMart := martingale_itoIntegral hW hL2
  have hae := hL.stopped _ hτ hL2
  have hsa : StronglyAdapted ℱ (stoppedProcess (localItoIntegral P ℱ W Φ) (locTime Φ n)) :=
    hL.adapted.stronglyAdapted.stoppedProcess hL.cont hτ
  refine ⟨hsa, fun i j hij => ?_⟩
  have h1 : ∀ t, stoppedProcess (localItoIntegral P ℱ W Φ) (locTime Φ n) t =ᵐ[P]
      itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ n)) t := fun t => by
    filter_upwards [hae] with ω hω using hω t
  calc P[stoppedProcess (localItoIntegral P ℱ W Φ) (locTime Φ n) j | ℱ i]
      =ᵐ[P] P[itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ n)) j | ℱ i] := condExp_congr_ae (h1 j)
    _ =ᵐ[P] itoIntegral P ℱ W (stopIntegrand Φ (locTime Φ n)) i := hMart.2 i j hij
    _ =ᵐ[P] stoppedProcess (localItoIntegral P ℱ W Φ) (locTime Φ n) i := (h1 i).symm

theorem continuous_stoppedProcess_of {M : ℝ → Ω → ℝ} {ω : Ω} (h : Continuous fun t => M t ω)
    (τ : Ω → WithTop ℝ) : Continuous fun t => stoppedProcess M τ t ω := by
  cases hτ : τ ω with
  | top =>
    have : (fun t => stoppedProcess M τ t ω) = fun t => M t ω := funext fun t => stoppedProcess_apply_top hτ t
    rw [this]; exact h
  | coe c =>
    have : (fun t => stoppedProcess M τ t ω) = fun t => M (min t c) ω :=
      funext fun t => stoppedProcess_apply_coe hτ t
    rw [this]; exact h.comp (continuous_id.min continuous_const)

theorem IsProgressiveLocL2.add (h : IsProgressiveLocL2 P ℱ Φ) (h' : IsProgressiveLocL2 P ℱ Φ') :
    IsProgressiveLocL2 P ℱ (fun s ω => Φ s ω + Φ' s ω) := by
  refine ⟨isProgressive_add h.prog h'.prog, fun T => ?_⟩
  filter_upwards [h.sq T, h'.sq T] with ω h1 h2
  have hm1 : Measurable fun s : ℝ => ∑ k, ‖Φ (min s T) ω k‖ₑ ^ 2 :=
    by have := (measurable_sqSum_clamp h.prog T).comp (measurable_prodMk_right (y := ω)); exact this
  have hm2 : Measurable fun s : ℝ => ∑ k, ‖Φ' (min s T) ω k‖ₑ ^ 2 :=
    by have := (measurable_sqSum_clamp h'.prog T).comp (measurable_prodMk_right (y := ω)); exact this
  rw [← lintegral_sqSum_clamp Φ T ω] at h1
  rw [← lintegral_sqSum_clamp Φ' T ω] at h2
  have step1 : ∫⁻ s in Set.Icc 0 T, ∑ k, ‖(Φ s ω + Φ' s ω) k‖ₑ ^ 2
      ≤ ∫⁻ s in Set.Icc 0 T, (2 * ∑ k, ‖Φ (min s T) ω k‖ₑ ^ 2 +
          2 * ∑ k, ‖Φ' (min s T) ω k‖ₑ ^ 2) := by
    refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
    rw [min_eq_left hs.2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => enorm_add_sq_le _ _
  refine lt_of_le_of_lt step1 ?_
  rw [lintegral_add_left (hm1.const_mul 2), lintegral_const_mul _ hm1,
    lintegral_const_mul _ hm2]
  finiteness

theorem IsProgressiveLocL2.smul (h : IsProgressiveLocL2 P ℱ Φ) (c : ℝ) :
    IsProgressiveLocL2 P ℱ (fun s ω => c • Φ s ω) := by
  refine ⟨isProgressive_smul h.prog c, fun T => ?_⟩
  filter_upwards [h.sq T] with ω h1
  have e : ∀ s, ∑ k, ‖(c • Φ s ω) k‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ∑ k, ‖Φ s ω k‖ₑ ^ 2 := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1

theorem ae_eq_forall_of_stopped {M M' : ℝ → Ω → ℝ} {ρ : ℕ → Ω → WithTop ℝ}
    (hρ : ∀ᵐ ω ∂P, ∀ T : ℝ, ∃ n, (T : WithTop ℝ) ≤ ρ n ω)
    (h : ∀ n, ∀ᵐ ω ∂P, ∀ t, stoppedProcess M (ρ n) t ω = stoppedProcess M' (ρ n) t ω) :
    ∀ᵐ ω ∂P, ∀ t, M t ω = M' t ω := by
  filter_upwards [ae_all_iff.2 h, hρ] with ω h1 h2 t
  obtain ⟨n, hn⟩ := h2 t
  have := h1 n t
  rwa [stoppedProcess_eq_of_le hn, stoppedProcess_eq_of_le hn] at this

theorem isProgressiveL2_stopIntegrand_of_le [IsProbabilityMeasure P] (hℱ : IsCompleteFiltration P ℱ)
    (hΦ : IsProgressiveLocL2 P ℱ Φ) {ρ : Ω → WithTop ℝ} (hρ : IsStoppingTime ℱ ρ) (n : ℕ)
    (hle : ∀ ω, ρ ω ≤ locTime Φ n ω) : IsProgressiveL2 P ℱ (stopIntegrand Φ ρ) := by
  rw [← stopIntegrand_stopIntegrand_of_le Φ hle]
  exact (isProgressiveL2_stopIntegrand_locTime hℱ hΦ n).stopIntegrand hρ

theorem locTime_min_exhaust (hΦ : IsProgressiveLocL2 P ℱ Φ) (hΦ' : IsProgressiveLocL2 P ℱ Φ') :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∃ n : ℕ, (T : WithTop ℝ) ≤ min (locTime Φ n ω) (locTime Φ' n ω) := by
  filter_upwards [locTime_exhaust hΦ, locTime_exhaust hΦ'] with ω a b T
  obtain ⟨n, hn⟩ := a T
  obtain ⟨m, hm⟩ := b T
  exact ⟨max n m, le_min (hn.trans (locTime_mono Φ (le_max_left n m) ω))
    (hm.trans (locTime_mono Φ' (le_max_right n m) ω))⟩

/-- Stopping the local integral: `∫ 1_{s ≤ τ} Φ dW = (∫ Φ dW)_{· ∧ τ}` for every stopping time. -/
theorem localItoIntegral_stopIntegrand [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2 P ℱ Φ) {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ) :
    ∀ᵐ ω ∂P, ∀ t, localItoIntegral P ℱ W (stopIntegrand Φ τ) t ω =
      stoppedProcess (localItoIntegral P ℱ W Φ) τ t ω := by
  have hΦτ : IsProgressiveLocL2 P ℱ (stopIntegrand Φ τ) := hΦ.stopIntegrand hτ
  have hL := isLocalItoIntegral_localItoIntegral hW hΦ
  have hM' : IsLocalItoIntegral P ℱ W (stopIntegrand Φ τ)
      (stoppedProcess (localItoIntegral P ℱ W Φ) τ) := by
    refine ⟨fun ω => continuous_stoppedProcess_of (hL.cont ω) τ, ?_, ?_, ?_⟩
    · intro t
      exact (hL.adapted.stronglyAdapted.stoppedProcess hL.cont hτ t).measurable
    · intro t ht ω
      cases h : τ ω with
      | top => rw [stoppedProcess_apply_top h]; exact hL.zero t ht ω
      | coe c => rw [stoppedProcess_apply_coe h]; exact hL.zero _ ((min_le_left _ _).trans ht) ω
    · intro σ hσ hL2
      have e : stopIntegrand (stopIntegrand Φ τ) σ = stopIntegrand Φ (fun ω => min (σ ω) (τ ω)) := by
        funext s ω
        by_cases h1 : (s : WithTop ℝ) ≤ σ ω <;> by_cases h2 : (s : WithTop ℝ) ≤ τ ω <;>
          simp [stopIntegrand, Set.indicator, h1, h2]
      rw [e] at hL2 ⊢
      have e2 : stoppedProcess (stoppedProcess (localItoIntegral P ℱ W Φ) τ) σ =
          stoppedProcess (localItoIntegral P ℱ W Φ) (fun ω => min (σ ω) (τ ω)) :=
        stoppedProcess_stoppedProcess'
      rw [e2]
      exact hL.stopped _ (hσ.min hτ) hL2
  exact IsLocalItoIntegral.ae_eq_forall hW hΦτ (isLocalItoIntegral_localItoIntegral hW hΦτ) hM'

theorem localItoIntegral_add [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2 P ℱ Φ) (hΦ' : IsProgressiveLocL2 P ℱ Φ') :
    ∀ᵐ ω ∂P, ∀ t, localItoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) t ω =
      localItoIntegral P ℱ W Φ t ω + localItoIntegral P ℱ W Φ' t ω := by
  have hΨ := hΦ.add hΦ'
  have hLΨ := isLocalItoIntegral_localItoIntegral hW hΨ
  have hLΦ := isLocalItoIntegral_localItoIntegral hW hΦ
  have hLΦ' := isLocalItoIntegral_localItoIntegral hW hΦ'
  refine ae_eq_forall_of_stopped (ρ := fun n ω => min (locTime Φ n ω) (locTime Φ' n ω))
    (M' := fun t ω => localItoIntegral P ℱ W Φ t ω + localItoIntegral P ℱ W Φ' t ω)
    (locTime_min_exhaust hΦ hΦ') fun n => ?_
  have hρ := (isStoppingTime_locTime hW.complete hΦ n).min (isStoppingTime_locTime hW.complete hΦ' n)
  have h1 := isProgressiveL2_stopIntegrand_of_le hW.complete hΦ hρ n (fun ω => min_le_left _ _)
  have h2 := isProgressiveL2_stopIntegrand_of_le hW.complete hΦ' hρ n (fun ω => min_le_right _ _)
  have e : stopIntegrand (fun s ω => Φ s ω + Φ' s ω) (fun ω => min (locTime Φ n ω) (locTime Φ' n ω)) =
      fun s ω => stopIntegrand Φ (fun ω => min (locTime Φ n ω) (locTime Φ' n ω)) s ω +
        stopIntegrand Φ' (fun ω => min (locTime Φ n ω) (locTime Φ' n ω)) s ω := by
    funext s ω
    simp only [stopIntegrand, Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> simp
  have h3 : IsProgressiveL2 P ℱ (stopIntegrand (fun s ω => Φ s ω + Φ' s ω)
      (fun ω => min (locTime Φ n ω) (locTime Φ' n ω))) := by
    rw [e]; exact h1.add h2
  filter_upwards [hLΨ.stopped _ hρ h3, hLΦ.stopped _ hρ h1, hLΦ'.stopped _ hρ h2,
    itoIntegral_add hW h1 h2] with ω a b c d t
  rw [a t, e, d t, ← b t, ← c t]
  rfl

theorem localItoIntegral_smul [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2 P ℱ Φ) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ t, localItoIntegral P ℱ W (fun s ω => c • Φ s ω) t ω =
      c * localItoIntegral P ℱ W Φ t ω := by
  have hΨ := hΦ.smul c
  have hLΨ := isLocalItoIntegral_localItoIntegral hW hΨ
  have hLΦ := isLocalItoIntegral_localItoIntegral hW hΦ
  refine ae_eq_forall_of_stopped (ρ := fun n => locTime Φ n)
    (M' := fun t ω => c * localItoIntegral P ℱ W Φ t ω) (locTime_exhaust hΦ) fun n => ?_
  have hρ := isStoppingTime_locTime hW.complete hΦ n
  have h1 := isProgressiveL2_stopIntegrand_locTime hW.complete hΦ n
  have e : stopIntegrand (fun s ω => c • Φ s ω) (locTime Φ n) =
      fun s ω => c • stopIntegrand Φ (locTime Φ n) s ω := by
    funext s ω
    by_cases h : (s : WithTop ℝ) ≤ locTime Φ n ω <;> simp [stopIntegrand, Set.indicator, h]
  have h3 : IsProgressiveL2 P ℱ (stopIntegrand (fun s ω => c • Φ s ω) (locTime Φ n)) := by
    rw [e]; exact h1.smul c
  filter_upwards [hLΨ.stopped _ hρ h3, hLΦ.stopped _ hρ h1,
    itoIntegral_smul hW h1 c] with ω a b d t
  rw [a t, e, d t, ← b t]
  rfl

/-- Integrands agreeing `ds`-a.e. on `[0, T]` for a.e. `ω` have indistinguishable local
integrals. -/
theorem localItoIntegral_congr [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2 P ℱ Φ) (hΦ' : IsProgressiveLocL2 P ℱ Φ')
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Ici (0 : ℝ))), Φ s ω = Φ' s ω) :
    ∀ᵐ ω ∂P, ∀ t, localItoIntegral P ℱ W Φ t ω = localItoIntegral P ℱ W Φ' t ω := by
  have hLΦ := isLocalItoIntegral_localItoIntegral hW hΦ
  have hLΦ' := isLocalItoIntegral_localItoIntegral hW hΦ'
  refine ae_eq_forall_of_stopped (ρ := fun n ω => min (locTime Φ n ω) (locTime Φ' n ω))
    (locTime_min_exhaust hΦ hΦ') fun n => ?_
  have hρ := (isStoppingTime_locTime hW.complete hΦ n).min (isStoppingTime_locTime hW.complete hΦ' n)
  have h1 := isProgressiveL2_stopIntegrand_of_le hW.complete hΦ hρ n (fun ω => min_le_left _ _)
  have h2 := isProgressiveL2_stopIntegrand_of_le hW.complete hΦ' hρ n (fun ω => min_le_right _ _)
  have h0 : ∀ T, sqIntegralOn P (fun s ω => stopIntegrand Φ (fun ω => min (locTime Φ n ω) (locTime Φ' n ω)) s ω -
      stopIntegrand Φ' (fun ω => min (locTime Φ n ω) (locTime Φ' n ω)) s ω) T = 0 := by
    intro T
    unfold sqIntegralOn
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [h] with ω hω
    have hω' : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Φ s ω = Φ' s ω :=
      ae_restrict_of_ae_restrict_of_subset Set.Icc_subset_Ici_self hω
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hω'] with s hs
    simp only [stopIntegrand, Set.indicator, Set.mem_ofPred_eq, Pi.sub_apply]
    split_ifs <;> simp [hs]
  have hc := itoIntegral_congr hW h1 h2 h0
  filter_upwards [hLΦ.stopped _ hρ h1, hLΦ'.stopped _ hρ h2, hc] with ω a b c t
  rw [a t, b t, c t]

end Loc

end HRS
