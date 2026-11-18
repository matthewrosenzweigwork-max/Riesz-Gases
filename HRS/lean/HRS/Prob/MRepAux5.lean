import HRS.Prob.MRepAux4

/-!
# MREP, part 5: the abstract representation theorem

On a complete filtered probability space carrying a regularised continuous `L²` Hilbert martingale `M̃` with covariation
density `Ct`, its progressive square root `S`, and an independent cylindrical Brownian motion `W`, we construct a
cylindrical Brownian motion `B` with `M̃ = ∫ S dB` (`exists_representation`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section DomConv

variable {α : Type*} {mα : MeasurableSpace α} {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- `L²` convergence by dominated convergence. -/
lemma tendsto_eLpNorm_of_dominated {μ : Measure α} {f : ℕ → α → E} {g : α → E} {d : α → ℝ}
    (hf : ∀ m, Measurable (f m)) (hg : Measurable g) (hd : Measurable d)
    (hdL2 : eLpNorm d 2 μ ≠ ∞)
    (hb : ∀ m, ∀ᵐ x ∂μ, ‖f m x - g x‖ ≤ d x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun m => f m x) atTop (𝓝 (g x))) :
    Tendsto (fun m => eLpNorm (fun x => f m x - g x) 2 μ) atTop (𝓝 0) := by
  set D : α → ℝ≥0∞ := fun x => ‖d x‖ₑ ^ 2 with hD
  have hDfin : ∫⁻ x, D x ∂μ ≠ ∞ := by
    rw [hD]
    simp only []
    rw [HRS.lintegral_enorm_sq_eq_eLpNorm_sq hd.aestronglyMeasurable]
    exact (ENNReal.pow_lt_top hdL2.lt_top).ne
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := μ) (f := fun _ => (0 : ℝ≥0∞)) D
    (fun m => ((hf m).sub hg).enorm.pow_const 2)
    (fun m => by
      filter_upwards [hb m] with x hx
      simp only [hD]
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      exact pow_le_pow_left₀ (norm_nonneg _) (hx.trans (le_abs_self _ |>.trans_eq
        (Real.norm_eq_abs _).symm)) 2) hDfin
    (by
      filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun m => ‖f m x - g x‖) atTop (𝓝 0) := by
        have := (hx.sub_const (g x))
        simpa using this.norm
      have h3 : Tendsto (fun m => ENNReal.ofReal (‖f m x - g x‖ ^ 2)) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_ofReal (h1.pow 2))
        simpa using this
      refine h3.congr (fun m => ?_)
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
      rfl)
  simp only [lintegral_zero] at hdct
  refine tendsto_of_tendsto_sq (hdct.congr (fun m => ?_))
  exact HRS.lintegral_enorm_sq_eq_eLpNorm_sq ((hf m).sub hg).aestronglyMeasurable

end DomConv

section AR
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

/-- The data of the abstract representation theorem. -/
structure ARData (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (e : HilbertBasis ι ℝ H) (T : ℝ)
    (Mt : ℝ → Ω → H) (Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ) (S : ℝ → Ω → H →L[ℝ] H)
    (W : ℝ≥0 → Ω → ι → ℝ) : Prop where
  complete : IsCompleteFiltration P ℱ
  cont : ∀ ω, Continuous fun t => Mt t ω
  adapted : ∀ t, Measurable[ℱ t] (Mt t)
  zero : ∀ t ≤ 0, ∀ ω, Mt t ω = 0
  sq : ∀ t x, MemLp (fun ω => inner ℝ (Mt t ω) x) 2 P
  mart : ∀ x, Martingale (fun t ω => inner ℝ (Mt t ω) x) ℱ P
  cov : ∀ x y, Martingale (fun t ω => inner ℝ (Mt t ω) x * inner ℝ (Mt t ω) y -
    ∫ r in Set.Icc 0 t, (if r ≤ T then Ct r ω x y else 0)) ℱ P
  wiener : IsCylindricalBrownian P ℱ W
  cross : ∀ x j, Martingale (fun t ω => inner ℝ (Mt t ω) x * ofNNRealTime W t ω j) ℱ P
  trace : ∀ r ω, IsTraceClassCov (Ct r ω)
  sqrt : ∀ r ω, IsSqrtOfForm (S r ω) (Ct r ω)
  Cprog : ∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y)
  Sprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (S r ω x) y)
  Cint : ∀ᵐ ω ∂P, ∀ i j, IntegrableOn (fun r => Ct r ω (e i) (e j)) (Set.Icc 0 T)
  Ctr : ∫⁻ ω, (∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (∑' i, Ct r ω (e i) (e i))) ∂P ≠ ∞

/-- The noise: coordinates of `M̃` and the Brownian coordinates. -/
def Nz (e : HilbertBasis ι ℝ H) (Mt : ℝ → Ω → H) (W : ℝ≥0 → Ω → ι → ℝ) :
    ℝ → Ω → ι ⊕ ι → ℝ :=
  fun t ω a => Sum.elim (fun i => inner ℝ (Mt t ω) (e i)) (fun j => ofNNRealTime W t ω j) a

/-- The factorisation of the covariation densities through `K = ℓ²(H × H)`. -/
def vz (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) :
    ℝ → Ω → ι ⊕ ι → WithLp 2 (H × H) :=
  fun r ω a => Sum.elim (fun i => WithLp.toLp 2 ((if r ≤ T then S r ω (e i) else 0), (0 : H)))
    (fun j => WithLp.toLp 2 ((0 : H), e j)) a

lemma inner_vz_ll (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (r : ℝ) (ω : Ω)
    (i j : ι) : inner ℝ (vz e T S r ω (Sum.inl i)) (vz e T S r ω (Sum.inl j)) =
      if r ≤ T then inner ℝ (S r ω (e i)) (S r ω (e j)) else 0 := by
  by_cases h : r ≤ T <;> simp [vz, h, WithLp.prod_inner_apply]

lemma inner_vz_rr (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (r : ℝ) (ω : Ω)
    (i j : ι) : inner ℝ (vz e T S r ω (Sum.inr i)) (vz e T S r ω (Sum.inr j)) =
      if i = j then 1 else 0 := by
  simp only [vz, Sum.elim_inr, WithLp.prod_inner_apply, inner_zero_left, zero_add]
  exact orthonormal_iff_ite.1 e.orthonormal i j

lemma inner_vz_lr (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (r : ℝ) (ω : Ω)
    (i j : ι) : inner ℝ (vz e T S r ω (Sum.inl i)) (vz e T S r ω (Sum.inr j)) = 0 := by
  by_cases h : r ≤ T <;> simp [vz, h, WithLp.prod_inner_apply]

lemma inner_vz_rl (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (r : ℝ) (ω : Ω)
    (i j : ι) : inner ℝ (vz e T S r ω (Sum.inr j)) (vz e T S r ω (Sum.inl i)) = 0 := by
  rw [real_inner_comm]; exact inner_vz_lr e T S r ω i j

section NoiseK

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {T : ℝ} {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

lemma ARData.measurable_S_apply (hA : ARData P ℱ e T Mt Ct S W) (x : H) :
    Measurable fun p : ℝ × Ω => S p.1 p.2 x := by
  refine measurable_of_inner_basis e (fun j => ?_)
  have : (fun p : ℝ × Ω => inner ℝ (e j) (S p.1 p.2 x)) = fun p => inner ℝ (S p.1 p.2 x) (e j) := by
    funext p; exact real_inner_comm _ _
  rw [this]
  exact isProgressive_measurable_uncurry (hA.Sprog x (e j))

lemma ARData.measurable_vz (hA : ARData P ℱ e T Mt Ct S W) (a : ι ⊕ ι) :
    Measurable fun p : ℝ × Ω => vz e T S p.1 p.2 a := by
  rcases a with i | j
  · have h1 : Measurable fun p : ℝ × Ω => (if p.1 ≤ T then S p.1 p.2 (e i) else 0) :=
      Measurable.ite (measurableSet_le measurable_fst measurable_const)
        (hA.measurable_S_apply (e i)) measurable_const
    exact (WithLp.measurable_toLp 2 (H × H)).comp (h1.prodMk measurable_const)
  · exact measurable_const

theorem ARData.isNoiseK (hA : ARData P ℱ e T Mt Ct S W) :
    IsNoiseK P ℱ (Nz e Mt W) (vz e T S) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hA.measurable_vz⟩
  · intro a
    rcases a with i | j
    · exact hA.mart (e i)
    · exact hA.wiener.martingale_coord j
  · intro ω a
    rcases a with i | j
    · exact (hA.cont ω).inner continuous_const
    · exact (hA.wiener {j} |>.cont ω |> fun h => (continuous_apply (⟨j, by simp⟩ :
        ({j} : Finset ι))).comp h |> fun h' => h'.comp continuous_real_toNNReal)
  · intro t a
    rcases a with i | j
    · exact hA.sq t (e i)
    · exact (hA.wiener {j}).memLp_two_coord_real t ⟨j, by simp⟩
  · intro a b
    exact meas_inner (hA.measurable_vz a) (hA.measurable_vz b)
  · -- Qint
    filter_upwards [hA.Cint] with ω hω a b t
    rcases a with i | j <;> rcases b with i' | j'
    · have e1 : (fun r => inner ℝ (vz e T S r ω (Sum.inl i)) (vz e T S r ω (Sum.inl i'))) =
          (Set.Iic T).indicator (fun r => Ct r ω (e i) (e i')) := by
        funext r
        rw [inner_vz_ll, (hA.sqrt r ω).sq]
        by_cases h : r ≤ T <;> simp [h]
      rw [e1, IntegrableOn, integrable_indicator_iff measurableSet_Iic]
      have h2 : IntegrableOn (fun r => Ct r ω (e i) (e i')) (Set.Iic T ∩ Set.Icc 0 t) volume :=
        (hω i i').mono_set (fun r hr => ⟨hr.2.1, hr.1⟩)
      rwa [IntegrableOn, Measure.restrict_restrict measurableSet_Iic] 
    · simp only [inner_vz_lr, integrableOn_zero]
    · simp only [inner_vz_rl, integrableOn_zero]
    · simp only [inner_vz_rr]
      exact integrableOn_const (by simp)
  · -- cov
    intro a b
    rcases a with i | j <;> rcases b with i' | j'
    · have e1 : ∀ t ω, ∫ r in Set.Icc 0 t, inner ℝ (vz e T S r ω (Sum.inl i))
          (vz e T S r ω (Sum.inl i')) = ∫ r in Set.Icc 0 t, (if r ≤ T then Ct r ω (e i) (e i') else 0) :=
        fun t ω => setIntegral_congr_fun measurableSet_Icc fun r _ => by
          rw [inner_vz_ll, (hA.sqrt r ω).sq]
      have e2 : (fun t ω => Nz e Mt W t ω (Sum.inl i) * Nz e Mt W t ω (Sum.inl i') -
          ∫ r in Set.Icc 0 t, inner ℝ (vz e T S r ω (Sum.inl i)) (vz e T S r ω (Sum.inl i'))) =
          fun t ω => inner ℝ (Mt t ω) (e i) * inner ℝ (Mt t ω) (e i') -
          ∫ r in Set.Icc 0 t, (if r ≤ T then Ct r ω (e i) (e i') else 0) := by
        funext t ω
        simp only [Nz, Sum.elim_inl]
        rw [e1]
      rw [e2]
      exact hA.cov _ _
    · have e2 : (fun t ω => Nz e Mt W t ω (Sum.inl i) * Nz e Mt W t ω (Sum.inr j') -
          ∫ r in Set.Icc 0 t, inner ℝ (vz e T S r ω (Sum.inl i)) (vz e T S r ω (Sum.inr j'))) =
          fun t ω => inner ℝ (Mt t ω) (e i) * ofNNRealTime W t ω j' := by
        funext t ω
        simp only [Nz, Sum.elim_inl, Sum.elim_inr, inner_vz_lr, integral_zero, sub_zero]
      rw [e2]
      exact hA.cross _ _
    · have e2 : (fun t ω => Nz e Mt W t ω (Sum.inr j) * Nz e Mt W t ω (Sum.inl i') -
          ∫ r in Set.Icc 0 t, inner ℝ (vz e T S r ω (Sum.inr j)) (vz e T S r ω (Sum.inl i'))) =
          fun t ω => inner ℝ (Mt t ω) (e i') * ofNNRealTime W t ω j := by
        funext t ω
        simp only [Nz, Sum.elim_inl, Sum.elim_inr, inner_vz_rl, integral_zero, sub_zero]
        ring
      rw [e2]
      exact hA.cross _ _
    · have e2 : (fun t ω => Nz e Mt W t ω (Sum.inr j) * Nz e Mt W t ω (Sum.inr j') -
          ∫ r in Set.Icc 0 t, inner ℝ (vz e T S r ω (Sum.inr j)) (vz e T S r ω (Sum.inr j'))) =
          fun t ω => ofNNRealTime W t ω j * ofNNRealTime W t ω j' -
            if j = j' then max t 0 else 0 := by
        funext t ω
        simp only [Nz, Sum.elim_inr, inner_vz_rr]
        by_cases h : j = j'
        · simp [h, Real.volume_real_Icc]
        · simp [h]
      rw [e2]
      exact hA.wiener.martingale_mul_sub j j'

end NoiseK

end AR

end HRS.MRep
