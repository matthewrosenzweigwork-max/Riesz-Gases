import HRS.Prob.MRepAux5

/-!
# MREP, part 6: approximability of the integrands of the Brownian coordinates

`G^k_r = (Q_r e_k, (I - Q_r) e_k)` for `r ≤ T` and `(0, e_k)` after `T` is an `L²_loc` limit of elementary integrands.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Gk
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

lemma norm_toLp_le (a b : H) : ‖(WithLp.toLp 2 (a, b) : WithLp 2 (H × H))‖ ≤ ‖a‖ + ‖b‖ := by
  have h : ‖(WithLp.toLp 2 (a, b) : WithLp 2 (H × H))‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    simp [WithLp.prod_norm_sq_eq_of_L2]
  have h2 : (‖a‖ + ‖b‖) ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * ‖a‖ * ‖b‖ := by ring
  refine le_of_sq_le_sq (by nlinarith [norm_nonneg a, norm_nonneg b]) (by positivity)

lemma norm_resolvent_le {S : H →L[ℝ] H} (hS : HilbertCLTAux.IsPSDOp S) (n : ℕ) (x : H) :
    ‖resolvent S n x‖ ≤ 2 * ((n : ℝ) + 1) * ‖x‖ := by
  have h1 := resolvent_right hS n x
  have h2 : epsn n • resolvent S n x = x - S (resolvent S n x) := eq_sub_of_add_eq' h1
  have h3 : epsn n * ‖resolvent S n x‖ ≤ 2 * ‖x‖ := by
    have := congrArg norm h2
    rw [norm_smul, Real.norm_of_nonneg (epsn_pos n).le] at this
    rw [this]
    calc ‖x - S (resolvent S n x)‖ ≤ ‖x‖ + ‖S (resolvent S n x)‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + ‖x‖ := by gcongr; exact norm_S_resolvent_le hS n x
      _ = 2 * ‖x‖ := by ring
  have h4 : epsn n = ((n : ℝ) + 1)⁻¹ := rfl
  rw [h4] at h3
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc ‖resolvent S n x‖ = ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ * ‖resolvent S n x‖) := by
        field_simp
    _ ≤ ((n : ℝ) + 1) * (2 * ‖x‖) := by gcongr
    _ = 2 * ((n : ℝ) + 1) * ‖x‖ := by ring

lemma norm_sub_proj_le (e : HilbertBasis ι ℝ H) (g : H) (F : Finset ι) :
    ‖g - ∑ i ∈ F, inner ℝ (e i) g • e i‖ ≤ ‖g‖ := by
  set gF : H := ∑ i ∈ F, inner ℝ (e i) g • e i with hgF
  have horth : inner ℝ gF (g - gF) = 0 := by
    have h1 : ∀ i ∈ F, inner ℝ (e i) gF = inner ℝ (e i) g := by
      intro i hi
      rw [hgF, inner_sum]
      simp only [inner_smul_right, orthonormal_iff_ite.1 e.orthonormal i, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq F i]
      simp [hi]
    have : ∑ i ∈ F, inner ℝ (e i) g * inner ℝ (e i) (g - gF) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [inner_sub_right, h1 i hi, sub_self, mul_zero]
    have h2 : inner ℝ gF (g - gF) = ∑ i ∈ F, inner ℝ (e i) g * inner ℝ (e i) (g - gF) := by
      conv_lhs => rw [hgF]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left]
    rw [h2, this]
  have hsq : ‖g‖ ^ 2 = ‖gF‖ ^ 2 + ‖g - gF‖ ^ 2 := by
    have := norm_add_sq_real gF (g - gF)
    rw [horth] at this
    simpa using this
  nlinarith [norm_nonneg (g - gF), norm_nonneg gF, norm_nonneg g]

section Defs

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {T : ℝ} {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

/-- The limiting integrand of the `k`-th Brownian coordinate. -/
def Gk (e : HilbertBasis ι ℝ H) (T : ℝ) (Q : ℝ → Ω → H →L[ℝ] H) (k : ι) :
    ℝ → Ω → WithLp 2 (H × H) :=
  fun r ω => WithLp.toLp 2 ((if r ≤ T then Q r ω (e k) else 0),
    (if r ≤ T then e k - Q r ω (e k) else e k))

/-- The regularised integrand. -/
def Gn (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) :
    ℝ → Ω → WithLp 2 (H × H) :=
  fun r ω => WithLp.toLp 2 ((if r ≤ T then e k - epsn n • resolvent (S r ω) n (e k) else 0),
    (if r ≤ T then epsn n • resolvent (S r ω) n (e k) else e k))

/-- The second component of the regularised integrand. -/
def psin (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) :
    ℝ → Ω → H :=
  fun r ω => if r ≤ T then epsn n • resolvent (S r ω) n (e k) else e k

/-- The coefficients of the regularised integrand in the noise coordinates. -/
def Thn (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) :
    ℝ → Ω → ι ⊕ ι → ℝ :=
  fun r ω a => Sum.elim (fun i => inner ℝ (e i) (resolvent (S r ω) n (e k)))
    (fun j => inner ℝ (e j) (psin e T S n k r ω)) a

/-- The finite-coordinate truncation. -/
def GF (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) (F : Finset ι) :
    ℝ → Ω → WithLp 2 (H × H) :=
  fun r ω => ∑ a : ↥(F.disjSum F), Thn e T S n k r ω a.1 • vz e T S r ω a.1

lemma GF_eq (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) (F : Finset ι)
    (r : ℝ) (ω : Ω) :
    GF e T S n k F r ω = WithLp.toLp 2
      ((if r ≤ T then S r ω (∑ i ∈ F, inner ℝ (e i) (resolvent (S r ω) n (e k)) • e i) else 0),
        ∑ j ∈ F, inner ℝ (e j) (psin e T S n k r ω) • e j) := by
  unfold GF
  rw [Finset.sum_coe_sort (F.disjSum F) (fun a => Thn e T S n k r ω a • vz e T S r ω a),
    Finset.sum_disjSum]
  apply WithLp.ofLp_injective
  by_cases h : r ≤ T
  · simp [Thn, vz, h, Prod.ext_iff, map_sum, Prod.fst_sum, Prod.snd_sum]
  · simp [Thn, vz, h, Prod.ext_iff, map_sum, Prod.fst_sum, Prod.snd_sum]

end Defs

section StageF

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {T : ℝ} {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

/-- The trace function. -/
def trf (e : HilbertBasis ι ℝ H) (Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ) : ℝ × Ω → ℝ :=
  fun p => ∑' i, Ct p.1 p.2 (e i) (e i)

/-- The dominating function `1_{r ≤ T} √tr`. -/
def dS (e : HilbertBasis ι ℝ H) (T : ℝ) (Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ) : ℝ × Ω → ℝ :=
  fun p => if p.1 ≤ T then Real.sqrt (trf e Ct p) else 0

lemma ARData.norm_S_le (hA : ARData P ℱ e T Mt Ct S W) (r : ℝ) (ω : Ω) (x : H) :
    ‖S r ω x‖ ≤ Real.sqrt (trf e Ct (r, ω)) * ‖x‖ := by
  obtain ⟨Tr, hT, hb⟩ := (hA.trace r ω).hasSum_basis e
  have h1 : ‖S r ω x‖ ^ 2 ≤ Tr * ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, (hA.sqrt r ω).sq x x]
    exact hb x
  have h2 : trf e Ct (r, ω) = Tr := hT.tsum_eq
  have hTr0 : 0 ≤ Tr := hT.nonneg (fun i => (hA.trace r ω).nonneg _)
  rw [h2]
  calc ‖S r ω x‖ = Real.sqrt (‖S r ω x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (Tr * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt Tr * ‖x‖ := by rw [Real.sqrt_mul hTr0, Real.sqrt_sq (norm_nonneg _)]

lemma ARData.measurable_trf (hA : ARData P ℱ e T Mt Ct S W) : Measurable (trf e Ct) :=
  Measurable.tsum fun i => isProgressive_measurable_uncurry (hA.Cprog (e i) (e i))

lemma ARData.measurable_dS (hA : ARData P ℱ e T Mt Ct S W) : Measurable (dS e T Ct) := by
  unfold dS
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
    hA.measurable_trf.sqrt measurable_const

lemma ARData.eLpNorm_dS (hA : ARData P ℱ e T Mt Ct S W) (t : ℝ) :
    eLpNorm (dS e T Ct) 2 (tsm P t) ≠ ∞ := by
  have hm := hA.measurable_dS
  have h1 : eLpNorm (dS e T Ct) 2 (tsm P t) ^ 2 = ∫⁻ p, ‖dS e T Ct p‖ₑ ^ 2 ∂(tsm P t) :=
    (HRS.lintegral_enorm_sq_eq_eLpNorm_sq hm.aestronglyMeasurable).symm
  have h2 : ∀ p, ‖dS e T Ct p‖ₑ ^ 2 = (Set.Iic T).indicator (fun r : ℝ => (1 : ℝ≥0∞)) p.1 *
      ENNReal.ofReal (trf e Ct p) := by
    intro p
    have hnn : 0 ≤ trf e Ct p := tsum_nonneg fun i => (hA.trace p.1 p.2).nonneg _
    by_cases h : p.1 ≤ T
    · simp only [dS, h, if_true, Set.indicator_of_mem (Set.mem_Iic.2 h), one_mul]
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_of_nonneg
        (Real.sqrt_nonneg _), Real.sq_sqrt hnn]
    · simp [dS, h]
  have h3 : ∫⁻ p, ‖dS e T Ct p‖ₑ ^ 2 ∂(tsm P t) ≠ ∞ := by
    simp_rw [h2]
    unfold tsm
    have hmeas : Measurable fun p : ℝ × Ω => (Set.Iic T).indicator (fun r : ℝ => (1 : ℝ≥0∞)) p.1 *
        ENNReal.ofReal (trf e Ct p) :=
      ((measurable_const.indicator measurableSet_Iic).comp measurable_fst).mul
        (ENNReal.measurable_ofReal.comp hA.measurable_trf)
    rw [lintegral_prod_symm' _ hmeas]
    refine ne_top_of_le_ne_top hA.Ctr (lintegral_mono fun ω => ?_)
    calc ∫⁻ r in Set.Icc 0 t, (Set.Iic T).indicator (fun r : ℝ => (1 : ℝ≥0∞)) r *
          ENNReal.ofReal (trf e Ct (r, ω))
        = ∫⁻ r in Set.Icc 0 t, (Set.Iic T).indicator
            (fun r => ENNReal.ofReal (trf e Ct (r, ω))) r := by
          refine lintegral_congr fun r => ?_
          by_cases h : r ≤ T <;> simp [h]
      _ = ∫⁻ r in Set.Icc 0 t ∩ Set.Iic T, ENNReal.ofReal (trf e Ct (r, ω)) := by
          rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
            Set.inter_comm]
      _ ≤ ∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (∑' i, Ct r ω (e i) (e i)) := by
          refine lintegral_mono_set ?_
          intro r hr; exact ⟨hr.1.1, hr.2⟩
  intro htop
  rw [htop] at h1
  simp at h1
  exact h3 h1.symm

end StageF

section ProjLemmas

lemma tendsto_proj (e : HilbertBasis ι ℝ H) (g : H) {F : ℕ → Finset ι}
    (hF : Tendsto F atTop atTop) :
    Tendsto (fun m => ∑ i ∈ F m, inner ℝ (e i) g • e i) atTop (𝓝 g) := by
  have h := e.hasSum_repr g
  simp only [HilbertBasis.repr_apply_apply] at h
  have h' : Tendsto (fun s : Finset ι => ∑ i ∈ s, inner ℝ (e i) g • e i) atTop (𝓝 g) := h
  exact h'.comp hF

lemma norm_toLp_sub_le (a b c d : H) :
    ‖(WithLp.toLp 2 (a, b) : WithLp 2 (H × H)) - WithLp.toLp 2 (c, d)‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  have : (WithLp.toLp 2 (a, b) : WithLp 2 (H × H)) - WithLp.toLp 2 (c, d) =
      WithLp.toLp 2 (a - c, b - d) := by
    apply WithLp.ofLp_injective; simp
  rw [this]; exact norm_toLp_le _ _

end ProjLemmas

section ApproxGn

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {T : ℝ} {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

lemma ARData.psd (hA : ARData P ℱ e T Mt Ct S W) (r : ℝ) (ω : Ω) :
    HilbertCLTAux.IsPSDOp (S r ω) := ⟨(hA.sqrt r ω).symm, (hA.sqrt r ω).nonneg⟩

lemma ARData.measurable_resolvent_inner (hA : ARData P ℱ e T Mt Ct S W) (n : ℕ) (x y : H) :
    Measurable fun p : ℝ × Ω => inner ℝ (resolvent (S p.1 p.2) n x) y :=
  isProgressive_measurable_uncurry
    (isProgressive_resolvent e Ct hA.trace S hA.sqrt hA.Cprog hA.Sprog n x y)

lemma ARData.measurable_resolvent (hA : ARData P ℱ e T Mt Ct S W) (n : ℕ) (x : H) :
    Measurable fun p : ℝ × Ω => resolvent (S p.1 p.2) n x := by
  refine measurable_of_inner_basis e (fun j => ?_)
  have : (fun p : ℝ × Ω => inner ℝ (e j) (resolvent (S p.1 p.2) n x)) =
      fun p => inner ℝ (resolvent (S p.1 p.2) n x) (e j) := by
    funext p; exact real_inner_comm _ _
  rw [this]
  exact hA.measurable_resolvent_inner n x (e j)

lemma ARData.measurable_Gn (hA : ARData P ℱ e T Mt Ct S W) (n : ℕ) (k : ι) :
    Measurable fun p : ℝ × Ω => Gn e T S n k p.1 p.2 := by
  unfold Gn
  have h1 := (hA.measurable_resolvent n (e k)).const_smul (epsn n)
  have hc : MeasurableSet {p : ℝ × Ω | p.1 ≤ T} := measurableSet_le measurable_fst measurable_const
  refine (WithLp.measurable_toLp 2 (H × H)).comp (Measurable.prodMk ?_ ?_)
  · exact Measurable.ite hc (measurable_const.sub h1) measurable_const
  · exact Measurable.ite hc h1 measurable_const

lemma ARData.measurable_psin (hA : ARData P ℱ e T Mt Ct S W) (n : ℕ) (k : ι) :
    Measurable fun p : ℝ × Ω => psin e T S n k p.1 p.2 := by
  unfold psin
  have h1 := (hA.measurable_resolvent n (e k)).const_smul (epsn n)
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const) h1 measurable_const

lemma ARData.measurable_Thn (hA : ARData P ℱ e T Mt Ct S W) (n : ℕ) (k : ι) (a : ι ⊕ ι) :
    Measurable fun p : ℝ × Ω => Thn e T S n k p.1 p.2 a := by
  rcases a with i | j
  · simp only [Thn, Sum.elim_inl]
    have : (fun p : ℝ × Ω => inner ℝ (e i) (resolvent (S p.1 p.2) n (e k))) =
        fun p => inner ℝ (resolvent (S p.1 p.2) n (e k)) (e i) := by
      funext p; exact real_inner_comm _ _
    rw [this]
    exact hA.measurable_resolvent_inner n (e k) (e i)
  · simp only [Thn, Sum.elim_inr]
    exact meas_inner measurable_const (hA.measurable_psin n k)

lemma ARData.norm_psin_le (hA : ARData P ℱ e T Mt Ct S W) (n : ℕ) (k : ι) (r : ℝ) (ω : Ω) :
    ‖psin e T S n k r ω‖ ≤ 2 := by
  unfold psin
  by_cases h : r ≤ T
  · simp only [h, if_true]
    have h2 : epsn n • resolvent (S r ω) n (e k) = e k - S r ω (resolvent (S r ω) n (e k)) :=
      eq_sub_of_add_eq' (resolvent_right (hA.psd r ω) n (e k))
    rw [h2]
    calc ‖e k - S r ω (resolvent (S r ω) n (e k))‖ ≤ ‖e k‖ + ‖S r ω (resolvent (S r ω) n (e k))‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := by
          gcongr
          · exact (e.orthonormal.norm_eq_one k).le
          · calc _ ≤ ‖e k‖ := norm_S_resolvent_le (hA.psd r ω) n (e k)
              _ = 1 := e.orthonormal.norm_eq_one k
      _ = 2 := by norm_num
  · simp only [h, if_false]
    exact (e.orthonormal.norm_eq_one k).le.trans (by norm_num)

theorem ARData.approx_Gn (hA : ARData P ℱ e T Mt Ct S W) (n : ℕ) (k : ι) :
    Approx P ℱ (vz e T S) (Gn e T S n k) := by
  classical
  have hN := hA.isNoiseK
  obtain ⟨F, hF⟩ := Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset ι))
  refine Approx.of_limit (Gs := fun m => GF e T S n k (F m)) (fun m => ?_) (fun N => ?_)
  · -- each truncation is approximable
    have := approx_of_bounded (P := P) (ℱ := ℱ) hA.complete hN ((F m).disjSum (F m))
      (fun r ω (a : ↥((F m).disjSum (F m))) => Thn e T S n k r ω a.1) (C := 2 * ((n : ℝ) + 1) + 2)
      ?_ (by positivity) ?_
    · exact this
    · -- progressive
      intro i
      letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
      refine measurable_pi_iff.2 fun a => ?_
      rcases a with ⟨a, ha⟩
      rcases a with i' | j
      · simp only [Thn, Sum.elim_inl]
        have : (fun z : Set.Iic i × Ω => inner ℝ (e i') (resolvent (S z.1 z.2) n (e k))) =
            fun z => inner ℝ (resolvent (S z.1 z.2) n (e k)) (e i') := by
          funext z; exact real_inner_comm _ _
        rw [this]
        exact (isProgressive_resolvent e Ct hA.trace S hA.sqrt hA.Cprog hA.Sprog n (e k) (e i')) i
      · simp only [Thn, Sum.elim_inr, psin]
        have h1 : Measurable fun z : Set.Iic i × Ω =>
            inner ℝ (e j) (epsn n • resolvent (S z.1 z.2) n (e k)) := by
          have : (fun z : Set.Iic i × Ω => inner ℝ (e j) (epsn n • resolvent (S z.1 z.2) n (e k))) =
              fun z => epsn n * inner ℝ (resolvent (S z.1 z.2) n (e k)) (e j) := by
            funext z; rw [real_inner_smul_right, real_inner_comm]
          rw [this]
          exact (isProgressive_resolvent e Ct hA.trace S hA.sqrt hA.Cprog hA.Sprog n (e k) (e j) i).const_mul _
        have hc : MeasurableSet {z : Set.Iic i × Ω | (z.1 : ℝ) ≤ T} :=
          measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_const
        have : (fun z : Set.Iic i × Ω => inner ℝ (e j) (if (z.1 : ℝ) ≤ T then
            epsn n • resolvent (S z.1 z.2) n (e k) else e k)) =
            fun z => if (z.1 : ℝ) ≤ T then inner ℝ (e j) (epsn n • resolvent (S z.1 z.2) n (e k))
              else inner ℝ (e j) (e k) := by
          funext z; by_cases h : (z.1 : ℝ) ≤ T <;> simp [h]
        rw [this]
        exact Measurable.ite hc h1 measurable_const
    · -- bounded
      intro r ω a
      rcases a with ⟨a, ha⟩
      rcases a with i' | j
      · simp only [Thn, Sum.elim_inl]
        calc |inner ℝ (e i') (resolvent (S r ω) n (e k))| ≤ ‖e i'‖ * ‖resolvent (S r ω) n (e k)‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ 1 * (2 * ((n : ℝ) + 1) * ‖e k‖) := by
              gcongr
              · exact (e.orthonormal.norm_eq_one i').le
              · exact norm_resolvent_le (hA.psd r ω) n (e k)
          _ ≤ 2 * ((n : ℝ) + 1) + 2 := by
              rw [e.orthonormal.norm_eq_one k]; linarith
      · simp only [Thn, Sum.elim_inr]
        calc |inner ℝ (e j) (psin e T S n k r ω)| ≤ ‖e j‖ * ‖psin e T S n k r ω‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ 1 * 2 := by
              gcongr
              · exact (e.orthonormal.norm_eq_one j).le
              · exact hA.norm_psin_le n k r ω
          _ ≤ 2 * ((n : ℝ) + 1) + 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · -- convergence of the truncations
    set d : ℝ × Ω → ℝ := fun p => 2 * ((n : ℝ) + 1) * dS e T Ct p + 2 with hd
    have hdm : Measurable d := (measurable_const.mul hA.measurable_dS).add measurable_const
    have hdL2 : eLpNorm d 2 (tsm P N) ≠ ∞ := by
      have h1 : eLpNorm ((2 * ((n : ℝ) + 1)) • dS e T Ct) 2 (tsm P N) ≠ ∞ := by
        rw [eLpNorm_const_smul]
        exact ENNReal.mul_ne_top enorm_ne_top (hA.eLpNorm_dS N)
      have h2 : eLpNorm (fun _ : ℝ × Ω => (2 : ℝ)) 2 (tsm P N) ≠ ∞ :=
        (memLp_const (2 : ℝ)).eLpNorm_ne_top
      have h3 : d = ((2 * ((n : ℝ) + 1)) • dS e T Ct) + (fun _ => (2 : ℝ)) := by
        funext p; simp [hd]
      rw [h3]
      exact ne_of_lt (lt_of_le_of_lt (eLpNorm_add_le (by norm_num))
        (ENNReal.add_lt_top.2 ⟨h1.lt_top, h2.lt_top⟩))
    refine tendsto_eLpNorm_of_dominated (μ := tsm P N) (f := fun m p => GF e T S n k (F m) p.1 p.2)
      (g := fun p => Gn e T S n k p.1 p.2) (d := d) (fun m => ?_) (hA.measurable_Gn n k) hdm hdL2
      (fun m => Eventually.of_forall fun p => ?_) (Eventually.of_forall fun p => ?_)
    · unfold GF
      exact Finset.measurable_sum _ fun a _ => (hA.measurable_Thn n k a.1).smul
        (hA.measurable_vz a.1)
    · -- domination
      obtain ⟨r, ω⟩ := p
      simp only []
      rw [GF_eq]
      have hRk := resolvent_right (hA.psd r ω) n (e k)
      have hg : ‖resolvent (S r ω) n (e k)‖ ≤ 2 * ((n : ℝ) + 1) := by
        have := norm_resolvent_le (hA.psd r ω) n (e k)
        rwa [e.orthonormal.norm_eq_one k, mul_one] at this
      have hGn : Gn e T S n k r ω = WithLp.toLp 2
          ((if r ≤ T then S r ω (resolvent (S r ω) n (e k)) else 0), psin e T S n k r ω) := by
        unfold Gn psin
        by_cases h : r ≤ T
        · simp only [h, if_true]
          rw [eq_sub_of_add_eq hRk]
        · simp [h]
      rw [hGn]
      refine (norm_toLp_sub_le _ _ _ _).trans ?_
      have hψ := norm_sub_proj_le e (psin e T S n k r ω) (F m)
      have hψ2 := hA.norm_psin_le n k r ω
      have hdS : ‖(if r ≤ T then S r ω (∑ i ∈ F m, inner ℝ (e i) (resolvent (S r ω) n (e k)) • e i)
          else 0) - (if r ≤ T then S r ω (resolvent (S r ω) n (e k)) else 0)‖ ≤
          2 * ((n : ℝ) + 1) * dS e T Ct (r, ω) := by
        by_cases h : r ≤ T
        · simp only [h, if_true, dS]
          rw [← map_sub]
          calc _ ≤ Real.sqrt (trf e Ct (r, ω)) * ‖(∑ i ∈ F m, inner ℝ (e i)
                (resolvent (S r ω) n (e k)) • e i) - resolvent (S r ω) n (e k)‖ :=
                hA.norm_S_le r ω _
            _ ≤ Real.sqrt (trf e Ct (r, ω)) * (2 * ((n : ℝ) + 1)) := by
                gcongr
                rw [norm_sub_rev]
                exact (norm_sub_proj_le e _ (F m)).trans hg
            _ = _ := by ring
        · simp [h, dS]
      calc _ ≤ 2 * ((n : ℝ) + 1) * dS e T Ct (r, ω) + 2 :=
            add_le_add hdS (by rw [norm_sub_rev]; exact hψ.trans hψ2)
        _ = d (r, ω) := by simp only [hd]
    · -- pointwise limit
      obtain ⟨r, ω⟩ := p
      simp only []
      have hRk := resolvent_right (hA.psd r ω) n (e k)
      have hlim1 : Tendsto (fun m => (if r ≤ T then S r ω (∑ i ∈ F m, inner ℝ (e i)
          (resolvent (S r ω) n (e k)) • e i) else 0)) atTop
          (𝓝 (if r ≤ T then e k - epsn n • resolvent (S r ω) n (e k) else 0)) := by
        by_cases h : r ≤ T
        · simp only [h, if_true]
          have := ((S r ω).continuous.tendsto _).comp
            (tendsto_proj e (resolvent (S r ω) n (e k)) hF)
          rwa [eq_sub_of_add_eq hRk] at this
        · simp only [h, if_false]; exact tendsto_const_nhds
      have hlim2 : Tendsto (fun m => ∑ j ∈ F m, inner ℝ (e j) (psin e T S n k r ω) • e j) atTop
          (𝓝 (psin e T S n k r ω)) := tendsto_proj e _ hF
      have := ((WithLp.prod_continuous_toLp 2 H H).tendsto _).comp (hlim1.prodMk_nhds hlim2)
      have hGn : Gn e T S n k r ω = WithLp.toLp 2 ((if r ≤ T then e k - epsn n •
          resolvent (S r ω) n (e k) else 0), psin e T S n k r ω) := by
        unfold Gn psin; rfl
      rw [hGn]
      simp only [GF_eq]
      exact this

end ApproxGn

section ApproxGk

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {T : ℝ} {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

lemma norm_Q_le (hA : ARData P ℱ e T Mt Ct S W) {Q : ℝ → Ω → H →L[ℝ] H}
    (hQlim : ∀ r ω x, Tendsto (fun n => S r ω (resolvent (S r ω) n x)) atTop (𝓝 (Q r ω x)))
    (r : ℝ) (ω : Ω) (x : H) : ‖Q r ω x‖ ≤ ‖x‖ :=
  le_of_tendsto' (hQlim r ω x).norm (fun n => norm_S_resolvent_le (hA.psd r ω) n x)

lemma measurable_Q_apply (hA : ARData P ℱ e T Mt Ct S W) {Q : ℝ → Ω → H →L[ℝ] H}
    (hQprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (Q r ω x) y)) (x : H) :
    Measurable fun p : ℝ × Ω => Q p.1 p.2 x := by
  refine measurable_of_inner_basis e (fun j => ?_)
  have : (fun p : ℝ × Ω => inner ℝ (e j) (Q p.1 p.2 x)) = fun p => inner ℝ (Q p.1 p.2 x) (e j) := by
    funext p; exact real_inner_comm _ _
  rw [this]
  exact isProgressive_measurable_uncurry (hQprog x (e j))

theorem ARData.approx_Gk (hA : ARData P ℱ e T Mt Ct S W) {Q : ℝ → Ω → H →L[ℝ] H}
    (hQlim : ∀ r ω x, Tendsto (fun n => S r ω (resolvent (S r ω) n x)) atTop (𝓝 (Q r ω x)))
    (hQprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (Q r ω x) y)) (k : ι) :
    Approx P ℱ (vz e T S) (Gk e T Q k) := by
  have hGk : Measurable fun p : ℝ × Ω => Gk e T Q k p.1 p.2 := by
    unfold Gk
    have h1 := measurable_Q_apply hA hQprog (e k)
    have hc : MeasurableSet {p : ℝ × Ω | p.1 ≤ T} := measurableSet_le measurable_fst measurable_const
    refine (WithLp.measurable_toLp 2 (H × H)).comp (Measurable.prodMk ?_ ?_)
    · exact Measurable.ite hc h1 measurable_const
    · exact Measurable.ite hc (measurable_const.sub h1) measurable_const
  refine Approx.of_limit (Gs := fun n => Gn e T S n k) (fun n => hA.approx_Gn n k) (fun N => ?_)
  refine tendsto_eLpNorm_of_dominated (μ := tsm P N) (f := fun n p => Gn e T S n k p.1 p.2)
    (g := fun p => Gk e T Q k p.1 p.2) (d := fun _ => (6 : ℝ)) (fun n => hA.measurable_Gn n k) hGk
    measurable_const (memLp_const (6 : ℝ)).eLpNorm_ne_top
    (fun n => Eventually.of_forall fun p => ?_) (Eventually.of_forall fun p => ?_)
  · obtain ⟨r, ω⟩ := p
    simp only []
    refine (norm_toLp_sub_le _ _ _ _).trans ?_
    by_cases h : r ≤ T
    · simp only [h, if_true]
      have hRk := resolvent_right (hA.psd r ω) n (e k)
      have h1 : ‖e k - epsn n • resolvent (S r ω) n (e k)‖ ≤ 1 := by
        rw [← eq_sub_of_add_eq hRk]
        calc _ ≤ ‖e k‖ := norm_S_resolvent_le (hA.psd r ω) n (e k)
          _ = 1 := e.orthonormal.norm_eq_one k
      have h2 : ‖Q r ω (e k)‖ ≤ 1 := (norm_Q_le hA hQlim r ω (e k)).trans
        (e.orthonormal.norm_eq_one k).le
      have h3 : ‖epsn n • resolvent (S r ω) n (e k)‖ ≤ 2 := by
        have := hA.norm_psin_le n k r ω
        simpa [psin, h] using this
      have h4 : ‖e k - Q r ω (e k)‖ ≤ 2 := by
        calc _ ≤ ‖e k‖ + ‖Q r ω (e k)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by rw [e.orthonormal.norm_eq_one k]; linarith
          _ = 2 := by norm_num
      calc _ ≤ (‖e k - epsn n • resolvent (S r ω) n (e k)‖ + ‖Q r ω (e k)‖) +
            (‖epsn n • resolvent (S r ω) n (e k)‖ + ‖e k - Q r ω (e k)‖) := by
            gcongr <;> exact norm_sub_le _ _
        _ ≤ 6 := by linarith
    · simp [h]
  · obtain ⟨r, ω⟩ := p
    simp only []
    unfold Gn Gk
    by_cases h : r ≤ T
    · simp only [h, if_true]
      have hRk : ∀ n, e k - epsn n • resolvent (S r ω) n (e k) =
          S r ω (resolvent (S r ω) n (e k)) := fun n => by
        rw [eq_sub_of_add_eq (resolvent_right (hA.psd r ω) n (e k))]
      have hRk' : ∀ n, epsn n • resolvent (S r ω) n (e k) =
          e k - S r ω (resolvent (S r ω) n (e k)) := fun n =>
        eq_sub_of_add_eq' (resolvent_right (hA.psd r ω) n (e k))
      have h1 := hQlim r ω (e k)
      have h2 : Tendsto (fun n => epsn n • resolvent (S r ω) n (e k)) atTop
          (𝓝 (e k - Q r ω (e k))) := by
        simp_rw [hRk']
        exact tendsto_const_nhds.sub h1
      have h1' : Tendsto (fun n => e k - epsn n • resolvent (S r ω) n (e k)) atTop
          (𝓝 (Q r ω (e k))) := by
        simp_rw [hRk]; exact h1
      exact ((WithLp.prod_continuous_toLp 2 H H).tendsto _).comp (h1'.prodMk_nhds h2)
    · simp only [h, if_false]
      exact tendsto_const_nhds

end ApproxGk

end Gk

end HRS.MRep
