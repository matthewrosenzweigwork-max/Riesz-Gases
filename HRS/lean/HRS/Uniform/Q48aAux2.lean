import HRS.Uniform.Q48aAux1

/-!
# Q48a, part 2: the Brownian motion `B` and the representation `M̃ = ∫ S dB` on the whole half-line

`⊤`-copy of `HRS/Prob/MRepAux7.lean`, `MRepAux8.lean` (section `Ident`) and `MRepAux9.lean`.
-/

noncomputable section

open HRS HRS.MRep
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48a

section Brown
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

lemma inner_GkT (Q : ℝ → Ω → H →L[ℝ] H) (e : HilbertBasis ι ℝ H)
    (hsym : ∀ r ω x y, inner ℝ (Q r ω x) y = inner ℝ x (Q r ω y))
    (hid : ∀ r ω x, Q r ω (Q r ω x) = Q r ω x) (k l : ι) (r : ℝ) (ω : Ω) :
    inner ℝ (GkT e Q k r ω) (GkT e Q l r ω) = if k = l then 1 else 0 := by
  have hel : inner ℝ (e k) (e l) = if k = l then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.1 e.orthonormal k l
  unfold GkT
  simp only [WithLp.prod_inner_apply]
  have h1 : inner ℝ (Q r ω (e k)) (Q r ω (e l)) = inner ℝ (e k) (Q r ω (e l)) := by
    rw [hsym, hid]
  have h2 : inner ℝ (Q r ω (e k)) (e l) = inner ℝ (e k) (Q r ω (e l)) := hsym r ω _ _
  have h3 : inner ℝ (e k - Q r ω (e k)) (e l - Q r ω (e l)) = inner ℝ (e k) (e l) -
      inner ℝ (e k) (Q r ω (e l)) - inner ℝ (Q r ω (e k)) (e l) +
      inner ℝ (Q r ω (e k)) (Q r ω (e l)) := by
    simp only [inner_sub_left, inner_sub_right]; ring
  rw [h3, h1, h2, hel]; ring

lemma ARTop.ae_integrableOn_trf (hA : ARTop P ℱ e Mt Ct S W) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, IntegrableOn (fun r => trf e Ct (r, ω)) (Set.Icc 0 t) := by
  have hm : Measurable fun p : ℝ × Ω => ENNReal.ofReal (trf e Ct p) :=
    ENNReal.measurable_ofReal.comp hA.measurable_trf
  have h1 : ∀ n : ℕ, Measurable fun ω => ∫⁻ r in Set.Icc 0 (n : ℝ), ENNReal.ofReal (trf e Ct (r, ω)) :=
    fun n => hm.lintegral_prod_left' (μ := volume.restrict (Set.Icc 0 (n : ℝ)))
  have h2 : ∀ n : ℕ, ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc 0 (n : ℝ), ENNReal.ofReal (trf e Ct (r, ω)) < ∞ :=
    fun n => ae_lt_top (h1 n) (hA.Ctr n)
  rw [← ae_all_iff] at h2
  filter_upwards [h2] with ω hω t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hI : IntegrableOn (fun r => trf e Ct (r, ω)) (Set.Icc 0 (n : ℝ)) := by
    refine ⟨(hA.measurable_trf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) (hω n)
    refine lintegral_congr fun r => ?_
    have hnn : 0 ≤ trf e Ct (r, ω) := tsum_nonneg fun i => (hA.trace r ω).nonneg _
    rw [Real.enorm_of_nonneg hnn]
  exact hI.mono_set (Set.Icc_subset_Icc le_rfl hn)

/-- The vector `w = (S x, 0)`. -/
def wzT (S : ℝ → Ω → H →L[ℝ] H) (x : H) : ℝ → Ω → WithLp 2 (H × H) :=
  fun r ω => WithLp.toLp 2 (S r ω x, (0 : H))

lemma ARTop.measurable_wz (hA : ARTop P ℱ e Mt Ct S W) (x : H) :
    Measurable fun p : ℝ × Ω => wzT S x p.1 p.2 := by
  unfold wzT
  exact (WithLp.measurable_toLp 2 (H × H)).comp ((hA.measurable_S_apply x).prodMk measurable_const)

lemma ARTop.eLpNorm_wz (hA : ARTop P ℱ e Mt Ct S W) (x : H) (t : ℝ) :
    eLpNorm (fun p : ℝ × Ω => wzT S x p.1 p.2) 2 (tsm P t) ≠ ∞ := by
  have h1 : eLpNorm (fun p : ℝ × Ω => wzT S x p.1 p.2) 2 (tsm P t) ≤
      eLpNorm (fun p : ℝ × Ω => ‖x‖ * dST e Ct p) 2 (tsm P t) := by
    refine eLpNorm_mono_real (hA.measurable_wz x).aestronglyMeasurable (fun p => ?_)
    unfold wzT dST
    have := hA.norm_S_le p.1 p.2 x
    calc ‖(WithLp.toLp 2 (S p.1 p.2 x, (0 : H)) : WithLp 2 (H × H))‖ ≤ ‖S p.1 p.2 x‖ + ‖(0 : H)‖ :=
          norm_toLp_le _ _
      _ ≤ ‖x‖ * Real.sqrt (trf e Ct p) := by rw [norm_zero, add_zero]; linarith
  refine ne_top_of_le_ne_top ?_ h1
  have : (fun p : ℝ × Ω => ‖x‖ * dST e Ct p) = ‖x‖ • dST e Ct := by funext p; simp
  rw [this, eLpNorm_const_smul]
  exact ENNReal.mul_ne_top enorm_ne_top (hA.eLpNorm_dS t)

lemma inner_vz_wzT_ll (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (x : H) (r : ℝ)
    (ω : Ω) (i : ι) : inner ℝ (vzT e S r ω (Sum.inl i)) (wzT S x r ω) =
      inner ℝ (S r ω (e i)) (S r ω x) := by
  simp [vzT, wzT, WithLp.prod_inner_apply]

lemma inner_vz_wzT_rr (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (x : H) (r : ℝ)
    (ω : Ω) (j : ι) : inner ℝ (vzT e S r ω (Sum.inr j)) (wzT S x r ω) = 0 := by
  simp [vzT, wzT, WithLp.prod_inner_apply]

lemma inner_GkT_wz (Q : ℝ → Ω → H →L[ℝ] H) (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H)
    (hsym : ∀ r ω x y, inner ℝ (Q r ω x) y = inner ℝ x (Q r ω y))
    (hQS : ∀ r ω x, Q r ω (S r ω x) = S r ω x) (k : ι) (x : H) (r : ℝ) (ω : Ω) :
    inner ℝ (GkT e Q k r ω) (wzT S x r ω) = inner ℝ (e k) (S r ω x) := by
  simp only [GkT, wzT, WithLp.prod_inner_apply, inner_zero_right, add_zero]
  rw [hsym, hQS]

lemma ARTop.ae_integrableOn_inner_vz_wz (hA : ARTop P ℱ e Mt Ct S W) (x : H) :
    ∀ᵐ ω ∂P, ∀ (a : ι ⊕ ι) (t : ℝ), IntegrableOn (fun r => inner ℝ (vzT e S r ω a)
      (wzT S x r ω)) (Set.Icc 0 t) := by
  filter_upwards [hA.ae_integrableOn_trf] with ω hω a t
  rcases a with i | j
  · have hbound : IntegrableOn (fun r => trf e Ct (r, ω) * ‖x‖) (Set.Icc 0 t) volume :=
      (hω t).mul_const ‖x‖
    refine Integrable.mono' hbound ?_ (Eventually.of_forall fun r => ?_)
    · have hm : Measurable fun r : ℝ => inner ℝ (vzT e S r ω (Sum.inl i)) (wzT S x r ω) :=
        (meas_inner (hA.measurable_vz _) (hA.measurable_wz x)).comp
          (measurable_id.prodMk measurable_const)
      exact hm.aestronglyMeasurable
    · rw [inner_vz_wzT_ll]
      have h1 := hA.norm_S_le r ω (e i)
      have h2 := hA.norm_S_le r ω x
      rw [e.orthonormal.norm_eq_one i, mul_one] at h1
      have hnn : 0 ≤ trf e Ct (r, ω) := tsum_nonneg fun i => (hA.trace r ω).nonneg _
      calc ‖inner ℝ (S r ω (e i)) (S r ω x)‖ ≤ ‖S r ω (e i)‖ * ‖S r ω x‖ := norm_inner_le_norm _ _
        _ ≤ Real.sqrt (trf e Ct (r, ω)) * (Real.sqrt (trf e Ct (r, ω)) * ‖x‖) := by gcongr
        _ = trf e Ct (r, ω) * ‖x‖ := by
            rw [← mul_assoc, Real.mul_self_sqrt hnn]
  · simp only [inner_vz_wzT_rr, integrableOn_zero]

lemma ARTop.measurable_Gk (hA : ARTop P ℱ e Mt Ct S W) {Q : ℝ → Ω → H →L[ℝ] H}
    (hQprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (Q r ω x) y)) (k : ι) :
    Measurable fun p : ℝ × Ω => GkT e Q k p.1 p.2 := by
  unfold GkT
  have h1 := measurable_Q_applyT hA hQprog (e k)
  exact (WithLp.measurable_toLp 2 (H × H)).comp (Measurable.prodMk h1 (measurable_const.sub h1))

theorem ARTop.exists_Bhat (hA : ARTop P ℱ e Mt Ct S W) :
    ∃ Y : ι → ℝ → Ω → ℝ,
      (∀ k ω, Continuous fun t => Y k t ω) ∧ (∀ k, ∀ t ≤ 0, ∀ ω, Y k t ω = 0) ∧
      (∀ k t, Measurable[ℱ t] (Y k t)) ∧ (∀ k, Martingale (Y k) ℱ P) ∧ (∀ k t, MemLp (Y k t) 2 P) ∧
      (∀ k l, Martingale (fun t ω => Y k t ω * Y l t ω - if k = l then max t 0 else 0) ℱ P) ∧
      (∀ k (x : H), Martingale (fun t ω => Y k t ω * inner ℝ (Mt t ω) x -
        ∫ r in Set.Icc 0 t, inner ℝ (e k) (S r ω x)) ℱ P) := by
  classical
  have hN := hA.isNoiseK
  obtain ⟨Q, hQlim, hQsym, hQid, hQS, hQprog⟩ :=
    exists_progressive_proj e Ct hA.trace S hA.sqrt hA.Cprog hA.Sprog
  have hex : ∀ k, ∃ Y : ℝ → Ω → ℝ, ∃ seq : ApproxSeq P ℱ (vzT e S) (GkT e Q k),
      IsIntOf (Nz e Mt W) seq Y := fun k => by
    obtain ⟨seq⟩ := (hA.approx_Gk hQlim hQprog k).exists_seq
    obtain ⟨Y, hY⟩ := exists_isIntOf hA.complete hN (hA.measurable_Gk hQprog k) seq
    exact ⟨Y, seq, hY⟩
  choose Y seq hY using hex
  refine ⟨Y, fun k => (hY k).cont, fun k => (hY k).zero, fun k => (hY k).adapted,
    fun k => (hY k).martingale hA.complete hN, fun k t => (hY k).memLp hN t, ?_, ?_⟩
  · intro k l
    have h := IsIntOf.bracket hA.complete hN (hA.measurable_Gk hQprog k)
      (hA.measurable_Gk hQprog l) (hY k) (hY l)
    have e1 : ∀ t ω, ∫ r in Set.Icc 0 t, inner ℝ (GkT e Q k r ω) (GkT e Q l r ω) =
        if k = l then max t 0 else 0 := by
      intro t ω
      have : ∀ r, inner ℝ (GkT e Q k r ω) (GkT e Q l r ω) = if k = l then 1 else 0 :=
        fun r => inner_GkT Q e hQsym hQid k l r ω
      simp_rw [this]
      by_cases hkl : k = l
      · simp [hkl, Real.volume_real_Icc]
      · simp [hkl]
    have e2 : (fun t ω => Y k t ω * Y l t ω - ∫ r in Set.Icc 0 t,
        inner ℝ (GkT e Q k r ω) (GkT e Q l r ω)) =
        fun t ω => Y k t ω * Y l t ω - if k = l then max t 0 else 0 := by
      funext t ω; rw [e1]
    rw [e2] at h
    exact h
  · intro k x
    have hV : Martingale (fun t ω => inner ℝ (Mt t ω) x) ℱ P := hA.mart x
    have hVw : ∀ a : ι ⊕ ι, Martingale (fun t ω => Nz e Mt W t ω a * inner ℝ (Mt t ω) x -
        ∫ r in Set.Icc 0 t, inner ℝ (vzT e S r ω a) (wzT S x r ω)) ℱ P := by
      intro a
      rcases a with i | j
      · have e1 : ∀ t ω, ∫ r in Set.Icc 0 t, inner ℝ (vzT e S r ω (Sum.inl i)) (wzT S x r ω) =
            ∫ r in Set.Icc 0 t, Ct r ω (e i) x := by
          intro t ω
          refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
          rw [inner_vz_wzT_ll, (hA.sqrt r ω).sq]
        have e2 : (fun t ω => Nz e Mt W t ω (Sum.inl i) * inner ℝ (Mt t ω) x -
            ∫ r in Set.Icc 0 t, inner ℝ (vzT e S r ω (Sum.inl i)) (wzT S x r ω)) =
            fun t ω => inner ℝ (Mt t ω) (e i) * inner ℝ (Mt t ω) x -
              ∫ r in Set.Icc 0 t, Ct r ω (e i) x := by
          funext t ω; simp only [Nz, Sum.elim_inl]; rw [e1]
        rw [e2]
        exact hA.cov _ _
      · have e2 : (fun t ω => Nz e Mt W t ω (Sum.inr j) * inner ℝ (Mt t ω) x -
            ∫ r in Set.Icc 0 t, inner ℝ (vzT e S r ω (Sum.inr j)) (wzT S x r ω)) =
            fun t ω => inner ℝ (Mt t ω) x * ofNNRealTime W t ω j := by
          funext t ω
          simp only [Nz, Sum.elim_inr, inner_vz_wzT_rr, integral_zero, sub_zero]
          ring
        rw [e2]
        exact hA.cross _ _
    have h := IsIntOf.cross hA.complete hN (hA.measurable_Gk hQprog k) (hY k) hV
      (fun t => hA.sq t x) (hA.measurable_wz x) (hA.eLpNorm_wz x)
      (hA.ae_integrableOn_inner_vz_wz x) hVw
    have e1 : ∀ t ω, ∫ r in Set.Icc 0 t, inner ℝ (GkT e Q k r ω) (wzT S x r ω) =
        ∫ r in Set.Icc 0 t, inner ℝ (e k) (S r ω x) := by
      intro t ω
      refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
      exact inner_GkT_wz Q e S hQsym hQS k x r ω
    have e2 : (fun t ω => Y k t ω * inner ℝ (Mt t ω) x -
        ∫ r in Set.Icc 0 t, inner ℝ (GkT e Q k r ω) (wzT S x r ω)) =
        fun t ω => Y k t ω * inner ℝ (Mt t ω) x -
          ∫ r in Set.Icc 0 t, inner ℝ (e k) (S r ω x) := by
      funext t ω; rw [e1]
    rw [e2] at h
    exact h

end Brown

section Ident
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ} {Y : ι → ℝ → Ω → ℝ}

/-- The coordinates `⟨e_k, S x⟩`. -/
def cxT (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (x : H) (k : ι) : ℝ → Ω → ℝ :=
  fun r ω => inner ℝ (e k) (S r ω x)

lemma ARTop.isProgressive_cx (hA : ARTop P ℱ e Mt Ct S W) (x : H) (k : ι) :
    IsProgressive ℱ (cxT e S x k) := by
  have h := hA.Sprog x (e k)
  have : cxT e S x k = fun r ω => inner ℝ (S r ω x) (e k) := by
    funext r ω; unfold cxT; simp only [real_inner_comm]
  rw [this]; exact h

lemma ARTop.hasSum_cx_sq (hA : ARTop P ℱ e Mt Ct S W) (x : H) (r : ℝ) (ω : Ω) :
    HasSum (fun k => cxT e S x k r ω * cxT e S x k r ω) (Ct r ω x x) := by
  have := e.hasSum_inner_mul_inner (S r ω x) (S r ω x)
  simp only [cxT]
  rw [← (hA.sqrt r ω).sq x x]
  convert this using 2 with k
  rw [real_inner_comm (S r ω x) (e k)]

lemma ARTop.sum_cx_sq_le (hA : ARTop P ℱ e Mt Ct S W) (x : H) (r : ℝ) (ω : Ω) (s : Finset ι) :
    ∑ k ∈ s, cxT e S x k r ω * cxT e S x k r ω ≤ dST e Ct (r, ω) ^ 2 * ‖x‖ ^ 2 := by
  have h1 := (hA.hasSum_cx_sq x r ω)
  have h2 : ∑ k ∈ s, cxT e S x k r ω * cxT e S x k r ω ≤ Ct r ω x x :=
    sum_le_hasSum s (fun k _ => mul_self_nonneg _) h1
  refine h2.trans ?_
  simp only [dST]
  have hnn : 0 ≤ trf e Ct (r, ω) := tsum_nonneg fun i => (hA.trace r ω).nonneg _
  rw [Real.sq_sqrt hnn, ← (hA.sqrt r ω).sq x x, real_inner_self_eq_norm_sq]
  have := hA.norm_S_le r ω x
  calc ‖S r ω x‖ ^ 2 ≤ (Real.sqrt (trf e Ct (r, ω)) * ‖x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = trf e Ct (r, ω) * ‖x‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hnn]

lemma ARTop.integrable_dS_sq (hA : ARTop P ℱ e Mt Ct S W) (t : ℝ) :
    Integrable (fun p : ℝ × Ω => dST e Ct p ^ 2) (tsm P t) := by
  have hmem : MemLp (dST e Ct) 2 (tsm P t) :=
    (hA.eLpNorm_dS t).lt_top
  exact hmem.integrable_sq

lemma ARTop.isProgressiveL2_cx (hA : ARTop P ℱ e Mt Ct S W) (x : H) (s : Finset ι) :
    IsProgressiveL2 P ℱ (fun r ω (k : s) => cxT e S x k r ω) := by
  refine ⟨isProgressive_pi (fun k => hA.isProgressive_cx x k.1), fun t => ?_⟩
  unfold sqIntegralOn
  have hm := hA.measurable_dS
  have hpt : ∀ r ω, ∑ k : s, ‖cxT e S x k r ω‖ₑ ^ 2 ≤ ‖dST e Ct (r, ω)‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := by
    intro r ω
    rw [sum_enorm_sq_eq_ofReal (fun k : s => cxT e S x k r ω)]
    have h1 : ∑ k : s, cxT e S x k r ω ^ 2 ≤ dST e Ct (r, ω) ^ 2 * ‖x‖ ^ 2 := by
      have := hA.sum_cx_sq_le x r ω s
      have h0 : ∑ k : s, cxT e S x k r ω ^ 2 = ∑ k ∈ s, cxT e S x k r ω * cxT e S x k r ω := by
        rw [Finset.sum_coe_sort s (fun k => cxT e S x k r ω ^ 2)]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h0]; exact this
    have e1 := enorm_sq_real (dST e Ct (r, ω))
    have e2 := enorm_sq_real ‖x‖
    rw [enorm_norm] at e2
    calc ENNReal.ofReal (∑ k : s, cxT e S x k r ω ^ 2)
        ≤ ENNReal.ofReal (dST e Ct (r, ω) ^ 2 * ‖x‖ ^ 2) := ENNReal.ofReal_le_ofReal h1
      _ = ‖dST e Ct (r, ω)‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), ← e1, ← e2]
  have hfin : (∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dST e Ct (r, ω)‖ₑ ^ 2) ∂P) ≠ ∞ := by
    have h1 : ∫⁻ p, ‖dST e Ct p‖ₑ ^ 2 ∂(tsm P t) =
        ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dST e Ct (r, ω)‖ₑ ^ 2) ∂P := by
      unfold tsm
      rw [lintegral_prod_symm' _ (by fun_prop : Measurable fun p : ℝ × Ω => ‖dST e Ct p‖ₑ ^ 2)]
    rw [← h1, HRS.lintegral_enorm_sq_eq_eLpNorm_sq hm.aestronglyMeasurable]
    exact (ENNReal.pow_lt_top (hA.eLpNorm_dS t).lt_top).ne
  have hx : ‖x‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top enorm_ne_top
  calc (∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ∑ k : s, ‖cxT e S x k r ω‖ₑ ^ 2) ∂P)
      ≤ ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dST e Ct (r, ω)‖ₑ ^ 2 * ‖x‖ₑ ^ 2) ∂P :=
        lintegral_mono fun ω => lintegral_mono fun r => hpt r ω
    _ = (∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dST e Ct (r, ω)‖ₑ ^ 2) ∂P) * ‖x‖ₑ ^ 2 := by
        simp_rw [lintegral_mul_const' _ _ hx]
    _ < ∞ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hfin) (lt_top_iff_ne_top.2 hx)

/-- The properties of the Brownian coordinates produced by `ARTop.exists_Bhat`. -/
structure BDataTop (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (e : HilbertBasis ι ℝ H)
    (Mt : ℝ → Ω → H) (S : ℝ → Ω → H →L[ℝ] H) (Y : ι → ℝ → Ω → ℝ) : Prop where
  cont : ∀ k ω, Continuous fun t => Y k t ω
  zero : ∀ k, ∀ t ≤ 0, ∀ ω, Y k t ω = 0
  adapted : ∀ k t, Measurable[ℱ t] (Y k t)
  mart : ∀ k, Martingale (Y k) ℱ P
  sq : ∀ k t, MemLp (Y k t) 2 P
  qv : ∀ k l, Martingale (fun t ω => Y k t ω * Y l t ω - if k = l then max t 0 else 0) ℱ P
  cross : ∀ k (x : H), Martingale (fun t ω => Y k t ω * inner ℝ (Mt t ω) x -
        ∫ r in Set.Icc 0 t, inner ℝ (e k) (S r ω x)) ℱ P

theorem ARTop.exists_bdata (hA : ARTop P ℱ e Mt Ct S W) : ∃ Y, BDataTop P ℱ e Mt S Y := by
  obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7⟩ := hA.exists_Bhat
  exact ⟨Y, ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩

theorem BDataTop.brownian (hY : BDataTop P ℱ e Mt S Y) (hℱ : IsCompleteFiltration P ℱ) :
    IsCylindricalBrownian P ℱ (Bfam Y) :=
  isCylindricalBrownian_of_Y hℱ Y hY.cont hY.zero hY.adapted hY.mart hY.qv

lemma ARTop.integral_sq_V (hA : ARTop P ℱ e Mt Ct S W) (x : H) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∫ ω, inner ℝ (Mt τ ω) x * inner ℝ (Mt τ ω) x ∂P =
      ∫ ω, (∫ r in Set.Icc 0 τ, Ct r ω x x) ∂P := by
  have hm := hA.cov x x
  have h0 := hm.setIntegral_eq hτ (MeasurableSet.univ)
  simp only [Measure.restrict_univ] at h0
  have hA2 : Integrable (fun ω => inner ℝ (Mt τ ω) x * inner ℝ (Mt τ ω) x) P :=
    (hA.sq τ x).integrable_mul (hA.sq τ x)
  have hfτ := hm.integrable τ
  have hB : Integrable (fun ω => ∫ r in Set.Icc 0 τ, Ct r ω x x) P := by
    have := hA2.sub hfτ
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp
  have hz : ∫ ω, (inner ℝ (Mt 0 ω) x * inner ℝ (Mt 0 ω) x -
      ∫ r in Set.Icc 0 0, Ct r ω x x) ∂P = 0 := by
    simp [hA.zero 0 le_rfl]
  rw [hz, integral_sub hA2 hB] at h0
  linarith

lemma ARTop.measurable_cx (hA : ARTop P ℱ e Mt Ct S W) (x : H) (k : ι) :
    Measurable fun p : ℝ × Ω => cxT e S x k p.1 p.2 :=
  isProgressive_measurable_uncurry (hA.isProgressive_cx x k)

lemma ARTop.measurable_Cxx (hA : ARTop P ℱ e Mt Ct S W) (x : H) :
    Measurable fun p : ℝ × Ω => Ct p.1 p.2 x x :=
  isProgressive_measurable_uncurry (hA.Cprog x x)

theorem ARTop.tendsto_partial (hA : ARTop P ℱ e Mt Ct S W) (x : H) (τ : ℝ) :
    Tendsto (fun s : Finset ι => ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cxT e S x k r ω * cxT e S x k r ω) ∂P)
      atTop (𝓝 (∫ ω, (∫ r in Set.Icc 0 τ, Ct r ω x x) ∂P)) := by
  have hbd : Integrable (fun p : ℝ × Ω => dST e Ct p ^ 2 * ‖x‖ ^ 2) (tsm P τ) :=
    (hA.integrable_dS_sq τ).mul_const _
  have hgm : ∀ s : Finset ι, Measurable fun p : ℝ × Ω => ∑ k ∈ s, cxT e S x k p.1 p.2 * cxT e S x k p.1 p.2 :=
    fun s => Finset.measurable_sum _ fun k _ => (hA.measurable_cx x k).mul (hA.measurable_cx x k)
  have hgb : ∀ s : Finset ι, ∀ p : ℝ × Ω,
      ‖∑ k ∈ s, cxT e S x k p.1 p.2 * cxT e S x k p.1 p.2‖ ≤ dST e Ct p ^ 2 * ‖x‖ ^ 2 := by
    intro s p
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => mul_self_nonneg _)]
    exact hA.sum_cx_sq_le x p.1 p.2 s
  have hgi : ∀ s : Finset ι, Integrable (fun p : ℝ × Ω =>
      ∑ k ∈ s, cxT e S x k p.1 p.2 * cxT e S x k p.1 p.2) (tsm P τ) := fun s =>
    hbd.mono' (hgm s).aestronglyMeasurable (ae_of_all _ (hgb s))
  have hli : Integrable (fun p : ℝ × Ω => Ct p.1 p.2 x x) (tsm P τ) := by
    refine hbd.mono' (hA.measurable_Cxx x).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    have := (hA.hasSum_cx_sq x p.1 p.2)
    have h1 : ∀ s : Finset ι, ∑ k ∈ s, cxT e S x k p.1 p.2 * cxT e S x k p.1 p.2 ≤
        dST e Ct p ^ 2 * ‖x‖ ^ 2 := fun s => hA.sum_cx_sq_le x p.1 p.2 s
    have h2 := le_of_tendsto' this h1
    rw [Real.norm_of_nonneg ((hA.trace p.1 p.2).nonneg x)]
    exact h2
  have h1 : ∀ s : Finset ι, ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cxT e S x k r ω * cxT e S x k r ω) ∂P =
      ∫ p, ∑ k ∈ s, cxT e S x k p.1 p.2 * cxT e S x k p.1 p.2 ∂(tsm P τ) := fun s =>
    iter_eq_tsm (f := fun p : ℝ × Ω => ∑ k ∈ s, cxT e S x k p.1 p.2 * cxT e S x k p.1 p.2) τ (hgi s)
  have h2 : ∫ ω, (∫ r in Set.Icc 0 τ, Ct r ω x x) ∂P = ∫ p, Ct p.1 p.2 x x ∂(tsm P τ) :=
    iter_eq_tsm (f := fun p : ℝ × Ω => Ct p.1 p.2 x x) τ hli
  simp_rw [h1]
  rw [h2]
  refine tendsto_integral_filter_of_dominated_convergence (fun p => dST e Ct p ^ 2 * ‖x‖ ^ 2)
    (Eventually.of_forall fun s => (hgm s).aestronglyMeasurable)
    (Eventually.of_forall fun s => ae_of_all _ (hgb s)) hbd (ae_of_all _ fun p => ?_)
  exact hA.hasSum_cx_sq x p.1 p.2

theorem ARTop.key_identity (hA : ARTop P ℱ e Mt Ct S W) (hY : BDataTop P ℱ e Mt S Y) (x : H)
    (τ : ℝ) (hτ : 0 ≤ τ) (s : Finset ι) :
    ∫⁻ ω, ‖itoIntegral P ℱ (fun t ω (k : s) => Bfam Y t ω k)
        (fun r ω (k : s) => cxT e S x k r ω) τ ω - inner ℝ (Mt τ ω) x‖ₑ ^ 2 ∂P =
      ENNReal.ofReal ((∫ ω, (∫ r in Set.Icc 0 τ, Ct r ω x x) ∂P) -
        ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cxT e S x k r ω * cxT e S x k r ω) ∂P) := by
  classical
  set q : ℝ → Ω → s → ℝ := fun r ω (k : s) => cxT e S x k r ω with hqdef
  have hq : IsProgressiveL2 P ℱ q := hA.isProgressiveL2_cx x s
  have hBs : IsBrownianFiltration P ℱ (fun t ω (k : s) => Bfam Y t ω k) :=
    (hY.brownian hA.complete) s
  set J := itoIntegral P ℱ (fun t ω (k : s) => Bfam Y t ω k) q with hJdef
  have hJ : IsItoIntegral P ℱ (fun t ω (k : s) => Bfam Y t ω k) q J :=
    isItoIntegral_itoIntegral hBs hq
  have hJ2 : MemLp (J τ) 2 P := hJ.memLp hBs hq τ
  have hV2 : MemLp (fun ω => inner ℝ (Mt τ ω) x) 2 P := hA.sq τ x
  have hJV := cross_ito (κ := s) hA.complete (fun k : s => Y k.1) (fun k => hY.zero k.1) hBs
    (fun k => hY.mart k.1) (fun k t => hY.sq k.1 t) (hA.mart x) (fun t => hA.sq t x) hq
    (fun k => hY.cross k.1 x) hq hJ τ hτ
  have hJJ := hJ.integral_mul hBs hq hq hJ τ
  have hVV := hA.integral_sq_V x τ hτ
  have hsum : ∀ r ω, ∑ k : s, q r ω k * q r ω k = ∑ k ∈ s, cxT e S x k r ω * cxT e S x k r ω :=
    fun r ω => Finset.sum_coe_sort s (fun k => cxT e S x k r ω * cxT e S x k r ω)
  simp_rw [hsum] at hJV hJJ
  set F := ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cxT e S x k r ω * cxT e S x k r ω) ∂P with hF
  set A := ∫ ω, (∫ r in Set.Icc 0 τ, Ct r ω x x) ∂P with hA'
  have hdiff : MemLp (fun ω => J τ ω - inner ℝ (Mt τ ω) x) 2 P := hJ2.sub hV2
  rw [lintegral_enorm_sq_eq_ofReal_integral hdiff]
  congr 1
  have e1 : (fun ω => (J τ ω - inner ℝ (Mt τ ω) x) * (J τ ω - inner ℝ (Mt τ ω) x)) =
      fun ω => (J τ ω * J τ ω - 2 * (J τ ω * inner ℝ (Mt τ ω) x)) +
        inner ℝ (Mt τ ω) x * inner ℝ (Mt τ ω) x := by
    funext ω; ring
  have i1 : Integrable (fun ω => J τ ω * J τ ω) P := hJ2.integrable_mul hJ2
  have i2 : Integrable (fun ω => 2 * (J τ ω * inner ℝ (Mt τ ω) x)) P :=
    (hJ2.integrable_mul hV2).const_mul 2
  have i3 : Integrable (fun ω => inner ℝ (Mt τ ω) x * inner ℝ (Mt τ ω) x) P := hV2.integrable_mul hV2
  have e2 := integral_add (μ := P) (f := fun ω => J τ ω * J τ ω - 2 * (J τ ω * inner ℝ (Mt τ ω) x))
    (g := fun ω => inner ℝ (Mt τ ω) x * inner ℝ (Mt τ ω) x) (i1.sub i2) i3
  have e3 := integral_sub (μ := P) (f := fun ω => J τ ω * J τ ω)
    (g := fun ω => 2 * (J τ ω * inner ℝ (Mt τ ω) x)) i1 i2
  have e4 := integral_const_mul (μ := P) (2 : ℝ) (fun ω => J τ ω * inner ℝ (Mt τ ω) x)
  rw [e1, e2, e3, e4, hJV, hJJ, hVV]
  ring

/-- The integrand of the representation. -/
def PhiRT (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) : ℝ → Ω → ι → H :=
  fun r ω j => S r ω (e j)

theorem ARTop.isHilbertItoIntegral (hA : ARTop P ℱ e Mt Ct S W) (hY : BDataTop P ℱ e Mt S Y) :
    IsHilbertItoIntegral P ℱ (Bfam Y) (PhiRT e S) Mt := by
  refine ⟨hA.cont, hA.adapted, hA.zero, fun τ hτ x => ?_⟩
  have hint : ∀ s : Finset ι, (fun r ω (k : s) => inner ℝ (PhiRT e S r ω k) x) =
      fun r ω (k : s) => cxT e S x k r ω := by
    intro s
    funext r ω k
    simp only [PhiRT, cxT]
    exact (hA.sqrt r ω).symm (e k) x
  have hlim : Tendsto (fun s : Finset ι => ENNReal.ofReal
      ((∫ ω, (∫ r in Set.Icc 0 τ, Ct r ω x x) ∂P) -
        ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cxT e S x k r ω * cxT e S x k r ω) ∂P)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∫ ω, (∫ r in Set.Icc 0 τ, Ct r ω x x) ∂P)).sub
      (hA.tendsto_partial x τ)
    have := ENNReal.tendsto_ofReal h
    simpa using this
  refine hlim.congr (fun s => ?_)
  rw [hint s]
  exact (hA.key_identity hY x τ hτ s).symm

end Ident

section Rep
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ} {Y : ι → ℝ → Ω → ℝ}

lemma ARTop.isProgressive_S (hA : ARTop P ℱ e Mt Ct S W) (x : H) :
    IsProgressive ℱ (fun r ω => S r ω x) := by
  refine isProgressive_of_inner_basis e (fun j => ?_)
  have : (fun r ω => inner ℝ (e j) (S r ω x)) = fun r ω => inner ℝ (S r ω x) (e j) := by
    funext r ω; exact real_inner_comm _ _
  rw [this]
  exact hA.Sprog x (e j)

lemma ARTop.isHSIntegrand (hA : ARTop P ℱ e Mt Ct S W) (t : ℝ) :
    IsHSIntegrand P ℱ t (PhiRT e S) := by
  refine ⟨fun k => hA.isProgressive_S (e k), fun r ω => ?_, ?_⟩
  · obtain ⟨Tr, hT, -⟩ := (hA.trace r ω).hasSum_basis e
    refine hT.summable.congr (fun k => ?_)
    simp only [PhiRT]
    rw [← real_inner_self_eq_norm_sq, (hA.sqrt r ω).sq]
  · have hpt : ∀ r ω, ∑' k, ‖PhiRT e S r ω k‖ₑ ^ 2 = ‖dST e Ct (r, ω)‖ₑ ^ 2 := by
      intro r ω
      have hnn : 0 ≤ trf e Ct (r, ω) := tsum_nonneg fun i => (hA.trace r ω).nonneg _
      obtain ⟨Tr, hT, -⟩ := (hA.trace r ω).hasSum_basis e
      have e1 : ∀ k, ‖PhiRT e S r ω k‖ₑ ^ 2 = ENNReal.ofReal (Ct r ω (e k) (e k)) := by
        intro k
        simp only [PhiRT]
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← real_inner_self_eq_norm_sq,
          (hA.sqrt r ω).sq]
      simp_rw [e1]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hA.trace r ω).nonneg _) hT.summable]
      simp only [dST]
      rw [enorm_sq_real, Real.sq_sqrt hnn]
      rfl
    unfold hsSqIntegralOn
    simp_rw [hpt]
    have hm := hA.measurable_dS
    have h1 : ∫⁻ p, ‖dST e Ct p‖ₑ ^ 2 ∂(tsm P t) =
        ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dST e Ct (r, ω)‖ₑ ^ 2) ∂P := by
      unfold tsm
      rw [lintegral_prod_symm' _ (by fun_prop : Measurable fun p : ℝ × Ω => ‖dST e Ct p‖ₑ ^ 2)]
    rw [← h1, HRS.lintegral_enorm_sq_eq_eLpNorm_sq hm.aestronglyMeasurable]
    exact ENNReal.pow_lt_top (hA.eLpNorm_dS t).lt_top

lemma ARTop.hsCovForm_PhiR (hA : ARTop P ℱ e Mt Ct S W) (r : ℝ) (ω : Ω) :
    hsCovForm (PhiRT e S r ω) = Ct r ω := by
  have hsum : Summable fun k => ‖PhiRT e S r ω k‖ ^ 2 := (hA.isHSIntegrand 0).summable r ω
  ext x y
  rw [hsCovForm_apply hsum]
  simp only [PhiRT]
  have := e.hasSum_inner_mul_inner (S r ω x) (S r ω y)
  rw [← (hA.sqrt r ω).sq x y, ← this.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [(hA.sqrt r ω).symm (e k) x, (hA.sqrt r ω).symm (e k) y, real_inner_comm (S r ω x) (e k),
    real_inner_comm (S r ω y) (e k)]

theorem ARTop.representation (hA : ARTop P ℱ e Mt Ct S W) :
    ∃ B : ℝ≥0 → Ω → ι → ℝ, IsCylindricalBrownian P ℱ B ∧
      IsHilbertItoIntegral P ℱ B (PhiRT e S) Mt := by
  obtain ⟨Y, hY⟩ := hA.exists_bdata
  exact ⟨Bfam Y, hY.brownian hA.complete, hA.isHilbertItoIntegral hY⟩

end Rep

end HRS.Uniform.Q48a
