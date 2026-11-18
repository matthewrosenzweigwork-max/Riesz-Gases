import HRS.Prob.MRepAux6

/-!
# MREP, part 7: the Brownian motion `B`

`B^k = ∫ G^k dN` is a continuous martingale with `⟨B^k, B^l⟩_t = δ_{kl} t` and cross-covariation `⟨B^k, M̃^x⟩ = ∫ 1_{r ≤ T} ⟨e_k, S x⟩`;
by Lévy it is a cylindrical Brownian motion.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Brown
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {T : ℝ} {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

lemma inner_Gk (Q : ℝ → Ω → H →L[ℝ] H) (e : HilbertBasis ι ℝ H) (T : ℝ)
    (hsym : ∀ r ω x y, inner ℝ (Q r ω x) y = inner ℝ x (Q r ω y))
    (hid : ∀ r ω x, Q r ω (Q r ω x) = Q r ω x) (k l : ι) (r : ℝ) (ω : Ω) :
    inner ℝ (Gk e T Q k r ω) (Gk e T Q l r ω) = if k = l then 1 else 0 := by
  have hel : inner ℝ (e k) (e l) = if k = l then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.1 e.orthonormal k l
  unfold Gk
  by_cases h : r ≤ T
  · simp only [h, if_true, WithLp.prod_inner_apply]
    have h1 : inner ℝ (Q r ω (e k)) (Q r ω (e l)) = inner ℝ (e k) (Q r ω (e l)) := by
      rw [hsym, hid]
    have h2 : inner ℝ (Q r ω (e k)) (e l) = inner ℝ (e k) (Q r ω (e l)) := hsym r ω _ _
    have h3 : inner ℝ (e k - Q r ω (e k)) (e l - Q r ω (e l)) = inner ℝ (e k) (e l) -
        inner ℝ (e k) (Q r ω (e l)) - inner ℝ (Q r ω (e k)) (e l) +
        inner ℝ (Q r ω (e k)) (Q r ω (e l)) := by
      simp only [inner_sub_left, inner_sub_right]; ring
    rw [h3, h1, h2, hel]; ring
  · simp [h, WithLp.prod_inner_apply, hel]

lemma ARData.ae_integrableOn_trf (hA : ARData P ℱ e T Mt Ct S W) :
    ∀ᵐ ω ∂P, IntegrableOn (fun r => trf e Ct (r, ω)) (Set.Icc 0 T) := by
  have hm : Measurable fun p : ℝ × Ω => ENNReal.ofReal (trf e Ct p) :=
    ENNReal.measurable_ofReal.comp hA.measurable_trf
  have h1 : Measurable fun ω => ∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (trf e Ct (r, ω)) := by
    have := hm.lintegral_prod_left' (μ := volume.restrict (Set.Icc 0 T))
    exact this
  have h2 : ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (trf e Ct (r, ω)) < ∞ :=
    ae_lt_top h1 hA.Ctr
  filter_upwards [h2] with ω hω
  refine ⟨(hA.measurable_trf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (le_of_eq ?_) hω
  refine lintegral_congr fun r => ?_
  have hnn : 0 ≤ trf e Ct (r, ω) := tsum_nonneg fun i => (hA.trace r ω).nonneg _
  rw [Real.enorm_of_nonneg hnn]

/-- The vector `w = 1_{r ≤ T} (S x, 0)`. -/
def wz (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (x : H) : ℝ → Ω → WithLp 2 (H × H) :=
  fun r ω => WithLp.toLp 2 ((if r ≤ T then S r ω x else 0), (0 : H))

lemma ARData.measurable_wz (hA : ARData P ℱ e T Mt Ct S W) (x : H) :
    Measurable fun p : ℝ × Ω => wz T S x p.1 p.2 := by
  unfold wz
  have h1 : Measurable fun p : ℝ × Ω => (if p.1 ≤ T then S p.1 p.2 x else 0) :=
    Measurable.ite (measurableSet_le measurable_fst measurable_const)
      (hA.measurable_S_apply x) measurable_const
  exact (WithLp.measurable_toLp 2 (H × H)).comp (h1.prodMk measurable_const)

lemma ARData.eLpNorm_wz (hA : ARData P ℱ e T Mt Ct S W) (x : H) (t : ℝ) :
    eLpNorm (fun p : ℝ × Ω => wz T S x p.1 p.2) 2 (tsm P t) ≠ ∞ := by
  have h1 : eLpNorm (fun p : ℝ × Ω => wz T S x p.1 p.2) 2 (tsm P t) ≤
      eLpNorm (fun p : ℝ × Ω => ‖x‖ * dS e T Ct p) 2 (tsm P t) := by
    refine eLpNorm_mono_real (hA.measurable_wz x).aestronglyMeasurable (fun p => ?_)
    unfold wz dS
    by_cases h : p.1 ≤ T
    · simp only [h, if_true]
      have := hA.norm_S_le p.1 p.2 x
      calc ‖(WithLp.toLp 2 (S p.1 p.2 x, (0 : H)) : WithLp 2 (H × H))‖ ≤ ‖S p.1 p.2 x‖ + ‖(0 : H)‖ :=
            norm_toLp_le _ _
        _ ≤ ‖x‖ * Real.sqrt (trf e Ct p) := by rw [norm_zero, add_zero]; linarith
    · simp [h]
  refine ne_top_of_le_ne_top ?_ h1
  have : (fun p : ℝ × Ω => ‖x‖ * dS e T Ct p) = ‖x‖ • dS e T Ct := by funext p; simp
  rw [this, eLpNorm_const_smul]
  exact ENNReal.mul_ne_top enorm_ne_top (hA.eLpNorm_dS t)

lemma inner_vz_wz_ll (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (x : H) (r : ℝ)
    (ω : Ω) (i : ι) : inner ℝ (vz e T S r ω (Sum.inl i)) (wz T S x r ω) =
      if r ≤ T then inner ℝ (S r ω (e i)) (S r ω x) else 0 := by
  by_cases h : r ≤ T <;> simp [vz, wz, h, WithLp.prod_inner_apply]

lemma inner_vz_wz_rr (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (x : H) (r : ℝ)
    (ω : Ω) (j : ι) : inner ℝ (vz e T S r ω (Sum.inr j)) (wz T S x r ω) = 0 := by
  simp [vz, wz, WithLp.prod_inner_apply]

lemma inner_Gk_wz (Q : ℝ → Ω → H →L[ℝ] H) (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H)
    (hsym : ∀ r ω x y, inner ℝ (Q r ω x) y = inner ℝ x (Q r ω y))
    (hQS : ∀ r ω x, Q r ω (S r ω x) = S r ω x) (k : ι) (x : H) (r : ℝ) (ω : Ω) :
    inner ℝ (Gk e T Q k r ω) (wz T S x r ω) = if r ≤ T then inner ℝ (e k) (S r ω x) else 0 := by
  by_cases h : r ≤ T
  · simp only [Gk, wz, h, if_true, WithLp.prod_inner_apply, inner_zero_right, add_zero]
    rw [hsym, hQS]
  · simp [Gk, wz, h, WithLp.prod_inner_apply]

lemma ARData.ae_integrableOn_inner_vz_wz (hA : ARData P ℱ e T Mt Ct S W) (x : H) :
    ∀ᵐ ω ∂P, ∀ (a : ι ⊕ ι) (t : ℝ), IntegrableOn (fun r => inner ℝ (vz e T S r ω a)
      (wz T S x r ω)) (Set.Icc 0 t) := by
  filter_upwards [hA.ae_integrableOn_trf] with ω hω a t
  rcases a with i | j
  · have hbound : IntegrableOn ((Set.Iic T).indicator (fun r => trf e Ct (r, ω) * ‖x‖))
        (Set.Icc 0 t) volume := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic]
      have h2 : IntegrableOn (fun r => trf e Ct (r, ω) * ‖x‖) (Set.Iic T ∩ Set.Icc 0 t) volume :=
        IntegrableOn.mono_set (hω.mul_const ‖x‖) (fun r hr => ⟨hr.2.1, hr.1⟩)
      rwa [IntegrableOn, Measure.restrict_restrict measurableSet_Iic]
    refine Integrable.mono' hbound ?_ (Eventually.of_forall fun r => ?_)
    · have hm : Measurable fun r : ℝ => inner ℝ (vz e T S r ω (Sum.inl i)) (wz T S x r ω) :=
        (meas_inner (hA.measurable_vz _) (hA.measurable_wz x)).comp
          (measurable_id.prodMk measurable_const)
      exact hm.aestronglyMeasurable
    · rw [inner_vz_wz_ll]
      by_cases h : r ≤ T
      · simp only [h, if_true, Set.indicator_of_mem (Set.mem_Iic.2 h)]
        have h1 := hA.norm_S_le r ω (e i)
        have h2 := hA.norm_S_le r ω x
        rw [e.orthonormal.norm_eq_one i, mul_one] at h1
        have hnn : 0 ≤ trf e Ct (r, ω) := tsum_nonneg fun i => (hA.trace r ω).nonneg _
        calc ‖inner ℝ (S r ω (e i)) (S r ω x)‖ ≤ ‖S r ω (e i)‖ * ‖S r ω x‖ := norm_inner_le_norm _ _
          _ ≤ Real.sqrt (trf e Ct (r, ω)) * (Real.sqrt (trf e Ct (r, ω)) * ‖x‖) := by gcongr
          _ = trf e Ct (r, ω) * ‖x‖ := by
              rw [← mul_assoc, Real.mul_self_sqrt hnn]
      · simp [h]
  · simp only [inner_vz_wz_rr, integrableOn_zero]

lemma ARData.measurable_Gk (hA : ARData P ℱ e T Mt Ct S W) {Q : ℝ → Ω → H →L[ℝ] H}
    (hQprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (Q r ω x) y)) (k : ι) :
    Measurable fun p : ℝ × Ω => Gk e T Q k p.1 p.2 := by
  unfold Gk
  have h1 := measurable_Q_apply hA hQprog (e k)
  have hc : MeasurableSet {p : ℝ × Ω | p.1 ≤ T} := measurableSet_le measurable_fst measurable_const
  refine (WithLp.measurable_toLp 2 (H × H)).comp (Measurable.prodMk ?_ ?_)
  · exact Measurable.ite hc h1 measurable_const
  · exact Measurable.ite hc (measurable_const.sub h1) measurable_const

theorem ARData.exists_Bhat (hA : ARData P ℱ e T Mt Ct S W) :
    ∃ Y : ι → ℝ → Ω → ℝ,
      (∀ k ω, Continuous fun t => Y k t ω) ∧ (∀ k, ∀ t ≤ 0, ∀ ω, Y k t ω = 0) ∧
      (∀ k t, Measurable[ℱ t] (Y k t)) ∧ (∀ k, Martingale (Y k) ℱ P) ∧ (∀ k t, MemLp (Y k t) 2 P) ∧
      (∀ k l, Martingale (fun t ω => Y k t ω * Y l t ω - if k = l then max t 0 else 0) ℱ P) ∧
      (∀ k (x : H), Martingale (fun t ω => Y k t ω * inner ℝ (Mt t ω) x -
        ∫ r in Set.Icc 0 t, (if r ≤ T then inner ℝ (e k) (S r ω x) else 0)) ℱ P) := by
  classical
  have hN := hA.isNoiseK
  obtain ⟨Q, hQlim, hQsym, hQid, hQS, hQprog⟩ :=
    exists_progressive_proj e Ct hA.trace S hA.sqrt hA.Cprog hA.Sprog
  have hex : ∀ k, ∃ Y : ℝ → Ω → ℝ, ∃ seq : ApproxSeq P ℱ (vz e T S) (Gk e T Q k),
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
    have e1 : ∀ t ω, ∫ r in Set.Icc 0 t, inner ℝ (Gk e T Q k r ω) (Gk e T Q l r ω) =
        if k = l then max t 0 else 0 := by
      intro t ω
      have : ∀ r, inner ℝ (Gk e T Q k r ω) (Gk e T Q l r ω) = if k = l then 1 else 0 :=
        fun r => inner_Gk Q e T hQsym hQid k l r ω
      simp_rw [this]
      by_cases hkl : k = l
      · simp [hkl, Real.volume_real_Icc]
      · simp [hkl]
    have e2 : (fun t ω => Y k t ω * Y l t ω - ∫ r in Set.Icc 0 t,
        inner ℝ (Gk e T Q k r ω) (Gk e T Q l r ω)) =
        fun t ω => Y k t ω * Y l t ω - if k = l then max t 0 else 0 := by
      funext t ω; rw [e1]
    rw [e2] at h
    exact h
  · intro k x
    have hV : Martingale (fun t ω => inner ℝ (Mt t ω) x) ℱ P := hA.mart x
    have hVw : ∀ a : ι ⊕ ι, Martingale (fun t ω => Nz e Mt W t ω a * inner ℝ (Mt t ω) x -
        ∫ r in Set.Icc 0 t, inner ℝ (vz e T S r ω a) (wz T S x r ω)) ℱ P := by
      intro a
      rcases a with i | j
      · have e1 : ∀ t ω, ∫ r in Set.Icc 0 t, inner ℝ (vz e T S r ω (Sum.inl i)) (wz T S x r ω) =
            ∫ r in Set.Icc 0 t, (if r ≤ T then Ct r ω (e i) x else 0) := by
          intro t ω
          refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
          rw [inner_vz_wz_ll, (hA.sqrt r ω).sq]
        have e2 : (fun t ω => Nz e Mt W t ω (Sum.inl i) * inner ℝ (Mt t ω) x -
            ∫ r in Set.Icc 0 t, inner ℝ (vz e T S r ω (Sum.inl i)) (wz T S x r ω)) =
            fun t ω => inner ℝ (Mt t ω) (e i) * inner ℝ (Mt t ω) x -
              ∫ r in Set.Icc 0 t, (if r ≤ T then Ct r ω (e i) x else 0) := by
          funext t ω; simp only [Nz, Sum.elim_inl]; rw [e1]
        rw [e2]
        exact hA.cov _ _
      · have e2 : (fun t ω => Nz e Mt W t ω (Sum.inr j) * inner ℝ (Mt t ω) x -
            ∫ r in Set.Icc 0 t, inner ℝ (vz e T S r ω (Sum.inr j)) (wz T S x r ω)) =
            fun t ω => inner ℝ (Mt t ω) x * ofNNRealTime W t ω j := by
          funext t ω
          simp only [Nz, Sum.elim_inr, inner_vz_wz_rr, integral_zero, sub_zero]
          ring
        rw [e2]
        exact hA.cross _ _
    have h := IsIntOf.cross hA.complete hN (hA.measurable_Gk hQprog k) (hY k) hV
      (fun t => hA.sq t x) (hA.measurable_wz x) (hA.eLpNorm_wz x)
      (hA.ae_integrableOn_inner_vz_wz x) hVw
    have e1 : ∀ t ω, ∫ r in Set.Icc 0 t, inner ℝ (Gk e T Q k r ω) (wz T S x r ω) =
        ∫ r in Set.Icc 0 t, (if r ≤ T then inner ℝ (e k) (S r ω x) else 0) := by
      intro t ω
      refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
      exact inner_Gk_wz Q e T S hQsym hQS k x r ω
    have e2 : (fun t ω => Y k t ω * inner ℝ (Mt t ω) x -
        ∫ r in Set.Icc 0 t, inner ℝ (Gk e T Q k r ω) (wz T S x r ω)) =
        fun t ω => Y k t ω * inner ℝ (Mt t ω) x -
          ∫ r in Set.Icc 0 t, (if r ≤ T then inner ℝ (e k) (S r ω x) else 0) := by
      funext t ω; rw [e1]
    rw [e2] at h
    exact h

/-- The real-time version of the Brownian family built from `Y`. -/
def Bfam (Y : ι → ℝ → Ω → ℝ) : ℝ≥0 → Ω → ι → ℝ := fun t ω k => Y k (t : ℝ) ω

lemma ofNNRealTime_Bfam (Y : ι → ℝ → Ω → ℝ) (hz : ∀ k, ∀ t ≤ 0, ∀ ω, Y k t ω = 0) (t : ℝ) (ω : Ω)
    (k : ι) : ofNNRealTime (Bfam Y) t ω k = Y k t ω := by
  simp only [ofNNRealTime_apply, Bfam, Real.coe_toNNReal']
  rcases le_total t 0 with h | h
  · rw [max_eq_right h, hz k 0 le_rfl ω, hz k t h ω]
  · rw [max_eq_left h]

theorem isCylindricalBrownian_of_Y (hℱ : IsCompleteFiltration P ℱ) (Y : ι → ℝ → Ω → ℝ)
    (hc : ∀ k ω, Continuous fun t => Y k t ω) (hz : ∀ k, ∀ t ≤ 0, ∀ ω, Y k t ω = 0)
    (had : ∀ k t, Measurable[ℱ t] (Y k t)) (hm : ∀ k, Martingale (Y k) ℱ P)
    (hqv : ∀ k l, Martingale (fun t ω => Y k t ω * Y l t ω - if k = l then max t 0 else 0) ℱ P) :
    IsCylindricalBrownian P ℱ (Bfam Y) := by
  intro s
  refine levy_characterization P ℱ hℱ (fun t ω (k : s) => Bfam Y t ω k.1) ?_ ?_ ?_ ?_ ?_
  · intro t
    exact (@measurable_pi_iff Ω s (fun _ => ℝ) (ℱ t) _ _).2 fun k => had k.1 t
  · intro ω
    funext k
    simp [Bfam, hz k.1 0 le_rfl ω]
  · intro ω
    exact continuous_pi fun k => (hc k.1 ω).comp NNReal.continuous_coe
  · intro k
    have : (fun (t : ℝ) ω => ofNNRealTime (fun t ω (k : s) => Bfam Y t ω k.1) t ω k) = Y k.1 := by
      funext t ω
      simp only [ofNNRealTime_apply]
      exact ofNNRealTime_Bfam Y hz t ω k.1
    rw [this]; exact hm k.1
  · intro k l
    have : (fun (t : ℝ) ω => ofNNRealTime (fun t ω (k : s) => Bfam Y t ω k.1) t ω k *
        ofNNRealTime (fun t ω (k : s) => Bfam Y t ω k.1) t ω l - if k = l then max t 0 else 0) =
        fun t ω => Y k.1 t ω * Y l.1 t ω - if k.1 = l.1 then max t 0 else 0 := by
      funext t ω
      have e1 : ofNNRealTime (fun t ω (k : s) => Bfam Y t ω k.1) t ω k = Y k.1 t ω :=
        ofNNRealTime_Bfam Y hz t ω k.1
      have e2 : ofNNRealTime (fun t ω (k : s) => Bfam Y t ω k.1) t ω l = Y l.1 t ω :=
        ofNNRealTime_Bfam Y hz t ω l.1
      rw [e1, e2]
      simp only [Subtype.ext_iff]
    rw [this]; exact hqv k.1 l.1

end Brown

end HRS.MRep
