import HRS.Prob.MRepAux7

/-!
# MREP, part 8: identification of `M̃` with the integral of `S` against the Brownian coordinates
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Cross

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {κ : Type*} [Fintype κ]

lemma ae_integrableOn_of_isProgressiveL2 {q : ℝ → Ω → κ → ℝ} (hq : IsProgressiveL2 P ℱ q) :
    ∀ᵐ ω ∂P, ∀ k t, IntegrableOn (fun r => q r ω k) (Set.Icc 0 t) := by
  have h1 : ∀ n : ℕ, ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc 0 (n : ℝ), ∑ k, ‖q s ω k‖ₑ ^ 2 < ∞ := by
    intro n
    have := hq.sq n
    unfold sqIntegralOn at this
    exact ae_lt_top (measurable_lintegral_sqSum' hq.prog n) this.ne
  rw [← ae_all_iff] at h1
  filter_upwards [h1] with ω hω k t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hmeas : Measurable fun r => q r ω k :=
    ((measurable_pi_apply k).comp (isProgressive_measurable_uncurry hq.prog)).comp
      (measurable_id.prodMk measurable_const)
  have hI : IntegrableOn (fun r => q r ω k) (Set.Icc 0 (n : ℝ)) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ r in Set.Icc 0 (n : ℝ), ‖q r ω k‖ₑ
        ≤ ∫⁻ r in Set.Icc 0 (n : ℝ), (1 + ∑ k, ‖q r ω k‖ₑ ^ 2) := by
          refine lintegral_mono fun r => ?_
          have h2 : ‖q r ω k‖ₑ ^ 2 ≤ ∑ k, ‖q r ω k‖ₑ ^ 2 :=
            Finset.single_le_sum (f := fun k => ‖q r ω k‖ₑ ^ 2) (fun _ _ => zero_le)
              (Finset.mem_univ k)
          rcases le_total ‖q r ω k‖ₑ 1 with h | h
          · exact h.trans le_self_add
          · exact (le_self_pow₀ h two_ne_zero).trans (h2.trans le_add_self)
      _ = (∫⁻ r in Set.Icc 0 (n : ℝ), (1 : ℝ≥0∞)) + ∫⁻ r in Set.Icc 0 (n : ℝ), ∑ k, ‖q r ω k‖ₑ ^ 2 := by
          rw [lintegral_add_right]
          exact (Finset.measurable_sum _ fun k _ =>
            (((measurable_pi_apply k).comp (isProgressive_measurable_uncurry hq.prog)).comp
              (measurable_id.prodMk measurable_const)).enorm.pow_const 2)
      _ < ∞ := by
          refine ENNReal.add_lt_top.2 ⟨?_, hω n⟩
          simp
  exact hI.mono_set (Set.Icc_subset_Icc le_rfl hn)

lemma Y_toNNReal (Y : κ → ℝ → Ω → ℝ) (hYz : ∀ k, ∀ t ≤ 0, ∀ ω, Y k t ω = 0) (k : κ) (x : ℝ)
    (ω : Ω) : Y k ((Real.toNNReal x : ℝ≥0) : ℝ) ω = Y k x ω := by
  rw [Real.coe_toNNReal']
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, hYz k 0 le_rfl ω, hYz k x h ω]
  · rw [max_eq_left h]

lemma elemIntegral_eq_nInt (Y : κ → ℝ → Ω → ℝ) (hYz : ∀ k, ∀ t ≤ 0, ∀ ω, Y k t ω = 0)
    (Ψ : SimpleIntegrand ℱ κ) (s : ℝ) (ω : Ω) :
    SimpleIntegrand.elemIntegral (fun t ω k => Y k (t : ℝ) ω) Ψ s ω =
      nInt (fun t ω (k : κ) => Y k t ω) id Ψ s ω := by
  unfold SimpleIntegrand.elemIntegral nInt
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [id]
  rw [Y_toNNReal Y hYz, Y_toNNReal Y hYz]

theorem cross_ito (hℱ : IsCompleteFiltration P ℱ) (Y : κ → ℝ → Ω → ℝ)
    (hYz : ∀ k, ∀ t ≤ 0, ∀ ω, Y k t ω = 0)
    (hW : IsBrownianFiltration P ℱ (fun t ω k => Y k (t : ℝ) ω))
    (hYm : ∀ k, Martingale (Y k) ℱ P) (hY2 : ∀ k t, MemLp (Y k t) 2 P)
    {V : ℝ → Ω → ℝ} (hV : Martingale V ℱ P) (hV2 : ∀ t, MemLp (V t) 2 P)
    {q : ℝ → Ω → κ → ℝ} (hq : IsProgressiveL2 P ℱ q)
    (hΛ : ∀ k, Martingale (fun t ω => Y k t ω * V t ω - ∫ r in Set.Icc 0 t, q r ω k) ℱ P)
    {ψ : ℝ → Ω → κ → ℝ} (hψ : IsProgressiveL2 P ℱ ψ) {J : ℝ → Ω → ℝ}
    (hJ : IsItoIntegral P ℱ (fun t ω k => Y k (t : ℝ) ω) ψ J) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∫ ω, J τ ω * V τ ω ∂P = ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k, ψ r ω k * q r ω k) ∂P := by
  classical
  set W : ℝ≥0 → Ω → κ → ℝ := fun t ω k => Y k (t : ℝ) ω with hWdef
  obtain ⟨Ψ, hΨ⟩ := exists_simple_approx P ℱ ψ hψ.prog τ (hψ.sq τ)
  have hqm : ∀ k, Measurable fun p : ℝ × Ω => q p.1 p.2 k := fun k =>
    (measurable_pi_apply k).comp (isProgressive_measurable_uncurry hq.prog)
  have hel : ∀ n, ∫ ω, (Ψ n).elemIntegral W τ ω * V τ ω ∂P =
      ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k, (Ψ n).toFun r ω k * q r ω k) ∂P := by
    intro n
    have hm := martingale_nInt_mul hℱ (N := fun t ω (k : κ) => Y k t ω) (fun k => hYm k)
      (fun t k => hY2 k t) id (Ψ n) hV hV2 (q := fun k r ω => q r ω k) hqm
      (ae_integrableOn_of_isProgressiveL2 hq) hΛ
    have h0 := hm.setIntegral_eq hτ (MeasurableSet.univ)
    simp only [Measure.restrict_univ] at h0
    have hA : Integrable (fun ω => nInt (fun t ω (k : κ) => Y k t ω) id (Ψ n) τ ω * V τ ω) P :=
      (memLp_nInt (fun t k => hY2 k t) id (Ψ n) τ).integrable_mul (hV2 τ)
    have hfτ := hm.integrable τ
    have hB : Integrable (fun ω => ∫ r in Set.Icc 0 τ, ∑ k, (Ψ n).toFun r ω k * q r ω k) P := by
      have := hA.sub hfτ
      refine this.congr (ae_of_all _ fun ω => ?_)
      simp
    have hz : ∫ ω, (nInt (fun t ω (k : κ) => Y k t ω) id (Ψ n) 0 ω * V 0 ω -
        ∫ r in Set.Icc 0 0, ∑ k, (Ψ n).toFun r ω k * q r ω k) ∂P = 0 := by
      simp [nInt_of_nonpos _ _ _ (le_refl (0:ℝ))]
    rw [hz] at h0
    have h1 : ∫ ω, (nInt (fun t ω (k : κ) => Y k t ω) id (Ψ n) τ ω * V τ ω -
        ∫ r in Set.Icc 0 τ, ∑ k, (Ψ n).toFun r ω k * q r ω k) ∂P =
        ∫ ω, nInt (fun t ω (k : κ) => Y k t ω) id (Ψ n) τ ω * V τ ω ∂P -
          ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k, (Ψ n).toFun r ω k * q r ω k) ∂P :=
      integral_sub hA hB
    rw [h1] at h0
    have h2 : ∀ ω, (Ψ n).elemIntegral W τ ω = nInt (fun t ω (k : κ) => Y k t ω) id (Ψ n) τ ω :=
      fun ω => elemIntegral_eq_nInt Y hYz (Ψ n) τ ω
    simp_rw [h2]
    linarith
  have hJ2 : MemLp (J τ) 2 P := hJ.memLp hW hψ τ
  have hel2 : ∀ n, MemLp ((Ψ n).elemIntegral W τ) 2 P := fun n =>
    SimpleIntegrand.memLp_elemIntegral hW (Ψ n) τ 2 (by norm_num)
  have h1 := tendsto_toLp_of_tendsto_lintegral hel2 hJ2 (hJ.approx τ hτ Ψ hΨ)
  have h2 := h1.inner (𝕜 := ℝ) (tendsto_const_nhds (x := (hV2 τ).toLp (V τ)))
  have h3 := (tendsto_embL2_of_isApprox hψ (Ψ := Ψ) (t := τ) hΨ).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := embL2 hq τ))
  have h4 : ∀ n, inner ℝ ((hel2 n).toLp ((Ψ n).elemIntegral W τ)) ((hV2 τ).toLp (V τ)) =
      inner ℝ (embL2 (IsProgressiveL2.simple P (Ψ n)) τ) (embL2 hq τ) := by
    intro n
    rw [inner_toLp, inner_embL2, hel n]
  simp_rw [h4] at h2
  have h5 := tendsto_nhds_unique h2 h3
  rw [inner_toLp, inner_embL2] at h5
  exact h5

end Cross


section Ident
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {T : ℝ} {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ} {Y : ι → ℝ → Ω → ℝ}

/-- A progressive process cut off after `T` is progressive. -/
lemma isProgressive_ite_le {β : Type*} [MeasurableSpace β] {f : ℝ → Ω → β}
    (hf : IsProgressive ℱ f) (T : ℝ) (c : β) :
    IsProgressive ℱ (fun r ω => if r ≤ T then f r ω else c) := by
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  have h1 : Measurable fun p : Set.Iic i × Ω => f p.1 p.2 := hf i
  exact Measurable.ite
    (measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_const) h1 measurable_const

/-- The coordinates `1_{r ≤ T} ⟨e_k, S x⟩`. -/
def cx (e : HilbertBasis ι ℝ H) (T : ℝ) (S : ℝ → Ω → H →L[ℝ] H) (x : H) (k : ι) : ℝ → Ω → ℝ :=
  fun r ω => if r ≤ T then inner ℝ (e k) (S r ω x) else 0

lemma ARData.isProgressive_cx (hA : ARData P ℱ e T Mt Ct S W) (x : H) (k : ι) :
    IsProgressive ℱ (cx e T S x k) := by
  have h := isProgressive_ite_le (hA.Sprog x (e k)) T 0
  have : cx e T S x k = fun r ω => if r ≤ T then inner ℝ (S r ω x) (e k) else 0 := by
    funext r ω; unfold cx; simp only [real_inner_comm]
  rw [this]; exact h

lemma ARData.hasSum_cx_sq (hA : ARData P ℱ e T Mt Ct S W) (x : H) (r : ℝ) (ω : Ω) :
    HasSum (fun k => cx e T S x k r ω * cx e T S x k r ω) (if r ≤ T then Ct r ω x x else 0) := by
  by_cases h : r ≤ T
  · have := e.hasSum_inner_mul_inner (S r ω x) (S r ω x)
    simp only [cx, h, if_true]
    rw [← (hA.sqrt r ω).sq x x]
    convert this using 2 with k
    rw [real_inner_comm (S r ω x) (e k)]
  · simp [cx, h]

lemma ARData.sum_cx_sq_le (hA : ARData P ℱ e T Mt Ct S W) (x : H) (r : ℝ) (ω : Ω) (s : Finset ι) :
    ∑ k ∈ s, cx e T S x k r ω * cx e T S x k r ω ≤ dS e T Ct (r, ω) ^ 2 * ‖x‖ ^ 2 := by
  have h1 := (hA.hasSum_cx_sq x r ω)
  have h2 : ∑ k ∈ s, cx e T S x k r ω * cx e T S x k r ω ≤ if r ≤ T then Ct r ω x x else 0 :=
    sum_le_hasSum s (fun k _ => mul_self_nonneg _) h1
  refine h2.trans ?_
  by_cases h : r ≤ T
  · simp only [h, if_true, dS]
    have hnn : 0 ≤ trf e Ct (r, ω) := tsum_nonneg fun i => (hA.trace r ω).nonneg _
    rw [Real.sq_sqrt hnn, ← (hA.sqrt r ω).sq x x, real_inner_self_eq_norm_sq]
    have := hA.norm_S_le r ω x
    calc ‖S r ω x‖ ^ 2 ≤ (Real.sqrt (trf e Ct (r, ω)) * ‖x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = trf e Ct (r, ω) * ‖x‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hnn]
  · simp [h, dS]

lemma enorm_sq_real (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

lemma ARData.integrable_dS_sq (hA : ARData P ℱ e T Mt Ct S W) (t : ℝ) :
    Integrable (fun p : ℝ × Ω => dS e T Ct p ^ 2) (tsm P t) :=
  by
  have hmem : MemLp (dS e T Ct) 2 (tsm P t) :=
    (hA.eLpNorm_dS t).lt_top
  exact hmem.integrable_sq

lemma ARData.isProgressiveL2_cx (hA : ARData P ℱ e T Mt Ct S W) (x : H) (s : Finset ι) :
    IsProgressiveL2 P ℱ (fun r ω (k : s) => cx e T S x k r ω) := by
  refine ⟨isProgressive_pi (fun k => hA.isProgressive_cx x k.1), fun t => ?_⟩
  unfold sqIntegralOn
  have hm := hA.measurable_dS
  have hpt : ∀ r ω, ∑ k : s, ‖cx e T S x k r ω‖ₑ ^ 2 ≤ ‖dS e T Ct (r, ω)‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := by
    intro r ω
    rw [sum_enorm_sq_eq_ofReal (fun k : s => cx e T S x k r ω)]
    have h1 : ∑ k : s, cx e T S x k r ω ^ 2 ≤ dS e T Ct (r, ω) ^ 2 * ‖x‖ ^ 2 := by
      have := hA.sum_cx_sq_le x r ω s
      have h0 : ∑ k : s, cx e T S x k r ω ^ 2 = ∑ k ∈ s, cx e T S x k r ω * cx e T S x k r ω := by
        rw [Finset.sum_coe_sort s (fun k => cx e T S x k r ω ^ 2)]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h0]; exact this
    have e1 := enorm_sq_real (dS e T Ct (r, ω))
    have e2 := enorm_sq_real ‖x‖
    rw [enorm_norm] at e2
    calc ENNReal.ofReal (∑ k : s, cx e T S x k r ω ^ 2)
        ≤ ENNReal.ofReal (dS e T Ct (r, ω) ^ 2 * ‖x‖ ^ 2) := ENNReal.ofReal_le_ofReal h1
      _ = ‖dS e T Ct (r, ω)‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), ← e1, ← e2]
  have hfin : (∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dS e T Ct (r, ω)‖ₑ ^ 2) ∂P) ≠ ∞ := by
    have h1 : ∫⁻ p, ‖dS e T Ct p‖ₑ ^ 2 ∂(tsm P t) =
        ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dS e T Ct (r, ω)‖ₑ ^ 2) ∂P := by
      unfold tsm
      rw [lintegral_prod_symm' _ (by fun_prop : Measurable fun p : ℝ × Ω => ‖dS e T Ct p‖ₑ ^ 2)]
    rw [← h1, HRS.lintegral_enorm_sq_eq_eLpNorm_sq hm.aestronglyMeasurable]
    exact (ENNReal.pow_lt_top (hA.eLpNorm_dS t).lt_top).ne
  have hx : ‖x‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top enorm_ne_top
  calc (∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ∑ k : s, ‖cx e T S x k r ω‖ₑ ^ 2) ∂P)
      ≤ ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dS e T Ct (r, ω)‖ₑ ^ 2 * ‖x‖ₑ ^ 2) ∂P :=
        lintegral_mono fun ω => lintegral_mono fun r => hpt r ω
    _ = (∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖dS e T Ct (r, ω)‖ₑ ^ 2) ∂P) * ‖x‖ₑ ^ 2 := by
        simp_rw [lintegral_mul_const' _ _ hx]
    _ < ∞ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hfin) (lt_top_iff_ne_top.2 hx)


/-- The properties of the Brownian coordinates produced by `ARData.exists_Bhat`. -/
structure BData (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (e : HilbertBasis ι ℝ H) (T : ℝ)
    (Mt : ℝ → Ω → H) (S : ℝ → Ω → H →L[ℝ] H) (Y : ι → ℝ → Ω → ℝ) : Prop where
  cont : ∀ k ω, Continuous fun t => Y k t ω
  zero : ∀ k, ∀ t ≤ 0, ∀ ω, Y k t ω = 0
  adapted : ∀ k t, Measurable[ℱ t] (Y k t)
  mart : ∀ k, Martingale (Y k) ℱ P
  sq : ∀ k t, MemLp (Y k t) 2 P
  qv : ∀ k l, Martingale (fun t ω => Y k t ω * Y l t ω - if k = l then max t 0 else 0) ℱ P
  cross : ∀ k (x : H), Martingale (fun t ω => Y k t ω * inner ℝ (Mt t ω) x -
        ∫ r in Set.Icc 0 t, (if r ≤ T then inner ℝ (e k) (S r ω x) else 0)) ℱ P

theorem ARData.exists_bdata (hA : ARData P ℱ e T Mt Ct S W) : ∃ Y, BData P ℱ e T Mt S Y := by
  obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7⟩ := hA.exists_Bhat
  exact ⟨Y, ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩

theorem BData.brownian (hY : BData P ℱ e T Mt S Y) (hℱ : IsCompleteFiltration P ℱ) :
    IsCylindricalBrownian P ℱ (Bfam Y) :=
  isCylindricalBrownian_of_Y hℱ Y hY.cont hY.zero hY.adapted hY.mart hY.qv

lemma lintegral_enorm_sq_eq_ofReal_integral {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, f ω * f ω ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal (f := fun ω => f ω * f ω) (hf.integrable_mul hf)
    (ae_of_all _ fun ω => mul_self_nonneg _)]
  refine lintegral_congr fun ω => ?_
  rw [enorm_sq_real, sq]

lemma ARData.integral_sq_V (hA : ARData P ℱ e T Mt Ct S W) (x : H) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∫ ω, inner ℝ (Mt τ ω) x * inner ℝ (Mt τ ω) x ∂P =
      ∫ ω, (∫ r in Set.Icc 0 τ, (if r ≤ T then Ct r ω x x else 0)) ∂P := by
  have hm := hA.cov x x
  have h0 := hm.setIntegral_eq hτ (MeasurableSet.univ)
  simp only [Measure.restrict_univ] at h0
  have hA2 : Integrable (fun ω => inner ℝ (Mt τ ω) x * inner ℝ (Mt τ ω) x) P :=
    (hA.sq τ x).integrable_mul (hA.sq τ x)
  have hfτ := hm.integrable τ
  have hB : Integrable (fun ω => ∫ r in Set.Icc 0 τ, (if r ≤ T then Ct r ω x x else 0)) P := by
    have := hA2.sub hfτ
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp
  have hz : ∫ ω, (inner ℝ (Mt 0 ω) x * inner ℝ (Mt 0 ω) x -
      ∫ r in Set.Icc 0 0, (if r ≤ T then Ct r ω x x else 0)) ∂P = 0 := by
    simp [hA.zero 0 le_rfl]
  rw [hz, integral_sub hA2 hB] at h0
  linarith


lemma iter_eq_tsm {f : ℝ × Ω → ℝ} (τ : ℝ) (hf : Integrable f (tsm P τ)) :
    ∫ ω, (∫ r in Set.Icc 0 τ, f (r, ω)) ∂P = ∫ p, f p ∂(tsm P τ) := by
  unfold tsm at hf ⊢
  rw [integral_prod_symm f hf]

lemma ARData.measurable_cx (hA : ARData P ℱ e T Mt Ct S W) (x : H) (k : ι) :
    Measurable fun p : ℝ × Ω => cx e T S x k p.1 p.2 :=
  isProgressive_measurable_uncurry (hA.isProgressive_cx x k)

lemma ARData.measurable_Cxx (hA : ARData P ℱ e T Mt Ct S W) (x : H) :
    Measurable fun p : ℝ × Ω => (if p.1 ≤ T then Ct p.1 p.2 x x else 0) :=
  Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (isProgressive_measurable_uncurry (hA.Cprog x x)) measurable_const

theorem ARData.tendsto_partial (hA : ARData P ℱ e T Mt Ct S W) (x : H) (τ : ℝ) :
    Tendsto (fun s : Finset ι => ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cx e T S x k r ω * cx e T S x k r ω) ∂P)
      atTop (𝓝 (∫ ω, (∫ r in Set.Icc 0 τ, (if r ≤ T then Ct r ω x x else 0)) ∂P)) := by
  have hbd : Integrable (fun p : ℝ × Ω => dS e T Ct p ^ 2 * ‖x‖ ^ 2) (tsm P τ) :=
    (hA.integrable_dS_sq τ).mul_const _
  have hgm : ∀ s : Finset ι, Measurable fun p : ℝ × Ω => ∑ k ∈ s, cx e T S x k p.1 p.2 * cx e T S x k p.1 p.2 :=
    fun s => Finset.measurable_sum _ fun k _ => (hA.measurable_cx x k).mul (hA.measurable_cx x k)
  have hgb : ∀ s : Finset ι, ∀ p : ℝ × Ω,
      ‖∑ k ∈ s, cx e T S x k p.1 p.2 * cx e T S x k p.1 p.2‖ ≤ dS e T Ct p ^ 2 * ‖x‖ ^ 2 := by
    intro s p
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => mul_self_nonneg _)]
    exact hA.sum_cx_sq_le x p.1 p.2 s
  have hgi : ∀ s : Finset ι, Integrable (fun p : ℝ × Ω =>
      ∑ k ∈ s, cx e T S x k p.1 p.2 * cx e T S x k p.1 p.2) (tsm P τ) := fun s =>
    hbd.mono' (hgm s).aestronglyMeasurable (ae_of_all _ (hgb s))
  have hli : Integrable (fun p : ℝ × Ω => (if p.1 ≤ T then Ct p.1 p.2 x x else 0)) (tsm P τ) := by
    refine hbd.mono' (hA.measurable_Cxx x).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    have := (hA.hasSum_cx_sq x p.1 p.2)
    have h1 : ∀ s : Finset ι, ∑ k ∈ s, cx e T S x k p.1 p.2 * cx e T S x k p.1 p.2 ≤
        dS e T Ct p ^ 2 * ‖x‖ ^ 2 := fun s => hA.sum_cx_sq_le x p.1 p.2 s
    have h2 := le_of_tendsto' this h1
    rw [Real.norm_of_nonneg ?_]
    · exact h2
    · by_cases h : p.1 ≤ T
      · simp only [h, if_true]; exact (hA.trace p.1 p.2).nonneg x
      · simp [h]
  have h1 : ∀ s : Finset ι, ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cx e T S x k r ω * cx e T S x k r ω) ∂P =
      ∫ p, ∑ k ∈ s, cx e T S x k p.1 p.2 * cx e T S x k p.1 p.2 ∂(tsm P τ) := fun s =>
    iter_eq_tsm (f := fun p : ℝ × Ω => ∑ k ∈ s, cx e T S x k p.1 p.2 * cx e T S x k p.1 p.2) τ (hgi s)
  have h2 : ∫ ω, (∫ r in Set.Icc 0 τ, (if r ≤ T then Ct r ω x x else 0)) ∂P =
      ∫ p, (if p.1 ≤ T then Ct p.1 p.2 x x else 0) ∂(tsm P τ) :=
    iter_eq_tsm (f := fun p : ℝ × Ω => (if p.1 ≤ T then Ct p.1 p.2 x x else 0)) τ hli
  simp_rw [h1]
  rw [h2]
  refine tendsto_integral_filter_of_dominated_convergence (fun p => dS e T Ct p ^ 2 * ‖x‖ ^ 2)
    (Eventually.of_forall fun s => (hgm s).aestronglyMeasurable)
    (Eventually.of_forall fun s => ae_of_all _ (hgb s)) hbd (ae_of_all _ fun p => ?_)
  exact hA.hasSum_cx_sq x p.1 p.2


theorem ARData.key_identity (hA : ARData P ℱ e T Mt Ct S W) (hY : BData P ℱ e T Mt S Y) (x : H)
    (τ : ℝ) (hτ : 0 ≤ τ) (s : Finset ι) :
    ∫⁻ ω, ‖itoIntegral P ℱ (fun t ω (k : s) => Bfam Y t ω k)
        (fun r ω (k : s) => cx e T S x k r ω) τ ω - inner ℝ (Mt τ ω) x‖ₑ ^ 2 ∂P =
      ENNReal.ofReal ((∫ ω, (∫ r in Set.Icc 0 τ, (if r ≤ T then Ct r ω x x else 0)) ∂P) -
        ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cx e T S x k r ω * cx e T S x k r ω) ∂P) := by
  classical
  set q : ℝ → Ω → s → ℝ := fun r ω (k : s) => cx e T S x k r ω with hqdef
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
  have hsum : ∀ r ω, ∑ k : s, q r ω k * q r ω k = ∑ k ∈ s, cx e T S x k r ω * cx e T S x k r ω :=
    fun r ω => Finset.sum_coe_sort s (fun k => cx e T S x k r ω * cx e T S x k r ω)
  simp_rw [hsum] at hJV hJJ
  set F := ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cx e T S x k r ω * cx e T S x k r ω) ∂P with hF
  set A := ∫ ω, (∫ r in Set.Icc 0 τ, (if r ≤ T then Ct r ω x x else 0)) ∂P with hA'
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

theorem ARData.isHilbertItoIntegral (hA : ARData P ℱ e T Mt Ct S W) (hY : BData P ℱ e T Mt S Y) :
    IsHilbertItoIntegral P ℱ (Bfam Y) (fun r ω j => if r ≤ T then S r ω (e j) else 0) Mt := by
  refine ⟨hA.cont, hA.adapted, hA.zero, fun τ hτ x => ?_⟩
  have hint : ∀ s : Finset ι, (fun r ω (k : s) => inner ℝ ((fun r ω j => if r ≤ T then S r ω (e j) else 0) r ω k) x) =
      fun r ω (k : s) => cx e T S x k r ω := by
    intro s
    funext r ω k
    by_cases h : r ≤ T
    · simp only [cx, h, if_true]
      exact (hA.sqrt r ω).symm (e k) x
    · simp [cx, h]
  have hlim : Tendsto (fun s : Finset ι => ENNReal.ofReal
      ((∫ ω, (∫ r in Set.Icc 0 τ, (if r ≤ T then Ct r ω x x else 0)) ∂P) -
        ∫ ω, (∫ r in Set.Icc 0 τ, ∑ k ∈ s, cx e T S x k r ω * cx e T S x k r ω) ∂P)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∫ ω, (∫ r in Set.Icc 0 τ, (if r ≤ T then Ct r ω x x else 0)) ∂P)).sub
      (hA.tendsto_partial x τ)
    have := ENNReal.tendsto_ofReal h
    simpa using this
  refine hlim.congr (fun s => ?_)
  rw [hint s]
  exact (hA.key_identity hY x τ hτ s).symm

end Ident

end HRS.MRep
